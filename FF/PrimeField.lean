import YatimaStdLib.AddChain
import YatimaStdLib.Zmod

/-!
# Defining field instances with PrimeField

The following module provides a metaprogramming layer to define new Field instances with optmized
arithmetic.

The following syntax:
```
new_field <name> with
  prime: <num>
  generator: <num>
  root_of_unity: <num>
```
defines a new structure with name `<name>` representing a prime field of characteristic `prime`,
together with a specific multiplicative generator and optionally defined primitive root of unity.

The implementations used for field arithmetic are based on the optimizations coming from
Montgomery reduction and multiplication. The terminology used for PrimeFields is `wrap` to bring an
element into Montgomery form and `unwrap` to bring it out.

The rough idea is that, though `wrap` is as expensive as a usual modular reduction, subsequent
multiplications, exponentiations, inversions are computationally cheaper (the other field operations
incur no additional cost)

Generally the user shouldn't have to worry about the specifics about wrapping and unwrapping field
elements, but the `PrimeField.wrap` and `PrimeField.unwrap` functions are available to the end-user.

A typeclass for `PrimeField` is provided (and an instance is automatically generated using the above
syntax) with the following functionality:

* `PrimeField.wrap` and `PrimeField.unwrap` to manually deal with Montgomery form
* Pre-computed addchains for `p`, `p - 1 / 2`
* Efficient calculation of the Legendre symbol using `PrimeField.legendre` 
  (using a pre-computed `AddChain` for `p - 1 / 2`)
* Pre-computed 2-adicity for `p - 1`
* Fixed-base batched exponentiation using `PrimeField.batchedExp`
* Batched inversion using `PrimeField.batchedInv` (replaces `n` field inversions with 1 inversion and 
  `3n` field multiplications)
* Efficient implementation of the Tonelli-Shank algorithm for square roots using `PrimeField.sqrt?`
-/

section newfieldclass

class PrimeField (K : Type _) extends Field K where
  char : Nat
  content : Nat
  twoAdicity : Nat × Nat
  legAC : Array ChainStep
  frobAC : Array ChainStep
  wrap : K → K
  unwrap : K → K 
  natRepr : K → Nat
  batchedExp : K → Array Nat → Array K
  batchedInv : Array K → Array K    

end newfieldclass

section metaprogramming

open Lean Syntax

syntax (docComment)? "new_field" ident "with"
  "prime:" num
  "generator:" num
  ("root_of_unity:" num)? : command

macro_rules
  | `(command| $[$doc:docComment]? new_field $name:ident with
      prime: $p:num
      generator: $g:num
      $[root_of_unity: $u?:num]?) => do
    let pNat := p.getNat
    let gNat := g.getNat
    let (s, t) := (pNat - 1).get2Adicity

    let u := match u? with
      | some u => u
      | none =>
        let uNat := Nat.powMod pNat gNat t
        Lean.Syntax.mkNumLit s!"{uNat}"
    
    let deltaNat := Nat.powMod pNat gNat s

    -- Names here
    -- Pre-computed constants
    let prime := mkIdent `prime
    let content := mkIdent `content
    let r := mkIdent `r
    let rMask := mkIdent `rMask
    let pInv := mkIdent `pInv
    let zero := mkIdent `zero
    let one := mkIdent `one
    let legNum := mkIdent `legNum
    let frobAC := mkIdent `frobAC
    let legAC := mkIdent `legAC
    let twoAdicity := mkIdent `twoAdicity
    let generator := mkIdent `generator
    let rootOfUnity := mkIdent `rootOfUnity

    -- Montgomery functions
    let wrap := mkIdent `wrap
    let unwrap := mkIdent `unwrap
    let reduce := mkIdent `reduce
    let natRepr := mkIdent `natRepr
    
    -- Arithmetic operations
    let add := mkIdent `add
    let mul := mkIdent `mul
    let neg := mkIdent `neg
    let sub := mkIdent `sub
    let powAux := mkIdent `powAux
    let pow := mkIdent `pow
    let batchedExp := mkIdent `batchedExp
    let batchedInv := mkIdent `batchedInv
    let invAux := mkIdent `invAux
    let inv := mkIdent `inv
    let sqrt? := mkIdent `sqrt?
    let legendre := mkIdent `legendre
    let frob := mkIdent `frob


    -- Syntax creation here
    `(
      $[$doc:docComment]? structure $name where
        data : Nat
        wrapped : Bool := Bool.false

      namespace $name

      /-- The number of bits encodable by elements of the field -/
      def $content : Nat := $p |>.log2 |> (· + 1)

      /-- The wrapping `R` used in Montgomery arithmetic -/
      def $r : Nat := 2 ^ $content

      private def $rMask : Nat := $r - 1

      /-- Characteristic <-> number of elements of the prime field -/
      def $prime : Nat := $p

      private def $pInv : Int := Nat.xgcd $p $r |>.fst

      def $generator : $name := ⟨$g, false⟩

      def $rootOfUnity : $name := ⟨$u, false⟩

      /-- The unwrapped `0` of the field -/
      def $zero : $name := ⟨0, false⟩

      instance : OfNat $name (nat_lit 0) where
        ofNat := $zero

      /-- The unwrapped `1` of the field -/
      def $one : $name := ⟨1, false⟩

      instance : OfNat $name (nat_lit 1) where
        ofNat := $one

      instance : Coe Nat $name where
        coe n := ⟨n , false⟩

      instance {n : Nat} : OfNat $name n where
        ofNat := ⟨n, false⟩

      /-- `(p - 1) / 2` -/
      def $legNum : Nat := $p >>> 1
      
      open AddChain in
      /-- Pre-computed array of `ChainStep`s to calculate the Legendre symbol -/
      def $legAC : Array ChainStep := $(mkIdent `buildSteps) $ $legNum |>.minChain

      open AddChain in
      /-- Pre-computed array of `ChainStep`s to calculuate the Frobenius endomorphism -/
      def $frobAC : Array ChainStep := $(mkIdent `buildSteps) $ $p |>.minChain

      /-- Pre-computed `(s, d)` where `p = 1 + 2 ^ s * d` with `d` odd -/
      def $twoAdicity : Nat × Nat := Nat.get2Adicity <| $p - 1 

      /-- The Montgomery reduction algorithm -/
      def $reduce (x : Nat) : Nat :=
        let q := (x * $pInv) &&& $rMask
        match (x - q * $p) with
        | .ofNat n => n >>> $content
        | .negSucc n => $p - (n + 1) >>> $content

      /-- Bring a field element into Montgomery form -/
      def $wrap (x : $name) : $name := 
        if x.wrapped then x else ⟨x.data <<< $content |>.mod $p, true⟩

      /-- Bring a field element out of Montgomery form -/
      def $unwrap (x: $name) : $name := 
        if x.wrapped then ⟨$reduce x.data, false⟩ else x

      /-- Unwrap and extract the `Nat` data of a field element -/
      def $natRepr (x : $name) : Nat := x.unwrap.data

      /-- Field addition -/
      partial def $add (x y : $name) : $name := -- TODO: Eliminate partial
        match x.wrapped, y.wrapped with
        | true, true =>
          let answer := x.data + y.data
          if $p ≤ answer then ⟨answer - $p, true⟩ else ⟨answer, true⟩
        | false, true =>
          let x := $wrap x
          $add x y
        | true, false =>
          let y := $wrap y
          $add x y
        | false, false =>
          let answer := x.data +  y.data
          if $p ≤ answer then ⟨answer - $p, false⟩ else ⟨answer, false⟩

      instance : Add $name where
        add := $add

      /-- Field multiplication-/
      partial def $mul (x y : $name) : $name := -- TODO: Eliminate partial
        match x.wrapped, y.wrapped with
        | true, true => ⟨$reduce <| x.data * y.data, true⟩
        | true, false => 
          let y := $wrap y
          $mul x y
        | false, true => 
          let x := $wrap x
          $mul x y
        | false, false => ⟨x.data * y.data % $p, false⟩

      instance : Mul $name where
        mul := $mul
      
      /-- Field negation-/
      def $neg (x : $name) : $name :=
        ⟨$p - x.data, x.wrapped⟩

      instance : Neg $name where
        neg := $neg

      /-- Field subraction -/
      def $sub (x y : $name) : $name :=
        $add x ($neg y)

      instance : Sub $name where
        sub := $sub

      private def $powAux (base : $name) (exp : Nat) : $name :=
        let rec go (base acc : $name) (exp : Nat) : $name :=
          if h : exp = 0 then acc
          else
            let exp' := exp / 2
            have : exp' < exp := Nat.div2_lt h
            if exp % 2 = 0
            then go (base * base) acc exp'   
            else go (base * base) (acc * base) exp'
        go base 1 exp

      /-- Field exponentiation -/
      def $pow (x : $name) (exp : Nat) : $name :=
        if 3 < exp then
          let x := $wrap x
          $powAux x exp |> ($unwrap ·) 
        else
          $powAux x exp

      instance : HPow $name Nat $name where
        hPow := $pow

      instance : BEq $name where
        beq x y := ($wrap x).data == ($wrap y).data

      private def $invAux (x : Nat) : Nat := Id.run do
        let mut (u, v, r, s, k) := ($p, x, 0, 1, 0)

        while v > 0 do
          if u % 2 == 0 then 
            u := u >>> 1
            s := s <<< 1
          else if v % 2 == 0 then
            v := v >>> 1
            r := r <<< 1
          else if v < u then
            u := (u - v) >>> 1
            r := r + s
            s := s <<< 1
          else if u ≤ v then
            v := (v - u) >>> 1
            s := s + r 
            r := r <<< 1
          k := k + 1
        
        if $p ≤ r then 
          r := 2 * $p - r
        else
          r := $p - r

        for _ in [1: k - $content + 1] do
          if r % 2 == 0 then
            r := r >>> 1
          else
            r := (r + $p) >>> 1
        
        return r
      
      /-- 
      Calculates the inverse of an element. If the element is wrapped, applies Montgomery inversion:
      <https://ieeexplore.ieee.org/document/403725>
      Otherwise calculates the inverse using the extended Euclidean Algorithm
      -/
      def $inv (x : $name) : $name :=
        if x.wrapped then 
          ⟨$invAux <| $reduce x.data, true⟩
        else 
          let ans := Nat.gcdA x.data $p
          let ans := if ans < 0 then ans + $p |>.toNat else ans.toNat
          ⟨ans, false⟩

      instance : Square $name where
        mul := $mul
        square x := x * x

      open Square in
      /-- 
      Calculates the Legendre symbol of the element `x`, using a pre-computed AddChain for 
      `p - 1 / 2`
      -/
      def $legendre (x : $name) : Nat :=
        $(mkIdent `chainExp) $legAC x.wrap |> $natRepr
      
      open Square in
      /-- 
      Calculates the Legendre symbol of the element `x`, using a pre-computed AddChain for `p`
      -/
      def $frob (x : $name) : $name :=
        $(mkIdent `chainExp) $frobAC x.wrap

      /--
      Given a list of exponents `[e₁ e₂, ..., eₙ]` calculates 
      `[base ^ e₁, base ^ e₂, ... , base ^ eₙ]` efficiently
      -/
      partial def $batchedExp (base : $name) (exps : Array Nat) : Array $name := Id.run do
        let mut maxExp : Nat := exps.maxD 0
        let size := exps.size
        let mut exps := exps
        let mut answer := .mkArray exps.size 1
        let mut pow := base.wrap

        while maxExp > 0 do
          maxExp := maxExp >>> 1
          for idx in [:size] do
            if exps[idx]! % 2 == 1 then answer := answer.set! idx (answer[idx]! * pow)
            exps := exps.set! idx (exps[idx]! >>> 1)
          pow := pow * pow
        
        return answer
      
      /-- 
      Given an array of field elements `#[x₁, x₂, ... , xₙ]` calculates `#[x₁⁻¹, x₂⁻¹, ..., xₙ⁻¹]` 
      as a batched calculating using 1 field inversion (and `3n` field multiplications)
      Note: Be careful to only apply to invertible elements.
      -/
      def $batchedInv (arr : Array $name) : Array $name := Id.run do
        let mut acc := 1
        let mut muls := #[]

        for num in arr do
          muls := muls.push acc
          acc := acc * num.wrap

        let mut inv := $inv acc
        let mut answer := #[]
        let mut idx := arr.size - 1
        let mut done := if idx == 0 then true else false

        while ! done do
          if idx == 0 then done := true
          let temp := inv * arr[idx]!
          answer := answer.push (inv * muls[idx]!)
          inv := temp
          idx := idx - 1

        return answer.reverse
      
      /--
      Calculates the 2 square roots of `x`, or returns `none` if `x` is not a square.
      -/
      def $sqrt? (x : $name) : Option $ $name × $name :=
        if $legendre x != 1 then none else Id.run do
        let (s, q) := $twoAdicity
        if s == 1 then
          let r := x ^ (($p + 1) / 4)
          return some (r, $neg r)
        let mut zMax : $name := 2
        for z in [2 : $p] do
          zMax := z
          if $p - 1 == $legendre z then break
        let mut c := zMax ^ q          -- TODO : Be strategic about where to wrap (here for example)
        let exps := $batchedExp x #[((q + 1) / 2), q]
        let mut r := exps[0]!
        let mut t := exps[1]!
        let mut m := s
        while t != 1 do
          let mut t2 := (t * t)
          let mut iMax := 1
          for i in [1:m] do
            iMax := i
            if (t2 - 1) == 0 then
              break
            t2 := (t2 * t2)
          let b := c ^ (2^(m - iMax - 1))
          r := (r * b)
          c := (b * b)
          t := (t * c) 
          m := iMax
        return some (r, $neg r)

      -- Instances: 
      instance : ToString $name where
        toString x := if x.wrapped then s!"{x.data}ₘ" else s!"{x.data}"
      
      instance : Ring $name where
        zero := ⟨0, false⟩
        one := ⟨1, false⟩

      instance : Field $name where
        inv := $inv
        sqrt := fun x => Prod.fst <$> $sqrt? x

      instance : NewField $name := {
        char := $p,
        content := $content,
        twoAdicity := $twoAdicity,
        legAC := $legAC
        frobAC := $frobAC
        wrap := $wrap
        unwrap := $unwrap
        natRepr := $natRepr
        batchedExp := $batchedExp
        batchedInv := $batchedInv
      }
      end $name
    )

end metaprogramming
