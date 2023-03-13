import FF.PrimeField

/-!
TODO: Major items to consider before we can finally settle on this design:
* Does the design allow for specific optimizations for specific curves?
  (for example, GLV optimization for scalar mul?)
-/

/--
Curves with Weierstrass form satisfying the equation `y² = x³ + a x + b`
for a prime field `F` such that `char K > 3`
TODO: Add
* different forms (Weierstrass, Jacobian)
-/
structure Curve (F : Type _) [Field F] where
  a : F
  b : F

namespace Curve

variable {F : Type _} [Field F] (C : Curve F)

instance [ToString F] : ToString $ Curve F where
  toString C := s!"y² = x³ + {C.a} x + {C.b}"

def discriminant : F := (- (16 : Nat)) * ((4 : Nat) * C.a^3 + (27 : Nat) * C.b^2)

def j : F := (1728 : Nat) * C.a^3 / ((4 : Nat) * C.discriminant)

end Curve


/-
TODO: Add more curve point operations
* Hash to curve
* random curve point
-/

structure ProjectivePoint {F : Type _} [Field F] (C : Curve F) where
  X : F
  Y : F
  Z : F

namespace ProjectivePoint

variable {F : Type _} [Field F] {C : Curve F}

def isInfinity (P : ProjectivePoint C) := P.X == 0 && P.Y == 1 && P.Z == 0

def infinity : ProjectivePoint C := ⟨0, 1, 0⟩

abbrev zero : ProjectivePoint C := infinity

instance : Inhabited $ ProjectivePoint C where
  default := infinity  

def onCurve (C : Curve F) (x y z : F) : Bool := z * y^2 == x^3 + C.a * x * z^2 + C.b * z^3

def mk? (x y z : F) : Option $ ProjectivePoint C :=
  if onCurve C x y z then some ⟨x, y, z⟩ else none

def mkD (x y z : F) : ProjectivePoint C :=
  if onCurve C x y z then ⟨x, y, z⟩ else default

def scale (f : F) : ProjectivePoint C → ProjectivePoint C
  | ⟨x, y, z⟩ => ⟨f * x, f * y, f * z⟩

instance : HMul F (ProjectivePoint C) (ProjectivePoint C) where
  hMul := scale

def norm : ProjectivePoint C → ProjectivePoint C
  | P@⟨_, _, z⟩ =>
    if z != 0 then z⁻¹ * P else
    infinity

instance  : BEq $ ProjectivePoint C where
  beq P Q :=
    let ⟨x₁, y₁, z₁⟩ := P.norm
    let ⟨x₂, y₂, z₂⟩ := Q.norm
    z₁ == z₂ && y₁ == y₂ && x₁ == x₂

instance [ToString F] : ToString $ ProjectivePoint C where
  toString := fun ⟨x, y, z⟩ => s!"({x} : {y} : {z})"

def double (p : ProjectivePoint C) : ProjectivePoint C := Id.run do
  let a := C.a
  let b := C.b
  let b₃ := (3 : Nat) * b
  let ⟨X, Y, Z⟩ := p
  let mut (t₀, t₁, t₂, t₃) := (X * X, Y * Y, Z * Z, X * Y)
  t₃ := t₃ + t₃
  let mut Z₃ := X * Z
  Z₃ := Z₃ + Z₃
  let mut X₃ := a * Z₃
  let mut Y₃ := b₃ * t₂
  Y₃ := X₃ + Y₃
  X₃ := t₁ - Y₃
  Y₃ := t₁ + Y₃
  Y₃ := X₃ * Y₃
  X₃ := t₃ * X₃
  Z₃ := b₃ * Z₃
  t₂ := a * t₂
  t₃ := t₀ - t₂
  t₃ := a * t₃
  t₃ := t₃ + Z₃
  Z₃ := t₀ + t₀
  t₀ := Z₃ + t₀
  t₀ := t₀ + t₂
  t₀ := t₀ * t₃
  Y₃ := Y₃ + t₀
  t₂ := Y * Z
  t₂ := t₂ + t₂
  t₀ := t₂ * t₃
  X₃ := X₃ - t₀
  Z₃ := t₂ * t₁
  Z₃ := Z₃ + Z₃
  Z₃ := Z₃ + Z₃
  return ⟨X₃, Y₃, Z₃⟩

def add (p₁ p₂ : ProjectivePoint C) : ProjectivePoint C :=
  let a := C.a
  let b := C.b
  match p₁, p₂ with
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ =>
    let z₁z₂ := z₁ * z₂
    let x₁z₂x₂z₁ := x₁ * z₂ + x₂ * z₁
    let ax₁z₂x₂z₁ := a * x₁z₂x₂z₁
    let b3 := (3 : Nat) * b
    let t₁ := b3 * x₁z₂x₂z₁ - a^2 * z₁z₂
    let x₃ :=
      (x₁ * y₂ + x₂ * y₁) * 
      (y₂ * y₁ - ax₁z₂x₂z₁ - b3 * z₁z₂) -
      (y₁ * z₂ + y₂ * z₁) *
      (a * x₁ * x₂ + t₁)
    let y₃ := ((3 : Nat) * x₁ * x₂ + a * z₁ * z₂) *
      (a * x₁ * x₂ + t₁) +
      (y₁ * y₂ + ax₁z₂x₂z₁ + b3 * z₁z₂) * (y₁ * y₂ - ax₁z₂x₂z₁ - b3 * z₁z₂)
    let z₃ := (y₁ * z₂ + y₂ * z₁) * (y₁ * y₂ + ax₁z₂x₂z₁ + b3 * z₁z₂) +
      (x₁ * y₂ + x₂ * y₁) * ((3 : Nat) * x₁ * x₂ + a * z₁ * z₂)
    ⟨x₃, y₃, z₃⟩

end ProjectivePoint

inductive AffinePoint {F : Type _} [Field F] (C : Curve F) where
  | affine (X : F) (Y : F) : AffinePoint C
  | infinity : AffinePoint C
  deriving BEq

variable {F : Type _} [Field F] {C : Curve F}

instance [ToString F] : ToString (AffinePoint C) where
  toString p :=
    match p with
      | .infinity => "O"
      | .affine x y => s!"({x} : {y})"

namespace AffinePoint

def zero : AffinePoint C := infinity

def neg : AffinePoint C → AffinePoint C 
  | infinity => infinity
  | affine x y => affine x (-y)

def double [Field F] {C : Curve F} :
  AffinePoint C → AffinePoint C
  | affine x y =>
    let xx := x^2
    let lambda := (xx + xx + xx + Curve.a C) / (y + y)
    let x' := lambda^2 - (2 : Nat) * x
    let y' := lambda * (x - x') - y
    affine x' y'
  | infinity => infinity

def add {F : Type _} [Field F] {C : Curve F} 
  : AffinePoint C → AffinePoint C → AffinePoint C
    | .infinity, p => p
    | p, .infinity => p
    | P@(.affine x₁ y₁), Q@(.affine x₂ y₂) =>
      if P == Q then double P else
      if P == neg Q then .infinity else
      let lambda := (y₁ - y₂)/(x₁ - x₂)
      let x₃ := (lambda^2 - x₁ - x₂)
      .affine x₃ (lambda*(x₁ - x₃) - y₁)

def onCurve (C : Curve F) (x y : F) : Bool := y * y == (x * x + C.a) * x + C.b

end AffinePoint

-- variable {F K : Type _} [Field F] (C : Curve F) 

def ProjectivePoint.toAffine (P : ProjectivePoint C) : AffinePoint C :=
  let P' := P.norm
  if P.Z == 0 then .infinity else .affine P'.X P'.Y

def AffinePoint.toProjective : AffinePoint C → ProjectivePoint C
  | infinity => .infinity
  | affine x y => ⟨x, y, 1⟩

class CurveGroup {F : outParam $ Type _} [Field F] (K : Type _) (C : outParam $ Curve F)  where 
  zero : K
  inv : K → K
  add : K → K → K
  double : K → K
/-
TODO: Add more methods to `CurveGroup`. This includes things like
* Order
* Cofactor
-/

instance [CurveGroup K C] : Add K where
  add := CurveGroup.add 

instance [CurveGroup K C] : Neg K where
  neg := CurveGroup.inv 

open CurveGroup in
partial def smulAux [CurveGroup K C] (n : Nat) (p : K) (acc : K) : K :=
  if n == 0 then acc
  else match n % 2 == 1 with
    | true => smulAux (n >>> 1) (double p) (add p acc)
    | false => smulAux (n >>> 1) (double p) acc

open CurveGroup in
/--
Double and add algorithm for fast scalar-point multiplication
-/
def smul [CurveGroup K C] (n : Nat) (p : K) : K := smulAux n p (zero)

instance [CurveGroup K C] : HMul Nat K K where
  hMul := smul  
  
instance [CurveGroup K C] : HMul Int K K where
  hMul n p := match n with
    | .ofNat n => n * p
    | .negSucc n => (n + 1) * (- p)

open ProjectivePoint in
instance : CurveGroup (ProjectivePoint C) C where 
  zero := infinity
  inv := fun ⟨x, y, z⟩ => ⟨x, 0 - y, z⟩ 
  add := add
  double := double

open AffinePoint in
instance : CurveGroup (AffinePoint C) C where 
  zero := infinity
  inv := neg
  add := add
  double := double

/--
Curve point serialisation
-/
class PointSerialise {F : Type _} [Field F] (C : Curve F) (K : Type _) [CurveGroup K C] where
  serialise : K → ByteArray
  deserialise : ByteArray → Option K

namespace Serialise
variable {F : Type _} [Field F] {C : Curve F}

instance : PointSerialise C (AffinePoint C) where
  serialise := sorry
  deserialise := sorry

instance : PointSerialise C (ProjectivePoint C) where
  serialise := sorry
  deserialise := sorry
