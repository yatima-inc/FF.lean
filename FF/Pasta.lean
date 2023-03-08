import FF.NewField
import FF.EllipticCurve

namespace Pasta

variable (F : Type _) [Field F] [OfNat F 5]

def Pasta : Curve F := Curve.mk 5 0

end Pasta

namespace Pallas

new_field PallasField with
  prime: 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
  generator: 1
  -- Assuming that Sage doesn't lie

open Pasta in
def Pallas := Pasta PallasField

end Pallas

namespace Vesta

new_field VestaField with
  prime: 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001
  generator: 1
  -- Assuming that Sage doesn't lie

open Pasta in
def Vesta := Pasta VestaField

end Vesta