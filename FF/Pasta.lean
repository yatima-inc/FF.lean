import FF.NewField
import FF.EllipticCurve

namespace Pasta

variable (p : Nat)

def Pasta : Curve (Zmod p) := Curve.mk 5 0

end Pasta

namespace Pallas

open Pasta in
def Pallas := Pasta 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001

end Pallas

namespace Vesta

open Pasta in
def Vesta := Pasta 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

end Vesta