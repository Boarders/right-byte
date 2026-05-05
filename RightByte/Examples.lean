import RightByte.C.Arch
import RightByte.C.Compile
import RightByte.C.Print
import RightByte.Examples.Base16

namespace RightByte.Examples

def base16 : Prog (fun _ => CExpr) Unit :=
  base16EncodeAll (.var "src") (.var "dst") (.var "len")

def base16_x86 : String :=
  let stmts := (compile base16).run 0 |>.1
  prettyPrintFunc x86 "base16_encode"
    [("const uint8_t*", "src"), ("uint8_t*", "dst"), ("size_t", "len")]
    stmts

end RightByte.Examples
