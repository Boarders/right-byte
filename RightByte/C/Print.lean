import RightByte.C.Arch

namespace RightByte

def BinOp.symbol : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .xor => "^" | .and => "&" | .or  => "|"
  | .shl => "<<" | .shr => ">>"
  | .lt  => "<"

def CType.str : CType → String
  | .u8      => "uint8_t"
  | .u16     => "uint16_t"
  | .u32     => "uint32_t"
  | .u64     => "uint64_t"
  | .vec128  => "__m128i"
  | .vec256  => "__m256i"
  | .ptr t   => t.str ++ "*"

def VecReduceOp.cType : VecReduceOp → CType
  | .movemask   => .u16
  | .testz      => .u32
  | .extract8 _ => .u8

partial def CExpr.str (arch : Arch) : CExpr → String
  | .lit n       => s!"{n}"
  | .var x       => x
  | .cast t e    => s!"({t.str})({e.str arch})"
  | .binop op l r => s!"({l.str arch} {op.symbol} {r.str arch})"
  | .shl e n => s!"({e.str arch} << {n})"
  | .shr e n => s!"({e.str arch} >> {n})"
  | .vecOp op args =>
      let argStr := String.intercalate ", " ((List.ofFn args).map (·.str arch))
      match op.immediate with
      | none   => s!"{arch.opName op}({argStr})"
      | some n => s!"{arch.opName op}({argStr}, {n})"
  | .vecLoad memOp ptr    => s!"{arch.loadName memOp}({ptr.str arch})"
  | .scalarLoad t ptr     => s!"*({t.str}*)({ptr.str arch})"
  | .vecConst v           =>
      -- _mm_set_epi8 lists bytes from highest index to lowest
      let bytes := (List.finRange 16).reverse.map (fun i => s!"{v[i]!}")
      s!"_mm_set_epi8({String.intercalate ", " bytes})"
  | .ternary c t e        => s!"({c.str arch} ? {t.str arch} : {e.str arch})"

def CStmt.str (arch : Arch) (indent : String := "") : CStmt → String
  | .decl t name expr =>
      s!"{indent}{t.str} {name} = {expr.str arch};"
  | .assign lhs rhs =>
      s!"{indent}{lhs.str arch} = {rhs.str arch};"
  | .vecStore memOp ptr val =>
      s!"{indent}{arch.storeName memOp}({ptr.str arch}, {val.str arch});"
  | .vecReduce (.extract8 i) name expr =>
      s!"{indent}{CType.u8.str} {name} = {arch.reduceName (.extract8 i)}({expr.str arch}, {i.val});"
  | .vecReduce op name expr =>
      s!"{indent}{op.cType.str} {name} = {arch.reduceName op}({expr.str arch});"

  | .forN var bound body =>
      let hd := s!"{indent}for (uint32_t {var} = 0; {var} < {bound.str arch}; {var}++) \{"
      let bd := body.str arch (indent ++ "  ")
      s!"{hd}\n{bd}\n{indent}}"
  | .ifElse cond t e =>
      let hd  := s!"{indent}if ({cond.str arch}) \{"
      let tStr := t.str arch (indent ++ "  ")
      let eStr := e.str arch (indent ++ "  ")
      s!"{hd}\n{tStr}\n{indent}} else \{\n{eStr}\n{indent}}"
  | .block stmts =>
      String.intercalate "\n" (stmts.map (·.str arch indent))
  | .abort msg =>
      s!"{indent}abort(); /* {msg} */"

/-- Top-level pretty printer: emit the SIMD header followed by the statements. -/
def prettyPrint (arch : Arch) (stmts : List CStmt) : String :=
  let body := String.intercalate "\n" (stmts.map (·.str arch))
  s!"{arch.simdHeader}\n\n{body}"

/-- Wrap compiled statements in a C function definition.
    `params` is a list of `(c-type-string, name)` pairs, e.g.
    `[("const uint8_t*", "src"), ("uint8_t*", "dst")]`. -/
def prettyPrintFunc (arch : Arch) (name : String)
    (params : List (String × String)) (stmts : List CStmt) : String :=
  let paramStr := String.intercalate ", " (params.map fun (t, n) => s!"{t} {n}")
  let body     := String.intercalate "\n" (stmts.map (·.str arch "  "))
  arch.simdHeader ++ "\n\nvoid " ++ name ++ "(" ++ paramStr ++ ") {\n" ++ body ++ "\n}"

end RightByte
