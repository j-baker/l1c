structure ParseTree =
struct
datatype a_value = Int of int | Bool of bool | Skip

datatype a_expr = Value of a_value
| Plus of a_expr * a_expr
| Geq of a_expr * a_expr
| If of a_expr * a_expr * a_expr
| Assign of string * a_expr
| Deref of string
| Seq of a_expr * a_expr
| While of a_expr * a_expr

end
