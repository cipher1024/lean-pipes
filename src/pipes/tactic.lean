
namespace tactic
open lean.parser interactive interactive.types
open tactic.interactive (generalize cases_arg_p)
local postfix `?`:9000 := optional
local postfix `*`:9000 := many

lemma cast_eq_of_heq {α β} {x : α} {y : β}
  (h : α = β)
  (h' : cast h x = y)
: x == y :=
by { subst β, subst y, symmetry, simp [cast_heq] }

meta def elim_cast (e : parse texpr) (n : parse (tk "with" *> ident)) : tactic unit :=
do let h : name := ("H" ++ n.to_string : string),
   interactive.generalize h () (``(cast _ %%e), n),
   asm ← get_local h,
   to_expr ``(cast_eq_of_heq _ %%asm) >>= note h none,
   clear asm

run_cmd add_interactive [`elim_cast]

end tactic
