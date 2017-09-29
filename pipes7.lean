
import util.data.coinductive

universes u v

open nat function

/-
coinductive proxy (x x' y y' : Type u) (m : Type u → Type v) (α : Type u)
: Type (max u v)
  | ret {} : α → proxy
  | action : ∀ β, m β → (β → proxy) → proxy
  | yield  : y → (y' → proxy) → proxy
  | await  : x' →  (x → proxy) → proxy
  | think : proxy → proxy
-/

inductive proxy₁ (x x' y y' : Type u) (m : Type u → Type v) (α : Type u)
: Type (max u v+1)
| ret {} : α → proxy₁
| action {} {β : Type u} : m β → proxy₁
| yield {} : y → proxy₁
| await {} : x' → proxy₁
| think {} : proxy₁

def proxy₂ {x x' y y' : Type u} {m : Type u → Type v} {α : Type u}
: proxy₁ x x' y y' m α → Type u
| (proxy₁.ret _) := ulift empty
| (@proxy₁.action _ _ _ _ _ _ β _) := β
| (proxy₁.yield _) := y'
| (proxy₁.await _) := x
| (proxy₁.think) := punit

def proxy (x x' y y' : Type u) (m : Type u → Type v) (α : Type u) :=
coind.cofix (@proxy₂ x x' y y' m α)

namespace proxy
section proxy
parameters {x x' y y' : Type u}
parameters {m : Type u → Type v}
variables {α β γ : Type u}

open nat

def empty.rec' : ulift empty → α := ulift.rec (empty.rec _)

protected def return (i : α) : proxy x x' y y' m α :=
coind.corec (λ _, ⟨proxy₁.ret i,empty.rec'⟩) ()

section atomic

variable cmd : proxy₁ x x' y y' m α

variable h : proxy₂ cmd = α
def s_atomic
: option (proxy₂ cmd) →
  (Σ (y_1 : proxy₁ x x' y y' m α), proxy₂ y_1 → option (proxy₂ cmd))
| none := ⟨ cmd , some ⟩
| (some x) := ⟨ proxy₁.ret (cast h x), ulift.rec (empty.rec _) ⟩

def atomic : proxy x x' y y' m α :=
coind.corec.{(max u v+1) u u}
(s_atomic cmd h) (@none $ proxy₂ cmd)

end atomic

section action

variables (cmd : m α)

protected def action : proxy x x' y y' m α :=
atomic (proxy₁.action cmd) rfl

end action

protected def lift (cmd : m α) : proxy x x' y y' m α :=
proxy.action cmd

section await

variables (i : x')

protected def request : proxy x x' y y' m x :=
atomic (proxy₁.await i) rfl

end await

section yield

variables (i : y)

protected def respond : proxy x x' y y' m y' :=
atomic (proxy₁.yield i) rfl

end yield

section bind

variables (cmd : proxy x x' y y' m α)
variables (f : α → proxy x x' y y' m β)

def state (α β : Type*) := proxy x x' y y' m α ⊕ proxy x x' y y' m β

def bind_aux
: state α β →
  (Σ (y_1 : proxy₁ x x' y y' m β), proxy₂ y_1 → state α β)
| (sum.inl param) :=
coind.cases_on param $ λ x xs,
match x, xs with
 | (proxy₁.action m), xs := ⟨ proxy₁.action m, sum.inl ∘ xs⟩
 | (proxy₁.ret r), xs := ⟨ coind.index (f r), sum.inr ∘ coind.children (f r) ⟩
 | (proxy₁.await x), xs := ⟨ proxy₁.await x, sum.inl ∘ xs⟩
 | (proxy₁.yield x), xs := ⟨ proxy₁.yield x, sum.inl ∘ xs⟩
 | (proxy₁.think), xs := ⟨ proxy₁.think, sum.inl ∘ xs⟩
end
 | (sum.inr param) :=
⟨ coind.index param, sum.inr ∘ coind.children param ⟩

protected def bind : proxy x x' y y' m β :=
coind.corec (bind_aux f) (sum.inl cmd)

end bind

instance : has_pure (proxy x x' y y' m) :=
⟨ @proxy.return ⟩

instance : has_bind (proxy x x' y y' m) :=
⟨ @proxy.bind ⟩

section
variables (z : proxy x x' y y' m α)

protected lemma id_map
: z >>= (pure ∘ id) = z :=
sorry

end

section
variables (z : α)
variables (f : α → proxy x x' y y' m β)

protected lemma pure_bind
: pure z >>= f = f z :=
sorry
end

section
variables (z : proxy x x' y y' m α)
variables (f : α → proxy x x' y y' m β)
variables (g : β → proxy x x' y y' m γ)

protected lemma bind_assoc
: z >>= f >>= g = z >>= (λ i, f i >>= g) :=
sorry

end

instance : monad (proxy x x' y y' m) :=
{ bind := @proxy.bind
, pure := @proxy.return
, id_map := @proxy.id_map
, pure_bind := @proxy.pure_bind
, bind_assoc := @proxy.bind_assoc }

end proxy

variables {γ x x' y y' : Type u}
variables {m : Type u → Type v}
variables {α β : Type u}

protected def await : proxy x punit y y' m x :=
proxy.request punit.star

protected def yield (i : y) : proxy x x' y punit m punit :=
proxy.respond i

end proxy
