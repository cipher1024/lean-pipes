
import data.coinductive

universes u v

open nat function

/- TODO:
  - [X] corec
  - [ ] main pipe composition
  - [ ] Prove that pipes form a monad
  - [ ] recursion
  - [ ] stdio
  - [ ] example with IO
  - [ ] Provide utilities
  - [ ] Prove that pipes form a category
-/

/-
coinductive proxy (x x' y y' : Type u) (m : Type u → Type v) (α : Type u)
: Type (max u v)
  | ret {} : α → proxy
  | action : ∀ β, m β → (β → proxy) → proxy
  | yield  : y → (y' → proxy) → proxy
  | await  : x' →  (x → proxy) → proxy
  | think : proxy → proxy
-/

section

parameters (x x' y y' : Type u) (m : Type u → Type v)
variable (α : Type u)

inductive proxy_node
: Type (max u v+1)
| ret {} : α → proxy_node
| action {} {β : Type u} : m β → proxy_node
| yield {} : y' → proxy_node
| await {} : x  → proxy_node
| think {} : proxy_node

-- variables {α}

def proxy_nxt : proxy_node α → Type u
| (proxy_node.ret _) := ulift empty
| (@proxy_node.action _ _ _ _ β _) := β
| (proxy_node.yield _) := y
| (proxy_node.await _) := x'
| (proxy_node.think) := punit


def proxy_intl : Type (max u v+1) :=
cofix (proxy_nxt α)

inductive proxy_v_mut_rec (var : Type (max u v+1)) (α : Type u) : bool → Type (max u v+1)
  | ret {} : α → proxy_v_mut_rec tt
  | action {} : ∀ β, m β → (β → proxy_v_mut_rec ff) → proxy_v_mut_rec tt
  | yield {}  : y' → (y → proxy_v_mut_rec ff)  → proxy_v_mut_rec tt
  | await {} :  x  → (x' → proxy_v_mut_rec ff) → proxy_v_mut_rec tt
  | think {} : proxy_v_mut_rec ff → proxy_v_mut_rec tt
  | hole {} : var → proxy_v_mut_rec ff
  | more {} : proxy_v_mut_rec tt → proxy_v_mut_rec ff

abbreviation proxy_v (var α) :=
proxy_v_mut_rec var α tt

abbreviation proxy_leaf_v (var α) :=
proxy_v_mut_rec var α ff

abbreviation proxy  : Type (max u v+1) :=
proxy_v (proxy_intl α) α

abbreviation proxy_leaf  : Type (max u v+1) :=
proxy_leaf_v (proxy_intl α) α

abbreviation proxy_mut (b : bool) : Type (max u v+1) :=
proxy_v_mut_rec (proxy_intl α) α b

end

namespace proxy_v
export proxy_v_mut_rec (ret action yield await think)
end proxy_v

namespace proxy
export proxy_v_mut_rec (ret action yield await think)
end proxy

namespace proxy_leaf_v
export proxy_v_mut_rec (more hole)
end proxy_leaf_v

namespace proxy_leaf
export proxy_v_mut_rec (more hole)
end proxy_leaf

namespace proxy
section defs

def X := ulift empty

abbreviation pipe (a b : Type u) := proxy punit a punit b
abbreviation producer (a : Type u) := proxy X punit punit a
abbreviation producer' (a : Type u) (m α) := ∀ {y y'}, proxy y y' punit a m α
abbreviation consumer (a : Type u) := proxy punit a punit X
abbreviation consumer' (a : Type u) (m α) := ∀ {y y'}, proxy punit a y y' m α

parameters {x x' y y' : Type u}
parameters {m : Type u → Type v}
variables {α β γ : Type u}

open nat proxy_v proxy_leaf_v

def empty.rec' : X → α := ulift.rec (empty.rec _)

def to_intl : Π {b}, proxy_mut x x' y y' m α b → proxy_intl x x' y y' m α
 | tt (ret i) := cofix.mk (proxy_node.ret i) empty.rec'
 | tt (action β cmd f) := cofix.mk (proxy_node.action cmd) (λ i, to_intl (f i))
 | tt (yield o f) := cofix.mk (proxy_node.yield o) (λ i, to_intl (f i))
 | tt (await o f) := cofix.mk (proxy_node.await o) (λ i, to_intl (f i))
 | tt (think cmd) := cofix.mk (proxy_node.think) (λ _, to_intl cmd)
 | ff (hole x) := x
 | ff (more t) := to_intl t

def of_intl : proxy_intl x x' y y' m α → proxy x x' y y' m α :=
cofix.cases $ λ node,
match node with
 | (proxy_node.ret i) := λ f, ret i
 | (proxy_node.action cmd) := λ f, action _ cmd (λ i, hole $ f i)
 | (proxy_node.yield o) := λ f, yield o (λ i, hole $ f i)
 | (proxy_node.await o) := λ f, await o (λ i, hole $ f i)
 | proxy_node.think := λ f, think (hole $ f punit.star)
end

open ulift
-- corec
-- #check @cofix.corec
universes w w'

protected def corec_aux  {S : Type (max u v+1)}
: proxy_v x x' y y' m S α →
  Σ i, proxy_nxt x x' y y' m α i → proxy_leaf_v x x' y y' m S α
| s' :=
match s' with
 | (ret i) := ⟨ proxy_node.ret i, empty.rec' ⟩
 | (action β cmd f) := ⟨ proxy_node.action cmd, f ⟩
 | (yield o f) := ⟨ proxy_node.yield o, f ⟩
 | (await o f) := ⟨ proxy_node.await o, f ⟩
 | (think f) := ⟨ proxy_node.think, λ _, f ⟩
end

protected def corec {S : Type (max u v+1)}
  (f : Π z : Type ((max u v)+1), (S → proxy_leaf_v x x' y y' m z α) → S → proxy_v x x' y y' m z α)
  (s : S)
: proxy x x' y y' m α :=
of_intl $
cofix.corec
  (λ s' : proxy_leaf_v x x' y y' m S α,
     match s' with
      | (hole s') := proxy.corec_aux (f _ hole s')
      | (more t) := proxy.corec_aux t
     end )
  (hole s)

protected def corec₂ {S₀ S₁ : Type (max u v+1)}
  (f : Π z, (S₀ → S₁ → proxy_leaf_v x x' y y' m z α) → S₀ → S₁ → proxy_v x x' y y' m z α)
  (s₀ : S₀) (s₁ : S₁)
: proxy x x' y y' m α :=
@proxy.corec α (S₀ × S₁) (λ z g s, f z (curry g) s.1 s.2) (s₀, s₁)

end defs
-- #check @cofix.corec
-- #check @proxy.corec
-- #check @proxy.corec₂
section seq
open ulift proxy_v proxy_leaf_v
parameters {m : Type u → Type v}

variables {x x' y y' z z' α : Type u}

def of_leaf : proxy_leaf x x' y y' m α → proxy x x' y y' m α
 | (hole x) := of_intl x
 | (more x) := x

def seq
: proxy x x' y y' m α →
  proxy y y' z z' m α →
  proxy x x' z z' m α :=
λ a b,
proxy.corec₂
  (λ k (seq : proxy_leaf x x' y y' m α →
              proxy_leaf y y' z z' m α →
              proxy_leaf_v x x' z z' m k α)
       a b,
       match of_leaf a with
         | (ret i) := ret i
         | (action β cmd f) := action β cmd (λ i, seq (f i) b)
         | (yield o f) :=
           match of_leaf b with
            | (ret i') := ret i'
            | (action β' cmd' f') := action β' cmd' $ λ i, seq a (f' i)
            | (yield o' f') := yield o' $ λ i, seq a (f' i)
            | (await o' f') := think $ seq (f o') (f' o)
            | (think f) := think $ seq a f
           end
         | (await o f) := await o $ λ i, seq (f i) b
         | (think f) := think $ seq f b
       end )
(more a) (more b)

notation `⊗` := punit.star

-- not before fix. Look into `computation`
def map (f : x → y) : pipe x y m α :=
proxy.corec
(λ z map u, await ⊗ $ λ i, more $ yield (f i) $ λ _, map ⊗)
punit.star

def mmap (f : x → m y) : pipe x y m α :=
proxy.corec
(λ z map u, await ⊗ $ λ i, more $ action y (f i) $ λ r, more $ yield r $ λ _, map ⊗)
punit.star

def diverge : proxy x x' y y' m α :=
proxy.corec (λ z diverge _, think $ diverge ⊗) punit.star

def cat : pipe x x m α :=
map id

-- EXAMPLE HERE

end seq

infixr ` >-> `:70 := seq

section lemmas

parameters {m : Type u → Type v}

variables {x x' y y' z z' α : Type u}

lemma map_seq_map (f : x → y) (g : y → z)
: map f >-> map g = (proxy.map (g ∘ f) : pipe x z m α) :=
sorry

lemma mmap_seq_mmap [monad m] (f : x → m y) (g : y → m z)
: mmap f >-> mmap g = (mmap (λ i, f i >>= g) : pipe x z m α) :=
sorry

-- protected def return (i : α) : proxy x x' y y' m α :=
-- coind.corec (λ _, ⟨proxy₁.ret i,empty.rec'⟩) ()

-- section atomic

-- variable cmd : proxy₁ x x' y y' m α

-- variable h : proxy₂ cmd = α
-- def s_atomic
-- : option (proxy₂ cmd) →
--   (Σ (y_1 : proxy₁ x x' y y' m α), proxy₂ y_1 → option (proxy₂ cmd))
-- | none := ⟨ cmd , some ⟩
-- | (some x) := ⟨ proxy₁.ret (cast h x), ulift.rec (empty.rec _) ⟩

-- def atomic : proxy x x' y y' m α :=
-- coind.corec.{(max u v+1) u u}
-- (s_atomic cmd h) (@none $ proxy₂ cmd)

-- end atomic

-- section action

-- variables (cmd : m α)

-- protected def action : proxy x x' y y' m α :=
-- atomic (proxy₁.action cmd) rfl

-- end action

-- protected def lift (cmd : m α) : proxy x x' y y' m α :=
-- proxy.action cmd

-- section await

-- variables (i : x')

-- protected def request : proxy x x' y y' m x :=
-- atomic (proxy₁.await i) rfl

-- end await

-- section yield

-- variables (i : y)

-- protected def respond : proxy x x' y y' m y' :=
-- atomic (proxy₁.yield i) rfl

-- end yield

-- section bind

-- variables (cmd : proxy x x' y y' m α)
-- variables (f : α → proxy x x' y y' m β)

-- def state (α β : Type*) := proxy x x' y y' m α ⊕ proxy x x' y y' m β

-- def t (α β) := (Σ (y_1 : proxy₁ x x' y y' m β), proxy₂ y_1 → state α β)

-- def bind_aux' : Π (i : proxy₁ x x' y y' m α),
--     (proxy₂ i → proxy x x' y y' m α) →
--     t α β
--  | (proxy₁.action m) xs := ⟨ proxy₁.action m, sum.inl ∘ xs⟩
--  | (proxy₁.ret r) xs := ⟨ coind.head (f r), sum.inr ∘ coind.children (f r) ⟩
--  | (proxy₁.await x) xs := ⟨ proxy₁.await x, sum.inl ∘ xs⟩
--  | (proxy₁.yield x) xs := ⟨ proxy₁.yield x, sum.inl ∘ xs⟩
--  | (proxy₁.think) xs := ⟨ proxy₁.think, sum.inl ∘ xs⟩

-- def bind_aux
-- : state α β → t α β
-- | (sum.inl param) :=
-- @coind.cases_on _ _ (λ _, t α β) param (bind_aux' f)
--  | (sum.inr param) :=
-- ⟨ coind.head param, sum.inr ∘ coind.children param ⟩

-- protected def bind : proxy x x' y y' m β :=
-- coind.corec (bind_aux f) (sum.inl cmd)

-- end bind

-- instance : has_pure (proxy x x' y y' m) :=
-- ⟨ @proxy.return ⟩

-- instance : has_bind (proxy x x' y y' m) :=
-- ⟨ @proxy.bind ⟩

-- section
-- variables (z : proxy x x' y y' m α)

-- protected lemma id_map
-- : z >>= (pure ∘ id) = z :=
-- sorry

-- example (p : ℕ → Prop) (h : p 17) : ∃ i, p i :=
-- begin
--   split,
--   tactic.swap,
--   abstract hh { exact 17 },
--   apply h,
-- end

-- end

-- section
-- variables (z : α)
-- variables (f : α → proxy x x' y y' m β)

-- protected lemma pure_bind
-- : pure z >>= f = f z :=
-- sorry
-- end

-- section
-- variables (z : proxy x x' y y' m α)
-- variables (f : α → proxy x x' y y' m β)
-- variables (g : β → proxy x x' y y' m γ)

-- protected lemma bind_assoc
-- : z >>= f >>= g = z >>= (λ i, f i >>= g) :=
-- sorry

-- end

-- instance : monad (proxy x x' y y' m) :=
-- { bind := @proxy.bind
-- , pure := @proxy.return
-- , id_map := @proxy.id_map
-- , pure_bind := @proxy.pure_bind
-- , bind_assoc := @proxy.bind_assoc }

-- end proxy

-- variables {γ x x' y y' : Type u}
-- variables {m : Type u → Type v}
-- variables {α β : Type u}

-- protected def await : proxy x punit y y' m x :=
-- proxy.request punit.star

-- protected def yield (i : y) : proxy x x' y punit m punit :=
-- proxy.respond i

-- end proxy
end proxy
