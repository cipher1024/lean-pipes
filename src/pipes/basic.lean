
import data.coinductive

import .tactic

universes u v w
local prefix `♯`:0 := cast (by simp [*] <|> cc <|> solve_by_elim)

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


def proxy : Type (max u v+1) :=
cofix (proxy_nxt α)

inductive proxy_v_mut_rec (var : Type w) (α : Type u) : bool → Type (max (u+1) v w)
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

abbreviation proxy_cons : Type (max u v+1) :=
proxy_v (proxy α) α

abbreviation proxy_leaf  : Type (max u v+1) :=
proxy_leaf_v (proxy α) α

abbreviation proxy_mut (b : bool) : Type (max u v+1) :=
proxy_v_mut_rec (proxy α) α b

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

def empty.rec' {α : Sort*} : X → α := ulift.rec (empty.rec _)

notation `⊗` := punit.star

def of_cons : Π {b}, proxy_mut x x' y y' m α b → proxy x x' y y' m α
 | tt (ret i) := cofix.mk (proxy_node.ret i) empty.rec'
 | tt (action β cmd f) := cofix.mk (proxy_node.action cmd) (λ i, of_cons (f i))
 | tt (yield o f) := cofix.mk (proxy_node.yield o) (λ i, of_cons (f i))
 | tt (await o f) := cofix.mk (proxy_node.await o) (λ i, of_cons (f i))
 | tt (think cmd) := cofix.mk (proxy_node.think) (λ _, of_cons cmd)
 | ff (hole x) := x
 | ff (more t) := of_cons t

def to_cons : proxy x x' y y' m α → proxy_cons x x' y y' m α :=
cofix.cases $ λ node,
match node with
 | (proxy_node.ret i) := λ f, ret i
 | (proxy_node.action cmd) := λ f, action _ cmd (λ i, hole $ f i)
 | (proxy_node.yield o) := λ f, yield o (λ i, hole $ f i)
 | (proxy_node.await o) := λ f, await o (λ i, hole $ f i)
 | proxy_node.think := λ f, think (hole $ f punit.star)
end

@[simp]
lemma to_cons_mk_ret
  (r : α)
  (ch : ulift empty → cofix (proxy_nxt x x' y y' m α))
: to_cons (cofix.mk (proxy_node.ret r) ch) = ret r :=
sorry

@[simp]
lemma to_cons_mk_action {β}
  (cmd : m β)
  (ch : β → cofix (proxy_nxt x x' y y' m α))
: to_cons (cofix.mk (proxy_node.action cmd) ch) = action β cmd (λ i, hole $ ch i) :=
sorry

@[simp]
lemma to_cons_mk_yield
  (o : y')
  (ch : y → cofix (proxy_nxt x x' y y' m α))
: to_cons (cofix.mk (proxy_node.yield o) ch) = yield o (λ i, hole $ ch i) :=
sorry

@[simp]
lemma to_cons_mk_await
  (o : x)
  (ch : x' → cofix (proxy_nxt x x' y y' m α))
: to_cons (cofix.mk (proxy_node.await o) ch) = await o (λ i, hole $ ch i) :=
sorry

@[simp]
lemma to_cons_mk_think
  (ch : punit → cofix (proxy_nxt x x' y y' m α))
: to_cons (cofix.mk proxy_node.think ch) = think (hole $ ch ⊗) :=
sorry

open ulift
-- corec
-- #check @cofix.corec
universes w'

protected def corec_aux  {S : Type w}
: proxy_v x x' y y' m S α →
  Σ i, proxy_nxt x x' y y' m α i → proxy_leaf_v x x' y y' m S α
 | (ret i) := ⟨ proxy_node.ret i, empty.rec' ⟩
 | (action β cmd f) := ⟨ proxy_node.action cmd, f ⟩
 | (yield o f) := ⟨ proxy_node.yield o, f ⟩
 | (await o f) := ⟨ proxy_node.await o, f ⟩
 | (think f) := ⟨ proxy_node.think, λ _, f ⟩

open cofix

protected def head : proxy_cons x x' y y' m α → proxy_node x y' m α
 | (ret i) := proxy_node.ret i
 | (action β m f) := proxy_node.action m
 | (yield o f) := proxy_node.yield o
 | (await o f) := proxy_node.await o
 | (think f) := proxy_node.think

protected def children
: Π c : proxy_cons x x' y y' m α, proxy_nxt x x' y y' m α (head c) → proxy x x' y y' m α
 | (ret i) := empty.rec'
 | (action β m f) := of_cons ∘ f
 | (yield o f) := of_cons ∘ f
 | (await o f) := of_cons ∘ f
 | (think f) := λ _, of_cons f

lemma head_to_cons (p : proxy x x' y y' m α)
: proxy.head (to_cons p) = cofix.head p :=
by { co_cases p ; cases i ;
     simp [to_cons,proxy.head], }

lemma children_to_cons (p : proxy x x' y y' m α)
  (i)
: proxy.children (to_cons p) (cast (by simp [head_to_cons]) i) = cofix.children p i :=
sorry

lemma of_cons_to_cons (p : proxy x x' y y' m α)
: of_cons (to_cons p) = p :=
sorry

inductive proxy_eq : proxy_cons x x' y y' m α → proxy_cons x x' y y' m α → Prop
 | ret (i : α) : proxy_eq (ret i) (ret i)
 | act (β cmd) (f f' : β → proxy_cons x x' y y' m α)
       (step : ∀ (FR : proxy_cons x x' y y' m α → proxy_cons x x' y y' m α → Prop),
                    reflexive FR →
                    FR (action β cmd (more ∘ f)) (action β cmd (more ∘ f')) →
                    ∀ i, FR (f i) (f' i)) :
   proxy_eq (action β cmd (more ∘ f)) (action β cmd (more ∘ f'))
 | yield (o f f')
       (step : ∀ (FR : proxy_cons x x' y y' m α → proxy_cons x x' y y' m α → Prop),
                    reflexive FR →
                    FR (yield o (more ∘ f)) (yield o (more ∘ f')) →
                    ∀ i, FR (f i) (f' i)) :
   proxy_eq (yield o $ more ∘ f) (yield o $ more ∘ f')
 | await (o f f')
       (step : ∀ (FR : proxy_cons x x' y y' m α → proxy_cons x x' y y' m α → Prop),
                    reflexive FR →
                    FR (await o (more ∘ f)) (await o (more ∘ f')) →
                    ∀ i, FR (f i) (f' i)) :
   proxy_eq (await o $ more ∘ f) (await o $ more ∘ f')
 | think (f f')
       (step : ∀ (FR : proxy_cons x x' y y' m α → proxy_cons x x' y y' m α → Prop),
                    reflexive FR →
                    FR (think (more f)) (think (more f')) →
                    FR f f') :
   proxy_eq (think $ more f) (think $ more f')

protected lemma coinduction_eq (p₀ p₁ : proxy x x' y y' m α)
  (H : proxy_eq (to_cons p₀) (to_cons p₁))
: p₀ = p₁ :=
begin
  rw [← of_cons_to_cons p₀,← of_cons_to_cons p₁],
  revert H,
  generalize : to_cons p₀ = pp₀,
  generalize : to_cons p₁ = pp₁,
  intros H,
  apply cofix.coinduction,
  cases H ; simp [of_cons],
  cases H
  ; introv Hrefl Hfr Hij,
  { apply empty.rec' i, },
  repeat
  { revert i j,
    rw [of_cons,children_mk,of_cons,children_mk],
    simp [proxy_nxt,head_mk,of_cons], intros,
    simp [of_cons] at Hfr, subst i,
    apply H_step (λ a b, FR (of_cons a) (of_cons b)) _ Hfr,
    intro, apply Hrefl, },
end

protected def corec {S : Type w}
  (f : Π z : Type w, (S → proxy_leaf_v x x' y y' m z α) → S → proxy_v x x' y y' m z α)
  (s : S)
: proxy x x' y y' m α :=
cofix.corec
  (λ s' : proxy_leaf_v x x' y y' m S α,
     match s' with
      | (hole s') := proxy.corec_aux (f _ hole s')
      | (more t) := proxy.corec_aux t
     end )
  (hole s)

protected def corec₂ {S₀ : Type w} {S₁ : Type w'}
  (f : Π z, (S₀ → S₁ → proxy_leaf_v x x' y y' m z α) → S₀ → S₁ → proxy_v x x' y y' m z α)
  (s₀ : S₀) (s₁ : S₁)
: proxy x x' y y' m α :=
@proxy.corec α (S₀ × S₁) (λ z g s, f z (curry g) s.1 s.2) (s₀, s₁)

end defs

section seq
open ulift proxy_v proxy_leaf_v
parameters {m : Type u → Type v}

variables {x x' y y' z z' α : Type u}

def of_leaf : proxy_leaf x x' y y' m α → proxy_cons x x' y y' m α
 | (hole x) := to_cons x
 | (more x) := x

def seq_push
: proxy x x' y y' m α →
  proxy y y' z z' m α →
  proxy x x' z z' m α :=
λ a b,
proxy.corec₂
  (λ k (seq_push : proxy_leaf x x' y y' m α →
                   proxy_leaf y y' z z' m α →
                   proxy_leaf_v x x' z z' m k α)
       a b,
       match of_leaf a with
         | (ret i) := ret i
         | (action β cmd f) := action β cmd (λ i, seq_push (f i) b)
         | (yield o f) :=
           match of_leaf b with
            | (ret i') := ret i'
            | (action β' cmd' f') := action β' cmd' $ λ i, seq_push a (f' i)
            | (yield o' f') := yield o' $ λ i, seq_push a (f' i)
            | (await o' f') := think $ seq_push (f o') (f' o)
            | (think f) := think $ seq_push a f
           end
         | (await o f) := await o $ λ i, seq_push (f i) b
         | (think f) := think $ seq_push f b
       end )
(hole a) (hole b)

def seq_pull
: proxy x x' y y' m α →
  proxy y y' z z' m α →
  proxy x x' z z' m α :=
λ a b,
proxy.corec₂
  (λ k (seq_pull : proxy_leaf x x' y y' m α →
                   proxy_leaf y y' z z' m α →
                   proxy_leaf_v x x' z z' m k α)
       a b,
       match of_leaf b with
         | (ret i) := ret i
         | (action β cmd f) := action β cmd (λ i, seq_pull a (f i))
         | (await o f) :=
           match of_leaf a with
            | (ret i') := ret i'
            | (action β' cmd' f') := action β' cmd' $ λ i, seq_pull (f' i) b
            | (await o' f') := await o' $ λ i, seq_pull (f' i) b
            | (yield o' f') := think $ seq_pull (f' o) (f o')
            | (think f) := think $ seq_pull f b
           end
         | (yield o f) := yield o $ λ i, seq_pull a (f i)
         | (think f) := think $ seq_pull a f
       end )
(hole a) (hole b)

def const (i : y) : producer y m α :=
proxy.corec
  (λ z const _, yield i $ λ _, const ⊗)
⊗

def of_list : list y → producer y m punit :=
proxy.corec
  (λ z of_list
     (xs : list y),
     match xs with
      | i::xs := yield i $ λ _, of_list xs
      | [] := ret ⊗
     end)

def diverge : proxy x x' y y' m α :=
proxy.corec (λ z diverge _, think $ diverge ⊗) punit.star

def map (f : x → y) : pipe x y m α :=
proxy.corec
(λ z map u, await ⊗ $ λ i, more $ yield (f i) $ λ _, map ⊗)
punit.star

def mmap (f : x → m y) : pipe x y m α :=
proxy.corec
(λ z map u, await ⊗ $ λ i, more $ action y (f i) $ λ r, more $ yield r $ λ _, map ⊗)
punit.star

def cat : pipe x x m α :=
map id

-- EXAMPLE HERE

end seq

infixr ` >-> `:70 := seq_pull

section lemmas

parameters {m : Type u → Type v}

variables {x x' y y' z z' α : Type u}
open cofix

lemma cat_seq (p : pipe x y m α)
: cat >-> p = p := sorry

lemma seq_cat (p : pipe x y m α)
: p >-> cat = p := sorry

lemma const_map (a : x) (f : x → y)
: const a >-> map f = (const (f a) : producer y m α) :=
sorry

lemma of_list_map (xs : list x) (f : x → y)
: of_list xs >-> map f = (of_list (xs.map f) : producer y m punit) := sorry

lemma map_seq_map (f : x → y) (g : y → z)
: map f >-> map g = (proxy.map (g ∘ f) : pipe x z m α) :=
sorry

lemma mmap_seq_mmap [monad m] (f : x → m y) (g : y → m z)
: mmap f >-> mmap g = (mmap (λ i, f i >>= g) : pipe x z m α) :=
sorry

-- protected def return (i : α) : proxy_cons x x' y y' m α :=
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
end lemmas
end proxy
