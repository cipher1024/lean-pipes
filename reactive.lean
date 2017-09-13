
import data.stream

universes u v w

namespace reactive

structure event (α : Type u) :=
  (get : ℕ → option α)

open has_map

lemma functor.id_map' {f : Type u → Type v} [functor f] {α : Type u}
: (map id : f α → f α) = id :=
by { apply funext, intro, apply functor.id_map }

lemma functor.map_comp' {f : Type u → Type v} [functor f] {α β γ : Type u}
  (g : α → β) (h : β → γ)
: (map (h ∘ g) : f α → f γ) = map h ∘ map g :=
by { apply funext, intro, apply functor.map_comp }

def event.map {α β} (f : α → β) (e : event α) : event β :=
⟨ λ i, option.map f (e.get i) ⟩

instance : functor event :=
 { map := λ α β f, event.mk ∘ function.comp (map f) ∘ event.get
 , map_comp := by { intros, simp, rw [functor.map_comp'] }
 , id_map := by { intros, cases x, simp [functor.id_map',function.comp], } }

structure behavior (α : Type u) :=
  (get : ℕ → α)

instance applicative_behavior : applicative behavior :=
 { pure := λ α x, behavior.mk $ λ _, x
 , seq  := λ α β f x, ⟨ λ i, f.get i (x.get i) ⟩
 , id_map   := by { introv, cases x, simp, }
 , map_pure := by { introv, simp }
 , seq_pure := by { introv, simp }
 , pure_seq_eq_map := by { introv, simp }
 , seq_assoc := by { introv, simp } }

variables {α : Type u}
variables {β : Type v}
variables {γ : Type w}

def behavior.map (f : α → β) (b : behavior α) : behavior β :=
⟨ λ i, f $ b.get i ⟩

def apply (b : behavior (α → β)) (e : event α) : event β :=
⟨ λ i, option.map (b.get i) (e.get i) ⟩

infix ` <@> `:99 := apply

notation x` <@ `:99 y:98 := (function.const _ <$> x) <@> y

def union_with' (f : α → γ) (g : β → γ) (h : α → β → γ)
  (e₀ : event α) (e₁ : event β)
: event γ :=
⟨ λ i, option.bind (e₀.get i) ((λ f, option.map f $ e₁.get i) ∘ h) <|>
       option.map f (e₀.get i) <|>
       option.map g (e₁.get i) ⟩

def union_with (f : α → α → α)
: event α → event α → event α :=
union_with' id id f

def never : event α :=
⟨ λ i, none ⟩

def filter_just (e : event (option α)) : event α :=
⟨ λ i, (e.get i).get_or_else none ⟩

def filter_apply (v : behavior (α → bool)) (e : event α) : event α :=
filter_just ((λ (p : α → bool) x, if p x then some x else none) <$> v <@> e)

def filterE (p : α → Prop) [decidable_pred p] : event α → event α :=
filter_apply (pure $ λ x, to_bool $ p x)

open nat

def accumB.beh (x : α) (e : stream (option (α → α))) : stream α
 | 0 := x
 | (succ i) :=
match e i with
 | none := accumB.beh i
 | (some f) := f $ accumB.beh i
end

def accumB (x : α) (e : event (α → α)) : behavior α :=
⟨ accumB.beh x e.get ⟩

def accumE.evt (x : α) (e : stream (option (α → α))) : stream (option α)
 | i := (λ f : α → α, f $ accumB.beh x e i) <$> e i

def accumE (x : α) (e : event (α → α)) : event α :=
⟨ accumE.evt x e.get ⟩

def stepper (x : α) (e : event α) : behavior α :=
accumB x (function.const _ <$> e)

def whenE (b : behavior bool) : event α → event α :=
filter_apply (behavior.map (function.const α) b)

def get_right : α ⊕ β → option β
 | (sum.inr x) := some x
 | (sum.inl x) := none

def get_left : α ⊕ β → option α
 | (sum.inr x) := none
 | (sum.inl x) := some x

def split (e : event (α ⊕ β)) : event α × event β :=
( filter_just (event.map get_left e) , filter_just (event.map get_right e) )

def unions (es : list (event $ α → α)) : event (α → α) :=
es.foldl (union_with function.comp) never

def map_accum.beh {acc x} (a₀ : acc) (e : stream (option (acc → x × acc)))
: stream acc
 | 0 := a₀
 | (succ n) :=
match e n with
 | none := map_accum.beh n
 | (some f) := prod.snd $ f (map_accum.beh n)
end

def map_accum.evt {acc x} (a₀ : acc) (e : stream (option (acc → x × acc)))
: stream (option x)
 | 0 := none
 | (succ n) :=
match e n with
 | none := none
 | (some f) := some $ prod.fst $ f (map_accum.beh a₀ e n)
end

def map_accum {acc x} (a₀ : acc) (e : event (acc → x × acc)) : event x × behavior acc :=
( ⟨ map_accum.evt a₀ e.get ⟩ , ⟨ map_accum.beh a₀ e.get ⟩ )

end reactive
