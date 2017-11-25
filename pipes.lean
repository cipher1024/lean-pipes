
universe variables u u₀ u₁ u₂ v v'

inductive proxy (x x' : Type v') (y y' : Type u) (m : Type u → Type v) (α : Type u)
: Type (max u v v'+1)
  | ret {} : α → proxy
  | action : ∀ β, m β → (β → proxy) → proxy
  | yield  : y → (y' → proxy) → proxy
  | await  : x' →  (x → proxy) → proxy

def proxy.bind {x x' y y' m} {α β}
: proxy x x' y y' m α → (α → proxy x x' y y' m β) → proxy x x' y y' m β
| (proxy.ret x) f := f x
| (proxy.action γ m next) f := proxy.action γ m (λ i, proxy.bind (next i) f)
| (proxy.yield x y) f := proxy.yield x (λ i, proxy.bind (y i) f)
| (proxy.await x y) f := proxy.await x (λ b, proxy.bind (y b) f)

instance {x x' y y' m} : has_bind (proxy x x' y y' m) :=
{ bind := @proxy.bind _ _ _ _ _ }

-- set_option trace.eqn_compiler true

section

variables {x x' : Type u₀}
variables {y y' : Type u₁}
variables {z z' : Type u₁}
variables {w w' : Type u₁}
variables {α : Type u₁}
variables {m : Type u₁ → Type v} [monad m]

-- (x : Type v') (y : Type u) (m : Type u → Type v) (α : Type u)
variable rec : y' → proxy y y' z z' m α → proxy x x' z z' m α

def yield : proxy y y' z z' m α → y → (y' → proxy x x' y y' m α) → proxy x x' z z' m α
  | (proxy.ret r) := λ m' p, proxy.ret r
  | (proxy.await act f) := λ m' p, rec act (f m')
  | (proxy.yield m ms)   := λ m' p, proxy.yield m (λ i, yield (ms i) m' p)
  | (proxy.action β x f) := λ m' p, proxy.action β x $ λ i, yield (f i) m' p

def app : proxy x x' y y' m α → proxy y y' z z' m α → proxy x x' z z' m α
  | (proxy.ret r) := λ _, proxy.ret r
  | (proxy.await act f)  := λ x, proxy.await act $ λ i, app (f i) x
  | (proxy.yield m ms) := λp, yield (λ i, app $ ms i) p m ms
  | (proxy.action β x f) := λ y, proxy.action β x $ λ i, app (f i) y

infixr ` >~> `:55 := app

-- mutual def app, yield
-- with app : proxy x y m α → proxy y z m α → proxy x z m α
--   | (proxy.ret r) := λ _, proxy.ret r
--   | (@proxy.await ._ ._ ._ ._ β act f)  := λ x, proxy.await act $ λ i, app (f i) x
--   | (proxy.yield m ms) := λp, yield p m ms
--   | (proxy.action β x f) := λ y, proxy.action β x $ λ i, app (f i) y
-- with yield : proxy y z m α → m y → proxy x y m α → proxy x z m α
--   | (proxy.ret r) := λ m' p, proxy.ret r
--   | (@proxy.await ._ ._ ._ ._ β act f) := λ m' p, proxy.action β (m' >>= act) (λ i, app p (f i))
--   | (proxy.yield m ms)   := λ m' p, proxy.yield m $ yield ms m' p
--   | (proxy.action β x f) := λ m' p, proxy.action β x $ λ i, yield (f i) m' p

open has_map

def dimap {x₀ x₁ x' y₀ y₁ y' m α} (f : x₁ → x₀) (g : y₀ → y₁)
: proxy x₀ x' y₀ y' m α → proxy x₁ x' y₁ y' m α
  | (proxy.ret i) := proxy.ret i
  | (proxy.action β m f) := proxy.action β m (λ i, dimap (f i))
  | (proxy.yield m ms) := proxy.yield (g m) (λi, dimap (ms i))
  | (proxy.await act h) := proxy.await act (λ i, dimap (h (f i)))

@[reducible]
def X := empty

def effect := proxy X X X X
def producer (α) := proxy X X α unit
def consumer (α) := proxy α unit X X
def pipe (α) (β) := proxy α unit β unit

def run {m α} [monad m] : proxy X X X X m α → m α
  | (proxy.ret i) := pure i
  | (proxy.action β m f) := m >>= λ i, run (f i)
  | (proxy.yield m ms) := empty.rec _ m
  | (proxy.await act f) := empty.rec _ act

def for : proxy x x' y y' m α → (y → proxy x x' z z' m y') → proxy x x' z z' m α
  | (proxy.ret i) f := proxy.ret i
  | (proxy.action β m f) g := proxy.action β m $ λ i, for (f i) g
  | (proxy.yield m ms) f := f m >>= λ i, for (ms i) f
  | (proxy.await act f) g := proxy.await act $ λ i, for (f i) g

variables (p₀ : proxy x x' y y' m α)
variables (p₁ : proxy y y' z z' m α)
variables (p₂ : proxy z z' w w' m α)

lemma app_assoc
: p₀ >~> (p₁ >~> p₂) = (p₀ >~> p₁) >~> p₂ :=
begin
  induction p₀,
  { refl },
  { simp [app,ih_1], },
  { simp [app], admit },
  { admit }
end

end
