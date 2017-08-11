
universes u v u₀ u₁ u₂

namespace ski

inductive var (α : Type u) (n : ℕ) : Type u
  | free  : α → var
  | bound : fin n → var

def var.rec' {α : Type u} {n : ℕ} {r} (x : r) (f : var α n → r) : var α (n+1) → r
 | (var.free ._ v) := f (var.free _ v)
 | (var.bound ._ ⟨v,h⟩) :=
if h' : v < n
then f (var.bound _ ⟨v,h'⟩)
else x

def var.split {α : Type u} {n : ℕ} : var α (n+1) → option (var α n) :=
var.rec' none some

def bound {α : Type u} {n : ℕ} : var α (n+1) :=
var.bound _ ⟨n,nat.lt_succ_self n⟩

def bump {α : Type u} {n : ℕ} : var α n → var α (n+1)
 | (var.free ._ v) := var.free _ v
 | (var.bound ._ ⟨v,h⟩) := var.bound _ ⟨v,by { transitivity n, apply h, apply nat.lt_succ_self }⟩

open has_map

def dumping {α α' : Type u} {n n' : ℕ} {f : Type u → Type v} [applicative f]
  (F : var α n → f (var α' n'))
: var α (n+1) → f (var α' (n'+1)) :=
var.rec' (pure bound) (map bump ∘ F)

inductive expr (t : Type u) (α : Type u) : ℕ → Type u
  | var {n : ℕ} : var α n → expr n
  | app {n : ℕ} : expr n → expr n → expr n
  | abstr (n : ℕ) : t → expr (n+1) → expr n
  | skip {n : ℕ} : expr n → expr (n+1)

def bind {t α α'}
: ∀ {v v'},
  expr t α v →
  (var α v → expr t α' v') →
  expr t α' v'
| v v' (expr.var ._ x) f := f x
| v v' (expr.app e₀ e₁) f := expr.app (bind e₀ f) (bind e₁ f)
| v v' (expr.abstr ._ x e) f :=
expr.abstr _ x (bind e $ var.rec' (expr.var _ bound) (expr.skip ∘ f))
| (v+1) v' (expr.skip e) f := bind e (f ∘ bump)

def substitute {γ α β : Type u} {xs : ℕ}
  (f : α → expr γ β xs)
  (e : expr γ α xs)
: expr γ β xs :=
bind e (λ v, var.rec_on v f (expr.var _ ∘ var.bound _))

def instantiate {α γ : Type u} {n : ℕ}
  (v : α)
  (e : expr γ α (n+1))
: expr γ α n :=
bind e (var.rec' (expr.var _ $ var.free _ v) (@expr.var _ _ n))

def abstract {γ α : Type u} {n : ℕ}
  (p : α) [decidable_eq α]
  (e : expr γ α n)
: expr γ α (n + 1) :=
bind e $ λ v, expr.var _ $
match v with
 | (var.free ._ x) :=  if p = x then bound
                                else var.free _ x
 | (var.bound ._ v) := bump $ var.bound α v
end

def size {t α : Type u} : ∀ {n : ℕ}, expr t α n → ℕ
 | n (expr.var ._ _)  := 0
 | n (expr.app e₀ e₁) := 1 + size e₀ + size e₁
 | n (expr.abstr ._ _ e) := 1 + size e
 | ._ (@expr.skip ._ ._ n e)   := 1 + size e

def traverse {f : Type u → Type v} [applicative f] {t α α' : Type u}
: ∀ {n n'},
  (var α n → f (var α' n')) →
  expr t α n → f (expr t α' n')
| n n' f (expr.var ._ v) := expr.var _ <$> f v
| n n' f (expr.app e₀ e₁) := expr.app <$> traverse f e₀ <*> traverse f e₁
| n n' f (expr.abstr ._ t e) := expr.abstr _ t <$> traverse (dumping f) e
| (nat.succ n) n' f (expr.skip e) := traverse (f ∘ bump) e

inductive expr.rel {t α α' : Type u} (P : ∀ {n n' : ℕ}, var α n → var α' n' → Prop)
: ∀ {n n'}, expr t α n → expr t α' n' → Prop
  | basis {i j} {v : var α i} {v' : var α' j} :
         P v v' → expr.rel (expr.var _ v) (expr.var _ v')
  | app {i j} {e₀ e₁ : expr t α i} {e₀' e₁' : expr t α' j} :
         expr.rel e₀ e₀' →
         expr.rel e₁ e₁' →
         expr.rel (expr.app e₀ e₁) (expr.app e₀' e₁')
  | abstr {i j} {x y : t} {e : expr t α $ i+1} {e' : expr t α' $ j+1} :
         expr.rel e e' →
         expr.rel (expr.abstr _ x e) (expr.abstr _ y e')
  | skip {i j} {e : expr t α i} {e' : expr t α' j} :
         expr.rel e e' →
         expr.rel (expr.skip e) e'
  | skip' {i j} {e : expr t α i} {e' : expr t α' j} :
         expr.rel e e' →
         expr.rel e (expr.skip e')

def dec_t {t α : Type u} {n : ℕ} (α' : Type u) (n' : ℕ) (x : expr t α n) :=
{ y : expr t α' n' // size y ≤ size x }

def expr_wf {t α : Type u} {n : ℕ}
: has_well_founded (expr t α n) :=
⟨ measure size, measure_wf size ⟩

def mk_var {t α α' : Type u} {n n' : ℕ}
  {v  : var α n}
  (v' : var α' n')
: dec_t α' n' (expr.var t v) :=
⟨ expr.var _ v', by simp [size] ⟩

def mk_app  {t α α' : Type u} {n n' : ℕ}
  {e₀ e₁ : expr t α n}
  (e₀' : dec_t α' n' e₀)
  (e₁' : dec_t α' n' e₁)
: dec_t α' n' (expr.app e₀ e₁) :=
have h : size (expr.app (e₀'.val) (e₁'.val)) ≤ size (expr.app e₀ e₁),
  begin
    simp [size],
    apply add_le_add_left,
    apply add_le_add e₀'.property e₁'.property
  end,
⟨ expr.app e₀'.val e₁'.val, h ⟩

def mk_abstr  {t α α' : Type u} {n n' : ℕ}
  {i : t} {e  : expr t α (n + 1)}
  (e' : dec_t α' (n' + 1) e)
: dec_t α' n' (expr.abstr n i e) :=
have size (expr.abstr n' i (e'.val)) ≤ size (expr.abstr n i e),
  by { simp [size], apply add_le_add_left, apply e'.property },
⟨ expr.abstr _ i e'.val , this ⟩

def mk_skip  {t α α' : Type u} {n n' : ℕ}
  {e  : expr t α n}
  (e' : dec_t α' n' e)
: dec_t α' n' (expr.skip e) :=
have size (e'.val) ≤ size (expr.skip e),
 by { simp [size],
      transitivity size e,
      { apply e'.property },
      { apply nat.le_add_left } },
⟨ e'.val, this ⟩

def traverse' {f : Type u → Type v} [applicative f] {t α α' : Type u}
: ∀ {n n'},
  (var α n → f (var α' n')) →
  ∀ e : expr t α n, f (dec_t α' n' e)
| n n' f (expr.var ._ v) :=
  mk_var <$> f v
| n n' f (expr.app e₀ e₁) :=
  mk_app <$> traverse' f e₀
         <*> traverse' f e₁
| n n' f (expr.abstr ._ i e) :=
  mk_abstr <$> traverse' (dumping f) e
| (n+1) n' f (expr.skip e) :=
  mk_skip <$> traverse' (f ∘ bump) e

inductive ski (α : Type u) : Type u
  | S {} : ski
  | K {} : ski
  | I {} : ski
  | var {} : α → ski

def K {t α : Type u} {n : ℕ} : expr t (ski α) n :=
expr.var _ (var.free n ski.K)

def is_free {t α : Type u} {n : ℕ} (e : expr t α (n+1))
: option (dec_t α n e) :=
traverse' (var.rec' none some) e





lemma nat.lt_add_of_zero_lt_right (a b : nat) (h : 0 < a) : b < a + b :=
suffices 0 + b < a + b, by {simp at this, assumption},
by {apply nat.add_lt_add_right, assumption}

lemma nat.foo_left {a b k : ℕ}
  (h  : 0 < k)
  (h' : a ≤ b)
: a < k + b := sorry

lemma nat.foo_right {a b k : ℕ}
  (h  : 0 < k)
  (h' : a ≤ b)
: a < b + k := sorry

local attribute [instance] expr_wf

def to_ski {α : Type u}
: ∀ {n}, expr (ulift unit) α n → expr (ulift empty) (ski α) n
 | n (expr.var ._ v) := expr.var _ $ var.rec_on v (var.free _ ∘ ski.var) (var.bound _)
 | n (expr.app e₀ e₁) :=
   have size e₀ < 1 + size e₀ + size e₁,
     by { apply nat.lt_add_right, apply nat.foo_left, apply zero_lt_one, refl },
   have size e₁ < 1 + size e₀ + size e₁,
     by { apply nat.foo_left, apply nat.zero_lt_one_add, refl },
   expr.app (to_ski e₀) (to_ski e₁)
 | n (expr.abstr ._ t e) :=
   match is_free e with
    | (some e') :=
      have h : size e'.val < 1 + size e,
        by { apply nat.foo_left, apply zero_lt_one, apply e'.property },
      expr.app K (to_ski e'.val)
    | none := sorry
   end
 | (n+1) (expr.skip e) := expr.skip $ to_ski e

end ski
