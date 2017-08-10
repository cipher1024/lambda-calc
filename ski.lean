
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

def bound {α : Type u} {n : ℕ} : var α (n+1) :=
var.bound _ ⟨n,nat.lt_succ_self n⟩

def bump {α : Type u} {n : ℕ} : var α n → var α (n+1)
 | (var.free ._ v) := var.free _ v
 | (var.bound ._ ⟨v,h⟩) := var.bound _ ⟨v,by { transitivity n, apply h, apply nat.lt_succ_self }⟩

open has_map

def dumped {α α' : Type u} {n n' : ℕ} {f : Type u → Type v} [applicative f]
  (F : var α n → f (var α' n'))
: var α (n+1) → f (var α' (n'+1)) :=
var.rec' (pure bound) (map bump ∘ F)

inductive expr (t : Type u) (α : Type u) : ℕ → Type u
  | var {} (n : ℕ) : var α n → expr n
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
bind e (var.rec' (expr.var _ $ var.free _ v) (expr.var n))

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

def traverse {f : Type u → Type v} [applicative f] {t α α' : Type u}
: ∀ {n n'},
  (var α n → f (var α' n')) →
  expr t α n → f (expr t α' n')
| n n' f (expr.var ._ v) := expr.var _ <$> f v
| n n' f (expr.app e₀ e₁) := expr.app <$> traverse f e₀ <*> traverse f e₁
| n n' f (expr.abstr ._ t e) := expr.abstr _ t <$> traverse (dumped f) e
| (n+1) n' f (expr.skip e) := traverse (f ∘ bump) e


inductive ski (α : Type u) : Type u
  | S {} : ski
  | K {} : ski
  | I {} : ski
  | var {} : α → ski

def K {t α : Type u} {n : ℕ} : expr t (ski α) n :=
expr.var n (var.free n ski.K)


def is_free {t α : Type u} {n : ℕ} (e : expr t α (n+1))
: option (expr t α n) :=
traverse (var.rec' none some) e

section well_founded_tactics

open tactic well_founded_tactics

meta def my_wf_tac : well_founded_tactics :=
{ rel_tac := λ _ _, trace_state >> apply_instance
, dec_tac := do
    clear_internals,
    unfold_wf_rel,
    process_lex (unfold_sizeof >> assumption <|> (cancel_nat_add_lt >> trivial_nat_lt))
}

end well_founded_tactics

def to_ski {α : Type u}
: ∀ {n}, expr (ulift unit) α n → expr (ulift empty) (ski α) n
 | n (expr.var ._ v) := expr.var _ $ var.rec_on v (var.free _ ∘ ski.var) (var.bound _)
 | n (expr.app e₀ e₁) :=
   have sizeof_measure ℕ n n, from sorry,
   expr.app (to_ski e₀) (to_ski e₁)
 | n (expr.abstr ._ t e) :=
   let x := is_free e in
   have h : x = is_free e, from rfl,
   match x, h with
    | (some e'), h :=
      have h : sizeof e' < n + (1 + (sizeof t + sizeof e)), from sorry,
      expr.app K (to_ski e')
    | none, _ := sorry
   end
 | (n+1) (expr.skip e) := sorry
using_well_founded my_wf_tac

end ski
