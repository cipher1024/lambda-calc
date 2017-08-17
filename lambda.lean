
import data.vector
import .variables.nary
import .lens

universes u u₀ u₁ u₂ u₃

namespace lambda

open nat has_map nary lenses

inductive expr (α β : Type u) : list ℕ → Type u
| var : ∀{n}, var α n → expr n
| app : ∀{n}, expr n → expr n → expr n
| abstr : ∀n {xs}, vector β n → expr (n :: xs) → expr xs
| skip : ∀n {xs}, expr xs → expr (n :: xs)

def expand {α β : Type u} {n : ℕ} {xs : list ℕ}
: expr α β xs → expr α β (n :: xs) :=
expr.skip n

def bind {γ α α'}
: ∀ {xs xs'},
  expr α γ xs →
  (var α xs → expr α' γ xs') →
  expr α' γ xs'
| xs xs' (expr.var ._ v) f := f v
| xs xs' (expr.app e₀ e₁) f := expr.app (bind e₀ f) (bind e₁ f)
| xs xs' (expr.abstr n' v e) f := expr.abstr n' v
  (bind e $ var.rec' (expr.var _ ∘ var.mk_bound) (expr.skip _ ∘ f) )
| (x :: xs) xs' (expr.skip ._ e) f :=
  bind e (f ∘ var.bump)

def expr.free {α β : Type u} {xs : list ℕ} : α -> expr α β xs :=
expr.var _ ∘ var.free _

def expr.bound {α β : Type u} {xs : list ℕ} : sum_of xs -> expr α β xs :=
expr.var _ ∘ var.bound _

def expr.mk_bound {α β : Type u} {x : ℕ} {xs : list ℕ} : fin x -> expr α β (x::xs) :=
expr.var _ ∘ var.mk_bound

def substitute {γ α β : Type u} {xs : list ℕ}
  (f : α → expr β γ xs)
  (e : expr α γ xs)
: expr β γ xs :=
bind e $ λ r, var.rec_on r expr.bound f

def instantiate {α β : Type u} {n : ℕ}
  (f : fin n → α) {xs : list ℕ}
  (e : expr α β (n :: xs))
: expr α β xs :=
bind e $ λ r, var.rec' (expr.free ∘ f) (expr.var _) r

def abstract {α β : Type u} {n : ℕ}
  (f : α → option (fin n)) {xs : list ℕ}
  (e : expr α β xs)
: expr α β (n :: xs) :=
bind e $ λ r, var.rec_on r
              (expr.bound ∘ sum_of.inr)
              (λ r, option.rec_on (f r) (expr.free r) expr.mk_bound)

def vars_ln {β f} [applicative f] {α α'}
: ∀ {n n'},
  (var α n → f (var α' n')) →
  (expr α β n → f (expr α' β n'))
 | n n' F (expr.var ._ v) :=
   expr.var _ <$> F v
 | n n' F (expr.app e₀ e₁) := expr.app <$> vars_ln F e₀ <*> vars_ln F e₁
 | (n :: ns) n' F (expr.skip ._ e) := vars_ln (F ∘ var.bump) e
 | ns ns' F (expr.abstr n v e) := expr.abstr n v <$> vars_ln (var.splitting F) e

def vars {α α' n n' β}
: traversal (expr α β n) (expr α' β n') (var α n) (var α' n')
 | F _inst := @vars_ln _ F _inst _ _ _ _

end lambda
