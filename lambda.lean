
import data.vector
import .applicative
import .lens

universes u u₀ u₁ u₂ u₃

namespace lambda

instance {α : Type u} : has_map (sum α) :=
 { map := λ β γ f x, sum.rec_on x sum.inl (sum.inr ∘ f) }

open nat has_map

class traversable' (t : Type u → Type u) extends functor t : Type (u+1) :=
  (traverse : ∀ {f : Type u → Type u} [applicative f] {α β : Type u},
       (α → f β) → t α → f (t β))
  (traverse_id : ∀ α, @traverse _ _ α _ identity.mk = identity.mk)
  (traverse_compose : ∀ α β γ f g [applicative f] [applicative g]
     (F : γ → f β) (G : β → g α),
       traverse (compose.mk ∘ has_map.map G ∘ F)
     = compose.mk ∘ has_map.map (traverse G) ∘ traverse F)
  (traverse_pure_eq_map : ∀ f [applicative f] α β (F : α → β),
       traverse (pure ∘ F) = (pure ∘ map F : t α → f (t β)))

def nth' {α : Type u} (xs : list α) (i : fin xs.length) : α :=
xs.nth_le i.val i.is_lt

def sum_of (xs : list ℕ) : Type :=
(Σ i : fin xs.length, fin (nth' xs i))

inductive var (α : Type u) (xs : list ℕ) : Type u
 | bound (v : sum_of xs) : var
 | free (v : α) : var

def sum_of.inl {x xs} (n : fin x) : sum_of (x :: xs) := ⟨ (0 : fin (succ _)) , n ⟩
def sum_of.inr {x xs} : sum_of xs → sum_of (x :: xs)
 | ⟨ ⟨ i, P ⟩ , j ⟩ := ⟨ fin.succ ⟨ i, P ⟩ , j ⟩

def split {x xs} : sum_of (x :: xs) → fin x ⊕ sum_of xs
 | ⟨ ⟨succ i,hi⟩ , j ⟩ := sum.inr ⟨ ⟨i, lt_of_succ_lt_succ hi⟩, j ⟩
 | ⟨ ⟨0,_⟩ , j ⟩ := sum.inl j

def join {x xs} : fin x ⊕ sum_of xs → sum_of (x :: xs)
 | ( sum.inr ⟨ ⟨i, hi⟩, j ⟩ ) := ⟨ ⟨succ i,succ_lt_succ hi⟩ , j ⟩
 | ( sum.inl j ) := ⟨ ⟨0,zero_lt_succ _⟩ , j ⟩

open lenses

def sum_of.rec {x xs r}
  (f : fin x → r) (g : sum_of xs → r)
  (m : sum_of (x :: xs))
: r :=
match split m with
 | (sum.inr x) := g x
 | (sum.inl y) := f y
end

def sum_of.map {x y xs ys} (f : fin x → fin y) (g : sum_of xs → sum_of ys)
  (m : sum_of (x :: xs))
: sum_of (y :: ys) :=
sum_of.rec (sum_of.inl ∘ f) (sum_of.inr ∘ g) m

def split' {x xs'} : ∀ {xs}, sum_of (xs ++ x :: xs') → fin x ⊕ sum_of (xs ++ xs')
 | [] s := split s
 | (x' :: xs) s :=
   let s' : sum_of (x' :: (xs ++ x :: xs')) := s in
   suffices fin x ⊕ sum_of (x' :: (xs ++ xs')), from this,
   sum.rec (sum.inr ∘ sum_of.inl) (map sum_of.inr ∘ split') (split s')

def insert {x xs'} (v : fin x) : ∀ xs, sum_of (xs ++ x :: xs')
 | [] := sum_of.inl v
 | (y :: ys) := sum_of.inr (insert ys)

def divide {x xs'} : ∀ xs, sum_of (xs ++ xs') → sum_of (xs ++ x :: xs')
 | [] := sum_of.inr
 | (y :: ys) := sum_of.map id (divide ys)

def sum_list.rec {α x xs r}
  (f : fin x → r)
  (g : sum_of xs ⊕ α → r)
: sum_of (x :: xs) ⊕ α → r
 | (sum.inl x) := match split x with
                   | (sum.inl x) := f x
                   | (sum.inr x) := g (sum.inl x)
                  end
 | (sum.inr x) := g (sum.inr x)

def var.rec' {α : Type u} {v : ℕ} {vs : list ℕ} {r} (f : fin v → r) (g : var α vs → r)
: var α (v :: vs) → r
 | (var.bound ._ v) := sum_of.rec f (g ∘ var.bound _) v
 | (var.free ._ v) := g $ var.free _ v

def var.mk_bound {α : Type u} {v : ℕ} {vs : list ℕ} : fin v → var α (v :: vs) :=
var.bound _ ∘ sum_of.inl

def var.bump {α : Type u} {v : ℕ} {vs : list ℕ} (x : var α vs) : var α (v :: vs) :=
var.rec_on x (var.bound _ ∘ sum_of.inr) (var.free _)

def sum_of.splitting {x x' xs xs'} {F} [applicative F]
: lens_like F (sum_of (x :: xs))   (sum_of (x' :: xs'))
              (fin x ⊕ sum_of xs) (fin x' ⊕ sum_of xs') :=
iso split join

def var.splitting {α α' x xs xs'} {F} [applicative F]
: lens_like F (var α (x :: xs)) (var α' (x :: xs'))
              (var α xs)        (var α' xs')
 | f := var.rec' (pure ∘ var.mk_bound) (map var.bump ∘ f)

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
