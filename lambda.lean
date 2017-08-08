
import data.vector

universes u u₀ u₁ u₂

namespace lambda

instance {α : Type u} : has_map (sum α) :=
sorry

inductive expr : Type u → Type (u+1)
 | var : ∀ {var : Type u}, var → expr var
 | app : ∀ {var : Type u}, expr var → expr var → expr var
 | abstr : ∀ {var : Type u}, expr (option var) → expr var

structure identity (α : Type u) : Type u :=
  (run : α)

structure compose (f : Type u₁ → Type u₀) (g : Type u₂ → Type u₁) (α : Type u₂) : Type u₀ :=
  (run : f (g α))

instance : applicative identity := sorry
instance applicative_comp {f : Type u₁ → Type u₀} {g : Type u₂ → Type u₁}
  [applicative f] [applicative g]
: applicative (compose f g) :=
sorry

open nat has_map

class traversable' (t : Type u → Type u) : Type (u+1) :=
  (traverse : ∀ (f : Type u → Type u) [applicative f] (α : Type u) (β : Type u),
       (α → f β) → t α → f (t β))
  (traverse_id : ∀ α, traverse identity α α identity.mk = identity.mk)
  (traverse_compose : ∀ α β γ f g [applicative f] [applicative g]
     (F : γ → f β) (G : β → g α),
       traverse (compose f g) γ α (compose.mk ∘ map G ∘ F)
     = compose.mk ∘ map (traverse _ _ _ G) ∘ traverse _ _ _ F)

structure {v} cell (α : Type u) : Type (max u v) :=
  (get : α)

class {v} traversable (t : Type u → Type u₀) : Type (max v u u₀+1) :=
  (traverse : ∀ (f : Type (max u u₀) → Type v) [applicative f] (α : Type u) (β : Type u),
       (α → f (cell β)) → t α → f (cell.{u} (t β)))

export traversable (traverse)

class traversable_identity (t : Type u → Type u) extends traversable t :=
  (traverse_id : ∀ α, traverse identity α α (identity.mk ∘ cell.mk) = identity.mk ∘ cell.mk)

-- class traversable_compose (t : Type u₂ → Type u₀) :=
-- --  (t₀ : traversable
--   (traverse_compose : ∀ (α : Type (u₂)) (β : Type u₁) (γ : Type u₀) f g [applicative f] [applicative g]
--      (F : γ → f (cell β)) (G : β → g (cell α)),
--        traverse _ _ _ (compose.mk ∘ map (G ∘ cell.get) ∘ _)
--      = compose.mk ∘ map _ ∘ traverse f α β F)

inductive expr' (α : Type u) : ℕ → Type u
| var : ∀{n}, α → expr' n
| bvar : ∀{n}, fin n → expr' n
| app : ∀{n}, expr' n → expr' n → expr' n
| abstr : ∀{n}, expr' (n+1) → expr' n

def nth' {α : Type u} (xs : list α) (i : fin xs.length) : α :=
xs.nth_le i.val i.is_lt

def sum_of (xs : list ℕ) : Type :=
(Σ i : fin xs.length, fin (nth' xs i))

def sum_of.inl {x xs} (n : fin x) : sum_of (x :: xs) := ⟨ (0 : fin (succ _)) , n ⟩
def sum_of.inr {x xs} : sum_of xs → sum_of (x :: xs)
 | ⟨ ⟨ i, P ⟩ , j ⟩ := ⟨ fin.succ ⟨ i, P ⟩ , j ⟩

def split {x xs} : sum_of (x :: xs) → fin x ⊕ sum_of xs
 | ⟨ ⟨succ i,hi⟩ , j ⟩ := sum.inr ⟨ ⟨i, lt_of_succ_lt_succ hi⟩, j ⟩
 | ⟨ ⟨0,_⟩ , j ⟩ := sum.inl j

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

inductive expr'' (α β : Type u) : list ℕ → Type u
| var : ∀{n}, α → expr'' n
| bvar : ∀{n}, sum_of n → expr'' n
| app : ∀{n}, expr'' n → expr'' n → expr'' n
| abstr : ∀n {xs}, vector β n → expr'' (n :: xs) → expr'' xs
| skip : ∀n {xs}, expr'' xs → expr'' (n :: xs)

def expand {α β : Type u} {n : ℕ} {xs : list ℕ}
: expr'' α β xs → expr'' α β (n :: xs) :=
expr''.skip n

def bind {γ α α'}
: ∀ {xs xs'},
  expr'' α γ xs →
  (sum_of xs ⊕ α → expr'' α' γ xs') →
  expr'' α' γ xs'
| xs xs' (expr''.var ._ v) f := f (sum.inr v)
| xs xs' (expr''.bvar ._ ._ v) f := f (sum.inl v)
| xs xs' (expr''.app e₀ e₁) f := expr''.app (bind e₀ f) (bind e₁ f)
| xs xs' (expr''.abstr n' v e) f := expr''.abstr n' v
  (bind e $ sum_list.rec (expr''.bvar _ _ ∘ sum_of.inl) (expr''.skip _ ∘ f))
| (x :: xs) xs' (expr''.skip ._ e) f :=
  bind e (λ r, f $ sum.rec (sum.inl ∘ sum_of.inr) sum.inr r)

def substitute {γ α β : Type u} {xs : list ℕ}
  (f : α → expr'' β γ xs)
  (e : expr'' α γ xs)
: expr'' β γ xs :=
bind e (λ r, sum.rec_on r (expr''.bvar β γ) f)

def instantiate {α β : Type u} {n : ℕ}
  (f : fin n → α) {xs : list ℕ}
  (e : expr'' α β (n :: xs))
: expr'' α β xs :=
bind e $ λ r, sum.rec_on r (sum_of.rec (expr''.var _ ∘ f)
                                       (expr''.bvar _ _))
                           (expr''.var _)

def abstract {α β : Type u} {n : ℕ}
  (f : α → option (fin n)) {xs : list ℕ}
  (e : expr'' α β xs)
: expr'' α β (n :: xs) :=
bind e $ λ r, sum.rec_on r (expr''.bvar _ _ ∘ sum_of.inr)
                           (λ x, option.rec_on (f x)
                                               (expr''.var _ x)
                                               (expr''.bvar _ _ ∘ sum_of.inl))

end lambda
