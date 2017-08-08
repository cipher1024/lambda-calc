
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

open has_map

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

inductive expr'' (α β : Type u) : list ℕ → Type u
| var : ∀{n}, α → expr'' n
| bvar : ∀{n}, sum_of n → expr'' n
| app : ∀{n}, expr'' n → expr'' n → expr'' n
| abstr : ∀n {xs}, vector β n → expr'' (n :: xs) → expr'' xs
-- | skip : ∀n {xs}, expr'' xs → expr'' (n :: xs)

def expand {α β : Type u}
: ∀ {n : ℕ} {xs : list ℕ},
    expr'' α β xs → expr'' α β (n :: xs) := sorry

def bind {γ α β : Type u}
: ∀ {xs : list ℕ},
    (α → expr'' β γ xs) →
    expr'' α γ xs → expr'' β γ xs
 | xs f (expr''.var ._ v) := f v
 | xs f (expr''.bvar ._ ._ v) := (expr''.bvar _ _ v)
 | xs f (expr''.abstr n v e) := expr''.abstr n v (bind (expand ∘ f) e)
 | xs f (expr''.app e₀ e₁) := expr''.app (bind f e₀) (bind f e₁)

open nat has_map

def sum_of.inl {x xs} : fin x → sum_of (x :: xs) := sorry
def sum_of.inr {x xs} : sum_of xs → sum_of (x :: xs) := sorry

def split {x xs} : sum_of (x :: xs) → fin x ⊕ sum_of xs
 | ⟨ ⟨succ i,hi⟩ , j ⟩ := sum.inr ⟨ ⟨i, lt_of_succ_lt_succ hi⟩, j ⟩
 | ⟨ ⟨0,_⟩ , j ⟩ := sum.inl j

def split' {x xs'} : ∀ {xs}, sum_of (xs ++ x :: xs') → fin x ⊕ sum_of (xs ++ xs')
 | [] s := split s
 | (x' :: xs) s :=
   let s' : sum_of (x' :: (xs ++ x :: xs')) := s in
   suffices fin x ⊕ sum_of (x' :: (xs ++ xs')), from this,
   sum.rec (sum.inr ∘ sum_of.inl) (map sum_of.inr ∘ split') (split s')

def instantiate' {α β : Type u} {n : ℕ}
  (f : fin n → α) {xs' : list ℕ}
: ∀ xs r, r = (xs ++ n :: xs') →
    expr'' α β r → expr'' α β (xs ++ xs')
 | xs r P (expr''.var ._ v) := (expr''.var _ v)
 | xs r P (expr''.bvar ._ ._ v) :=
   match split' (cast (by rw P) v) with
    | (sum.inr v') := expr''.bvar _ _ v'
    | (sum.inl x) := expr''.var _ (f x)
   end
 | xs r P (expr''.abstr n' v e) :=
  expr''.abstr n' v (instantiate' (n' :: xs) _ (by simp [P]) e : expr'' α β (n' :: xs ++ xs'))
 | xs r P (expr''.app e₀ e₁) := expr''.app (instantiate' xs _ P e₀) (instantiate' xs _ P e₁)

def instantiate {α β : Type u} {n : ℕ}
  (f : fin n → α) {xs : list ℕ}
: expr'' α β (n :: xs) → expr'' α β xs
:= instantiate' f [] _ rfl

end lambda
