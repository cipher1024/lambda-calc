
import util.data.sum
import ..lens

universes u v w

namespace nary

open nat lenses has_map

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

end nary
