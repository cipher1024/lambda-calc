
universes u v

namespace unary

open has_map

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

def dumping {α α' : Type u} {n n' : ℕ} {f : Type u → Type v} [applicative f]
  (F : var α n → f (var α' n'))
: var α (n+1) → f (var α' (n'+1)) :=
var.rec' (pure bound) (map bump ∘ F)

end unary
