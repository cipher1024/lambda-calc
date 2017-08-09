
import .applicative

universes u u₀ u₁ u₂ u₃

namespace lenses

def focus (f : Type u₀ → Type u₁) (α : Type u₂) (β : Type u₀) :=
  (α → f β)

@[reducible]
def lens_like (f : Type u₀ → Type u₁) (s : Type u₃) (t : Type u₀) (α : Type u₂) (β : Type u₀) :=
focus f α β → focus f s t

@[reducible]
def getting (r : Type u₁) (s : Type u₂) (a : Type u₂) := lens_like (const r) s s a a

@[reducible]
def asetter (s : Type u₀) (t : Type u₁) (a : Type u₂) (b : Type u₁) :=
lens_like identity s t a b

@[reducible]
def lens (s : Type u₃) (t : Type u₀) (α : Type u₂) (β : Type u₀) :=
∀ {f} [functor f], lens_like f s t α β

@[reducible]
def lens' (s : Type u₂) (α : Type u₂) :=
lens s s α α

@[reducible]
def traversal (s : Type u₃) (t : Type u₀) (α : Type u₂) (β : Type u₀) :=
∀ {f} [applicative f], lens_like f s t α β

@[reducible]
def traversal' (s : Type u₂) (α : Type u₂) :=
traversal s s α α

section accessors

variables {s : Type u₃} {t : Type u₀}
variables {s' : Type u₂} {α : Type u₂} {β : Type u₀}

def view (ln : getting α s' α) (x : s') : α :=
((ln ( const.mk _ )) x).run

def set (ln : asetter s t α β) (x : β) (y : s) : t :=
((ln (λ _, ⟨ x ⟩)) y).run

def over (ln : asetter s t α β) (f : α → β) (y : s) : t :=
((ln (identity.mk ∘ f)) y).run

def iso (f : s → α) (g : β → t) : traversal s t α β
  | F _inst h := @has_map.map _ _inst.to_has_map _ _ g ∘ h ∘ f

end accessors

def Left {α α' β F} [applicative F] : lens_like F (α ⊕ β) (α' ⊕ β) α α'
  | f (sum.inl x) := sum.inl <$> f x
  | f (sum.inr x) := pure $ sum.inr x

def Right {α β β' F} [applicative F] : lens_like F (α ⊕ β) (α ⊕ β') β β'
  | f (sum.inr x) := sum.inr <$> f x
  | f (sum.inl x) := pure $ sum.inl x

def sum.map {α α' β β'} (f : α → α') (g : β → β') : α ⊕ β → α' ⊕ β'
  | (sum.inl x) := sum.inl (f x)
  | (sum.inr x) := sum.inr (g x)

def sum.bitraverse {α α' β β' F} [applicative F] (f : α → F α') (g : β → F β')
: α ⊕ β → F (α' ⊕ β')
  | (sum.inl x) := sum.inl <$> f x
  | (sum.inr x) := sum.inr <$> g x

end lenses
