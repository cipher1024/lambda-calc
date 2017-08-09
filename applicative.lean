universes u u₀ u₁ u₂ u₃

structure identity (α : Type u) : Type u :=
  (run : α)

structure const (α : Type u) (β : Type u₀) : Type u :=
  (run : α)

structure compose (f : Type u₁ → Type u₀) (g : Type u₂ → Type u₁) (α : Type u₂) : Type u₀ :=
  (run : f (g α))

instance : monad identity :=
 { bind := λ α β x f, f x.run
 , pure := λ α, identity.mk
 , id_map := λ α ⟨ x ⟩, rfl
 , bind_assoc := λ α β γ ⟨ x ⟩ f g, rfl
 , pure_bind := λ α β x f, rfl }

instance {f : Type u₁ → Type u₀} {g : Type u₂ → Type u₁}
  [has_pure f] [has_pure g] : has_pure (compose f g) :=
 { pure := λ α x, ⟨ pure $ pure x ⟩ }

instance {f : Type u₁ → Type u₀} {g : Type u₂ → Type u₁}
 [has_pure f] [has_seq f] [has_seq g] : has_seq (compose f g) :=
 { seq := λ α β ⟨ f ⟩ ⟨ x ⟩, ⟨ pure has_seq.seq <*> f <*> x ⟩ }

section applicative

open applicative has_map functor

lemma id_map' {f : Type u → Type u₀} [functor f]
: ∀ {α : Type u}, map id = (id : f α → f α) :=
by { introv, apply funext, intro, apply id_map }

lemma pure_seq_eq_map' {f : Type u → Type u₀} [applicative f]
: ∀ {α β : Type u} (g : α → β), (has_seq.seq $ has_pure.pure _ g) = (map g : f α → f β) :=
by { introv, apply funext, intro, apply pure_seq_eq_map }

instance applicative_comp {f : Type u₁ → Type u₀} {g : Type u₂ → Type u₁}
  [applicative f] [applicative g]
: applicative (compose f g) :=
 { pure := @pure _ _
 , seq := @has_seq.seq _ _
 , seq_assoc :=
   begin
     introv, cases x with x, cases h with h₀, cases g_1 with h₁,
     simp [pure,has_pure.pure,has_seq.seq,compose.has_seq._match_2,compose.has_seq._match_1],
     apply congr_arg, simp [seq_assoc],
     simp [pure_seq_eq_map'],
     simp [seq_pure,map_pure],
     repeat { rw ← map_comp }, unfold function.comp, tactic.congr,
     simp [seq_assoc,pure_seq_eq_map],
   end
 , seq_pure :=
   begin
     introv, cases g_1 with h,
     simp [pure,has_pure.pure,has_seq.seq],
     simp [compose.has_seq._match_2,compose.has_seq._match_1],
     simp [pure_seq_eq_map,seq_pure,map_pure],
     rw ← map_comp, simp [function.comp,seq_pure,pure_seq_eq_map'],
   end
 , map_pure :=
   begin
     introv,
     simp [pure,has_pure.pure,has_seq.seq,compose.has_seq._match_2,compose.has_seq._match_1],
     simp [pure_seq_eq_map,map_pure],
   end
 , pure_seq_eq_map :=
   begin
     introv, cases x with x,
     simp,
   end
 , id_map :=
   begin
     introv, cases x with x,
     simp [has_seq.seq,pure,has_pure.pure,compose.has_seq._match_2,compose.has_seq._match_1],
     simp [pure_seq_eq_map,map_pure,pure_seq_eq_map',id_map'],
   end }

instance {α} : functor (const α) :=
 { map := λ β γ f x, ⟨ _, x.run ⟩
 , id_map := by { introv, cases x, simp, }
 , map_comp := by { introv, cases x, simp } }

instance {α} [monoid α] : applicative (const α) :=
 { map  := @has_map.map _ _
 , seq  := λ α β f x, ⟨ _, f.run * x.run ⟩
 , pure := λ α x, ⟨ _, 1 ⟩
 , id_map := @functor.id_map _ _
 , seq_pure  := by { introv, cases g, simp [has_map.map] }
 , map_pure  := by { introv, simp [has_map.map] }
 , pure_seq_eq_map := by { introv, simp [has_map.map] }
 , seq_assoc := by { introv, cases g, simp [has_map.map] }
 }

end applicative
