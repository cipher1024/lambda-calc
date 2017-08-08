
universe variables u v w

open nat

lemma left_rec (m n : ℕ) : m < 1 + (m + n) :=
begin
  rw [add_comm,← nat.succ_eq_add_one],
  apply nat.succ_le_succ, apply nat.le_add_right
end

-- lemma left_rec' {m n : ℕ} (i : ℕ) (h : 1 + m + n < succ i)
-- : m < i :=
-- sorry

-- lemma right_rec' {m n : ℕ} (i : ℕ) (h : 1 + m + n < succ i)
-- : n < i :=
-- sorry

namespace interpreter

inductive type : Type
 | int : type
 | list : type → type
 | fn : type → type → type

infixr ` ↦ `:50 := type.fn

inductive list_cons : Type
 | nil : list_cons
 | cons : list_cons

inductive expr : Type u → Type (u+1)
 | var : ∀ {var : Type u}, var → expr var
 | lit : ∀ {var : Type u}, ℕ → expr var
 | constr : ∀ {var : Type u}, type → list_cons → expr var
 | case : ∀ {v : Type u},
       expr v →
       expr v →
       expr (fin 2 ⊕ v) →
       expr v
 | abs : ∀ {v : Type u},
       type →
       expr (fin 1 ⊕ v) →
       expr v
 | app : ∀ {v : Type u}, expr v → expr v → expr v
 | bind' : ∀ {v : Type u} (n : ℕ),
       (fin (succ n) → type) →
       (fin (succ n) → expr (fin (succ n) ⊕ v)) →
       expr (fin (succ n) ⊕ v) →
       expr v

open expr

def option.map {γ α β} (f : α → β) : γ ⊕ α → γ ⊕ β
  | (sum.inr x) := sum.inr $ f x
  | (sum.inl x) := sum.inl x

lemma option.id_map {α β} (x : α ⊕ β)
: option.map id x = x :=
by { induction x ; refl }

lemma option.map_comp {e} {α β γ}
  (g : α → β) (h : β → γ) (x : e ⊕ α)
: option.map (h ∘ g) x = option.map h (option.map g x) :=
by { induction x ; refl }

instance {α} : functor (sum α) :=
{ map := @option.map α
, id_map := @option.id_map _
, map_comp := @option.map_comp α }

-- def expr.map_t := ∀ {α β}, (α → β) → expr α → expr β

-- def expr.map' (map : expr.map_t) : expr.map_t
--   | _ _ f (expr.var v) := expr.var $ f v
--   | _ _ f (expr.lit n) := expr.lit n
--   | α β f (@expr.abs .(_) n t e) :=
--        let h := left_rec (sizeof e) (sizeof e) in
--        @expr.abs _ n t $ map (has_map.map f) e
--   | α β _ (expr.constr c t) := expr.constr c t
--   | α β f (expr.case p e₀ e₁) :=
--         expr.case
--           (map f p)
--           (map f e₀)
--           (map (has_map.map f) e₁)
--   | α β f (@expr.abs .(_) n t e) := expr.abs t $ .map (has_map.map f) e
--   | α β f (expr.app e₀ e₁) := expr.app (expr.map f e₀) (expr.map f e₁)
--   | α β f (@expr.bind' .(_) n Γ bs e) :=
--         expr.bind' Γ
--           (expr.map (has_map.map f) ∘ bs)
--           (expr.map (has_map.map f) e)

-- #print expr.sizeof

-- #print prefix interpreter.expr.

open has_map

-- lemma functor.id_map' {α} (f : Type u → Type v) [functor f]
-- : (map id : f α → f α) = id :=
-- funext functor.id_map
lemma functor.id_map' {α} (f : Type u → Type v) [functor f]
: (map id : f α → f α) = id :=
funext functor.id_map

lemma functor.map_comp' {α β γ} (f : Type u → Type v) [functor f]
  (g : α → β) (h : β → γ)
: (map (h ∘ g) : f α → f γ) = map h ∘ map g :=
funext (functor.map_comp g h)

def expr.map : ∀ {α β}, (α → β) → expr α → expr β
  | _ _ f (expr.var v) := expr.var (f v)
  | _ _ f (expr.lit v) := expr.lit v
  | _ _ f (expr.constr t c) := expr.constr t c
  | _ _ f (expr.case e e₀ e₁) :=
    expr.case (expr.map f e) (expr.map f e₀) (expr.map (map f) e₁)
  | _ _ f (expr.app e₀ e₁) := expr.app (expr.map f e₀) (expr.map f e₁)
  | _ _ f (expr.abs t e) := expr.abs t (expr.map (map f) e)
  | α β f (expr.bind' n ts bs e) :=
    expr.bind' n ts (λ i, expr.map (map f) (bs i)) (expr.map (map f) e)
-- -- begin
-- --   intros α β f e,
-- --   revert β f,
-- --   induction e ; intros β f,
-- --   { apply expr.var (f a) },
-- --   { apply expr.lit a },
-- --   { apply expr.constr a a_1 },
-- --   { apply expr.case (ih_1 f) (ih_2 f) (ih_3 $ map f) },
-- --   { apply expr.abs a (ih_1 $ map f) },
-- --   { apply expr.app (ih_1 f) (ih_2 f) },
-- --   { apply expr.bind' a (λ v, ih_1 v $ map f) (ih_2 $ map f), },
-- -- end

instance : has_map expr := { map :=  @expr.map }

open has_map

namespace expr

def right {α : Type u} {β : Type (max w v)} {γ : Type w}
  (f : α → expr β) : γ ⊕ α → expr (γ ⊕ β)
  | (sum.inl x) := expr.var (sum.inl x)
  | (sum.inr e) := sum.inr <$> f e

def bind : ∀ {α β : Type u}, expr α → (α → expr β) → expr β
  | _ _ (expr.var v) f := f v
  | _ _ (expr.lit n) f := expr.lit n
  | _ _ (expr.constr t c) f   := expr.constr t c
  | _ _ (expr.case p e₀ e₁) f := case (bind p f) (bind e₀ f) (bind e₁ $ expr.right f)
  | _ _ (expr.abs t e) f   := expr.abs t (bind e $ expr.right f)
  | _ _ (expr.app e₀ e₁) f := expr.app (bind e₀ f) (bind e₁ f)
  | _ _ (expr.bind' n ts bs e) f := expr.bind' n ts
           (λ i, bind (bs i) $ expr.right f)
           (bind e $ expr.right f)

instance : has_bind expr :=
{ bind := @expr.bind }

lemma right_var_eq_var_comp_map {α β γ} (f : α → β)
: right (var ∘ f) = var ∘ (has_map.map f : γ ⊕ α → γ ⊕ β) :=
begin
  apply funext,
  intro, cases x with x x ;
  refl,
end

lemma map_eq_bind {α β} (e : expr α) (f : α → β)
: f <$> e = e >>= expr.var ∘ f :=
begin
  revert β f,
  induction e ; intros β f ; try { refl },
  case expr.case α e e₀ e₁
  { unfold has_map.map map has_bind.bind bind at *,
    simp [ih_1,ih_2,ih_3,right_var_eq_var_comp_map],
    refl },
  case expr.abs α t e
  { unfold has_map.map map has_bind.bind bind at *,
    simp [ih_1,right_var_eq_var_comp_map],
    refl },
  case expr.app α e₀ e₁
  { unfold has_map.map map has_bind.bind bind at *,
    simp [ih_1,ih_2] },
  case expr.bind' α n ts bs e
  { unfold has_map.map map has_bind.bind bind at *,
    simp [ih_1,ih_2,right_var_eq_var_comp_map],
    refl },
end

lemma expr.pure_bind {α β} (x : α) (f : α → expr β)
: (expr.var x >>= f) = f x :=
by refl

lemma expr.map_bind_assoc {α β γ} (x : expr α) (f : α → β) (g : β → expr γ)
: f <$> x >>= g = x >>= (g ∘ f) :=
sorry

lemma expr.bind_map_assoc {α β γ} (x : expr α) (f : β → γ) (g : α → expr β)
: x >>= (λ i, f <$> g i) = f <$> (x >>= g) :=
sorry

lemma expr.bind_map_inr_eq_map_inr_bind {α β : Type (max u v)} {γ : Type u}
  (x : expr α) (g : α → expr β)
: sum.inr <$> x >>= right g = (sum.inr <$> (x >>= g) : expr (γ ⊕ β)) :=
by simp [expr.map_bind_assoc,right,function.comp,expr.bind_map_assoc]

lemma option_id_map (α n) : option.map id = @id (fin n ⊕ α) :=
functor.id_map' _

lemma expr.id_map {α}(e : expr α)
: id <$> e = e :=
begin
  induction e
  ; simp [has_map.map,expr.map,option_id_map] at *,
  all_goals { simp [ih_1] },
  all_goals { simp [ih_2] },
  all_goals { simp [ih_3] },
end

lemma expr.bind_assoc {α β : Type (u)} {γ : Type (u)}
  (x : expr α) (f : α → expr β) (g : β → expr γ)
: x >>= f >>= g = x >>= (λ i, f i >>= g) :=
begin
  unfold has_bind.bind at *,
  revert f g β γ,
  induction x ; intros β γ f g ; try { refl },
  case expr.case v e e₀ e₁
  { simp [bind,ih_1,ih_2,ih_3],
    apply congr_arg,
    apply congr_arg,
    apply funext, intro x, cases x with x x, refl,
    apply @expr.bind_map_inr_eq_map_inr_bind _ _ (fin 2) (f x) g },
  case expr.abs v t e
  { simp [bind,ih_1],
    apply congr_arg, apply congr_arg,
    apply funext, intro x, cases x with x x, refl,
    apply @expr.bind_map_inr_eq_map_inr_bind _ _ (fin 1) (f x) g },
  case expr.app v e₀ e₁
  { simp [bind,ih_1,ih_2], },
  case expr.bind' v n ts bs e
  { simp [bind,ih_1,ih_2],
    tactic.congr,
    { apply funext, intro i,
      apply congr_arg,
      apply funext, intro j,
      cases j with j j, refl,
      apply @expr.bind_map_inr_eq_map_inr_bind _ _ (fin (succ n)) (f j) g },
    { apply funext, intro i,
      cases i with i i, refl,
      unfold right,
      apply @expr.bind_map_inr_eq_map_inr_bind _ _ (fin (succ n)) (f i) g, } },
end

lemma bind_pure_comp_eq_map {α β : Type u} (f : α → β) (x : expr α)
: x >>= expr.var ∘ f = f <$> x :=
begin
  revert β ,
  induction x ; intros β f
  ; try { refl }
  ; unfold has_bind.bind bind at *,
  { simp [ih_1,ih_2,right_var_eq_var_comp_map,has_map.map,expr.map],
    apply congr_arg,
    rw [ih_3], refl },
  { simp [right_var_eq_var_comp_map,ih_1], refl },
  { simp [ih_1,ih_2], refl },
  { simp [right_var_eq_var_comp_map,ih_1,ih_2], refl }
end

instance : monad expr :=
{ pure := λ α, expr.var
, bind := @expr.bind
, map := @expr.map
, id_map := @expr.id_map
, bind_pure_comp_eq_map := @bind_pure_comp_eq_map
, pure_bind := @expr.pure_bind
, bind_assoc := @expr.bind_assoc
}

def split_max {n} : fin (succ n) → option (fin n)
| ⟨i,_⟩ := if h : i < n then some ⟨i,h⟩
                        else none

def mk_local {n γ} (t : γ) (Γ : fin n → γ) (i : fin (succ n)) : γ :=
match split_max i with
 | none := t
 | (some i) := Γ i
end

def add_local {v γ} (t : γ) (Γ : v → γ) : fin 1 ⊕ v → γ
  | (sum.inr v) := Γ v
  | (sum.inl _) :=  t

def add_locals {α β γ} (t : α → γ) (Γ : β → γ) : α ⊕ β → γ
  | (sum.inr x) := Γ x
  | (sum.inl x) := t x

def l_pair {γ} (t₀ t₁ : γ) : fin 2 → γ
  | x := if x = 0 then t₀ else t₁

infixr ` <+ `:10 := add_local
infixr ` << `:10 := add_locals
infixr ` <| `:10 := mk_local

inductive has_type : ∀ {v}, (v → type) → expr v → type → Prop
  | var : ∀ {v} (Γ : v → type) (var : v),
       has_type Γ (expr.var var) (Γ var)
  | lit : ∀ {v} (Γ : v → type) (n : ℕ),
       has_type Γ (expr.lit n) type.int
  | nil : ∀ {v} (Γ : v → type) (t : type),
       has_type Γ (expr.constr t list_cons.nil) (type.list t)
  | cons : ∀ {v} (Γ : v → type) (t : type),
       has_type Γ (expr.constr t list_cons.cons) (type.fn t $ type.fn (type.list t) (type.list t))
  | app : ∀ {v} (Γ : v → type) (e₀ e₁ : expr v) (t₀ t₁ : type),
       has_type Γ e₀ (type.fn t₀ t₁) →
       has_type Γ e₁ t₀ →
       has_type Γ (expr.app e₀ e₁) t₁
  | case : ∀ {v} (Γ : v → type) (p e₀ : expr v) (e₁ : expr (fin 2 ⊕ v)) (tp t : type),
       has_type Γ p (type.list tp) →
       has_type Γ e₀ t →
       has_type (l_pair tp (type.list tp) << Γ) e₁ t →
       has_type Γ (expr.case p e₀ e₁) t
  | abs : ∀ {v} (Γ : v → type)
          (t : type)
          (e : expr (fin 1 ⊕ v)) (t' : type),
       has_type (t <+ Γ) e t' →
       has_type Γ (expr.abs t e) (t ↦ t')
  | bind : ∀ {v} (Γ : v → type) {n : ℕ}
          (Γ' : fin (succ n) → type)
          (ls : fin (succ n) → expr (fin (succ n) ⊕ v))
          (e : expr (fin (succ n) ⊕ v)) (t : type),
       (∀ l, has_type (Γ' << Γ) (ls l) (Γ' l)) →
       has_type (Γ' << Γ) e t →
       has_type Γ (expr.bind' _ Γ' ls e) t

notation g` ⊢ `:50 e` :: `:0 t := has_type g e t

theorem unique_type {v}
   (Γ : v → type)
   (e : expr v)
   (t₀ t₁ : type)
   (h₀ : Γ ⊢ e :: t₀)
   (h₁ : Γ ⊢ e :: t₁)
: t₀ = t₁ :=
begin
  revert t₀, revert t₁,
  induction e
  ; intros t₀ h₀ t₁ h₁
  ; try { cases h₀ ; cases h₁ ; refl },
  case expr.case _ v
  { cases h₀, cases h₁, apply ih_2 _ _ a_3 _ a_6, },
  case expr.abs v' t term
  { cases h₀, cases h₁,
    apply congr_arg,
    apply ih_1 _ _ a _ a_1 },
  case expr.app v' e₀ e₁
  { cases h₀, cases h₁,
    have h := ih_1 _ _ a _ a_2,
    injection h with h₀ h₁,  },
  case expr.bind' v' n Γ' defs body
  { cases h₀, cases h₁,
    apply ih_2  (Γ' << Γ)
    ; assumption }
end

def insert_last {n v} (e : expr $ fin n ⊕ v) : fin (succ n) ⊕ v → expr (fin n ⊕ v)
| (sum.inl i) := match split_max i with
                  | none := e
                  | (some i) := expr.var (sum.inl i)
                 end
| (sum.inr v) := expr.var $ sum.inr v

def from_right {α β} (f : α → β) : α ⊕ β → β
  | (sum.inr x) := x
  | (sum.inl x) := f x

def subst_last {n v} (e₀ : expr v) (e₁ : expr (fin (succ n) ⊕ v)) : expr (fin n ⊕ v) :=
e₁ >>= insert_last (sum.inr <$> e₀)

def subst_one {v} (e₀ : expr v) (e₁ : expr (fin 1 ⊕ v)) : expr v :=
from_right fin.elim0 <$> subst_last e₀ e₁
-- e₁ >>= has_map.map (from_right fin.elim0) ∘ insert_last (sum.inr <$> e₀)

def subst_two {v} (x xs : expr v) (e₁ : expr (fin 2 ⊕ v)) : expr v :=
subst_one x $ subst_last xs e₁

def nil {v} (t : type) : expr v :=
expr.constr t list_cons.nil

def cons {v} (t : type) (e₀ e₁ : expr v) : expr v :=
expr.app (expr.app (expr.constr t list_cons.cons) e₀) e₁

inductive small_step : ∀ {v}, (v → expr v) → expr v → expr v → Prop
  | var : ∀ {v} (t : v → expr v) (var : v),
       small_step t (expr.var var) (t var)
  | app : ∀ {v} (Γ : v → expr v) {n : ℕ}
       (t : type)
       (e₀ : expr $ fin 1 ⊕ v) (e₁ : expr v),
       small_step Γ (expr.app (expr.abs t e₀) e₁) (subst_one e₁ e₀)
  | case : ∀ {v} (Γ : v → expr v) (p p' e₀ : expr v) (e₁ : expr (fin 2 ⊕ v)),
       small_step Γ p p' →
       small_step Γ (expr.case p e₀ e₁) (expr.case p' e₀ e₁)
  | case_nil : ∀ {v} (Γ : v → expr v) (t : type)
          (p p' e₀ : expr v) (e₁ : expr (fin 2 ⊕ v)),
       small_step Γ (expr.case (expr.nil t) e₀ e₁) e₀
  | case_cons : ∀ {v} (Γ : v → expr v) (t : type)
          (x xs e₀ : expr v) (e₁ : expr (fin 2 ⊕ v)),
       small_step Γ (expr.case (expr.cons t x xs) e₀ e₁) (subst_two x xs e₁)
  | bind : ∀ {v} (Γ : v → expr v) {n : ℕ}
          (Γ' : fin (succ n) → type)
          (ls : fin (succ n) → expr (fin (succ n) ⊕ v))
          (e e' : expr (fin (succ n) ⊕ v)),
       small_step (ls << (has_map.map sum.inr ∘ Γ)) e e' →
       small_step Γ (expr.bind' _ Γ' ls e) (expr.bind' _ Γ' ls e')
  | bind' : ∀ {v} (Γ : v → expr v) {n : ℕ}
          (Γ' : fin (succ n) → type)
          (ls : fin (succ n) → expr (fin (succ n) ⊕ v))
          (e : expr v),
       small_step Γ (expr.bind' _ Γ' ls $ sum.inr <$> e) e

notation g` ⊧ `e` ~> `t := small_step g e t

inductive value' (v : Type (u+1)) : Type v → Type ((max v u)+1)
  | nat {} : ∀ {v' : Type v}, ℕ → value' v'
  | cons : ∀ {v'}, type → v → v → value' v'
  | nil {} : ∀ {v'}, type → value' v'
  | abs {} : Π {v'}, type → expr (fin 1 ⊕ v') → value' v'

inductive value : Type (u+1)
  | mk : value' value empty → value

def whnf (v : Type u) : Type (u+1) := value' (expr v) v

def i0 {v n} : expr (fin (succ n) ⊕ v) := expr.var (sum.inl 0)

def i1 {v n} : expr (fin (succ $ succ n) ⊕ v) := expr.var (sum.inl 1)

-- def mk_app {v : Type u} : expr v → list (expr v) → expr v
--   | e list.nil := e
--   | e₀ (list.cons e₁ es) := mk_app (expr.app e₀ e₁) es

-- def is_whnf {v : Type u} : expr v → list (expr v) → option (whnf v)
--   | (lit v) es := _ -- some (mk_app (value'.nat v) es)
--   | (var v) es := none
--   | (cons t list_cons.nil) es := _ -- some value'.nil
--   | (cons t list_cons.cons) es := _
-- -- some $ value'.abs (l_pair t $ type.list t) (expr.cons i0 i1)
--   | (app e₀ e₁) es := _
--   | (@abs .(v) _ t e) es := _ -- some $ value'.abs t e
--   | (@bind' .(v) _ _ _ _) es := _ -- none
--   | (case _ _ _) es := _ -- none

def whnf.to_expr {v} : whnf v → expr v
  | (value'.nat n) := expr.lit n
  | (value'.cons t e₀ e₁) := cons t e₀ e₁
  | (value'.nil t) := expr.nil t
  | (@value'.abs .(_) .(_) t e) := expr.abs t e

def whnf_eval {v} (st : v → expr v) (e : expr v) (e' : whnf v) : Prop :=
tc (small_step st) e e'.to_expr

notation g` ⊧ `e` ~>⁺ `t := whnf_eval g e t

/- theorems -/

-- unique type
-- deterministic evaluation

theorem map_preserves_types {var var'}
  (Γ : var → type) (Γ' : var' → type)
  {e : expr var} {t : type}
  {sub : var → var'}
  (He : Γ ⊢ e :: t)
  (Hsub : ∀ v, Γ' (sub v) = Γ v)
: Γ' ⊢ (sub <$> e) :: t :=
sorry

theorem bind_preserves_types {var var'}
  (Γ : var → type) (Γ' : var' → type)
  {e : expr var} {t : type}
  {sub : var → expr var'}
  (He : Γ ⊢ e :: t)
  (Hsub : ∀ v, Γ' ⊢ sub v :: Γ v)
: Γ' ⊢ (e >>= sub) :: t :=
begin
  revert var' Γ' t,
  induction e
  ; intros var' Γ' t sub He Hsub
  ; unfold has_bind.bind bind at *,
  case expr.var
  { cases He, apply Hsub },
  case expr.lit
  { cases He, apply has_type.lit, },
  case expr.constr
  { cases He,
    apply has_type.nil,
    apply has_type.cons },
  case expr.case
  { cases He with h₀ h₁ h₂,
    apply has_type.case,
    { apply ih_1 a_3 Hsub, },
    { apply ih_2 a_4 Hsub, },
    { apply ih_3 a_5,
      intro v,
      cases v with v v ; unfold right,
      { apply has_type.var },
      { apply map_preserves_types Γ', apply Hsub,
        intro, refl } } },
  case expr.abs
  { cases He,
    apply has_type.abs,
    apply ih_1 a_2,
    intro v, cases v with v v ; unfold right,
    { apply has_type.var },
    { apply map_preserves_types, apply Hsub,
      intro, refl } },
  case expr.app
  { cases He,
    apply has_type.app,
    apply ih_1 a_2 Hsub,
    apply ih_2 a_3 Hsub, },
  case expr.bind'
  { cases He,
    apply has_type.bind,
    { intro v', apply ih_1 v' (a_3 _),
      intro v'', cases v'' with v'' v'' ; unfold right,
      { apply has_type.var },
      { apply map_preserves_types, apply Hsub,
        intro, refl } },
    { apply ih_2 a_4,
      intro v'', cases v'' with v'' v'' ; unfold right,
      { apply has_type.var },
      { apply map_preserves_types, apply Hsub,
        intro, refl } } },
end

theorem subst_last_preserves_types {n var}
  {Γ : var → type}
  {Γ' : fin n → type}
  {e : expr (fin (succ n) ⊕ var)}
  {t : type}
  {e' : expr var} (t' : type)
  (He : ((t' <| Γ') << Γ) ⊢ e :: t)
  (He' : Γ ⊢ e' :: t')
: (Γ' << Γ) ⊢ subst_last e' e :: t :=
begin
  unfold subst_last,
  apply bind_preserves_types _ _ He,
  intro v,
  cases v with v v ; unfold insert_last,
  { destruct (split_max v),
    { intros h, simp [h,insert_last._match_1],
      apply map_preserves_types Γ,
      simp [add_locals,mk_local,h],
      apply He', intro, refl },
    { intros i h,
      simp [h,insert_last._match_1,add_locals,mk_local,h],
      apply has_type.var } },
  { apply has_type.var }
end

theorem subst_one_preserves_types {var} {Γ : var → type}
  {e : expr (fin 1 ⊕ var)} {t : type}
  {e' : expr var} (t' : type)
  (He : (t' <+ Γ) ⊢ e :: t)
  (He' : Γ ⊢ e' :: t')
: Γ ⊢ subst_one e' e :: t :=
begin
  unfold subst_one,
  apply map_preserves_types (fin.elim0 << Γ) _,
  apply subst_last_preserves_types _ _ He,
  apply He',
  intro, cases v with v v,
  apply v.elim0,
  refl
end

theorem subst_two_preserves_types {var} {Γ : var → type}
  {e : expr (fin 2 ⊕ var)} {t : type}
  {e₀ : expr var} (t₀ : type)
  {e₁ : expr var} (t₁ : type)
  (He : (l_pair t₀ t₁ << Γ) ⊢ e :: t)
  (He₀ : Γ ⊢ e₀ :: t₀)
  (He₁ : Γ ⊢ e₁ :: t₁)
: Γ ⊢ subst_two e₀ e₁ e :: t :=
begin
  unfold subst_two,
  apply subst_one_preserves_types,
  apply subst_last_preserves_types,
end

-- evaluation preserves types
theorem evaluation_preserves_types {var} (V : var → expr var) (Γ : var → type)
  (Hstore : ∀ i, Γ ⊢ V i :: Γ i)
  (e e' : expr var) (t : type)
  (Hval : V ⊧ e ~> e')
  (Htype : Γ ⊢ e :: t)
: Γ ⊢ e' :: t :=
begin
  revert t,
  induction Hval ; introv  Ht,
  case small_step.var vv store
  { cases Ht, apply Hstore },
  case expr.small_step.app _ M
  { rename Γ_1 Γ, cases Ht, cases a,
    apply subst_one_preserves_types t
    ; assumption },
  case expr.small_step.case
  { cases Ht, apply has_type.case _ _ _ _ tp,
    { apply ih_1 _ Hstore _ a_1, },
    all_goals { assumption } },
  case expr.small_step.case_nil
  { cases Ht with d ; assumption },
  case expr.small_step.case_cons
  { cases Ht,
    cases a, cases a_3, cases a_5,
    apply subst_two_preserves_types t (type.list t),
    { assumption },
    { cases a_3,
      have H := unique_type _ _ _ _ a_5 a_7, cases H,
      assumption },
    { cases a, cases a_7, cases a_9,
      assumption, }, },
  case expr.small_step.bind
  { cases Ht,
    apply has_type.bind _ _ _ _ _ a_1,
    apply ih_1 _ _ _ a_2, },
end

end expr

end interpreter
