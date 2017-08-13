
universe u

inductive fix (f : Type u → Type u) : Type (u+1)
  | fix (n : ℕ) : f (ulift $ fin n) → (fin n → fix) → fix

structure identity (x : Type u) : Type u :=
  (get : x)

open ulift

#check fix identity

def of_nat : ℕ → fix option
 | 0 := (fix.fix 0 none fin.elim0)
 | (nat.succ n) := fix.fix 1 (some $ ulift.up 0) (λ _, of_nat n)

def to_nat : fix option → ℕ
 | (fix.fix β none f) := 0
 | (fix.fix β (some x) f) := nat.succ $ to_nat (f $ down x)

example {n : ℕ} : to_nat (of_nat n) = n :=
begin
  induction n ;
  unfold of_nat to_nat,
  simp [ih_1]
end

example {f : fix option} : to_nat (of_nat $ to_nat f) = to_nat f :=
begin
  induction f with β x f,
  cases x ;
  unfold to_nat of_nat,
  simp [ih_1]
end

inductive link (α β : Type u) : Type u
  | nil {} : link
  | mk : α → β → link

#check fix (link ℕ)

def of_list {α} : list α → fix (link α)
 | [] := (fix.fix 0 link.nil fin.elim0)
 | (x :: xs) := fix.fix 1 (link.mk x $ up 0) (λ _, of_list xs)

def to_list {α} : fix (link α) → list α
 | (fix.fix β link.nil f) := []
 | (fix.fix β (link.mk x xs) f) := x :: to_list (f $ down xs)

example {α} {xs : list α} : to_list (of_list xs) = xs :=
begin
  induction xs ;
  unfold of_list to_list,
  simp [ih_1]
end

example {α} {f : fix (link α)} : to_list (of_list $ to_list f) = to_list f :=
begin
  induction f with β x f,
  cases x ;
  unfold to_list of_list,
  simp [ih_1]
end

inductive node (α β : Type u) : Type u
 | nil {} : node
 | mk : β → α → β → node

inductive tree (α : Type u) : Type u
 | leaf {} : tree
 | node : tree → α → tree → tree

#check fix (node ℕ)

def list_array {α} (xs : list α) (i : fin xs.length) : α :=
list.nth_le xs i.val i.is_lt

@[simp]
lemma list_array_zero {α} (x : α) (xs : list α)
: list_array (x :: xs) (0 : fin (nat.succ _)) = x := rfl

@[simp]
lemma list_array_one {α} (x₀ x₁ : α) (xs : list α)
: list_array (x₀ :: x₁ :: xs) (1 : fin (nat.succ _)) = x₁ := rfl

def of_tree {α} : tree α → fix (node α)
 | tree.leaf := (fix.fix 0 node.nil fin.elim0)
 | (tree.node t₀ x t₁) := fix.fix 2
                              (node.mk (up 0) x (up 1))
                              (list_array [of_tree t₀, of_tree t₁])

def to_tree {α} : fix (node α) → tree α
 | (fix.fix β node.nil f) := tree.leaf
 | (fix.fix β (node.mk t₀ x t₁) f) :=
tree.node (to_tree $ f $ down t₀) x
          (to_tree $ f $ down t₁)

example {α} {xs : tree α} : to_tree (of_tree xs) = xs :=
begin
  induction xs ;
  unfold of_tree to_tree,
  simp [ih_1,ih_2]
end

example {α} {f : fix (node α)} : to_tree (of_tree $ to_tree f) = to_tree f :=
begin
  induction f with β x f,
  cases x ;
  unfold to_tree of_tree,
  simp [ih_1]
end

structure compose (f : Type u → Type u) (g : Type u → Type u) (x : Type u) : Type u :=
  (get : f (g x))

inductive ntree (α : Type u) : Type u
  | node : α → list ntree → ntree

#check fix (compose (prod ℕ) list)

def n_node (α : Type u) : Type u → Type u := compose (prod α) list

def indices_aux {n} : ∀ i, i ≤ n → list (fin n)
 | 0 P := []
 | (nat.succ i) P :=
have n - nat.succ i < n, from sorry,
⟨ n - nat.succ i , this ⟩ :: indices_aux i (nat.le_of_succ_le P)

def indices (n : ℕ) : list (fin n) :=
indices_aux n (le_refl n)

def of_ntree {α} : ntree α → fix (n_node α)
 | (ntree.node x ts) :=
fix.fix ts.length ⟨ (x,up <$> indices _) ⟩
        (λ i,
           have ntree.sizeof α (list.nth_le ts (i.val) i.is_lt) < 1 + list.sizeof ts,
             begin
               induction ts,
               cases i.is_lt,
               cases i with i P, cases i with i ;
               unfold list.nth_le ntree.sizeof list.sizeof,
               { admit },
               { admit },
             end,
           of_ntree $ list.nth_le ts i.val i.is_lt)

section

variable {α : Type u}

def to_ntree : fix (n_node α) → ntree α
 | (fix.fix β ⟨ (x,xs) ⟩ f) := ntree.node x (list.map (λ i, to_ntree (f $ down i)) xs)

end

example {α} {t : ntree α} : to_ntree (of_ntree t) = t :=
begin
  induction t ;
  unfold of_ntree to_ntree,
  apply congr_arg,
  induction a_1,
  { simp [indices,indices_aux,list.map], refl },
  { admit }
end

example {α} {f : fix (n_node α)} : to_ntree (of_ntree $ to_ntree f) = to_ntree f :=
begin
  induction f with β x f,
  cases x ;
  admit
end

def cata {α} {F : Type u → Type u} [has_map F] (f : F α → α) : fix F → α
 | (fix.fix β x g) := f $ (λ i, cata (g $ down i)) <$> x

class foldable (f : Type u → Type u) extends functor f :=
  (size : ∀ {α}, f α → ℕ)
  (fold : ∀ {α} (x : f α), fin (size x) → α)
  (idx : ∀ {α} (x : f α), f (ulift $ fin (size x)))
  (correct_fold : ∀ {α} (x : f α), map (λ i, (fold x) (ulift.down i)) (idx x) = x)

export foldable (size fold idx correct_fold)

section

parameters {F : Type u → Type u} [foldable F]
parameters {α : Type u}
parameters (r : α → α → Prop) (wf : well_founded r)
parameter (f : ∀ x : α, F ({ y : α // r y x }))

def ana : α → fix F :=
wf.fix $ λ x ana,
  fix.fix _ (idx $ f x) $ λ j,
    let y := @fold F _ _ (f x) j in
    ana y y.property

end
