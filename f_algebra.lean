
universe u

inductive fix (f : Type u → Type u) : Type (u+1)
  | fix (β : Type u) : f β → (β → fix) → fix

structure identity (x : Type u) : Type u :=
  (get : x)

#check fix identity

def of_nat : ℕ → fix option
 | 0 := (fix.fix empty none (empty.rec _))
 | (nat.succ n) := fix.fix unit (some ()) (λ _, of_nat n)

def to_nat : fix option → ℕ
 | (fix.fix β none f) := 0
 | (fix.fix β (some x) f) := nat.succ $ to_nat (f x)

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
 | [] := (fix.fix empty link.nil (empty.rec _))
 | (x :: xs) := fix.fix unit (link.mk x ()) (λ _, of_list xs)

def to_list {α} : fix (link α) → list α
 | (fix.fix β link.nil f) := []
 | (fix.fix β (link.mk x xs) f) := x :: to_list (f xs)

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

def of_tree {α} : tree α → fix (node α)
 | tree.leaf := (fix.fix empty node.nil (empty.rec _))
 | (tree.node t₀ x t₁) := fix.fix bool
                              (node.mk ff x tt)
                              (λ b, bool.rec_on b (of_tree t₀) (of_tree t₁))

def to_tree {α} : fix (node α) → tree α
 | (fix.fix β node.nil f) := tree.leaf
 | (fix.fix β (node.mk t₀ x t₁) f) := tree.node (to_tree $ f t₀) x (to_tree $ f t₁)

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
fix.fix (fin ts.length) ⟨ (x,indices _) ⟩
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
 | (fix.fix β ⟨ (x,xs) ⟩ f) := ntree.node x (list.map (λ i, to_ntree (f i)) xs)

end

example {α} {t : ntree α} : to_ntree (of_ntree t) = t :=
begin
  induction t ;
  unfold of_ntree to_ntree,
  apply congr_arg,
  induction a_1,
  { simp [indices,indices_aux,list.map] },
  { admit }
end

example {α} {f : fix (n_node α)} : to_ntree (of_ntree $ to_ntree f) = to_ntree f :=
begin
  induction f with β x f,
  cases x ;
  admit
end
