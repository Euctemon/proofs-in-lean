class group (G : Type u) :=
  (id : G)
  (inv : G → G)
  (binop : G → G → G)
  binop_assoc : ∀ (a b c : G), binop (binop a b) c = binop a (binop b c)
  id_binop : ∀ (a : G), binop id a = a
  binop_left_inv (a : G) : binop (inv a) a = id

attribute [simp] group.id_binop group.binop_left_inv
infixl : 75 "⊙" => group.binop
variable {S : Type u} [group S]

namespace group

@[simp] theorem binop_left_cancel (a b c : S) (h1 : a ⊙ b = a ⊙ c) : b = c :=
calc b = id ⊙ b := by rw [id_binop b]
     _ = ((inv a) ⊙ a) ⊙ b := by rw [binop_left_inv]
     _ = (inv a) ⊙ (a ⊙ b) := by rw [binop_assoc]
     _ = (inv a) ⊙ (a ⊙ c) := by rw [h1]
     _ = ((inv a) ⊙ a) ⊙ c := by rw [binop_assoc]
     _ = id ⊙ c := by rw [binop_left_inv]
     _ = c := by rw [id_binop]

theorem binop_eq_of_eq_inv_binop (a x y : S) (h1 : x = (inv a) ⊙ y) : a ⊙ x = y := by
apply binop_left_cancel (inv a)
rw [← binop_assoc,binop_left_inv,id_binop]
exact h1

@[simp] theorem binop_id (a : S) : a ⊙ id = a := by
apply binop_eq_of_eq_inv_binop
rw [binop_left_inv]

@[simp] theorem binop_right_inv (a : S) : a ⊙ (inv a) = id := by
apply binop_eq_of_eq_inv_binop
rw [binop_id]

@[simp] theorem inv_binop_cancel_left (a b : S) : (inv a) ⊙ (a ⊙ b) = b := by
rw [← binop_assoc]
simp

@[simp] theorem binop_inv_cancel_left (a b : S) : a ⊙ ((inv a) ⊙ b) = b := by
rw [← binop_assoc]
simp

@[simp] theorem inv_binop (a b : S) : inv (a ⊙ b) = (inv b) ⊙ (inv a) := by
rw [← id_binop (inv b), binop_assoc]
rw [← binop_left_inv (a ⊙ b),binop_assoc]
rw [binop_assoc]
simp

@[simp] theorem id_inv : inv id = (id : S) := by
rw [← binop_id (inv id)]
rw [binop_left_inv]

@[simp] theorem inv_inv (a : S) : inv (inv a) = a := by
apply binop_left_cancel (inv a)
simp

class abelian_group (A : Type u) extends group A :=
  binop_comm : ∀ (a b : A), binop a b = binop b a

namespace abelian_group
variable (K : Type u) [abelian_group K]

@[simp] theorem group_commutator_eq_id (a b : K) : (inv a) ⊙ (inv b) ⊙ a ⊙ b = id := by
rw [← binop_comm a, ← binop_assoc a]
simp
