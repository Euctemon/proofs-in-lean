class group (G : Type u) :=
  (one : G)
  (inv : G → G)
  (mul : G → G → G)
  mul_assoc : ∀ (a b c : G), mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ (a : G), mul one a = a
  mul_left_inv (a : G) : mul (inv a) a = one

namespace group
attribute [simp] one_mul mul_left_inv
infix : 75 "*" => mul
variable {S : Type u} [group S]


@[simp] theorem mul_left_cancel (a b c : S) (h1 : a*b = a*c) : b = c :=
calc b = (one : S)*b := by rw [one_mul b]
     _ = ((inv a)*a)*b := by rw [mul_left_inv]
     _ = (inv a)*(a*b) := by rw [mul_assoc]
     _ = (inv a)*(a*c) := by rw [h1]
     _ = ((inv a)*a)*c := by rw [mul_assoc]
     _ = (one : S)*c := by rw [mul_left_inv]
     _ = c := by rw [one_mul]

theorem mul_eq_of_eq_inv_mul (a x y : S) (h1 : x = (inv a) * y) : a*x = y := by
apply mul_left_cancel (inv a)
rw [← mul_assoc,mul_left_inv,one_mul]
exact h1

@[simp] theorem mul_one (a : S) : a*(one : S)=a := by
apply mul_eq_of_eq_inv_mul
rw [mul_left_inv]

@[simp] theorem mul_right_inv (a : S) : a*(inv a)=one := by
apply mul_eq_of_eq_inv_mul
rw [mul_one]

@[simp] theorem inv_mul_cancel_left (a b : S) : (inv a) * (a*b) = b := by
rw [← mul_assoc]
simp

@[simp] theorem mul_inv_cancel_left (a b : S) : a * ((inv a)*b) = b := by
rw [← mul_assoc]
simp

@[simp] theorem inv_mul (a b : S) : (inv (a*b)) = (inv b)*(inv a) := by
rw [← one_mul (inv b), mul_assoc]
rw [← mul_left_inv (a*b),mul_assoc]
rw [mul_assoc]
simp

@[simp] theorem one_inv : inv one = (one : S) := by
rw [← mul_one (inv one)]
rw [mul_left_inv]

@[simp] theorem inv_inv (a : S) : inv (inv a) = a := by
apply mul_left_cancel (inv a)
simp