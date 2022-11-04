def divisor (n m : Nat) : Prop := ∃ c, n = m*c
def even (n : Nat) : Prop := ∃ d, n=2*d

infixl:40 " | " => divisor

example : (a | b*c) → a | b ∧ a | c := by
intro h
apply Exists.elim h
intro x hx
apply And.intro <;> rw [Nat.mul_assoc] at hx
exact Exists.intro (c*x) hx
rw [Nat.mul_left_comm] at hx
exact Exists.intro (b*x) hx

def rel_prime (n m : Nat) : Prop := (¬ n = 1 ∧ ¬ m = 1) ∧ ∀ c, (n | c) ∧ (m | c) → c = 1

example (a b : Nat) : even a → rel_prime a b → ¬ even b := by
intro h1 h2 h3
apply Exists.elim h1
intro x hx
apply Exists.elim h3
intro y hy
have ab_even : a | 2 ∧ b | 2 := And.intro (Exists.intro x hx) (Exists.intro y hy)
have : 2 = 1 := (h2.right 2) ab_even
contradiction

theorem rel_prime_not_eq (n m : Nat) : rel_prime n m → ¬ n = m := by
intro h1 h2
have h4 : n | m ∧ m | m → m = 1 := h1.right m
apply h1.left.right
apply h4
apply And.intro
rw [h2]
apply Exists.intro 1
exact Eq.symm (Nat.mul_one m)
apply Exists.intro 1
exact Eq.symm (Nat.mul_one m)