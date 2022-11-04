open Nat

def even (n : Nat) : Prop := ∃ d, n=2*d

example (n : Nat) : (even n) → (even (n+2)) := by
intro h1
apply Exists.elim h1
intro a h2
rw [h2,← Nat.mul_one 2,← Nat.left_distrib, Nat.mul_one]
apply Exists.intro (a+1)
rfl

theorem leq_eq_exist_nat_add {n m : Nat} : n ≤ m → ∃ k, m = n + k := by
intro h
induction h with
| refl => exact (Exists.intro 0 (Nat.add_zero n))
| step _ ih => apply Exists.elim ih
               intro x hx
               rw [hx,← Nat.add_comm, ← Nat.succ_add, Nat.add_comm]
               exact Exists.intro (succ x) rfl

def subtract (n m : Nat) : Nat :=
match m with
| zero => n
| succ k => pred (subtract n k)

theorem zero_sub : subtract zero k = zero := by
induction k with
| zero => rfl
| succ l ih => rw [subtract,ih,Nat.pred_zero]

theorem pred_sub_eq_sub_pred : pred (subtract n k) = subtract (pred n) k := by
induction k with
| zero => rw [subtract,subtract]
| succ k ih => rw [subtract,ih,subtract]

theorem left_sub_cancel : subtract (n+k) n = k := by
induction n with
| zero => rw [Nat.zero_add,subtract]
| succ n ih => rw [Nat.succ_add,subtract,pred_sub_eq_sub_pred,Nat.pred_succ,ih]

theorem sub_add_eq_sub_diff (h1 : n ≤ m) (h2 : k ≤ n) : subtract m n + subtract n k = subtract m k := by
cases n with
| zero => rw [subtract,zero_sub,Nat.add_zero,Nat.eq_zero_of_le_zero h2,subtract]
| succ l => have : ∃ r, m = succ l + r := leq_eq_exist_nat_add h1
            apply Exists.elim this
            intro x hx
            rw [hx]
            have : ∃ r, succ l = k + r := leq_eq_exist_nat_add h2
            apply Exists.elim this
            intro y hy
            rw [hy]
            rw [left_sub_cancel,left_sub_cancel]
            rw [Nat.add_assoc,left_sub_cancel,Nat.add_comm]

theorem sub_add_eq_sub_sub : subtract n (k+l) = subtract (subtract n k) l := by
induction l with
| zero => rw [Nat.add_zero,subtract]
| succ s ih => rw [Nat.add_succ,subtract,ih,← subtract]

theorem sub_mul_eq_mul_sub : subtract (k*n) (k*m) = k*(subtract n m) := by
induction m with
| zero => rw [Nat.mul_zero,subtract,subtract]
| succ s ih => rw [Nat.mul_succ,sub_add_eq_sub_sub,ih,subtract]
               cases (subtract n s) with
               | zero => rw [Nat.mul_zero,Nat.pred_zero,Nat.mul_zero,zero_sub]
               | succ r => rw [Nat.mul_succ,Nat.add_comm,left_sub_cancel,Nat.pred_succ]

-- simple lemma for even numbers
example {n m k : Nat} : (even n) → (even m) → subtract n m = k → even k := by
intro h1 h2 h3
apply Exists.elim h1
intro s hs
apply Exists.elim h2
intro r hr
rw [hs,hr] at h3
have : subtract (2*s) (2*r) = 2*(subtract s r) := sub_mul_eq_mul_sub
rw [this] at h3
exact Exists.intro (subtract s r) (Eq.symm h3)