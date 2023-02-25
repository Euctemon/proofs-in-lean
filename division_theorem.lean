theorem lt_succ_eq_or_succ_lt (x b : Nat) (hb : b ≠ 0) : x < b → Nat.succ x = b ∨ Nat.succ x < b := by
intro h1
have h2 : Nat.succ x ≤ b := Nat.succ_le_of_lt h1
rw [Eq.symm (Nat.succ_pred hb)] at h2
have h3 : Nat.succ x ≤ Nat.pred b ∨ Nat.succ x = Nat.succ (Nat.pred b) := Nat.le_or_eq_or_le_succ h2
rw [Nat.succ_pred hb] at h3
apply Or.elim h3
intro h4
have h5 : Nat.succ x < Nat.succ (Nat.pred b) := Nat.lt_succ_of_le h4
rw [Nat.succ_pred hb] at h5
exact Or.intro_right (Nat.succ x = b) h5
intro h6
exact Or.intro_left (Nat.succ x < b) h6

theorem succ_eq_succ (a b : Nat) : a = b → Nat.succ a = Nat.succ b := by
intro hp
induction a <;> rw [hp]

theorem division_theorem (a b : Nat) (h : b ≠ 0) : ∃ r q : Nat, a = q*b+r ∧ r < b := by
induction a with
| zero => apply Exists.intro 0
          apply Exists.intro 0
          rw [Nat.zero_mul]
          have h1 : 0 = 0 + 0 := rfl
          have h2 : 0 < b := Nat.zero_lt_of_ne_zero h
          apply And.intro h1 h2
| succ a ha => apply Exists.elim ha
               intro x hx
               apply Exists.elim hx
               intro y hy
               have shoo : Nat.succ x = b ∨ Nat.succ x < b := lt_succ_eq_or_succ_lt x b h hy.right
               apply Or.elim shoo
               intro foo2
               apply Exists.intro 0
               apply Exists.intro (y+1)
               have h9 : 0<b := Nat.zero_lt_of_ne_zero h
               suffices h : Nat.succ a = (y+1)*b + 0 from And.intro h h9
               rw [Nat.add_mul,Nat.one_mul,Nat.add_zero,Eq.symm foo2,Nat.succ_eq_add_one x]
               rw [← Nat.add_assoc,Nat.add_one,Nat.add_one]
               apply succ_eq_succ
               rw [foo2]
               exact hy.left
               intro hu
               apply Exists.intro (x+1)
               apply Exists.intro y
               apply And.intro
               rw [← Nat.add_assoc,Nat.add_one]
               apply succ_eq_succ
               exact hy.left
               exact hu
