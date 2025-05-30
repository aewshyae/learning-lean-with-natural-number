import CrashCourse.Induction

--1.6 simp: 単純化

example (n : MyNat) : 0 +  (n + 0) = n := by
  fail_if_success simp
  rw [MyNat.add_zero, MyNat.zero_add]

attribute [simp] MyNat.add_zero MyNat.zero_add
example (n : MyNat) : 0 +  (n + 0) = n := by simp

theorem MyNat.ctor_eq_zero : MyNat.zero = 0 := by rfl
example : MyNat.zero = 0 := by
  simp [MyNat.ctor_eq_zero]

attribute [simp] MyNat.add_succ

example (m n : MyNat) (h : m + n + 0 = n + m) : m + n = n + m := by
  simp at h
  guard_hyp h : m + n = n + m
  rw [h]

@[simp] theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n
  case zero => rfl
  case succ n' ih => simp[ih]

/-- info: Try this: simp only [MyNat.add_succ, ih] -/
#guard_msgs in
  example ( m n : MyNat) : .succ m + n = .succ (m + n) := by
    induction n
    case zero => rfl
    case succ n' ih => simp? [ih]

-- calc
example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n
  case zero => rfl
  case succ n' ih => calc
    _ = (m.succ + n').succ := by rw[MyNat.add_succ]
    _ = (m + n').succ.succ := by rw [MyNat.succ_add]
    _ = (m + n'.succ).succ := by rw [MyNat.add_succ]

example (n : MyNat) : 1 + n = n + 1 := calc
  _ = .succ 0 + n := by rfl
  _ = .succ (0 + n) := by rw [MyNat.succ_add]
  _ = .succ n := by rw [MyNat.zero_add]
  _ = n + 1 := by rfl

-- 1.6.6 練習問題
example (n : MyNat) : 2 + n = n + 2 := by
  induction n
  case zero => rfl
  case succ n' ih => simp [ih]
