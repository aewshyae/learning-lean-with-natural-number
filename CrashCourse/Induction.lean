import CrashCourse.TypeClass

--  rfl はエラーになる: tactic 'rfl' failed, the left-hand side 0 + n is not definitionally equal to the right-hand side
example (n : MyNat) : 0 + n = n := by
  fail_if_success rfl -- 失敗の検証
  sorry

-- 異なる式として簡約される。 fun() はラムダ式,無名関数
#reduce fun (n : MyNat) => n + 0
#reduce fun (n : MyNat) => 0 + n

set_option pp.fieldNotation.generalized false in

-- guard_target: https://seasawher.github.io/mathlib4-help/tactics/#guard_target
-- guard_hyp: https://lean-ja.github.io/lean-by-example/Tactic/GuardHyp.html
-- =ₛ の ₛは `\_` + `s` で入力できる
example (n : MyNat) : 0 + n = n := by
  induction n
  case zero =>
    -- 0 + 0 = 0
    guard_target =ₛ 0 + MyNat.zero = MyNat.zero
    rfl
  case succ n' ih =>
    guard_target =ₛ 0 + MyNat.succ n' = MyNat.succ n'
    guard_hyp ih : 0 + n' = n'
    sorry


-- 1.5.4 `rw` 等式置換
theorem MyNat.add_zero (n : MyNat): n + 0 = n := by rfl
example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [MyNat.add_zero]

theorem MyNat.add_zero_rev (n : MyNat) : n = n + 0 := by rfl
example (m n : MyNat) : n + m = (n + 0) + m := by
  rw [← MyNat.add_zero_rev]

example (m n : MyNat) (h : m + 0 = n) : n + m = m+ n := by
  rw [MyNat.add_zero] at h -- h を置換し m = n
  rw [h]

-- 1.5.5 証明完成
theorem MyNat.add_succ (m n : MyNat) : m + MyNat.succ n = MyNat.succ (m + n) := by rfl
theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    rw [MyNat.add_succ, ih]

-- 1.5.6 練習問題
example (n : MyNat) : 1 + n = MyNat.succ n := by
  induction n
  case zero =>
    rfl
  case succ n' ih =>
    rw [MyNat.add_succ, ih]
