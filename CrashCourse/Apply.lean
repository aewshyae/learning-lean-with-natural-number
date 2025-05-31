-- a + b = a + c ならば b = c

import CrashCourse.BetterInduction

#eval True → True
#eval True → False

-- h(hypothesis): P → Q の場合に apply h すると、 goal が P　から Q　に変わる
example (P Q : Prop) (h: P → Q) (hP: P) : Q := by
  apply h
  guard_target =ₛ P
  apply hP

example (P Q : Prop) (h : P → Q) (hP : P) : Q := by
  apply h hP

-- intro: 仮定を置く
example (P Q : Prop): Q → (P → Q) := by
  intro hQ
  guard_hyp hQ: Q
  guard_target =ₛ P → Q
  intro hP -- h は仮定の接頭辞
  apply hQ

-- ¬: 否定 (`\not`)
example (P Q: Prop) (h : P → ¬ Q) : Q → ¬ P := by
  intro hQ
  guard_target =ₛ ¬ P
  intro hP
  guard_target =ₛ False
  apply h hP hQ

-- injection: 各コンストラクタの像が重ならず、すべて単射となることを示す
example (n : MyNat) : MyNat.succ n ≠ MyNat.zero := by
  intro h
  injection h

example (m n : MyNat) (h : MyNat.succ m = MyNat.succ n) : m = n := by
  injection h

example (m n : MyNat) (h : m + 1 = n + 1) : m = n := by
  injection h

-- 加法のキャンセル可能性の証明
-- 左から足す演算 `(l + ⬝)`
theorem MyNat.add_left_cancel {l m n : MyNat} : l + m = l + n → m = n := by
  intro h
  induction l
  case zero =>
    simp at h
    rw [h]
  case succ l ih =>
    apply ih
    rw [show l + 1 + m = l + m + 1 from by ac_rfl] at h
    rw [show l + 1 + n = l + n + 1 from by ac_rfl] at h
    injection h

-- 右から足す演算 `(⬝ + m)`
theorem MyNat.add_right_cancel {l m n : MyNat} : l + m = n + m → l = n := by
  intro h
  rw [MyNat.add_comm l, MyNat.add_comm n] at h
  apply MyNat.add_left_cancel h --左からの演算を適用

-- 加法のキャンセルはsimpで扱いたいが今のままではできない
section
  -- section local な定義
  attribute [local simp] MyNat.add_left_cancel

  example {l m n : MyNat} : l + m = l + n → m = n := by
    fail_if_success simp
    sorry
end

-- 同値性 `↔` (`\iff`, if and only if)
@[simp] theorem MyNat.add_left_cancel_iff {l m n : MyNat} : l + m = l + n ↔ m = n := by
  constructor
  . apply MyNat.add_left_cancel
  . intro h
    rw [h]

@[simp] theorem MyNat.add_right_cancel_iff {l m n : MyNat} : l + m = n + m ↔ l = n := by
  constructor
  . apply MyNat.add_right_cancel
  . intro h
    rw [h]

example {l m n : MyNat} : l + m = l + n → m = n := by simp

-- 同値性の証明
example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  . apply h1
  . apply h2

-- 同値な命題の置換
example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q := by
  rw [h] at hP
  apply hP

-- 1.9.7 練習問題
example (n m : MyNat) : n + (1 + m) = n + 2 →  m = 1 := by
  intro h
  simp at h
  rw [show 2 = 1 + 1 from rfl] at h
  simp at h
  rw[h]
