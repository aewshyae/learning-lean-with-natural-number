import CrashCourse.Simp

-- 加法の交換法則
theorem MyNat.add_comm ( m n : MyNat) : m + n = n + m := by
  induction n
  case zero => simp[MyNat.ctor_eq_zero]
  case succ n' ih => simp[ih]
-- 加法の結合法則
theorem MyNat.add_assoc (l m n : MyNat) : l + m + n = l + (m + n) := by
  induction n
  case zero => rfl
  case succ _ ih => simp[ih]

-- 使えるけど煩雑
example (l m n : MyNat): l + m + n + 3 = m + (l + n) + 3 := calc
  _ = m + l + n + 3 := by rw [MyNat.add_comm l m]
  _ = m + (l + n) + 3 := by rw [MyNat.add_assoc m l n]

-- α: 型引数
instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc
instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm

example (l m n : MyNat): l + m + n + 3 = m + (l + n) + 3 := by ac_rfl

-- 1.7.3 練習問題

example (l m n : MyNat): l + (1 + m) + n = m + (l + n) + 1 := by ac_rfl

-- TODO: add_assoc と add_comm でも書けるはず
-- example (l m n : MyNat): l + (1 + m) + n = m + (l + n) + 1 := calc
--   _ = l + 1 + m + n := by rw [MyNat.add_assoc l 1 m]
--   _ = l + 1 + n + m := by sorry
