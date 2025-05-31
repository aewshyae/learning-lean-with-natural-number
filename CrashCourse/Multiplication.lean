import CrashCourse.Apply

-- 掛け算を、足し算の繰り返しとして再帰的に定義
def MyNat.mul (m n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => n + (MyNat.mul m n + m)

instance : Mul MyNat where
  mul := MyNat.mul

-- 乗算の分配法則
-- - m * (n * 1) = m * n + m
-- - (m + 1) * n = m * n + n
-- TODO: FIXME: なぜか rfl でエラーになる...
theorem MyNat.mul_add_one (m n : MyNat) : m * (n + 1) = m * n + m := by rfl

-- こちらのエラーは、 mul_add_one のエラーの伝播によるものと考えられる
theorem MyNat.add_one_mul (m n : MyNat) : (m + 1) * n = m * n + n := by
  induction n
  case zero => rfl
  case succ n ih => calc
    _ = (m + 1) * (n + 1) := by rfl
    _ = (m + 1) * n + (m + 1) := by rw [MyNat.mul_add_one]
    _ = m * n + n + (m + 1) := by rw [ih]
    _ = m * n + m + (n + 1) := by ac_rfl
    _ = m * (n + 1) + n + 1 := by rw [MyNat.mul_add_one]
