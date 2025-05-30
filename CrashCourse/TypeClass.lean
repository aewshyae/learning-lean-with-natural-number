import CrashCourse.NaturalNumber

def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => MyNat.zero
  | n + 1 => MyNat.succ (MyNat.ofNat n)

@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

#check 0
#check 1

instance : Add MyNat where
  add := MyNat.add

#check 1 + 1
#check MyNat.zero + MyNat.one

-- 1.4.4 練習問題
example : 1 = MyNat.one := by
  rfl

example : 2 = MyNat.two := by
  rfl

example : 1 + 1 = 2 := by
  rfl

example (n : MyNat) : n + 0 = n := by
  rfl
