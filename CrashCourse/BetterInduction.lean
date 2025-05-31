import CrashCourse.AcRfl

-- デフォルトの帰納の仕組み上、煩雑になる
example (m n : MyNat) : m + n = n + m := by
  induction n
  case zero =>
    guard_target =ₛ m + MyNat.zero = MyNat.zero + m
    simp[MyNat.ctor_eq_zero]
  case succ n ih =>
    guard_target =ₛ m + MyNat.succ n = MyNat.succ n + m
    simp[ih]

-- 帰納法の原理
def MyNat.rec_.{u} {motive : MyNat → Sort u} -- {u}: 暗黙の引数, {}内: 証明したい命題
  (zero : motive .zero)  -- 0で成り立つ仮定
  (succ : (n : MyNat) → motive n → motive (.succ n)) (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.rec_ zero succ n)

-- MyNatコンストラクタを直接使わない書き直し
def MyNat.recAux.{u} {motive : MyNat → Sort u}
  (zero : motive 0)
  (succ : (n : MyNat) → motive n → motive (n + 1)) (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

attribute [induction_eliminator] MyNat.recAux

-- rexAux を使った帰納法
example (m n : MyNat) : m + n = n + m := by
  induction n
  case zero =>
    guard_target =ₛ m + 0 = 0 + m
    simp[MyNat.ctor_eq_zero]
  case succ n ih =>
    guard_target =ₛ m + (n + 1) = (n + 1) + m
    ac_rfl

-- 1.8.4 練習問題
private def MyNat.pred (n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => n

example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  induction n
  case zero => rfl
  case succ n' ih =>
    ac_rfl
