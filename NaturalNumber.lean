set_option pp.fieldNotation.generalized false

/-- 自前で実装した自然数 -/
inductive MyNat where
  | zero
  | succ (N :MyNat)

#check MyNat.zero
#check MyNat.succ
#check MyNat.succ MyNat.zero

/-- 1 -/
def MyNat.one := MyNat.succ MyNat.zero
/-- 2 -/
def MyNat.two := MyNat.succ MyNat.one

/-- 足し算 -/
def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n => MyNat.succ (MyNat.add m n)

-- check: 型チェック
#check MyNat.add MyNat.one MyNat.one = MyNat.two

-- reduce: 簡約. 関数適用、定数展開してコンストラクタの表現にする
#reduce MyNat.add MyNat.one MyNat.one
#reduce MyNat.two

-- example: 命題の証明を名前をつけずに行う(後で参照しない)
example : MyNat.add MyNat.one MyNat.one = MyNat.two := by
rfl -- tacticのひとつ.証明のキーワード
