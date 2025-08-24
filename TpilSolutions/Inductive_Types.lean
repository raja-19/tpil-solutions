namespace Exercise1

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

open Nat

def add (n m : Nat) : Nat :=
  match m with
  | zero => n
  | succ m => succ (add n m)

instance : Add Nat where
  add := add

theorem add_zero (n : Nat) : n + zero = n := rfl
theorem add_succ (n m : Nat) : n + succ m = succ (n + m) := rfl

theorem zero_add (n : Nat) : zero + n = n := by
  induction n with
  | zero => rfl
  | succ n hn => rw [add_succ, hn]

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) := by
  induction m with
  | zero => rfl
  | succ m hm => rw [add_succ, add_succ, hm]

theorem add_assoc (n m k : Nat) : n + m + k = n + (m + k) := by
  induction k with
  | zero => rfl
  | succ k hk => rw [add_succ, add_succ, add_succ, hk]

theorem add_comm (n m : Nat) : n + m = m + n := by
  induction m with
  | zero => rw [add_zero, zero_add]
  | succ m hm => rw [add_succ, succ_add, hm]

def mul (n m : Nat) : Nat :=
  match m with
  | zero => zero
  | succ m => mul n m + n

instance : Mul Nat where
  mul := mul

theorem mul_zero (n : Nat) : n * zero = zero := rfl
theorem mul_succ (n m : Nat) : n * succ m = n * m + n := rfl

theorem zero_mul (n : Nat) : zero * n = zero := by
  induction n with
  | zero => rfl
  | succ n hn => rw [mul_succ, add_zero, hn]

theorem succ_mul (n m : Nat) : succ n * m = n * m + m := by
  induction m with
  | zero => rfl
  | succ m hm => rw [mul_succ, hm, add_succ, mul_succ, add_succ, add_assoc, add_comm m, ← add_assoc]

theorem mul_comm (n m : Nat) : n * m = m * n := by
  induction m with
  | zero => rw [mul_zero, zero_mul]
  | succ m hm => rw [mul_succ, succ_mul, hm]

theorem mul_add (n m k : Nat) : n * (m + k) = n * m + n * k := by
  induction k with
  | zero => rfl
  | succ k hk => rw [add_succ, mul_succ, hk, mul_succ, ← add_assoc]

theorem add_mul (n m k : Nat) : (n + m) * k = n * k + m * k := by
  rw [mul_comm, mul_comm n, mul_comm m, mul_add]

theorem mul_assoc (n m k : Nat) : n * m * k = n * (m * k) := by
  induction k with
  | zero => rfl
  | succ k hk => rw [mul_succ, mul_succ, mul_add, hk]

theorem mul_one (n : Nat) : n * succ zero = n := by
  rw [mul_succ, mul_zero, zero_add]

theorem one_mul (n : Nat) : succ zero * n = n := by
  rw [mul_comm, mul_one]

def pred (n : Nat) :=
  match n with
  | zero => zero
  | succ n => n

theorem pred_zero : pred zero = zero := rfl
theorem pred_succ (n : Nat) : pred (succ n) = n := rfl

def sub (n m : Nat) :=
  match m with
  | zero => n
  | succ m => pred (sub n m)

instance : Sub Nat where
  sub := sub

def sub_zero (n : Nat) : n - zero = n := rfl
def sub_succ (n m : Nat) : n - succ m = pred (n - m) := rfl

theorem zero_sub (n : Nat) : zero - n = zero := by
  induction n with
  | zero => rfl
  | succ n hn => rw [sub_succ, hn, pred_zero]

theorem succ_sub_succ (n m : Nat) : succ n - succ m = n - m := by
  induction m with
  | zero => rfl
  | succ m hm => rw [sub_succ, hm, sub_succ]

theorem add_sub (n m : Nat) : n + m - m = n := by
  induction m with
  | zero => rfl
  | succ m hm => rw [add_succ, succ_sub_succ, hm]

theorem mul_pred (n m : Nat) : n * pred m = n * m - n := by
  induction m with
  | zero => rw [pred_zero, mul_zero, zero_sub]
  | succ m hm => rw [pred_succ, mul_succ, add_sub]

def sub_sub (n m k : Nat) : n - m - k = n - (m + k) := by
  induction k with
  | zero => rfl
  | succ k hk => rw [sub_succ, add_succ, sub_succ, hk]

def mul_sub (n m k : Nat) : n * (m - k) = n * m - n * k := by
  induction k with
  | zero => rfl
  | succ k hk => rw [sub_succ, mul_pred, hk, mul_succ, ← sub_sub]

def pow (n m : Nat) :=
  match m with
  | zero => succ zero
  | succ m => (pow n m) * n

theorem pow_zero (n : Nat) : pow n zero = succ zero := rfl
theorem pow_succ (n m : Nat) : pow n (succ m) = pow n m * n := rfl

theorem pow_add (n m k : Nat) : pow n (m + k) = pow n m * pow n k := by
  induction k with
  | zero => rw [add_zero, pow_zero, mul_one]
  | succ k hk => rw [add_succ, pow_succ, hk, pow_succ, mul_assoc]

theorem mul_pow (n m k : Nat) : pow (n * m) k = pow n k * pow m k := by
  induction k with
  | zero => rfl
  | succ k hk => rw [pow_succ, hk, pow_succ, pow_succ, ← mul_assoc, mul_assoc _ _ n, mul_comm _ n,
    ← mul_assoc, ← mul_assoc]

theorem pow_pow (n m k : Nat) : pow (pow n m) k = pow n (m * k) := by
  induction k with
  | zero => rfl
  | succ k hk => rw [pow_succ, hk, mul_succ, pow_add]

end Exercise1

namespace Exercise2

open List

def length (as : List α) : Nat :=
  match as with
  | nil => 0
  | cons _ as => length as + 1

theorem length_nil : length (nil : List α) = 0 := rfl
theorem length_cons (a : α) (as : List α) : length (a :: as) = length as + 1 := rfl

theorem length_append (as bs : List α) : length (as ++ bs) = length as + length bs := by
  induction as with
  | nil => rw [nil_append, length_nil, Nat.zero_add]
  | cons a as ha =>
    rw [cons_append, length_cons, ha, length_cons]
    simp [Nat.add_assoc, Nat.add_comm]

def reverse (as : List α) :=
  match as with
  | nil => as
  | cons a as => reverse as ++ [a]

theorem reverse_nil : reverse (nil : List α) = nil := rfl
theorem reverse_cons (as : List α) : reverse (a :: as) = reverse as ++ [a] := rfl

theorem length_reverse (as : List α) : length (reverse as) = length as := by
  induction as with
  | nil => rfl
  | cons a as ha => rw [reverse_cons, length_append, ha, length_cons, length_cons, length_nil,
    Nat.zero_add]

theorem reverse_append (as bs : List α) : reverse (as ++ bs) = reverse bs ++ reverse as := by
  induction as with
  | nil => rw [nil_append, reverse_nil, append_nil]
  | cons a as ha => rw [cons_append, reverse_cons, ha, reverse_cons, append_assoc]


theorem reverse_reverse (as : List α) : reverse (reverse as) = as := by
  induction as with
  | nil => rfl
  | cons a as ha => rw [reverse_cons, reverse_append, ha, reverse_cons, reverse_nil, nil_append,
    cons_append, nil_append]

end Exercise2

namespace Exercise3

inductive Formula where
  | const : Nat → Formula
  | var : Nat → Formula
  | plus : Formula → Formula → Formula
  | times : Formula → Formula → Formula

open Formula

def eval (f : Formula) (val : Nat → Nat) : Nat :=
  match f with
  | const n => n
  | var n => val n
  | plus a b => eval a val + eval b val
  | times a b => eval a val * eval b val

end Exercise3

namespace Exercise4

inductive Proposition where
  | const : Bool → Proposition
  | var : Nat → Proposition
  | not : Proposition → Proposition
  | and : Proposition → Proposition → Proposition
  | or : Proposition → Proposition → Proposition
  | imp : Proposition → Proposition → Proposition
  | iff : Proposition → Proposition → Proposition

def eval (p : Proposition) (val : Nat → Bool) : Bool :=
  match p with
  | Proposition.const t => t
  | Proposition.var a => val a
  | Proposition.not a => !(eval a val)
  | Proposition.and a b => (eval a val) && (eval b val)
  | Proposition.or a b => (eval a val) || (eval b val)
  | Proposition.imp a b => (eval a val) ≤ (eval b val)
  | Proposition.iff a b => (eval a val) == (eval b val)

-- complexity as in nestedness?

def complexity (p : Proposition) : Nat :=
  match p with
  | Proposition.const _ => 1
  | Proposition.var _ => 1
  | Proposition.not a => complexity a + 1
  | Proposition.and a b => max (complexity a) (complexity b) + 1
  | Proposition.or a b => max (complexity a) (complexity b) + 1
  | Proposition.imp a b => max (complexity a) (complexity b) + 1
  | Proposition.iff a b => max (complexity a) (complexity b) + 1

def subst (p q : Proposition) (n : Nat) : Proposition :=
  match p with
  | Proposition.const _ => p
  | Proposition.var m => cond (n = m) q p
  | Proposition.not a => Proposition.not (subst a q n)
  | Proposition.and a b => Proposition.and (subst a q n) (subst b q n)
  | Proposition.or a b => Proposition.or (subst a q n) (subst b q n)
  | Proposition.imp a b => Proposition.imp (subst a q n) (subst b q n)
  | Proposition.iff a b => Proposition.iff (subst a q n) (subst b q n)

end Exercise4
