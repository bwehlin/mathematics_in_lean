import Mathlib.Data.Nat.GCD.Basic
import MIL.Common

example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right

theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
  induction' n with n hn
  · simp [fac]
  simp at *
  rw [pow_succ', fac]
  apply Nat.mul_le_mul (by linarith) hn

section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset

example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

example : (range n).prod f = ∏ x in range n, f x :=
  rfl

example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x in range n.succ, f x = ∑ x in range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
  Finset.prod_range_succ f n

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  induction' n with n ih
  · simp [fac, prod_range_zero]
  simp [fac, ih, prod_range_succ, mul_comm]

example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring

-- ##################################
-- ##### HOMEWORK 2 #################
-- ##################################

-- Not in the book: define the Fibonacci sequence as a function "fib : ℕ → ℕ" and run “#eval fib 10”, “#eval fib 1000” to check it computes

-- This works for small n (starts to struggle around n=30)
def fib : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 1 => fib n + fib (n - 1)

#eval fib 20
-- This does n=millions
def fib2 : Nat := Id.run do
  let mut x₂ := 1
  let mut x₁ := 1
  let mut x₀ := 1

  for _ in List.range (n - 2) do
    x₀ := x₁ + x₂
    x₂ := x₁
    x₁ := x₀

  return x₀

#eval fib2 1000
--#eval Nat.log 10 (fib2 10000000) -- 2,089,876 (after several minutes)
#check Nat.fib

#time #eval fib2 1000000
#time #eval Nat.fib 1000000

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction' n with n ih
  · simp

  have : (n+1)^2 = (6 * (n+1)^2)/6 := by norm_num

  have : ∑ i in range (n + 2), i ^ 2 = ((n*(n+1)*(2*n+1)) + (6*(n+1)^2))/6 := calc
    ∑ i in range (n + 2), i ^ 2 = ∑ i in range (n + 1), i ^ 2 + (n+1)^2 := by rw[Finset.sum_range_succ]
    _ = (n*(n+1)*(2*n+1))/6 + (n+1)^2 := by rw [ih]
    _ = (n*(n+1)*(2*n+1))/6 + (6*(n+1)^2)/6 := by linarith[this] -- somehow rw[this] doesn't work here
    _ = ((n*(n+1)*(2*n+1)) + (6*(n+1)^2))/6 := by omega  --by rw[Nat.add_div_of_dvd_left]; simp

  rw[this]
  ring_nf


end

-- ##################################
-- ##### HOMEWORK 2 END #############
-- ##################################

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | x, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  rw [add, ih]
  rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
  sorry
theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
  sorry
theorem zero_mul (n : MyNat) : mul zero n = zero := by
  sorry
theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
  sorry
theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
  sorry
end MyNat
