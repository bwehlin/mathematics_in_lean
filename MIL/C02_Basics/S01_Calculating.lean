import MIL.Common
import Mathlib.Data.Real.Basic
-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_assoc, mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm, mul_comm a b, mul_comm, mul_assoc]

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc, mul_assoc, ← mul_assoc b, h, ← mul_assoc, ← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp', mul_comm, sub_self] at hyp
  exact hyp

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

variable (n : ℕ )
#check n
#check (n + 1.5 : ℝ )
-- #check (a : ℕ )

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

#check two_mul a

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw[ mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, ← add_assoc]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b, ← two_mul]

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)


-- ##################################
-- ##### HOMEWORK 1 #################
-- ##################################

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [add_mul, mul_add, mul_add, ← add_assoc]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := calc
  -- Using rw in calc
  (a + b) * (c + d) = a * (c + d) + b * (c + d) := by
    rw [add_mul]
  _ = a * c + a * d + b * (c + d) := by
    rw [mul_add]
  _ = a * c + a * d + b * c + b * d := by
    rw [mul_add, ← add_assoc]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := calc
  -- Using ring in each calc step
  (a + b) * (c + d) = a * (c + d) + b * (c + d) := by
    ring
  _ = a * c + a * d + b * (c + d) := by
    ring
  _ = a * c + a * d + b * c + b * d := by
    ring

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  -- I tried doing this only with the #checks below and above, but I'm not sure
  -- if it can be done without at least also using sub_self, and I'm unsure how
  -- to deal with (- b*a) without turning it into +(-(b * a)) using sub_eq_add_neg
  calc
    (a + b) * (a - b) = a * a - a * b + b * a - b * b := by
      rw [add_mul, mul_sub, mul_sub, add_sub]
    _ = a ^ 2 - a * b + b * a - b ^2 := by
      rw [pow_two, pow_two]
    _ = a ^ 2 + (b * a - b * a) - b ^ 2 := by
      rw [mul_comm, sub_eq_add_neg (a ^ 2) (b * a)]
      rw [add_assoc, add_comm (-(b * a)) (b * a), ← sub_eq_add_neg]
    _ = a ^ 2 - b ^ 2 := by
      rw [sub_self, add_zero]

-- It also works with linarith
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  linarith

-- ...and ring
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

-- ##################################
-- ##### HOMEWORK 1 END #############
-- ##################################

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
