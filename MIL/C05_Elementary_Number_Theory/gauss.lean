import MIL.Common

open Finset
open List

theorem gauss (n : ℕ) : 2 * (∑ i ∈ range (n+1), i) = n * (n+1) := by

  -- We have two lists, l1 containing the terms of (∑ i ∈ range (n+1), i),
  -- and l2 being the reverse of l1.
  let l1 : List ℕ := List.range (n+1)
  let l2 : List ℕ := l1.reverse

  -- We begin by showing that summing the elements in the lists is the same
  -- as taking the original sums.
  have r1sum : l1.sum = (∑ i ∈ range (n+1), i) := by
    dsimp[l1]
    induction' n with n ih
    · simp
      apply List.sum_eq_zero
      simp
    · rw [← List.map_id (List.range (n+1+1)), List.sum_range_succ, List.map_id, id_def]
      rw [ih]
      nth_rw 2 [Finset.sum_range_succ]

  have r2sum : l2.sum = (∑ i ∈ range (n+1), i) := by
    dsimp [l2]
    rw [List.sum_reverse]
    apply r1sum

  -- Turn the goal into l1.sum + l2.sum = n*(n+1)
  rw [two_mul]
  nth_rw 1 [← r1sum, ← r2sum]

  -- Next, we create a new list `l3` that is `l1+l2` pointwise. It seems that
  -- in the past there was List.Func.add for this purpose, but it appears
  -- to be gone. In lieu, we create a zipped list:
  -- `lz = [(l1[0], l2[0]), (l1[1], l2[1]), ..., (l1[n], l2[n])]`
  -- The "summed list" can then be created by mapping `x => x.1 + x.2` over `lz`
  let lz : List (ℕ × ℕ) := List.zip l1 l2
  let l3 : List ℕ := List.map (fun x => x.1 + x.2) lz

  -- As a technicality, we must establish that l1, l2 and l3 all have the same
  -- length: n+1.
  have l1len : l1.length = n + 1 := by apply List.length_range
  have l2len : l2.length = n + 1 := by
    symm at l1len
    rw [l1len]
    apply List.length_reverse
  have l3len : l3.length = n + 1 := by
    simp [l3,lz,l1,l2]

  -- We now show that l3 is equal to a constant list of `n`

  let lc : List ℕ := List.map (fun x => n) l3

  have : l3 = lc := by
    have : ∀ i, (h : i < n+1) → l3[i] = n := by
      intro i ih
      simp[l3,lz,l1,l2]
      rw [Nat.add_sub_cancel']
      apply Nat.lt_add_one_iff.mp at ih
      exact ih

    apply List.ext_get
    · symm
      rw [List.length_map]
    simp
    intro x nl3 nlc
    rw [this]
    simp[lc]
    simp[l3,lc,lz, l1len,l2len] at nl3
    exact nl3

  -- Sum of a constant list of `n`, of length `(n+1)` is `(n+1)*n`

  have l3sum : l3.sum = (n+1)*n := by
    rw [← l3len]
    apply List.sum_eq_card_nsmul l3
    · rw [this]
      intro x
      simp[lc]

  -- Some unzipping to show that the sum over list of pairs is them same
  -- as adding the individual list sums.

  have : l3.sum = l1.sum + l2.sum := by

    have pfst : List.map Prod.fst (l1.zip l2) = l1 := by
      apply List.map_fst_zip
      rw[l1len,l2len]
    have psnd : List.map Prod.snd (l1.zip l2) = l2 := by
      apply List.map_snd_zip
      rw[l1len,l2len]

    simp[l3,lz]
    rw[pfst,psnd]

  -- Putting it all together!
  rw[← this, l3sum, mul_comm]
