import MIL.Common

open Finset
open List

#check Finset.sum

theorem gauss (n : ℕ) : 2 * (∑ i ∈ range (n+1), i) = n * (n+1) := by

  let l1 : List ℕ := List.range (n+1)
  let l2 : List ℕ := l1.reverse

  let r1 : ℕ := l1.sum
  let r2 : ℕ := l2.sum

  have r1sum : r1 = (∑ i ∈ range (n+1), i) := by
    dsimp[r1, l1]
    induction' n with n ih
    · simp
      apply List.sum_eq_zero
      simp
    · rw [← List.map_id (List.range (n+1+1)), List.sum_range_succ, List.map_id, id_def]
      rw [ih]
      nth_rw 2 [Finset.sum_range_succ]

  have r2sum : r2 = (∑ i ∈ range (n+1), i) := by
    dsimp [r2,l2]
    rw [List.sum_reverse]
    apply r1sum

  rw [two_mul]
  nth_rw 1 [← r1sum, ← r2sum]

  let lz : List (ℕ × ℕ) := List.zip l1 l2
  let l3 : List ℕ := List.map (fun x => x.1 + x.2) lz

  have l1len : l1.length = n + 1 := by apply List.length_range
  have l2len : l2.length = n + 1 := by
    symm at l1len
    rw [l1len]
    apply List.length_reverse

  have l1less : ∀ i ∈ List.range (n+1), i < l1.length := by
    intro i ih
    apply List.mem_range.mp
    rw[l1len]
    exact ih

  have ll : ∀ i < (n+1), i < l1.length := by
    intro i ih
    apply l1less
    apply List.mem_range.mpr at ih
    exact ih

  have isum : ∀ i, (h : i < n+1) → l1[i] + l2[i] = n := by
    intro i ih
    simp[l1, l2]
    rw [Nat.add_sub_cancel']
    apply Nat.lt_add_one_iff.mp at ih
    exact ih

  have l3len : l3.length = n + 1 := by
    simp [l3,lz,l1,l2]


  have l3len_pred : ∀ i < (n+1), i < l3.length := by
    rw [List.length_map, List.length_zip, l1len, l2len]
    intro i ih
    rw [min_self]
    exact ih

  have l3i_eq_n : ∀ i, (h : i < n+1) → l3[i]'(l3len_pred i h) = n := by
    simp [l3, lz]
    apply isum

  -- We will show that l3 is equal to a constant list of `n`

  let lc : List ℕ := List.map (fun x => n) l3
  have lcl3len : lc.length = l3.length := by rw[List.length_map]

  have l3len_eq_np1 : l3.length = n+1 := by simp [l3,lz, l1len,l2len]
  have lclen : ∀ i < (n+1), i < lc.length := by
    rw [lcl3len]
    apply l3len_pred

  have : l3 = lc := by
    apply List.ext_get
    symm
    apply lcl3len
    simp
    intro x nl3 nlc
    rw [l3i_eq_n]
    simp[lc]
    simp[l3,lc,lz, l1len,l2len] at nl3
    exact nl3

  -- Sum of a constant list

  have l3sum : l3.sum = (n+1)*n := by
    rw [← l3len]
    apply List.sum_eq_card_nsmul l3
    · rw [this]
      intro x
      simp[lc]

  have : l3.sum = l1.sum + l2.sum := by

    have pfst : List.map Prod.fst (l1.zip l2) = l1 := by
      apply List.map_fst_zip
      rw[l1len,l2len]
    have psnd : List.map Prod.snd (l1.zip l2) = l2 := by
      apply List.map_snd_zip
      rw[l1len,l2len]

    simp[l3,lz]
    rw[pfst,psnd]

  simp[r1,r2]
  rw[← this, l3sum, mul_comm]
