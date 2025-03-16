import MIL.Common

open Finset
open List

#check Finset.sum

theorem gauss (n : ℕ) : 2 * (∑ i ∈ range (n+1), i) = n * (n+1) := by

  let l1 : List ℕ := List.range (n+1)

  --let l1 : List ℕ := List.map Nat.succ (List.range (n+1))
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

  have isum : ∀ i < (n+1), l1[i] + l2[i] = n := by
    intro i ih
    simp[l1, l2]
    rw [Nat.add_sub_cancel']
    apply Nat.lt_add_one_iff.mp at ih
    exact ih




  have : ∀ x ∈ lz, x.2 = n - x.1 := by
    intro x h
    simp[lz,l2,l1] at h
    let g : ℕ := List.findIdx x.1
    rw [List.reverse] at h




    rw [List.unzip lz] at h


    dsimp[lz]
    intro x



  have : ∀ x ∈ l3, x = n - 1 := by
    intro x
    dsimp[l3]







  apply List.sum_eq_card_nsmul







  have : r1 + r2 = n * (n + 1) := by
    linarith

  have l1_nonempty : l1 ≠ [] := by simp[l1]

  have : List.foldl Nat.add 0 l1 = ∑ i ∈ range (n+1), i := by
    #check ∑ i ∈ range (n+1), i
