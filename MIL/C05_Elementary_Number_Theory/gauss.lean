import MIL.Common


open Finset
open List

#check Finset.sum

theorem gauss (n : ℕ) : 2 * (∑ i ∈ range (n+1), i) = n * (n+1) := by

  let l1 : List ℕ := List.map Nat.succ (List.range (n+1))
  let l2 : List ℕ := l1.reverse

  have l1_nonempty : l1 ≠ [] := by simp[l1]

  have : List.foldl Nat.add 0 l1 = ∑ i ∈ range (n+1), i := by
    #check ∑ i ∈ range (n+1), i
  
    
