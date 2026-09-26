import Mathlib

namespace Work.PTCert.ldlChainSound

/-- Evaluating the sum of `g .val` over `Fin n` with one index `i` removed: it splits into
the terms with index below `i.val` and the terms with index above `i.val`. -/
theorem sum_univ_erase_eq {n : ℕ} (i : Fin n) (g : ℕ → ℤ) :
    Finset.sum (Finset.univ.erase i) (fun j => g j.val)
      = Finset.sum (Finset.range i.val) g + Finset.sum (Finset.range (n - i.val - 1)) (fun d => g (i.val + (d + 1))) := by
  have hm : n - i.val - 1 + 1 = n - i.val := by omega
  have hn : i.val + (n - i.val) = n := by omega
  -- Rewrite the erased sum as the full sum over `range n` minus the removed term.
  have h1 : Finset.sum (Finset.univ.erase i) (fun j => g j.val)
      = Finset.sum (Finset.range n) g - g i.val := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), Fin.sum_univ_eq_sum_range]
  -- Split `range n` at `i.val` and isolate the removed term.
  have key : Finset.sum (Finset.range n) g
      = Finset.sum (Finset.range i.val) g
        + (g i.val + Finset.sum (Finset.range (n - i.val - 1)) (fun d => g (i.val + (d + 1)))) := by
    conv_lhs => rw [← hn]
    rw [Finset.sum_range_add]
    congr 1
    conv_lhs => rw [← hm]
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero]
    ring
  rw [h1, key]
  ring

end Work.PTCert.ldlChainSound
