import Mathlib
import Submission.Work.ChenPlan.H3.Defs

namespace Work.ChenPlan.H3

open Finset
open scoped BigOperators

open Commons.NumberTheory.Chen.ChenEight

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The odd primes below `M` that are `≥ k` are exactly the odd primes below `M` that are not
below `k`, i.e. `oddLt M \ oddLt k`. -/
lemma filter_oddLt_eq_sdiff (M k : ℕ) :
    (oddLt M).filter (fun p => k ≤ p) = oddLt M \ oddLt k := by
  ext p
  rw [Finset.mem_filter, Finset.mem_sdiff, Submission.mem_oddLt, Submission.mem_oddLt]
  constructor
  · rintro ⟨hp, hkp⟩
    exact ⟨hp, fun h => (not_lt.mpr hkp) h.2.2⟩
  · rintro ⟨hp, hpk⟩
    refine ⟨hp, ?_⟩
    by_contra hlt
    exact hpk ⟨hp.1, hp.2.1, not_le.mp hlt⟩

/-- **Splitting the odd sieve product at a real cut `w`.**  For `w < Y`, the odd primes below `Y`
that are `≥ w` are exactly the odd primes below `Y` that are not `< w`; consequently the product of
the inverse sieve factors over the former is `VsieveOdd ⌈w⌉₊ / VsieveOdd Y`. -/
theorem prod_oddLt_filter_inv_eq (Y : ℕ) (w : ℝ) (hw : w < (Y : ℝ)) :
    ∏ p ∈ (Commons.NumberTheory.Chen.ChenEight.oddLt Y).filter (fun p : ℕ => w ≤ (p : ℝ)),
        (1 - 1 / ((p:ℝ) - 1))⁻¹
      = Commons.NumberTheory.Chen.ChenEight.VsieveOdd ⌈w⌉₊
        / Commons.NumberTheory.Chen.ChenEight.VsieveOdd Y := by
  have hkY : ⌈w⌉₊ ≤ Y := Nat.ceil_le.mpr (le_of_lt hw)
  have hfil : (oddLt Y).filter (fun p : ℕ => w ≤ (p:ℝ))
      = (oddLt Y).filter (fun p : ℕ => ⌈w⌉₊ ≤ p) := by
    apply Finset.filter_congr
    intro p _
    exact Nat.ceil_le.symm
  rw [hfil, filter_oddLt_eq_sdiff]
  have hsub : oddLt ⌈w⌉₊ ⊆ oddLt Y := by
    intro p hp
    rw [Submission.mem_oddLt] at hp ⊢
    exact ⟨hp.1, hp.2.1, lt_of_lt_of_le hp.2.2 hkY⟩
  have hsd := Finset.prod_sdiff hsub (f := fun p : ℕ => (1 - 1/((p:ℝ)-1)))
  rw [Finset.prod_inv_distrib]
  have hVk : VsieveOdd ⌈w⌉₊ ≠ 0 := ne_of_gt (VsieveOdd_pos ⌈w⌉₊)
  have hP : (∏ x ∈ oddLt Y \ oddLt ⌈w⌉₊, (1 - 1/((x:ℝ)-1))) = VsieveOdd Y / VsieveOdd ⌈w⌉₊ := by
    rw [eq_div_iff hVk]
    simpa [VsieveOdd] using hsd
  rw [hP, inv_div]

end

end Work.ChenPlan.H3
