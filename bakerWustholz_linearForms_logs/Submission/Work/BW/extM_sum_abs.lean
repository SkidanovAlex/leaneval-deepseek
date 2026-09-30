import Mathlib
import Submission.Work.BW.DefsMP

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `extM_sum_abs`: the weight sums of `extM σ M'` and of `M'` agree

`extM σ M'` extends the rows of an integer matrix `M' : Fin ρ → Fin N → ℤ` by zero off the
coordinate set `range σ`, `σ : Fin N → Fin r` being injective (`DefsMP`). Consequently, for any
weight function `a : Fin r → ℝ`, the sum `∑ i, a i * |(extM σ M' j i : ℝ)|` only sees the columns
`σ i`, where the entry is `M' j i`, and so collapses to `∑ i, a (σ i) * |(M' j i : ℝ)|`. Taking
the product over the rows `j : Fin ρ` gives the identity below.

This is the `cardMod`-style bookkeeping used in the partial-degeneracy reduction
(`zeroDeg_reduce`, `extM_primSys`, `extM_cardMod`, `extM_minorJ`).
-/

namespace Work.BW

theorem extM_sum_abs {r N ρ : ℕ} (σ : Fin N → Fin r) (hσ : Function.Injective σ)
    (M' : Fin ρ → Fin N → ℤ) (a : Fin r → ℝ) :
    (∏ j, ∑ i : Fin r, a i * |(extM σ M' j i : ℝ)|) =
      ∏ j, ∑ i : Fin N, a (σ i) * |(M' j i : ℝ)| := by
  refine Finset.prod_congr rfl (fun j _ => ?_)
  -- `extM` recovers `M'` on the columns in `range σ` and vanishes off it.
  have hmem : ∀ i : Fin N, extM σ M' j (σ i) = M' j i := by
    intro i; simp only [extM]; exact hσ.extend_apply (M' j) 0 i
  have hzero : ∀ i : Fin r, i ∉ Set.range σ → extM σ M' j i = 0 := by
    intro i hi; simp only [extM]; exact Function.extend_apply' _ _ _ hi
  -- the sum over all of `Fin r` is the sum over `range σ`
  have hsub : (∑ i ∈ Finset.univ.image σ, a i * |(extM σ M' j i : ℝ)|)
      = ∑ i : Fin r, a i * |(extM σ M' j i : ℝ)| := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    rw [hzero x (fun hcon => hx (Set.mem_range.mp hcon))]
    simp
  rw [← hsub]
  -- reindex the sum over `range σ` by the injective map `σ`
  rw [Finset.sum_image (s := Finset.univ) (g := σ)
        (f := fun i => a i * |(extM σ M' j i : ℝ)|) (fun x _ y _ h => hσ h)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hmem i]

end Work.BW
