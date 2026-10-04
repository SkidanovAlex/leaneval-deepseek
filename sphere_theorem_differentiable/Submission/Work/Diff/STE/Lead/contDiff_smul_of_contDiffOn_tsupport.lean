import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

lemma contDiff_smul_of_contDiffOn_tsupport {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : (Fin n → ℝ) → ℝ} {f : (Fin n → ℝ) → F} {U : Set (Fin n → ℝ)}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (hU : IsOpen U)
    (ht : tsupport χ ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => χ z • f z) := by
  -- Reduce a global `ContDiff` statement to a pointwise one.
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · -- Inside `U` both factors are smooth at `x`, so the product is.
    exact (hχ.contDiffAt).smul (hf.contDiffAt (hU.mem_nhds hx))
  · -- Outside `U`, the point `x` is not in `tsupport χ`, so `χ` vanishes
    -- on a neighbourhood of `x` and the product is locally the zero function.
    have hx' : x ∉ tsupport χ := fun h => hx (ht h)
    have hev : χ =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    simp [hy]

end Work.Diff.STE.Lead
