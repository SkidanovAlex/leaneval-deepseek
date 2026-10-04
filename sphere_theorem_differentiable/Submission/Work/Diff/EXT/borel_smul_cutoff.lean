import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- A globally smooth cut-off `χ` whose topological support is contained in an open set `U`
multiplies any function `f` that is smooth on `U` into a globally smooth function.

At a point of `U` both factors are smooth; at a point outside `U` (hence outside `tsupport χ`)
the factor `χ` vanishes on a whole neighbourhood, so the product agrees there with the zero
function. -/
theorem borel_smul_cutoff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : E → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {U : Set E} (hU : IsOpen U)
    (hsupp : tsupport χ ⊆ U) (f : E → F) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y • f y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · -- Inside `U` both factors are smooth at `x`.
    exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
  · -- Outside `U`, hence outside `tsupport χ`, the cut-off vanishes nearby.
    have hxcl : x ∉ tsupport χ := fun h => hx (hsupp h)
    have hmem : (tsupport χ)ᶜ ∈ nhds x := (isClosed_tsupport χ).isOpen_compl.mem_nhds hxcl
    have hev : (fun y => χ y • f y) =ᶠ[nhds x] (fun _ => (0 : F)) := by
      filter_upwards [hmem] with y hy
      have hy0 : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hy0]
    exact contDiffAt_const.congr_of_eventuallyEq hev

end Work.Diff.EXT
