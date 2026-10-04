import Mathlib
import Submission.Work.Diff.STE.Lead.JointSmoothKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

theorem exists_contDiff_tsupport_eq_one_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ φ : E → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ tsupport φ ⊆ U ∧ (∀ x ∈ K, φ x = 1) ∧
      (∀ x ∈ K, fderiv ℝ φ x = 0) := by
  -- Enlarge `K` to a closed neighbourhood `cthickening δ K` still inside `U`.
  obtain ⟨δ, hδpos, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨θ, hθsm, hθtsup, hθ1, _⟩ :=
    Work.Diff.STE.Lead.exists_contDiff_tsupport_subset_isCompact
      (hK.cthickening (r := δ)) hU hδU
  refine ⟨θ, hθsm, hθtsup, fun x hx => hθ1 x ?_, ?_⟩
  · exact (Metric.self_subset_cthickening (δ := δ) K) hx
  -- `θ` is `1` on an open neighbourhood of every point of `K`, so its derivative vanishes there.
  · intro x hx
    have hmem : Metric.cthickening δ K ∈ nhds x :=
      Filter.mem_of_superset
        (Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening hδpos K hx))
        (Metric.thickening_subset_cthickening δ K)
    have hev : θ =ᶠ[nhds x] (fun _ : E => (1 : ℝ)) := by
      filter_upwards [hmem] with y hy
      exact hθ1 y hy
    rw [hev.fderiv_eq, fderiv_const_apply]

end Work.Diff.STE.B3.VarCoef
