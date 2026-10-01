import Mathlib
import Submission.Work.LinnikAreas.DhRepel.extCosFbasic

namespace Work.LinnikAreas.DhRepel

/-- On the open support `(0, 2γ)` the extremal function `extCosF θ λ` agrees with the
smooth closed form, hence it is `C²` there and its second derivative is bounded
(`extCosF` is cut off outside the compact interval `[0, 2γ]`, where it vanishes). -/
theorem extCosFtestProps {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ContDiffOn ℝ 2 (fun t : ℝ => Commons.NumberTheory.Linnik.extCosF θ lam t)
        (Set.Ioo 0 (2 * (θ / (lam * Real.tan θ)))) ∧
      ∃ B : ℝ, ∀ t ∈ Set.Ioo (0:ℝ) (2 * (θ / (lam * Real.tan θ))),
        ‖iteratedDeriv 2 (fun s : ℝ => Commons.NumberTheory.Linnik.extCosF θ lam s) t‖ ≤ B := by
  have hcd : ContDiff ℝ 2 (closedForm θ lam) := contDiff_closedForm hθ0 hθ1 hlam
  -- on the open support `extCosF` coincides with the closed form
  have hEqOn : ∀ x ∈ Set.Ioo (0:ℝ) (2 * gammaF θ lam),
      Commons.NumberTheory.Linnik.extCosF θ lam x = closedForm θ lam x :=
    fun x hx => extCosF_eq_closedForm hθ0 hθ1 hlam ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hcontDiff : ContDiffOn ℝ 2 (fun t : ℝ => Commons.NumberTheory.Linnik.extCosF θ lam t)
      (Set.Ioo 0 (2 * (θ / (lam * Real.tan θ)))) :=
    hcd.contDiffOn.congr hEqOn
  -- the second derivative of the closed form is continuous, hence bounded on the compact support
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * gammaF θ lam)).exists_bound_of_continuousOn
    (hcd.continuous_iteratedDeriv 2 (by norm_num)).continuousOn
  refine ⟨hcontDiff, B, fun t ht => ?_⟩
  have ht' : t ∈ Set.Ioo (0:ℝ) (2 * gammaF θ lam) := ht
  -- `iteratedDeriv` is a local (germ) notion, so it transports across the open support
  have hEq : (fun s : ℝ => Commons.NumberTheory.Linnik.extCosF θ lam s) =ᶠ[nhds t]
      (fun s : ℝ => closedForm θ lam s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht'] with s hs
    exact extCosF_eq_closedForm hθ0 hθ1 hlam ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  rw [(Filter.EventuallyEq.iteratedDeriv hEq 2).eq_of_nhds]
  exact hB t ⟨le_of_lt ht'.1, le_of_lt ht'.2⟩

end Work.LinnikAreas.DhRepel
