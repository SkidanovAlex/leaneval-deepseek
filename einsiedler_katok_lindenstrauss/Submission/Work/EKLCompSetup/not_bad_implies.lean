import Mathlib
import Submission.Work.EKLComp.C8Defs

/-!
# `not_bad_implies` — passing from the exceptional-set hypothesis to a flow average lower bound

The hypothesis `hx` says that *no* time scale `T > 0` realises
`ε T < ∫_0^T (1 - 1_S(Φ_τ x))`; equivalently `∫_0^T (1 - 1_S(Φ_τ x)) ≤ ε T` for every `T > 0`.
Since `1_S(Φ_τ x) ∈ {0,1}`, the two integrands `1 - 1_S(Φ_τ x)` and `1_S(Φ_τ x)` are
complementary pointwise:
`(1 - 1_S(Φ_τ x)) + 1_S(Φ_τ x) = 1`. `τ ↦ Φ_τ x` is continuous (hence measurable), the
indicator is bounded by `1`, so both are interval integrable and additivity of the interval
integral gives

`∫_0^T (1 - 1_S(Φ_τ x)) = T - ∫_0^T 1_S(Φ_τ x)`.

Combining with `∫_0^T (1 - 1_S(Φ_τ x)) ≤ ε T` yields `(1 - ε) T ≤ ∫_0^T 1_S(Φ_τ x)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLCompSetup

/-! ## Continuity / measurability of the flow orbit -/

private theorem cont_aDiag : Continuous fun t : Fin 3 → ℝ => Work.EKLContract.aDiag t := by
  refine Continuous.subtype_mk (p := fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det = 1)
    (f := fun t : Fin 3 → ℝ => Matrix.diagonal (fun i => Real.exp (t i - (∑ j, t j) / 3)))
    ?_ (fun t => (Work.EKLContract.aDiag t).2)
  apply continuous_matrix
  intro k l
  simp only [Matrix.diagonal_apply]
  by_cases hkl : k = l
  · simp only [hkl, if_true]; fun_prop
  · simp only [hkl, if_false]; exact continuous_const

private theorem cont_phi : Continuous Work.EKLComp.phi := by
  have hkey : Work.EKLComp.phi = fun τ : ℝ => Work.EKLContract.aDiag (τ • ![-1, 1, 0]) := rfl
  rw [hkey]
  exact cont_aDiag.comp (by fun_prop)

/-- The orbit `τ ↦ Φ_τ x` of the contracting flow through a fixed point is measurable. -/
private theorem measurable_Phi (x : Work.EKLContract.X3) :
    Measurable fun τ : ℝ => Work.EKLComp.Phi τ x := by
  have h2 : Continuous fun τ : ℝ => Work.EKLComp.phi τ • x :=
    continuous_smul.comp (cont_phi.prodMk continuous_const)
  simpa [Work.EKLComp.Phi] using h2.measurable

/-! ## The main statement -/

theorem not_bad_implies
    {S : Set Work.EKLContract.X3} (hS : MeasurableSet S) {ε : ℝ} (hε : 0 < ε)
    (x : Work.EKLContract.X3)
    (hx : ¬ ∃ T : ℝ, 0 < T ∧
      ε * T < ∫ τ in (0 : ℝ)..T,
        (1 - Set.indicator S (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x))) :
    ∀ T : ℝ, 0 < T →
      (1 - ε) * T ≤ ∫ τ in (0 : ℝ)..T,
        Set.indicator S (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x) := by
  intro T hT
  have hfmeas : Measurable fun τ : ℝ =>
      Set.indicator S (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x) :=
    (measurable_const.indicator hS).comp (measurable_Phi x)
  have hIntf : IntervalIntegrable
      (fun τ : ℝ => Set.indicator S (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x)) volume 0 T := by
    rw [intervalIntegrable_iff]
    refine IntegrableOn.of_bound ?_ hfmeas.aestronglyMeasurable 1 ?_
    · simp
    · filter_upwards with τ
      by_cases h : Work.EKLComp.Phi τ x ∈ S
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
  have hsplit : (∫ τ in (0 : ℝ)..T,
        (1 - Set.indicator S (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x)))
      = T - ∫ τ in (0 : ℝ)..T, Set.indicator S (fun _ => (1 : ℝ)) (Work.EKLComp.Phi τ x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hIntf]
    simp [intervalIntegral.integral_const]
  by_contra hcon
  push Not at hcon
  apply hx
  refine ⟨T, hT, ?_⟩
  rw [hsplit]
  linarith

end Work.EKLCompSetup
