import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.NormSymAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open Metric

/-- The base smooth radial profile used to build the cut-off family: it equals `1` on the closed
ball of radius `√2` and vanishes outside the closed ball of radius `√3`. -/
private noncomputable def cutBase : EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun x => Real.smoothTransition (3 - ‖x‖ ^ 2)

private lemma cutBase_contDiff : ContDiff ℝ (⊤ : ENat) cutBase := by
  unfold cutBase
  have h2 : ContDiff ℝ (⊤ : ENat) (fun x : EuclideanSpace ℝ (Fin 3) => 3 - ‖x‖ ^ 2) := by
    have h1 : ContDiff ℝ (⊤ : ENat) (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖ ^ 2) :=
      contDiff_norm_sq ℝ
    exact contDiff_const.sub h1
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp h2

private lemma cutBase_hasCompactSupport : HasCompactSupport cutBase := by
  refine HasCompactSupport.intro (isCompact_closedBall 0 2) ?_
  intro x hx
  rw [mem_closedBall, not_le, dist_zero_right] at hx
  show Real.smoothTransition (3 - ‖x‖ ^ 2) = 0
  rw [Real.smoothTransition.zero_iff_nonpos]
  have : (3 : ℝ) < ‖x‖ ^ 2 := by nlinarith [norm_nonneg x, hx]
  linarith

/-- All iterated derivatives of the base profile are bounded (it is smooth with compact support). -/
private lemma cutBase_iteratedFDeriv_bdd (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ k cutBase x‖ ≤ C := by
  have hk : ContDiff ℝ (k : ℕ∞) cutBase :=
    cutBase_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
  have hcont : Continuous (iteratedFDeriv ℝ k cutBase) := hk.continuous_iteratedFDeriv le_rfl
  have hcs : HasCompactSupport (iteratedFDeriv ℝ k cutBase) :=
    cutBase_hasCompactSupport.iteratedFDeriv k
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  exact ⟨max C 0, le_max_right _ _, fun x => le_trans (hC x) (le_max_left _ _)⟩

/-- A family of smooth radial cutoffs `θ R`, `R > 0`, with `θ R = 1` on `closedBall 0 R`,
`θ R = 0` off `closedBall 0 (2R)`, values in `[0,1]`, compact support, and the scaling
derivative bound `‖iteratedFDeriv ℝ k (θ R) x‖ ≤ C / R ^ k` with `C` independent of `R ≥ 1`.
Suggested construction: `θ R x = φ (R⁻¹ • x)` with `φ x = Real.smoothTransition (3 - ‖x‖ ^ 2)`,
using Mathlib's `iteratedFDeriv_comp_const_smul` for the derivative bound and compact support +
`HasCompactSupport.fderiv` / `fderiv_of_notMem_tsupport` for `sup ‖iteratedFDeriv ℝ k φ‖ < ∞`. -/
theorem cutFam_exists : ∃ θ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ,
    (∀ R, ContDiff ℝ (⊤ : ENat) (θ R)) ∧
    (∀ R x, 0 ≤ θ R x ∧ θ R x ≤ 1) ∧
    (∀ R, 0 < R → ∀ x, ‖x‖ ≤ R → θ R x = 1) ∧
    (∀ R, 0 < R → ∀ x, 2 * R ≤ ‖x‖ → θ R x = 0) ∧
    (∀ R, 0 < R → HasCompactSupport (θ R)) ∧
    (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ R, 1 ≤ R → ∀ x,
      ‖iteratedFDeriv ℝ k (θ R) x‖ ≤ C / R ^ k) := by
  refine ⟨fun R x => cutBase (R⁻¹ • x), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R
    exact cutBase_contDiff.comp (contDiff_const_smul (𝕜 := ℝ) (R⁻¹))
  · intro R x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro R hR x hx
    show cutBase (R⁻¹ • x) = 1
    unfold cutBase
    rw [Real.smoothTransition.eq_one_iff_one_le]
    have hnorm : ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le)]
    have hle : ‖R⁻¹ • x‖ ≤ 1 := by
      rw [hnorm]
      calc R⁻¹ * ‖x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
        _ = 1 := by field_simp
    have : ‖R⁻¹ • x‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hle
    linarith
  · intro R hR x hx
    show cutBase (R⁻¹ • x) = 0
    unfold cutBase
    rw [Real.smoothTransition.zero_iff_nonpos]
    have hnorm : ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le)]
    have hge : (2 : ℝ) ≤ ‖R⁻¹ • x‖ := by
      rw [hnorm]
      calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
        _ ≤ R⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
    have hsq : (3 : ℝ) < ‖R⁻¹ • x‖ ^ 2 := by
      nlinarith [norm_nonneg (R⁻¹ • x)]
    linarith
  · intro R hR
    refine HasCompactSupport.intro (isCompact_closedBall 0 (2 * R)) ?_
    intro x hx
    rw [mem_closedBall, not_le, dist_zero_right] at hx
    show cutBase (R⁻¹ • x) = 0
    unfold cutBase
    rw [Real.smoothTransition.zero_iff_nonpos]
    have hnorm : ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le)]
    have hge : (2 : ℝ) < ‖R⁻¹ • x‖ := by
      rw [hnorm]
      calc (2 : ℝ) = R⁻¹ * (2 * R) := by field_simp
        _ < R⁻¹ * ‖x‖ := mul_lt_mul_of_pos_left hx (inv_pos.mpr hR)
    have hsq : (3 : ℝ) < ‖R⁻¹ • x‖ ^ 2 := by
      nlinarith [norm_nonneg (R⁻¹ • x)]
    linarith
  · intro k
    obtain ⟨C, hC0, hC⟩ := cutBase_iteratedFDeriv_bdd k
    refine ⟨C, hC0, ?_⟩
    intro R hR x
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hk : ContDiff ℝ (k : ℕ∞) cutBase :=
      cutBase_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [iteratedFDeriv_comp_const_smul (R⁻¹) hk]
    calc ‖(R⁻¹ : ℝ) ^ k • iteratedFDeriv ℝ k cutBase (R⁻¹ • x)‖
        = (R⁻¹) ^ k * ‖iteratedFDeriv ℝ k cutBase (R⁻¹ • x)‖ := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hRpos.le) k)]
      _ ≤ (R⁻¹) ^ k * C :=
          mul_le_mul_of_nonneg_left (hC _) (pow_nonneg (inv_nonneg.mpr hRpos.le) k)
      _ = C / R ^ k := by rw [inv_pow]; ring

end Work.BoseBoxFock
