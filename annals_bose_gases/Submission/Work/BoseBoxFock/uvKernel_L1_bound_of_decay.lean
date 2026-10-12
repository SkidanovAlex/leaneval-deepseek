import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFock.PotCubicSmoothWeight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The `L¹` bound for a decaying UV kernel

If `ψ_Λ = uvKernel fu Λ` satisfies the pointwise decay bound
`‖ψ_Λ z‖ ≤ C Λ³ (1 + Λ ‖z‖)^{-5}` (uniformly in `Λ > 0`), then the `L¹`-norms `∫ ‖ψ_Λ‖` are
uniformly bounded in `Λ`.

The reason is the scaling: the change of variables `z ↦ Λ z` turns the majorant into the *fixed*
function `z ↦ C (1 + ‖z‖)^{-5}`, whose integral over `ℝ³` is finite (`5 > 3 = dim`), so

    `∫ z, C Λ³ (1 + Λ ‖z‖)^{-5} = ∫ y, C (1 + ‖y‖)^{-5}`

for every `Λ > 0`. -/

/-- The decay profile `z ↦ C (1 + ‖z‖)^{-5}` is integrable on `ℝ³` (the exponent `5` exceeds the
dimension `3`). -/
private lemma integrable_decay_profile (C : ℝ) :
    Integrable (fun z : E3 => C * (1 + ‖z‖) ^ (-(5 : ℤ))) := by
  have h5 : (Module.finrank ℝ E3 : ℝ) < 5 := by
    rw [finrank_euclideanSpace]; norm_num
  refine ((integrable_one_add_norm (μ := volume) (E := E3) h5).const_mul C).congr ?_
  filter_upwards with z
  have : ((-(5 : ℤ) : ℤ) : ℝ) = -(5 : ℝ) := by norm_num
  rw [← Real.rpow_intCast (1 + ‖z‖) (-(5 : ℤ)), this]

theorem uvKernel_L1_bound_of_decay (fu : Work.BoseBoxFix.LowCut) {C : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ (Λ : ℝ), 0 < Λ → ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.uvKernel fu Λ z‖ ≤ C * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Λ : ℝ), 0 < Λ →
      ∫ z : EuclideanSpace ℝ (Fin 3), ‖Work.BoseBoxFock.uvKernel fu Λ z‖ ≤ M := by
  refine ⟨∫ z : E3, C * (1 + ‖z‖) ^ (-(5 : ℤ)), ?_, ?_⟩
  · refine integral_nonneg (fun z => ?_)
    exact mul_nonneg hC (zpow_nonneg (by positivity) _)
  · intro Λ hΛ
    have hΛne : Λ ≠ 0 := hΛ.ne'
    -- the pointwise majorant
    set G : E3 → ℝ := fun z => C * Λ ^ 3 * (1 + Λ * ‖z‖) ^ (-(5 : ℤ)) with hG
    have hG_eq : ∀ z : E3, G z = Λ ^ 3 * (C * (1 + ‖(Λ : ℝ) • z‖) ^ (-(5 : ℤ))) := by
      intro z
      simp only [hG]
      rw [norm_smul, Real.norm_of_nonneg hΛ.le]
      ring
    have hbase : Integrable (fun z : E3 => C * (1 + ‖z‖) ^ (-(5 : ℤ))) :=
      integrable_decay_profile C
    have hIntG : Integrable G := by
      have h2 : Integrable (fun z : E3 => C * (1 + ‖(Λ : ℝ) • z‖) ^ (-(5 : ℤ))) :=
        hbase.comp_smul hΛne
      have h3 : Integrable (fun z : E3 => Λ ^ 3 * (C * (1 + ‖(Λ : ℝ) • z‖) ^ (-(5 : ℤ)))) :=
        h2.const_mul (Λ ^ 3)
      refine h3.congr ?_
      filter_upwards with z
      rw [hG_eq z]
    have hmono : ∫ z, ‖uvKernel fu Λ z‖ ≤ ∫ z, G z :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => norm_nonneg _)) hIntG
        (Filter.Eventually.of_forall (fun z => hdec Λ hΛ z))
    have hGval : ∫ z, G z = ∫ z : E3, C * (1 + ‖z‖) ^ (-(5 : ℤ)) := by
      have step1 : ∫ z, G z
          = ∫ z : E3, Λ ^ 3 * (C * (1 + ‖(Λ : ℝ) • z‖) ^ (-(5 : ℤ))) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hG_eq z]
      rw [step1, integral_const_mul,
        Measure.integral_comp_smul volume (fun y : E3 => C * (1 + ‖y‖) ^ (-(5 : ℤ))) Λ]
      have hfindim : Module.finrank ℝ E3 = 3 := by
        rw [finrank_euclideanSpace]; simp
      have hΛ3 : (0 : ℝ) < Λ ^ 3 := by positivity
      simp only [hfindim, smul_eq_mul]
      rw [abs_of_pos (inv_pos.mpr hΛ3), ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hΛ3), one_mul]
    linarith [hmono, hGval]

end Work.BoseBoxFock
