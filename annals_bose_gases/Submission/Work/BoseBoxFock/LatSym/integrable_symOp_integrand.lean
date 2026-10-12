import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.FRKDefs
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_decay_gen
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.LatSym

open MeasureTheory

/-- The domination profile `p ↦ (1 + ‖p‖)⁻⁴` is integrable on `ℝ³` (since `4 > 3 = finrank ℝ ℝ³`). -/
private lemma integrable_one_add_norm_inv_four :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ((1 + ‖p‖ : ℝ) ^ 4)⁻¹) := by
  have h := integrable_one_add_norm (E := EuclideanSpace ℝ (Fin 3)) (μ := volume) (r := 4) (by
    rw [finrank_euclideanSpace_fin]; norm_num)
  refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
  show (1 + ‖p‖) ^ (-(4 : ℝ)) = ((1 + ‖p‖ : ℝ) ^ 4)⁻¹
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
  congr 1
  exact Real.rpow_natCast (1 + ‖p‖) 4

theorem integrable_symOp_integrand {σ : EuclideanSpace ℝ (Fin 3) → ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (hσg : ∃ A : ℝ, ∀ p : EuclideanSpace ℝ (Fin 3), |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    (η : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (Complex.I * (inner ℝ p η : ℂ)) * (σ p : ℂ) * Submission.BoseGases.kinFT g p) := by
  obtain ⟨A, hA⟩ := hσg
  -- `σ 0` bounds force `A ≥ 0`
  have hA0 : 0 ≤ A := (abs_nonneg (σ 0)).trans (by simpa using hA 0)
  -- the phase factor has modulus one, so only `σ · kinFT g` has to be dominated
  have hφ : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Complex.exp (Complex.I * (inner ℝ p η : ℂ))‖ = 1 := fun p =>
    Complex.norm_exp_I_mul_ofReal (inner ℝ p η)
  -- `kinFT g` decays faster than any power of `‖p‖`
  obtain ⟨K, hK, hdec⟩ := SqrtKin.kinFT_decay_gen hg hgc 6
  -- measurability: `g` is integrable, so `kinFT g` is continuous
  have hgint : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport (μ := volume) hgc
  have hcont : Continuous (Submission.BoseGases.kinFT g) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hgint
  have hmeas : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (Complex.I * (inner ℝ p η : ℂ)) * (σ p : ℂ) * Submission.BoseGases.kinFT g p)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
    refine Continuous.aestronglyMeasurable ?_
    exact ((Complex.continuous_exp.comp
        (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)))).mul
      (Complex.continuous_ofReal.comp hσ.continuous)).mul hcont
  -- the dominating profile `A K (1 + ‖p‖)⁻⁴`
  have hdom : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => A * K * ((1 + ‖p‖ : ℝ) ^ 4)⁻¹) :=
    integrable_one_add_norm_inv_four.const_mul (A * K)
  refine hdom.mono' hmeas ?_
  filter_upwards with p
  have h1 : (0 : ℝ) < 1 + ‖p‖ := by positivity
  have hnorm : ‖Complex.exp (Complex.I * (inner ℝ p η : ℂ)) * (σ p : ℂ) *
        Submission.BoseGases.kinFT g p‖ = |σ p| * ‖Submission.BoseGases.kinFT g p‖ := by
    rw [norm_mul, norm_mul, hφ p, Complex.norm_real, Real.norm_eq_abs, one_mul]
  rw [hnorm]
  calc |σ p| * ‖Submission.BoseGases.kinFT g p‖
      ≤ (A * (1 + ‖p‖) ^ 2) * (K / (1 + ‖p‖) ^ 6) :=
        mul_le_mul (hA p) (hdec p) (norm_nonneg _) (mul_nonneg hA0 (by positivity))
    _ = A * K * ((1 + ‖p‖ : ℝ) ^ 4)⁻¹ := by
        have hne : (1 + ‖p‖ : ℝ) ≠ 0 := ne_of_gt h1
        field_simp
        try ring

end Work.BoseBoxFock.LatSym
