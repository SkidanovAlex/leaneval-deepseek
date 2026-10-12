import ChallengeDeps
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Submission.Work.BoseSWE.chiMass_sub_autoCorr_leW
import Submission.Work.BoseSWE.chiScaleGradMulC
import Submission.Work.BoseSWE.chiScaleSqMulGradC
import Submission.Work.BoseSWE.massiveThreshArith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSWE

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## Auxiliary facts -/

/-- `‖∇f x‖ = ‖fderiv ℝ f x‖` (the Fréchet–Riesz dual is an isometry). -/
private lemma gradNorm_eq_fderivNorm (f : E3 → ℝ) (x : E3) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  rw [← toDual_gradient (𝕜 := ℝ) (F := E3) (f := f) (x := x)]
  exact (LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ E3) (gradient f x)).symm

/-- `|chiSmall M z| ≤ chiSmallNormFactor M`. -/
private lemma abs_chiSmall_le_normFactor {M : ℕ} (hM : 1 ≤ M) (z : E3) :
    |Submission.BoseGases.chiSmall M z| ≤ Submission.BoseGases.chiSmallNormFactor M := by
  have hζ : ∀ i : Fin 3, 0 ≤ Submission.BoseGases.zeta1d (z.ofLp i) :=
    fun i => Submission.BoseGases.zeta1d_nonneg _
  have hζ1 : ∀ i : Fin 3, Submission.BoseGases.zeta1d (z.ofLp i) ≤ 1 :=
    fun i => Submission.BoseGases.zeta1d_le_one _
  have hprod0 : 0 ≤ Submission.BoseGases.zeta1d (z.ofLp 0)
      * Submission.BoseGases.zeta1d (z.ofLp 1) * Submission.BoseGases.zeta1d (z.ofLp 2) :=
    mul_nonneg (mul_nonneg (hζ 0) (hζ 1)) (hζ 2)
  have hprod1 : Submission.BoseGases.zeta1d (z.ofLp 0)
      * Submission.BoseGases.zeta1d (z.ofLp 1) * Submission.BoseGases.zeta1d (z.ofLp 2) ≤ 1 := by
    have h01 : Submission.BoseGases.zeta1d (z.ofLp 0)
        * Submission.BoseGases.zeta1d (z.ofLp 1) ≤ 1 :=
      mul_le_one₀ (hζ1 0) (hζ 1) (hζ1 1)
    exact mul_le_one₀ h01 (hζ 2) (hζ1 2)
  have hbase : |Submission.BoseGases.chiSmallBase M z| ≤ 1 := by
    rw [Submission.BoseGases.chiSmallBase, abs_of_nonneg (pow_nonneg hprod0 M)]
    exact pow_le_one₀ hprod0 hprod1
  have hpos : 0 < Submission.BoseGases.chiSmallNormSq M :=
    Submission.BoseGases.chiSmallNormSq_pos hM
  rw [Submission.BoseGases.chiSmall, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
    Submission.BoseGases.chiSmallNormFactor, ← one_div]
  exact div_le_div_of_nonneg_right hbase (Real.sqrt_nonneg _)

/-! ## The two mass thresholds implied by the massive hypothesis -/

private lemma sqrt_mass_ge {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    (hmass : d ^ 108 * (ℓ * d) ^ 3 ≤ Work.SmallBoxSliding.chiMass M ℓ d u) :
    d ^ 54 * (ℓ * d) ^ (3 / 2 : ℝ) ≤ Real.sqrt (Work.SmallBoxSliding.chiMass M ℓ d u) := by
  have heq : Real.sqrt (d ^ 108 * (ℓ * d) ^ 3) = d ^ 54 * (ℓ * d) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast d 108, ← Real.rpow_natCast d 54,
      ← Real.rpow_natCast (ℓ * d) 3,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (le_of_lt hd),
      ← Real.rpow_mul (le_of_lt (mul_pos hℓ hd))]
    norm_num
  rw [← heq]
  exact Real.sqrt_le_sqrt hmass

private lemma rpow_mass_ge {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    (hmass : d ^ 108 * (ℓ * d) ^ 3 ≤ Work.SmallBoxSliding.chiMass M ℓ d u) :
    d ^ (9 / 4 : ℝ) * (ℓ * d) ^ (1 / 16 : ℝ)
      ≤ (Work.SmallBoxSliding.chiMass M ℓ d u) ^ (1 / 48 : ℝ) := by
  have heq : (d ^ 108 * (ℓ * d) ^ 3) ^ (1 / 48 : ℝ)
      = d ^ (9 / 4 : ℝ) * (ℓ * d) ^ (1 / 16 : ℝ) := by
    rw [← Real.rpow_natCast d 108, ← Real.rpow_natCast (ℓ * d) 3,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (le_of_lt hd),
      ← Real.rpow_mul (le_of_lt (mul_pos hℓ hd))]
    norm_num
  rw [← heq]
  exact Real.rpow_le_rpow (by positivity) hmass (by norm_num)

/-! ## Integrability of the two gradient halves -/

private lemma integrable_gradA_mul_c {M : ℕ} (hM : 1 ≤ M) {N : ℝ} (hN0 : 0 ≤ N)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    (hN : ∀ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
        ≤ 2 * (N / ℓ ^ 2) * Submission.BoseGases.chiScale ℓ x) :
    Integrable (fun x : E3 => ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
        * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2) := by
  have hcont_c : Continuous (fun x : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
    (Submission.BoseGases.chiSmall_continuous hM).comp
      ((continuous_id.const_smul ((ℓ * d)⁻¹)).sub continuous_const)
  have hcs_c : HasCompactSupport
      (fun x : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
    ((Submission.BoseGases.chiSmall_hasCompactSupport (M := M) hM).comp_homeomorph
        (Homeomorph.addRight (-u))).comp_smul (c := (ℓ * d)⁻¹)
      (inv_ne_zero (ne_of_gt (mul_pos hℓ hd)))
  have hInt : Integrable (fun x : E3 => (2 * (N / ℓ ^ 2) * Submission.BoseGases.chiSupAbs)
      * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2) :=
    ((hcont_c.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two] using hcs_c.mul_right
        (f := fun x : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
        (f' := fun x : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)))).const_mul _
  refine Integrable.mono' hInt ?_ ?_
  · exact ((Measurable.pow_const
        (measurable_fderiv ℝ (Submission.BoseGases.chiScale ℓ)).norm 2).aestronglyMeasurable).mul
      (hcont_c.pow 2).aestronglyMeasurable
  · filter_upwards with x
    have hA0 : 0 ≤ Submission.BoseGases.chiScale ℓ x := Submission.BoseGases.chi_nonneg _
    have hAle : Submission.BoseGases.chiScale ℓ x ≤ Submission.BoseGases.chiSupAbs := by
      have h := Submission.BoseGases.chiScale_abs_le_sup ℓ x
      rwa [abs_of_nonneg hA0] at h
    have hcoef : 0 ≤ 2 * (N / ℓ ^ 2) :=
      mul_nonneg (by norm_num) (div_nonneg hN0 (sq_nonneg ℓ))
    have h1 : ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
        * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 ≤
        2 * (N / ℓ ^ 2) * Submission.BoseGases.chiScale ℓ x
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 :=
      mul_le_mul_of_nonneg_right (hN x) (sq_nonneg _)
    have h2 : 2 * (N / ℓ ^ 2) * Submission.BoseGases.chiScale ℓ x
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 ≤
        2 * (N / ℓ ^ 2) * Submission.BoseGases.chiSupAbs
          * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 := by
      have h3 : Submission.BoseGases.chiScale ℓ x
            * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 ≤
          Submission.BoseGases.chiSupAbs
            * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 :=
        mul_le_mul_of_nonneg_right hAle (sq_nonneg _)
      calc 2 * (N / ℓ ^ 2) * Submission.BoseGases.chiScale ℓ x
            * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2
          = 2 * (N / ℓ ^ 2) * (Submission.BoseGases.chiScale ℓ x
              * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2) := by ring
        _ ≤ 2 * (N / ℓ ^ 2) * (Submission.BoseGases.chiSupAbs
              * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2) :=
            mul_le_mul_of_nonneg_left h3 hcoef
        _ = 2 * (N / ℓ ^ 2) * Submission.BoseGases.chiSupAbs
              * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 := by ring
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    linarith

private lemma integrable_A_sq_mul_gradc_sq {M : ℕ} (hM : 2 ≤ M)
    {ℓ d Cc : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) (hCc0 : 0 ≤ Cc)
    (hCc : ∀ z : E3, ‖fderiv ℝ (fun w : E3 =>
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • w - u)) z‖ ≤
        Cc * (ℓ * d)⁻¹ * (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)) ^ (((M : ℝ) - 1) / M)) :
    Integrable (fun x : E3 => (Submission.BoseGases.chiScale ℓ x) ^ 2
        * ‖fderiv ℝ (fun w : E3 =>
            Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2) := by
  have hM1 : 1 ≤ M := by omega
  have hcont_A : Continuous (fun x : E3 => Submission.BoseGases.chiScale ℓ x) :=
    Submission.BoseGases.chiScale_continuous ℓ
  have hcs_A : HasCompactSupport (fun x : E3 => Submission.BoseGases.chiScale ℓ x) :=
    Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)
  have hIntA2 : Integrable (fun x : E3 => (Submission.BoseGases.chiScale ℓ x) ^ 2) :=
    (hcont_A.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two] using hcs_A.mul_right
        (f := fun x : E3 => Submission.BoseGases.chiScale ℓ x)
        (f' := fun x : E3 => Submission.BoseGases.chiScale ℓ x))
  have hInt : Integrable (fun x : E3 => ((Cc * (ℓ * d)⁻¹
      * (Submission.BoseGases.chiSmallNormFactor M) ^ (((M : ℝ) - 1) / M)) ^ 2)
        * (Submission.BoseGases.chiScale ℓ x) ^ 2) := hIntA2.const_mul _
  refine Integrable.mono' hInt ?_ ?_
  · exact ((hcont_A.pow 2).aestronglyMeasurable).mul
      ((Measurable.pow_const
        (measurable_fderiv ℝ (fun w : E3 =>
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • w - u))).norm 2).aestronglyMeasurable)
  · filter_upwards with x
    have hc0 : 0 ≤ Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) :=
      Submission.BoseGases.chiSmall_nonneg M _
    have hcκ : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
        ≤ Submission.BoseGases.chiSmallNormFactor M := by
      have h := abs_chiSmall_le_normFactor hM1 ((ℓ * d)⁻¹ • x - u)
      rwa [abs_of_nonneg hc0] at h
    have hbase : 0 ≤ ((M : ℝ) - 1) / M := by
      have h1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
      have h2 : (0 : ℝ) < (M : ℝ) := by positivity
      exact div_nonneg (by linarith) (le_of_lt h2)
    have hcκa : (Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ (((M : ℝ) - 1) / M)
        ≤ (Submission.BoseGases.chiSmallNormFactor M) ^ (((M : ℝ) - 1) / M) :=
      Real.rpow_le_rpow hc0 hcκ hbase
    have h1 : 0 ≤ Cc * (ℓ * d)⁻¹ := mul_nonneg hCc0 (le_of_lt (inv_pos.mpr (mul_pos hℓ hd)))
    have hb : ‖fderiv ℝ (fun w : E3 =>
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • w - u)) x‖
        ≤ Cc * (ℓ * d)⁻¹ * (Submission.BoseGases.chiSmallNormFactor M) ^ (((M : ℝ) - 1) / M) :=
      le_trans (hCc x) (mul_le_mul_of_nonneg_left hcκa h1)
    have hb2 : ‖fderiv ℝ (fun w : E3 =>
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2
        ≤ (Cc * (ℓ * d)⁻¹
            * (Submission.BoseGases.chiSmallNormFactor M) ^ (((M : ℝ) - 1) / M)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hA2 : 0 ≤ (Submission.BoseGases.chiScale ℓ x) ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg hA2 (sq_nonneg _))]
    calc (Submission.BoseGases.chiScale ℓ x) ^ 2
          * ‖fderiv ℝ (fun w : E3 =>
              Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2
        ≤ (Submission.BoseGases.chiScale ℓ x) ^ 2
            * ((Cc * (ℓ * d)⁻¹
                * (Submission.BoseGases.chiSmallNormFactor M) ^ (((M : ℝ) - 1) / M)) ^ 2) :=
          mul_le_mul_of_nonneg_left hb2 hA2
      _ = ((Cc * (ℓ * d)⁻¹
              * (Submission.BoseGases.chiSmallNormFactor M) ^ (((M : ℝ) - 1) / M)) ^ 2)
            * (Submission.BoseGases.chiScale ℓ x) ^ 2 := by ring

/-! ## The integrated gradient bound -/

private theorem gradSq_le
    {N : ℝ} (hN0 : 0 ≤ N) {Cc K1 K2 : ℝ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    (hCc0 : 0 ≤ Cc)
    (hN : ∀ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
        ≤ 2 * (N / ℓ ^ 2) * Submission.BoseGases.chiScale ℓ x)
    (hCc : ∀ z : E3, ‖fderiv ℝ (fun w : E3 =>
        Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • w - u)) z‖ ≤
        Cc * (ℓ * d)⁻¹
          * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • z - u)) ^ (((48 : ℝ) - 1) / 48))
    (hE1 : (∫ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
              * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) ^ 2)
          ≤ K1 * (ℓ⁻¹) ^ 2 * Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u)
              * (ℓ * d) ^ (3 / 2 : ℝ))
    (hE2 : (∫ x : E3, (Submission.BoseGases.chiScale ℓ x) ^ 2
              * ‖fderiv ℝ (fun w : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2)
          ≤ K2 * ((ℓ * d)⁻¹) ^ 2
              * (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ ((47 : ℝ) / 48)
              * ℓ ^ ((1 : ℝ) / 16)) :
    (∫ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiSmallB 48 ℓ d u) x‖ ^ 2)
      ≤ 2 * K1 * (ℓ⁻¹) ^ 2 * Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u)
          * (ℓ * d) ^ (3 / 2 : ℝ)
        + 2 * K2 * ((ℓ * d)⁻¹) ^ 2 * (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ ((47 : ℝ) / 48)
          * ℓ ^ ((1 : ℝ) / 16) := by
  -- ### the pointwise splitting
  have hsplit : ∀ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiSmallB 48 ℓ d u) x‖ ^ 2
      ≤ 2 * (‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
              * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) ^ 2)
          + 2 * ((Submission.BoseGases.chiScale ℓ x) ^ 2
              * ‖fderiv ℝ (fun w : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2) := by
    intro x
    have hAd : DifferentiableAt ℝ (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x :=
      (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).differentiable (by norm_num) x
    have hcd : DifferentiableAt ℝ
        (fun y : E3 => Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x := by
      have h1 : DifferentiableAt ℝ (fun y : E3 => (ℓ * d)⁻¹ • y - u) x :=
        ((differentiableAt_id (x := x)).const_smul ((ℓ * d)⁻¹)).sub_const u
      exact (Work.BoseSWE.differentiableAt_chiSmall (M := 48) (by norm_num) _).comp x h1
    have hAB : Submission.BoseGases.chiSmallB 48 ℓ d u
        = (fun y : E3 => Submission.BoseGases.chiScale ℓ y)
          * (fun y : E3 => Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) := by
      funext y
      rfl
    have hfm := fderiv_mul (𝕜 := ℝ) hAd hcd
    rw [hAB, hfm]
    have hA0 : 0 ≤ Submission.BoseGases.chiScale ℓ x := Submission.BoseGases.chi_nonneg _
    have hc0 : 0 ≤ Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u) :=
      Submission.BoseGases.chiSmall_nonneg 48 _
    have hnorm : ‖(Submission.BoseGases.chiScale ℓ x) • fderiv ℝ
            (fun y : E3 => Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x
          + (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) • fderiv ℝ
            (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖
        ≤ Submission.BoseGases.chiScale ℓ x
              * ‖fderiv ℝ (fun y : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x‖
          + Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)
              * ‖fderiv ℝ (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖ := by
      have hn1 : ‖(Submission.BoseGases.chiScale ℓ x) • fderiv ℝ
              (fun y : E3 => Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x‖
          ≤ Submission.BoseGases.chiScale ℓ x
              * ‖fderiv ℝ (fun y : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hA0]
      have hn2 : ‖(Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) • fderiv ℝ
              (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖
          ≤ Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)
              * ‖fderiv ℝ (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
      exact le_trans (norm_add_le _ _) (add_le_add hn1 hn2)
    have hsq : ‖(Submission.BoseGases.chiScale ℓ x) • fderiv ℝ
            (fun y : E3 => Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x
          + (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) • fderiv ℝ
            (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖ ^ 2
        ≤ 2 * (Submission.BoseGases.chiScale ℓ x
              * ‖fderiv ℝ (fun y : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x‖) ^ 2
          + 2 * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)
              * ‖fderiv ℝ (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖) ^ 2 := by
      have hq1 : (0 : ℝ) ≤ Submission.BoseGases.chiScale ℓ x
          * ‖fderiv ℝ (fun y : E3 =>
              Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x‖ :=
        mul_nonneg hA0 (norm_nonneg _)
      have hq2 : (0 : ℝ) ≤ Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)
          * ‖fderiv ℝ (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖ :=
        mul_nonneg hc0 (norm_nonneg _)
      have h12 : (0 : ℝ) ≤ (Submission.BoseGases.chiScale ℓ x
              * ‖fderiv ℝ (fun y : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x‖)
            * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)
              * ‖fderiv ℝ (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖) :=
        mul_nonneg hq1 hq2
      have hpq : (0 : ℝ) ≤ 2 * (Submission.BoseGases.chiScale ℓ x
              * ‖fderiv ℝ (fun y : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x‖)
            * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)
              * ‖fderiv ℝ (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖) := by
        nlinarith [h12]
      have hsq1 : ‖(Submission.BoseGases.chiScale ℓ x) • fderiv ℝ
              (fun y : E3 => Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x
            + (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) • fderiv ℝ
              (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖ ^ 2
          ≤ (Submission.BoseGases.chiScale ℓ x
                * ‖fderiv ℝ (fun y : E3 =>
                    Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x‖
              + Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)
                * ‖fderiv ℝ (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      nlinarith [hsq1, hpq, hq1, hq2,
        sq_nonneg (Submission.BoseGases.chiScale ℓ x
            * ‖fderiv ℝ (fun y : E3 =>
                Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x‖
          - Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)
            * ‖fderiv ℝ (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖)]
    calc ‖(Submission.BoseGases.chiScale ℓ x) • fderiv ℝ
            (fun y : E3 => Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x
          + (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) • fderiv ℝ
            (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖ ^ 2
        ≤ 2 * (Submission.BoseGases.chiScale ℓ x
              * ‖fderiv ℝ (fun y : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • y - u)) x‖) ^ 2
          + 2 * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)
              * ‖fderiv ℝ (fun y : E3 => Submission.BoseGases.chiScale ℓ y) x‖) ^ 2 := hsq
      _ = 2 * (‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
              * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) ^ 2)
          + 2 * ((Submission.BoseGases.chiScale ℓ x) ^ 2
              * ‖fderiv ℝ (fun w : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2) := by ring
  -- ### integrability
  have hInt1 := integrable_gradA_mul_c (M := 48) (by norm_num) hN0 hℓ hd u hN
  have hInt2 := integrable_A_sq_mul_gradc_sq (M := 48) (by norm_num) hℓ hd u hCc0 hCc
  have hIntSum : Integrable (fun x : E3 =>
      2 * (‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
              * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) ^ 2)
      + 2 * ((Submission.BoseGases.chiScale ℓ x) ^ 2
              * ‖fderiv ℝ (fun w : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2)) :=
    (hInt1.const_mul 2).add (hInt2.const_mul 2)
  have hmono : (∫ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiSmallB 48 ℓ d u) x‖ ^ 2)
      ≤ ∫ x : E3, (2 * (‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
              * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) ^ 2)
      + 2 * ((Submission.BoseGases.chiScale ℓ x) ^ 2
              * ‖fderiv ℝ (fun w : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2)) :=
    integral_mono_of_nonneg (ae_of_all _ (fun x => sq_nonneg _)) hIntSum
      (ae_of_all _ hsplit)
  have hsplit_int : (∫ x : E3, (2 * (‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
              * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) ^ 2)
      + 2 * ((Submission.BoseGases.chiScale ℓ x) ^ 2
              * ‖fderiv ℝ (fun w : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2)))
      = 2 * (∫ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) x‖ ^ 2
              * (Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • x - u)) ^ 2)
        + 2 * (∫ x : E3, (Submission.BoseGases.chiScale ℓ x) ^ 2
              * ‖fderiv ℝ (fun w : E3 =>
                  Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2) := by
    rw [integral_add (hInt1.const_mul 2) (hInt2.const_mul 2), integral_const_mul,
      integral_const_mul]
  linarith [hmono, hsplit_int, hE1, hE2]

/-- **The autocorrelation defect of the sliding cutoff on a massive box, at loss `1/50`.**

Under the massive hypothesis `d^{108}(ℓd)³ ≤ χ_m` the two-factor sliding cutoff satisfies the
pointwise shift bound `(49/50)·∫χ_B² ≤ ∫χ_B(x)χ_B(x−z)` for every `‖z‖ ≤ R` — the hypothesis that
turns FS `lm:w2>w1` into the two mass rows of `Regular`.

Route (the design's steps (i)+(ii)): the PROVED `L²`-form defect
`Work.BoseB1Cube.chiMass_sub_autoCorr_le` (`χ_m − ∫χ_Bχ_B(·−z) ≤ ½‖z‖²∫‖∇χ_B‖²`), plus the sharp
gradient bound `∫‖∇χ_B‖² ≤ 2‖D²chi‖∞ℓ⁻²χ_m^{1/2}(ℓd)^{3/2} + C_c²(ℓd)⁻²χ_m^{47/48}ℓ^{1/16}`
obtained from `Work.BoseSWE.chiScaleGlaeser` (Glaeser for `chiScale ℓ`), the pointwise Hölder bound
`Work.BoseSWE.chiSmallGradHolder` (for the `ℓd`-scale cosine factor) and Hölder; the massive
threshold `d^{108}(ℓd)³ ≤ χ_m` makes both terms `≤ χ_m/(100R²)` once `ε₀` is small.
**Note (both reviewers)**: `ε₀` must be shrunk beyond `Work.BoseFixB1.regime_sideAt_ge`'s
`16R ≤ ℓd` — the proof needs `ℓd ≥ K·R` with a large fixed `K` (the constants of the two gradient
terms), which is available since `ℓd = a(μa³)^{−157/323} → ∞` as `ε₀ → 0`; likewise `d ≤ 1`. -/
theorem massiveDefect {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        (Work.BoseFixB1.bD v μ) ^ 108
            * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3
          ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u →
        ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
          (49 / 50) * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
              (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
            ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u x
                  * Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u (x - z) := by
  obtain ⟨K1, hK1nn, hE1⟩ := chiScaleGradMulC (M := 48) (by norm_num)
  obtain ⟨K2, hK2nn, hE2gen⟩ := chiScaleSqMulGradC (M := 48) (by norm_num)
  have hc1pos : 0 < max K1 1 := lt_of_lt_of_le one_pos (le_max_right K1 1)
  have hc2pos : 0 < max K2 1 := lt_of_lt_of_le one_pos (le_max_right K2 1)
  obtain ⟨εa, hεapos, harith⟩ := massiveThreshArith (v := v) hav hR hc1pos hc2pos
  refine ⟨min εa 1, lt_min hεapos one_pos, ?_⟩
  intro μ hAdm u hu hmass z hz
  have hAdm' : Work.BoseBoxFix.Adm v εa μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  obtain ⟨hdpos0, hℓpos0, hAr1, hAr2⟩ := harith μ hAdm'
  have hbM : Work.BoseFixB1.bM v μ = 48 := by
    simp [Work.BoseFixB1.bM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
  rw [hbM] at hmass ⊢
  set ℓ : ℝ := Work.BoseFixB1.bSide v μ with hℓdef
  set d : ℝ := Work.BoseFixB1.bD v μ with hddef
  have hℓpos : 0 < ℓ := by rw [hℓdef]; exact hℓpos0
  have hdpos : 0 < d := by rw [hddef]; exact hdpos0
  have hχnn : 0 ≤ Work.SmallBoxSliding.chiMass 48 ℓ d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hχpos : 0 < Work.SmallBoxSliding.chiMass 48 ℓ d u :=
    lt_of_lt_of_le (by positivity) hmass
  obtain ⟨N, hN0, hN⟩ := Work.BoseSWE.chiScaleGlaeser
  obtain ⟨Cc, hCc0, hCc⟩ := Work.BoseSWE.chiSmallGradHolder 48 (by norm_num)
  have hE2 : (∫ x : E3, (Submission.BoseGases.chiScale ℓ x) ^ 2
        * ‖fderiv ℝ (fun w : E3 => Submission.BoseGases.chiSmall 48 ((ℓ * d)⁻¹ • w - u)) x‖ ^ 2)
      ≤ K2 * ((ℓ * d)⁻¹) ^ 2 * (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ ((47 : ℝ) / 48)
        * ℓ ^ ((1 : ℝ) / 16) := by
    have h := hE2gen ℓ d hℓpos hdpos u
    simp only [show ((((48 : ℕ) : ℝ) - 1) / ((48 : ℕ) : ℝ)) = ((47 : ℝ) / 48) by norm_num,
      show (3 : ℝ) / ((48 : ℕ) : ℝ) = ((1 : ℝ) / 16) by norm_num] at h
    exact h
  have hgradSq0 := gradSq_le hN0 hℓpos hdpos u hCc0 (hN ℓ hℓpos)
    (hCc (ℓ * d) (mul_pos hℓpos hdpos) u)
    (hE1 ℓ d hℓpos hdpos u) hE2
  have hsqrt := sqrt_mass_ge (M := 48) hℓpos hdpos u hmass
  have hrpow := rpow_mass_ge (M := 48) hℓpos hdpos u hmass
  -- ### the two term estimates
  have hstep : (ℓ * d) ^ (33 / 16 : ℝ) * ((ℓ * d)⁻¹) ^ 2 = (ℓ * d) ^ (1 / 16 : ℝ) := by
    have h0 : (0 : ℝ) < ℓ * d := mul_pos hℓpos hdpos
    have hA : (ℓ * d) ^ (33 / 16 : ℝ)
        = (ℓ * d) ^ (1 / 16 : ℝ) * (ℓ * d) ^ (2 : ℝ) := by
      rw [← Real.rpow_add h0]; norm_num
    have hB : (ℓ * d) ^ (2 : ℝ) * ((ℓ * d)⁻¹) ^ 2 = 1 := by
      have h2 : (ℓ * d) ^ (2 : ℝ) = (ℓ * d) ^ 2 := Real.rpow_natCast _ _
      rw [h2, ← mul_pow, mul_inv_cancel₀ (ne_of_gt h0), one_pow]
    rw [hA, mul_assoc, hB, mul_one]
  have hAr1'' : 100 * R ^ 2 * K1 * (ℓ⁻¹) ^ 2 ≤ d ^ 54 := by
    have h1 : 100 * R ^ 2 * K1 ≤ 100 * R ^ 2 * max K1 1 :=
      mul_le_mul_of_nonneg_left (le_max_left K1 1) (by positivity)
    have h2 : 100 * R ^ 2 * K1 ≤ ℓ ^ 2 * d ^ 54 := le_trans h1 hAr1
    have h3 : ℓ ^ 2 * (ℓ⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hℓpos), one_pow]
    have h4 : ℓ ^ 2 * d ^ 54 * (ℓ⁻¹) ^ 2 = d ^ 54 := by
      rw [show ℓ ^ 2 * d ^ 54 * (ℓ⁻¹) ^ 2 = d ^ 54 * (ℓ ^ 2 * (ℓ⁻¹) ^ 2) by ring, h3,
        mul_one]
    calc 100 * R ^ 2 * K1 * (ℓ⁻¹) ^ 2 ≤ ℓ ^ 2 * d ^ 54 * (ℓ⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = d ^ 54 := h4
  have hT1 : (R ^ 2 / 2) * (2 * K1 * (ℓ⁻¹) ^ 2
        * Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u) * (ℓ * d) ^ (3 / 2 : ℝ))
      ≤ Work.SmallBoxSliding.chiMass 48 ℓ d u / 100 := by
    have h5 : 0 ≤ (ℓ * d) ^ (3 / 2 : ℝ) :=
      Real.rpow_nonneg (le_of_lt (mul_pos hℓpos hdpos)) _
    have h4 : 100 * R ^ 2 * K1 * (ℓ⁻¹) ^ 2 * (ℓ * d) ^ (3 / 2 : ℝ)
        ≤ Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u) := by
      calc 100 * R ^ 2 * K1 * (ℓ⁻¹) ^ 2 * (ℓ * d) ^ (3 / 2 : ℝ)
          ≤ d ^ 54 * (ℓ * d) ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_right hAr1'' h5
        _ ≤ Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u) := hsqrt
    have h7 : Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u)
        * Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u)
        = Work.SmallBoxSliding.chiMass 48 ℓ d u := Real.mul_self_sqrt hχnn
    have hmul : 100 * R ^ 2 * K1 * (ℓ⁻¹) ^ 2 * (ℓ * d) ^ (3 / 2 : ℝ)
          * Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u)
        ≤ Work.SmallBoxSliding.chiMass 48 ℓ d u := by
      have h := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg (Work.SmallBoxSliding.chiMass 48 ℓ d u))
      rwa [h7] at h
    have hgoal : (R ^ 2 / 2) * (2 * K1 * (ℓ⁻¹) ^ 2
          * Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u) * (ℓ * d) ^ (3 / 2 : ℝ))
        = (100 * R ^ 2 * K1 * (ℓ⁻¹) ^ 2 * (ℓ * d) ^ (3 / 2 : ℝ)
            * Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u)) / 100 := by ring
    rw [hgoal]
    exact div_le_div_of_nonneg_right hmul (by norm_num)
  have hAr2'' : 100 * R ^ 2 * K2 * ((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ)
      ≤ d ^ (9 / 4 : ℝ) * (ℓ * d) ^ (1 / 16 : ℝ) := by
    have hcoef : 0 ≤ ((ℓ * d)⁻¹) ^ 2 := sq_nonneg _
    have step1 : 100 * R ^ 2 * max K2 1 * ℓ ^ (1 / 16 : ℝ) * ((ℓ * d)⁻¹) ^ 2
        ≤ d ^ (9 / 4 : ℝ) * (ℓ * d) ^ (33 / 16 : ℝ) * ((ℓ * d)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_right hAr2 hcoef
    have e1 : 100 * R ^ 2 * max K2 1 * ℓ ^ (1 / 16 : ℝ) * ((ℓ * d)⁻¹) ^ 2
        = 100 * R ^ 2 * max K2 1 * ((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ) := by ring
    have e2 : d ^ (9 / 4 : ℝ) * (ℓ * d) ^ (33 / 16 : ℝ) * ((ℓ * d)⁻¹) ^ 2
        = d ^ (9 / 4 : ℝ) * (ℓ * d) ^ (1 / 16 : ℝ) := by rw [mul_assoc, hstep]
    have step2 : 100 * R ^ 2 * max K2 1 * ((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ)
        ≤ d ^ (9 / 4 : ℝ) * (ℓ * d) ^ (1 / 16 : ℝ) := by
      rw [← e1, ← e2]; exact step1
    have step3 : 100 * R ^ 2 * K2 * ((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ)
        ≤ 100 * R ^ 2 * max K2 1 * ((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ) := by
      have hb : 0 ≤ ((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hℓpos) _)
      calc 100 * R ^ 2 * K2 * ((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ)
          = 100 * R ^ 2 * K2 * (((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ)) := by ring
        _ ≤ 100 * R ^ 2 * max K2 1 * (((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (le_max_left K2 1) (by positivity)) hb
        _ = 100 * R ^ 2 * max K2 1 * ((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ) := by ring
    linarith [step2, step3]
  have hT2 : (R ^ 2 / 2) * (2 * K2 * ((ℓ * d)⁻¹) ^ 2
        * (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ ((47 : ℝ) / 48) * ℓ ^ (1 / 16 : ℝ))
      ≤ Work.SmallBoxSliding.chiMass 48 ℓ d u / 100 := by
    have h8 : 100 * R ^ 2 * K2 * ((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ)
        ≤ (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ (1 / 48 : ℝ) := le_trans hAr2'' hrpow
    have h9 : (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ (1 / 48 : ℝ)
        * (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ ((47 : ℝ) / 48)
        = Work.SmallBoxSliding.chiMass 48 ℓ d u := by
      rw [← Real.rpow_add hχpos,
        show (1 / 48 : ℝ) + 47 / 48 = 1 by norm_num, Real.rpow_one]
    have hpow0 : 0 ≤ (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ ((47 : ℝ) / 48) :=
      Real.rpow_nonneg hχnn _
    have hmul : 100 * R ^ 2 * K2 * ((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ)
          * (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ ((47 : ℝ) / 48)
        ≤ Work.SmallBoxSliding.chiMass 48 ℓ d u := by
      have h := mul_le_mul_of_nonneg_right h8 hpow0
      rwa [h9] at h
    have hgoal : (R ^ 2 / 2) * (2 * K2 * ((ℓ * d)⁻¹) ^ 2
          * (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ ((47 : ℝ) / 48) * ℓ ^ (1 / 16 : ℝ))
        = (100 * R ^ 2 * K2 * ((ℓ * d)⁻¹) ^ 2 * ℓ ^ (1 / 16 : ℝ)
            * (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ ((47 : ℝ) / 48)) / 100 := by ring
    rw [hgoal]
    exact div_le_div_of_nonneg_right hmul (by norm_num)
  -- ### the defect
  have hAC := Work.BoseSWE.chiMass_sub_autoCorr_leW (M := 48) (by norm_num) hℓpos hdpos u z
  have hsym : (∫ y : E3, Submission.BoseGases.chiSmallB 48 ℓ d u (z + y)
          * Submission.BoseGases.chiSmallB 48 ℓ d u y)
      = ∫ x : E3, Submission.BoseGases.chiSmallB 48 ℓ d u x
          * Submission.BoseGases.chiSmallB 48 ℓ d u (x - z) := by
    rw [← MeasureTheory.integral_add_left_eq_self
      (fun x : E3 => Submission.BoseGases.chiSmallB 48 ℓ d u x
        * Submission.BoseGases.chiSmallB 48 ℓ d u (x - z)) z]
    refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
    show Submission.BoseGases.chiSmallB 48 ℓ d u (z + y) * Submission.BoseGases.chiSmallB 48 ℓ d u y
      = Submission.BoseGases.chiSmallB 48 ℓ d u (z + y)
        * Submission.BoseGases.chiSmallB 48 ℓ d u (z + y - z)
    rw [add_sub_cancel_left]
  have hgradE : (∫ x : E3, ‖gradient (fun w : E3 =>
          Submission.BoseGases.chiSmallB 48 ℓ d u w) x‖ ^ 2)
      = ∫ x : E3, ‖fderiv ℝ (Submission.BoseGases.chiSmallB 48 ℓ d u) x‖ ^ 2 :=
    integral_congr_ae (Eventually.of_forall (fun x => by
      show ‖gradient (fun w : E3 => Submission.BoseGases.chiSmallB 48 ℓ d u w) x‖ ^ 2
        = ‖fderiv ℝ (Submission.BoseGases.chiSmallB 48 ℓ d u) x‖ ^ 2
      rw [gradNorm_eq_fderivNorm (fun w : E3 => Submission.BoseGases.chiSmallB 48 ℓ d u w) x]))
  have hchi : (∫ x : E3, Submission.BoseGases.chiSmallB 48 ℓ d u x ^ 2)
      = Work.SmallBoxSliding.chiMass 48 ℓ d u :=
    Work.SmallBoxSliding.chiMass_def 48 ℓ d u
  have hdef : Work.SmallBoxSliding.chiMass 48 ℓ d u
      - (∫ x : E3, Submission.BoseGases.chiSmallB 48 ℓ d u x
          * Submission.BoseGases.chiSmallB 48 ℓ d u (x - z))
      ≤ (R ^ 2 / 2) * ∫ x : E3,
          ‖fderiv ℝ (Submission.BoseGases.chiSmallB 48 ℓ d u) x‖ ^ 2 := by
    rw [hsym, hgradE, hchi] at hAC
    have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg z]
    have hG0 : 0 ≤ ∫ x : E3,
        ‖fderiv ℝ (Submission.BoseGases.chiSmallB 48 ℓ d u) x‖ ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    nlinarith [hAC, hz2, hG0]
  -- ### the gradient budget
  have hmain : (R ^ 2 / 2) * (∫ x : E3,
        ‖fderiv ℝ (Submission.BoseGases.chiSmallB 48 ℓ d u) x‖ ^ 2)
      ≤ Work.SmallBoxSliding.chiMass 48 ℓ d u / 50 := by
    have hR2 : (0 : ℝ) ≤ R ^ 2 / 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hgradSq0 hR2
    have h2 : (R ^ 2 / 2) * (2 * K1 * (ℓ⁻¹) ^ 2 * Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u)
            * (ℓ * d) ^ (3 / 2 : ℝ)
          + 2 * K2 * ((ℓ * d)⁻¹) ^ 2
              * (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ ((47 : ℝ) / 48) * ℓ ^ (1 / 16 : ℝ))
        = (R ^ 2 / 2) * (2 * K1 * (ℓ⁻¹) ^ 2 * Real.sqrt (Work.SmallBoxSliding.chiMass 48 ℓ d u)
            * (ℓ * d) ^ (3 / 2 : ℝ))
          + (R ^ 2 / 2) * (2 * K2 * ((ℓ * d)⁻¹) ^ 2
              * (Work.SmallBoxSliding.chiMass 48 ℓ d u) ^ ((47 : ℝ) / 48) * ℓ ^ (1 / 16 : ℝ)) := by
      ring
    rw [h2] at h1
    linarith [h1, hT1, hT2]
  linarith [hdef, hmain]

end

end Work.BoseSWE
