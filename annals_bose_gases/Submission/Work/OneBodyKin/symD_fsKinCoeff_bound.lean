import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.ProfHatDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.symD_fsKinCoeff_bound` — uniform bound on the cross symbol `symD`
at the FS cut-off `fsKinCoeff C`

The second symbol term of the projected moving-box family form is

    `symD ℓ F q = ∫_p F(‖p‖) · profHat(ℓ p) · profHat(ℓ (q−p)) dp`.

Here we bound it *uniformly in the momentum `q`* at scale `ℓ = 1` and for the (untruncated)
FS cut-off `F = fsKinCoeff C = [·−C]₊²`.

The mechanism is a one-step domination.  The first factor grows at most quadratically,
`fsKinCoeff C ‖p‖ ≤ (1+|C|)² (1+‖p‖)²`, the *second* factor decays like `(1+‖p‖)^{-6}`
(`ProfHatDecay`), and the *third* factor is merely *bounded* by the same constant `K ≥ 0`.  The
two growths cancel, the radial weight `(1+‖p‖)^{-4}` is integrable in three dimensions, and the
third factor's bound is independent of `q` — so the integral is dominated uniformly in `q`:

    `|symD 1 (fsKinCoeff C) q| ≤ (1+|C|)² K² ∫_p (1+‖p‖)^{-4} dp`.

No decay of `profHat(q−p)` is needed; the constant is completely explicit but we only record its
existence.
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. Pointwise inputs -/

/-- **The FS cut-off is dominated by a fixed quadratic weight**: for every `p`,
`fsKinCoeff C ‖p‖ ≤ (1+|C|)² (1+‖p‖)²`.  Indeed `[‖p‖−C]₊ ≤ |‖p‖−C| ≤ ‖p‖+|C| ≤ (1+|C|)(1+‖p‖)`
and both sides are nonnegative. -/
private lemma fsKinCoeff_le (C : ℝ) (p : ℝ³) :
    fsKinCoeff C ‖p‖ ≤ (1 + |C|) ^ 2 * (1 + ‖p‖) ^ 2 := by
  rw [Submission.BoseGases.fsKinCoeff]
  have hr : 0 ≤ ‖p‖ := norm_nonneg _
  have hle : max (‖p‖ - C) 0 ≤ (1 + |C|) * (1 + ‖p‖) := by
    have h1 : ‖p‖ - C ≤ |‖p‖ - C| := le_abs_self _
    have h2 : |‖p‖ - C| ≤ ‖p‖ + |C| := by
      calc |‖p‖ - C| ≤ |‖p‖| + |C| := abs_sub _ _
        _ = ‖p‖ + |C| := by rw [abs_of_nonneg hr]
    have h3 : max (‖p‖ - C) 0 ≤ ‖p‖ + |C| := max_le (le_trans h1 h2) (by positivity)
    nlinarith [abs_nonneg C, hr]
  have h0 : 0 ≤ max (‖p‖ - C) 0 := le_max_right _ _
  calc max (‖p‖ - C) 0 ^ 2 ≤ ((1 + |C|) * (1 + ‖p‖)) ^ 2 := pow_le_pow_left₀ h0 hle 2
    _ = (1 + |C|) ^ 2 * (1 + ‖p‖) ^ 2 := by ring

/-- **The first profile factor carries the decay**: `|profHat p| ≤ K (1+‖p‖)^{-6}`. -/
private lemma profHat_abs_le_inv (K : ℝ)
    (hd : ∀ p : ℝ³, |profHat p| ≤ K / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    |profHat p| ≤ K * ((1 + ‖p‖) ^ 6)⁻¹ := by
  rw [← div_eq_mul_inv]; exact hd p

/-- **The second profile factor is bounded by `K` alone** (its decay is not needed): the decay
hypothesis at the shifted argument gives `|profHat q| ≤ K/(1+‖q‖)^6 ≤ K`. -/
private lemma profHat_abs_le (K : ℝ) (hKnn : 0 ≤ K)
    (hd : ∀ p : ℝ³, |profHat p| ≤ K / (1 + ‖p‖) ^ 6) (q : ℝ³) :
    |profHat q| ≤ K := by
  refine (hd q).trans ?_
  have hden : (1 : ℝ) ≤ (1 + ‖q‖) ^ 6 := one_le_pow₀ (by linarith [norm_nonneg q])
  have hle : K / (1 + ‖q‖) ^ 6 ≤ K / 1 :=
    div_le_div_of_nonneg_left hKnn (by norm_num) hden
  simpa using hle

/-- **Integrability of the dominating weight** `p ↦ (1+‖p‖)^{-4}` on `ℝ³` (the exponent `4`
beats the dimension `3`). -/
private lemma integrable_one_add_norm_inv_four :
    Integrable (fun p : ℝ³ => ((1 + ‖p‖) ^ 4)⁻¹) := by
  have hb : Integrable (fun p : ℝ³ => (1 + ‖p‖) ^ (-(4 : ℝ))) := by
    refine integrable_one_add_norm (E := ℝ³) (μ := volume) (r := 4) ?_
    rw [finrank_euclideanSpace_fin]
    norm_num
  refine hb.congr (Filter.Eventually.of_forall (fun p => ?_))
  show (1 + ‖p‖) ^ (-(4 : ℝ)) = ((1 + ‖p‖) ^ 4)⁻¹
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
  congr 1
  exact Real.rpow_natCast (1 + ‖p‖) 4

/-! ## 2. The uniform bound -/

theorem symD_fsKinCoeff_bound (C : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ρ : EuclideanSpace ℝ (Fin 3),
      |Work.OneBodyKin.symD 1 (Submission.BoseGases.fsKinCoeff C) ρ| ≤ D := by
  classical
  obtain ⟨K, hKnn, hK⟩ := ProfHatDecay
  set h : ℝ³ → ℝ := fun p => ((1 + ‖p‖) ^ 4)⁻¹ with hh
  have hint : Integrable h := by rw [hh]; exact integrable_one_add_norm_inv_four
  have hhnn : ∀ p : ℝ³, 0 ≤ h p := by intro p; rw [hh]; positivity
  have hInt : 0 ≤ ∫ p : ℝ³, h p := integral_nonneg hhnn
  set A : ℝ := (1 + |C|) ^ 2 * K ^ 2 with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  refine ⟨A * ∫ p : ℝ³, h p, mul_nonneg hAnn hInt, ?_⟩
  intro ρ
  set I : ℝ³ → ℝ := fun p => fsKinCoeff C ‖p‖ * profHat p * profHat (ρ - p) with hIdef
  have hsym : symD 1 (fsKinCoeff C) ρ = ∫ p : ℝ³, I p := by
    rw [hIdef]
    simp only [symD, one_smul]
  -- the pointwise domination of the integrand
  have hdom : ∀ p : ℝ³, ‖I p‖ ≤ A * h p := by
    intro p
    have hr : 0 ≤ ‖p‖ := norm_nonneg _
    have hA' := fsKinCoeff_le C p
    have hB := profHat_abs_le_inv K hK p
    have hD' := profHat_abs_le K hKnn hK (ρ - p)
    have hfs0 : 0 ≤ fsKinCoeff C ‖p‖ := fsKinCoeff_nonneg C ‖p‖
    have hb1nn : 0 ≤ (1 + |C|) ^ 2 * (1 + ‖p‖) ^ 2 := by positivity
    have hb2nn : 0 ≤ K * ((1 + ‖p‖) ^ 6)⁻¹ :=
      mul_nonneg hKnn (inv_nonneg.mpr (pow_nonneg (by positivity) 6))
    have hstep : ‖I p‖
        ≤ ((1 + |C|) ^ 2 * (1 + ‖p‖) ^ 2) * (K * ((1 + ‖p‖) ^ 6)⁻¹) * K := by
      rw [hIdef, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hfs0]
      exact mul_le_mul (mul_le_mul hA' hB (abs_nonneg _) hb1nn) hD' (abs_nonneg _)
        (mul_nonneg hb1nn hb2nn)
    have hpow : (1 + ‖p‖) ^ 2 * ((1 + ‖p‖) ^ 6)⁻¹ = ((1 + ‖p‖) ^ 4)⁻¹ := by
      have hne : (1 + ‖p‖ : ℝ) ≠ 0 := by positivity
      field_simp
    calc ‖I p‖ ≤ ((1 + |C|) ^ 2 * (1 + ‖p‖) ^ 2) * (K * ((1 + ‖p‖) ^ 6)⁻¹) * K := hstep
      _ = (1 + |C|) ^ 2 * K ^ 2 * ((1 + ‖p‖) ^ 2 * ((1 + ‖p‖) ^ 6)⁻¹) := by ring
      _ = (1 + |C|) ^ 2 * K ^ 2 * ((1 + ‖p‖) ^ 4)⁻¹ := by rw [hpow]
      _ = A * h p := by rw [hA, hh]
  have hAint : Integrable (fun p : ℝ³ => A * h p) := hint.const_mul A
  have e1 : |∫ p : ℝ³, I p| ≤ ∫ p : ℝ³, ‖I p‖ := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume) I
  have e2 : ∫ p : ℝ³, ‖I p‖ ≤ ∫ p : ℝ³, A * h p :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall (fun p => norm_nonneg (I p))) hAint
      (Filter.Eventually.of_forall hdom)
  have e3 : ∫ p : ℝ³, A * h p = A * ∫ p : ℝ³, h p := integral_const_mul A h
  rw [hsym]
  linarith

end Work.OneBodyKin
