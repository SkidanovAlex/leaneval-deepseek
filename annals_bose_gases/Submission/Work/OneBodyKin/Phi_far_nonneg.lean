import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.Phi
import Submission.Work.OneBodyKin.integrable_chiMul_integral
import Submission.Work.OneBodyKin.profHat_sq_integral
import Submission.Work.OneBodyKin.symD_fsKinCoeff_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.Phi_far_nonneg` — the residual is positive far out

`Phi C ρ = ‖ρ‖² − famSym 1 (fsKinCoeff C) ρ` (`OneBodyKin/Phi.lean`).  This file proves the
**far-region coercivity** of the residual: as soon as `C` exceeds the first moment

    `K1 = (2π)⁻³ ∫_t profHat(t)² ‖t‖ dt`

of the squared bump profile, `Phi C ρ ≥ 0` for every `‖ρ‖ ≥ R` (some `R` depending on `C`).
This is exactly item 4(i) ("coercivity at infinity") of the roadmap of
`OneBodyKin/README.md` §5.

## The mechanism

Write `T = ‖ρ‖`, `c = (2π)⁻³`, `F = fsKinCoeff C = [·−C]₊²`, `A = symA 1 F ρ`,
`A₀ = symA 1 F 0`, `σ = boxHat 1 ρ` and `Δ = symD 1 F ρ`.  Expanding (`Phi_eq_expand`),

    `Phi C ρ = T² − A + 2c σ Δ − A₀ σ²`.

* *The gain.* `‖ρ+p‖ ≤ ‖ρ‖ + ‖p‖`, so for `T ≥ C` the pointwise bound
  `[‖ρ+p‖−C]₊² ≤ ((T−C) + ‖p‖)²`, integrated against `(2π)⁻³ profHat²` and using
  `profHat_sq_integral` (`(2π)⁻³∫profHat² = 1`), gives

      `A ≤ (T−C)² + 2(T−C)K1 + K2`,   `K2 = (2π)⁻³ ∫_t profHat(t)² ‖t‖² dt`,

  i.e. `T² − A ≥ 2T(C − K1) − (C² − 2C K1 + K2)`, which grows linearly because `C > K1`.
* *The error terms.* `|σ| ≤ 1` (`abs_boxHat_le`) and `|Δ| ≤ D` for a constant `D` (the decay of
  `profHat` against the quadratic weight `F(‖p‖)`), so `2cσΔ ≥ −2cD`; and `A₀ ≥ 0` with
  `σ² ≤ 1` gives `−A₀σ² ≥ −A₀`.  Both are only *constants*.

Hence `Phi C ρ ≥ 2T(C−K1) − E` with the explicit constant
`E = C² − 2C K1 + K2 + 2cD + A₀`, and any `R ≥ max C (E/(2(C−K1)))` works.

## What is used from the corpus

* `Phi_eq_expand`, `symA_nonneg`, `abs_boxHat_le` (`OneBodyKin/Phi.lean`, `SymAPI.lean`),
* `profHat_sq_integral` (`(2π)⁻³∫profHat² = 1`),
* `ProfHatDecay` (`|profHat p| ≤ Cd(1+‖p‖)^{-6}`), which turns all polynomial weights into
  integrable majorants `(1+‖p‖)^{-8}` (the `(2π)⁻³`-normalized weight `‖p‖^k` costs `k` powers
  of decay, and `8 > 3 = dim`),
* `symD_fsKinCoeff_bound` (the uniform bound `|symD 1 (fsKinCoeff C) ρ| ≤ D`),
* `continuous_profHat` (`integrable_chiMul_integral.lean`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false


/-- `(1+‖p‖)^{-k}` is integrable on `ℝ³` for `k > 3`. -/
private lemma integrable_inv_one_add_norm (k : ℕ) (hk : 3 < k) :
    Integrable (fun p : ℝ³ => ((1 + ‖p‖ : ℝ) ^ k)⁻¹) := by
  have h3 : (Module.finrank ℝ ℝ³ : ℝ) < (k : ℝ) := by
    rw [finrank_euclideanSpace_fin]; exact_mod_cast hk
  have h := integrable_one_add_norm (E := ℝ³) (μ := volume) (r := (k : ℝ)) h3
  refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
  show (1 + ‖p‖ : ℝ) ^ (-(k : ℝ)) = ((1 + ‖p‖ : ℝ) ^ k)⁻¹
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖), Real.rpow_natCast]

private lemma inv_pow_anti {r : ℝ} (hr : 0 ≤ r) {k l : ℕ} (hkl : k ≤ l) :
    ((1 + r) ^ l)⁻¹ ≤ ((1 + r) ^ k)⁻¹ := by
  refine inv_anti₀ (by positivity) ?_
  exact pow_le_pow_right₀ (by linarith) hkl

private lemma inv_mul_self_pow (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    ((1 + r) ^ k)⁻¹ * (1 + r) ^ k = 1 :=
  inv_mul_cancel₀ (by positivity)

private lemma inv_pow_mul_pow (r : ℝ) (hr : 0 ≤ r) {l k : ℕ} (hk : k ≤ l) :
    ((1 + r) ^ l)⁻¹ * (1 + r) ^ k = ((1 + r) ^ (l - k))⁻¹ := by
  have hle : (1 + r) ^ l = (1 + r) ^ (l - k) * (1 + r) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  calc ((1 + r) ^ l)⁻¹ * (1 + r) ^ k
      = ((1 + r) ^ k)⁻¹ * ((1 + r) ^ (l - k))⁻¹ * (1 + r) ^ k := by
        rw [hle, mul_inv_rev]
    _ = ((1 + r) ^ (l - k))⁻¹ * (((1 + r) ^ k)⁻¹ * (1 + r) ^ k) := by ring
    _ = ((1 + r) ^ (l - k))⁻¹ := by rw [inv_mul_self_pow r hr k, mul_one]

/-- Squaring the decay hypothesis: `profHat(p)² ≤ Cd²(1+‖p‖)^{-12}`. -/
private lemma profHat_sq_le_twelve {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hd : ∀ p : ℝ³, |profHat p| ≤ Cd / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    (profHat p) ^ 2 ≤ Cd ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹ := by
  have h1 : (profHat p) ^ 2 ≤ (Cd / (1 + ‖p‖) ^ 6) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hd p) 2
  have h2 : (Cd / (1 + ‖p‖) ^ 6) ^ 2 = Cd ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹ := by
    rw [div_pow, div_eq_mul_inv, ← pow_mul]
  rwa [h2] at h1

/-- The three weighted profiles are all dominated by `Cd²(1+‖p‖)^{-8}`. -/
private lemma profHat_sq_le_majorant {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hd : ∀ p : ℝ³, |profHat p| ≤ Cd / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    (profHat p) ^ 2 ≤ Cd ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ :=
  (profHat_sq_le_twelve hCd hd p).trans
    (mul_le_mul_of_nonneg_left (inv_pow_anti (norm_nonneg p) (by norm_num)) (sq_nonneg Cd))

private lemma profHat_sq_mul_norm_le_majorant {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hd : ∀ p : ℝ³, |profHat p| ≤ Cd / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    (profHat p) ^ 2 * ‖p‖ ≤ Cd ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ := by
  have hr : 0 ≤ ‖p‖ := norm_nonneg p
  calc (profHat p) ^ 2 * ‖p‖
      ≤ (Cd ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹) * (1 + ‖p‖) :=
        mul_le_mul (profHat_sq_le_twelve hCd hd p) (by linarith) hr (by positivity)
    _ = Cd ^ 2 * (((1 + ‖p‖) ^ 12)⁻¹ * (1 + ‖p‖)) := by ring
    _ = Cd ^ 2 * ((1 + ‖p‖) ^ 11)⁻¹ := by
        congr 1
        simpa using inv_pow_mul_pow ‖p‖ hr (l := 12) (k := 1) (by norm_num)
    _ ≤ Cd ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_pow_anti hr (by norm_num)) (sq_nonneg Cd)

private lemma profHat_sq_mul_normSq_le_majorant {Cd : ℝ} (hCd : 0 ≤ Cd)
    (hd : ∀ p : ℝ³, |profHat p| ≤ Cd / (1 + ‖p‖) ^ 6) (p : ℝ³) :
    (profHat p) ^ 2 * ‖p‖ ^ 2 ≤ Cd ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ := by
  have hr : 0 ≤ ‖p‖ := norm_nonneg p
  calc (profHat p) ^ 2 * ‖p‖ ^ 2
      ≤ (Cd ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹) * (1 + ‖p‖) ^ 2 :=
        mul_le_mul (profHat_sq_le_twelve hCd hd p) (by nlinarith) (sq_nonneg _) (by positivity)
    _ = Cd ^ 2 * (((1 + ‖p‖) ^ 12)⁻¹ * (1 + ‖p‖) ^ 2) := by ring
    _ = Cd ^ 2 * ((1 + ‖p‖) ^ 10)⁻¹ := by
        congr 1
        simpa using inv_pow_mul_pow ‖p‖ hr (l := 12) (k := 2) (by norm_num)
    _ ≤ Cd ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_pow_anti hr (by norm_num)) (sq_nonneg Cd)


/-- **The far-region coercivity of the unprojected symbol** at the FS cut-off
`fsKinCoeff C = [·−C]₊²`: for `‖ρ‖ ≥ C` the unprojected symbol `symA 1 F ρ` is bounded by
`(‖ρ‖−C)² + 2(‖ρ‖−C)K1 + K2` with the two moments `K1 = (2π)⁻³∫profHat²‖t‖` and
`K2 = (2π)⁻³∫profHat²‖t‖²` of the squared profile.

(Also available as the standalone lemma `Work.OneBodyKin.symA_fsKinCoeff_far_le`; this private
copy keeps the file self-contained.) -/
private theorem symA_far_le {C : ℝ} (ρ : ℝ³) (hρ : C ≤ ‖ρ‖) :
    symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
      ≤ (‖ρ‖ - C) ^ 2
        + 2 * (‖ρ‖ - C) * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ t : EuclideanSpace ℝ (Fin 3), (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖)
        + ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ t : EuclideanSpace ℝ (Fin 3), (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖ ^ 2 := by
  obtain ⟨Cd, hCd, hd⟩ := ProfHatDecay
  -- the common integrable majorant of the three weighted profiles
  have hmaj : Integrable (fun p : ℝ³ => Cd ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹) :=
    (integrable_inv_one_add_norm 8 (by norm_num)).const_mul (Cd ^ 2)
  have hI0 : Integrable (fun p : ℝ³ => (profHat p) ^ 2) :=
    hmaj.mono' ((continuous_profHat.pow 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact profHat_sq_le_majorant hCd hd p))
  have hI1 : Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖) :=
    hmaj.mono' (((continuous_profHat.pow 2).mul continuous_norm).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))]
        exact profHat_sq_mul_norm_le_majorant hCd hd p))
  have hI2 : Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖ ^ 2) :=
    hmaj.mono' (((continuous_profHat.pow 2).mul (continuous_norm.pow 2)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        exact profHat_sq_mul_normSq_le_majorant hCd hd p))
  -- the square of the sum, expanded
  have hexp : (fun p : ℝ³ => ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2)
      = fun p : ℝ³ => (‖ρ‖ - C) ^ 2 * (profHat p) ^ 2
          + (2 * (‖ρ‖ - C) * ((profHat p) ^ 2 * ‖p‖) + (profHat p) ^ 2 * ‖p‖ ^ 2) := by
    funext p; ring
  have hdomint : Integrable (fun p : ℝ³ => ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2) := by
    rw [hexp]
    exact (hI0.const_mul _).add ((hI1.const_mul _).add hI2)
  -- the pointwise domination
  have hpt : ∀ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖ρ + p‖ * (profHat p) ^ 2
      ≤ ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2 := by
    intro p
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [Submission.BoseGases.fsKinCoeff]
    refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ ?_) 2
    · have h1 := norm_add_le ρ p; linarith
    · have h1 := norm_nonneg ρ; have h2 := norm_nonneg p; linarith
  have hstep : ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖ρ + p‖ * (profHat p) ^ 2
      ≤ ∫ p : ℝ³, ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2 :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun p =>
        mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg C _) (sq_nonneg _)))
      hdomint (Filter.Eventually.of_forall hpt)
  -- the integral of the majorant, computed
  have hA : Integrable (fun p : ℝ³ => (‖ρ‖ - C) ^ 2 * (profHat p) ^ 2) := hI0.const_mul _
  have hB : Integrable (fun p : ℝ³ => 2 * (‖ρ‖ - C) * ((profHat p) ^ 2 * ‖p‖)) := hI1.const_mul _
  have hBC : Integrable (fun p : ℝ³ =>
      2 * (‖ρ‖ - C) * ((profHat p) ^ 2 * ‖p‖) + (profHat p) ^ 2 * ‖p‖ ^ 2) := by
    exact hB.add hI2
  have hval : ∫ p : ℝ³, ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2
      = (‖ρ‖ - C) ^ 2 * (∫ p : ℝ³, (profHat p) ^ 2)
        + 2 * (‖ρ‖ - C) * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖)
        + (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2) := by
    rw [hexp, integral_add hA hBC, integral_add hB hI2, integral_const_mul, integral_const_mul]
    ring

  -- unfold `symA` at `ℓ = 1`
  have hmain : symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2 := by
    rw [symA]
    simp only [inv_one, one_smul]
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  calc symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2 := hmain
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          ((‖ρ‖ - C) ^ 2 * (∫ p : ℝ³, (profHat p) ^ 2)
            + 2 * (‖ρ‖ - C) * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖)
            + (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2)) := by rw [hval]
    _ = (‖ρ‖ - C) ^ 2
        + 2 * (‖ρ‖ - C) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖)
        + ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2 := by
        rw [profHat_sq_integral]
        have hpi : ((2 * Real.pi) ^ 3) ≠ 0 := by positivity
        field_simp

/-- **The numerical core of the far-region bound.**  From the four inputs

* `A ≤ (T−C)² + 2(T−C)K1 + K2` (the coercivity gain of the cut-off),
* `|σ| ≤ 1`, `|Δ| ≤ D` (boundedness of the two remaining symbol pieces),
* `0 ≤ A₀` (nonnegativity of the mass term),
* `C² − 2CK1 + K2 + 2(2π)⁻³D + A₀ ≤ 2T(C − K1)` (the choice of `T`),

we get `0 ≤ T² − A + 2(2π)⁻³ σΔ − A₀σ²`. -/
private lemma far_core {C A A0 σ Δ D K1 K2 T : ℝ}
    (hA0 : 0 ≤ A0) (hσ : |σ| ≤ 1) (hΔ : |Δ| ≤ D)
    (hsymA : A ≤ (T - C) ^ 2 + 2 * (T - C) * K1 + K2)
    (hlin : C ^ 2 - 2 * C * K1 + K2 + 2 * ((2 * Real.pi) ^ 3)⁻¹ * D + A0 ≤ 2 * T * (C - K1)) :
    0 ≤ T ^ 2 - A + 2 * ((2 * Real.pi) ^ 3)⁻¹ * (σ * Δ) - A0 * σ ^ 2 := by
  -- the cross term is bounded below by `−(2π)⁻³`-times the constant `D`
  have hcross : -(2 * ((2 * Real.pi) ^ 3)⁻¹ * D) ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ * (σ * Δ) := by
    have h : -D ≤ σ * Δ := by
      have h2 : |σ * Δ| ≤ 1 * D := by
        rw [abs_mul]
        exact mul_le_mul hσ hΔ (abs_nonneg _) (by norm_num)
      linarith [neg_le_of_abs_le h2]
    have hc : 0 ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h hc]
  -- and the mass term absorbs into the constant `A₀`
  have hA0σ : A0 * σ ^ 2 ≤ A0 := by
    have h1 : σ ^ 2 ≤ 1 := by
      have hh := abs_le.mp hσ
      nlinarith [hh.1, hh.2]
    nlinarith [h1, hA0]
  nlinarith only [hsymA, hlin, hcross, hA0σ, hA0]

theorem Phi_far_nonneg {C : ℝ}
    (hC : ((2 * Real.pi) ^ 3)⁻¹ * (∫ t : EuclideanSpace ℝ (Fin 3),
        (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖) < C) :
    ∃ R : ℝ, ∀ ρ : EuclideanSpace ℝ (Fin 3), R ≤ ‖ρ‖ → 0 ≤ Work.OneBodyKin.Phi C ρ := by
  obtain ⟨D, _hDnn, hDb⟩ := symD_fsKinCoeff_bound C
  have hA0 : 0 ≤ Work.OneBodyKin.symA 1 (fsKinCoeff C) 0 :=
    Work.OneBodyKin.symA_nonneg (fun r => fsKinCoeff_nonneg C r) 1 0
  -- the three constants of the estimate
  set K1 : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * (∫ t : ℝ³, (profHat t) ^ 2 * ‖t‖) with hK1
  set K2 : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * (∫ t : ℝ³, (profHat t) ^ 2 * ‖t‖ ^ 2) with hK2
  set E : ℝ := C ^ 2 - 2 * C * K1 + K2 + 2 * ((2 * Real.pi) ^ 3)⁻¹ * D
      + Work.OneBodyKin.symA 1 (fsKinCoeff C) 0 with hE
  have hCK : K1 < C := by rw [hK1]; exact hC
  have hpos : 0 < C - K1 := by linarith
  refine ⟨max C (max 0 (E / (2 * (C - K1)))), fun ρ hρ => ?_⟩
  have hTC : C ≤ ‖ρ‖ := le_trans (le_max_left _ _) hρ
  have hTz : E / (2 * (C - K1)) ≤ ‖ρ‖ :=
    le_trans (le_trans (le_max_right 0 _) (le_max_right C _)) hρ
  -- the coercivity gain of the cut-off
  have hsymA := symA_far_le (C := C) ρ hTC
  rw [← hK1, ← hK2] at hsymA
  -- the two bounded pieces
  have hσ : |Work.OneBodyKin.boxHat 1 ρ| ≤ 1 := by
    simpa using Work.OneBodyKin.abs_boxHat_le (ℓ := 1) (by norm_num) ρ
  have hΔ : |Work.OneBodyKin.symD 1 (fsKinCoeff C) ρ| ≤ D := hDb ρ
  -- the choice of `R`
  have hlin : E ≤ 2 * ‖ρ‖ * (C - K1) := by
    have h2 : 0 ≤ 2 * (C - K1) := by linarith
    have h3 : E / (2 * (C - K1)) * (2 * (C - K1)) ≤ ‖ρ‖ * (2 * (C - K1)) :=
      mul_le_mul_of_nonneg_right hTz h2
    rw [div_mul_cancel₀ _ (by linarith : (2 * (C - K1)) ≠ 0)] at h3
    linarith
  have hcore := far_core hA0 hσ hΔ hsymA hlin
  rw [Work.OneBodyKin.Phi_eq_expand C ρ]
  nlinarith only [hcore]

end Work.OneBodyKin
