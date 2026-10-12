import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.cnPlus_eq_slotSum
import Submission.Work.BSKinetic.familyForm_zero_eq
import Submission.Work.BSKinetic.locKinEnWordBox_of_familyBound
import Submission.Work.BSKinetic.tBwordBInd_slotSwap_and_integrable
import Submission.Work.OneBodyKin.Phi_far_nonneg
import Submission.Work.OneBodyKin.SecondOrder.boxHat_one_sub_sq_le
import Submission.Work.OneBodyKin.SecondOrder.symA_zero_small
import Submission.Work.OneBodyKin.SecondOrder.symD_diff_bound_uniform
import Submission.Work.OneBodyKin.SecondOrder.symD_fsKinCoeff_small
import Submission.Work.OneBodyKin.SymBound_iff_SymBoundOne
import Submission.Work.OneBodyKin.SymbolIntegral_fsKinCoeff
import Submission.Work.OneBodyKin.dSpace_eq_fourier
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq
import Submission.Work.OneBodyKin.symA_fsKinCoeff_far_le
import Submission.Work.OneBodyKin.symD_second_order
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.symA_Ftrunc_quad_bound` — uniform quadratic growth of `symA` at the truncations

The unprojected family symbol with the truncated FS cut-off `Ftrunc c n` grows at most
quadratically in the momentum, *uniformly in the truncation parameter* `n`:

    `|symA ℓ (Ftrunc c n) q| ≤ A ‖q‖² + B`

with `A, B ≥ 0` depending on `ℓ` and `c` only.  Here (`Work.OneBodyKin.Defs`)

    `symA ℓ F q = (2π)⁻³ ∫_p F ‖q + ℓ⁻¹ • p‖ · profHat(p)² dp`,

so the statement is a bound on the second moment of the bump profile weighted by the radial
cut-off `Ftrunc c n = [· − c]₊² · 1_{· ≤ n}`.

## The proof

* **Integrability of the two moments.**  `p ↦ profHat(p)² ‖p‖^k` is integrable for `k ≤ 2`
  (`Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow`, which squares the Schwartz decay
  `|profHat p| ≤ C(1+‖p‖)^{-6}` of `Work.OneBodyKin.ProfHatDecay` and invokes
  `integrable_one_add_norm`).  Hence `I₀ = ∫ profHat²` and `I₁ = ∫ ‖p‖² profHat²` are finite and
  nonnegative.
* **Pointwise domination.**  With `r = ‖q + ℓ⁻¹ • p‖` we have on the one hand
  `Ftrunc c n r ≤ [r − c]₊² = (max (r−c) 0)² ≤ (r−c)² ≤ 2r² + 2c²` (the last step is
  `(r+c)² ≥ 0`), and on the other hand `r ≤ ‖q‖ + ℓ⁻¹‖p‖`, whence
  `r² ≤ 2‖q‖² + 2ℓ⁻²‖p‖²` (from `(‖q‖ − ℓ⁻¹‖p‖)² ≥ 0`).  Multiplying by `profHat(p)² ≥ 0`,

      `Ftrunc c n ‖q + ℓ⁻¹•p‖ · profHat(p)² ≤ (4‖q‖² + 4ℓ⁻²‖p‖² + 2c²) · profHat(p)²`,

  an integrable domination *independent of* `n`.
* **Assembly.**  `symA ℓ (Ftrunc c n) q` is `(2π)⁻³` times the `p`-integral of a nonnegative
  function, so `|symA …| = (2π)⁻³ ∫ …`; `norm_integral_le_of_norm_le` against the pointwise bound
  followed by linearity of the integral,
  `∫ (4‖q‖² + 4ℓ⁻²‖p‖² + 2c²) profHat² = (4‖q‖² + 2c²) I₀ + 4ℓ⁻² I₁`, gives the claim with

      `A = (2π)⁻³ · 4 I₀`,   `B = (2π)⁻³ · (2c² I₀ + 4ℓ⁻² I₁)`,

  both nonnegative.  (A nonnegativity-only lower bound also follows immediately from
  `Ftrunc ≥ 0`, but the exact computation above is just as short.)
-/

namespace Work.BoseFixB1

noncomputable section

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. Integrability of the two moments of the bump profile -/

/-- `p ↦ profHat(p)²` is integrable (the `k = 0` case of
`Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow`). -/
private lemma integrable_profHat_sq :
    Integrable (fun p : ℝ³ => (Work.OneBodyKin.profHat p) ^ 2) := by
  simpa using Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow 0 (by norm_num)

/-- `p ↦ ‖p‖² profHat(p)²` is integrable (the `k = 2` case, with the factors commuted). -/
private lemma integrable_normSq_profHat_sq :
    Integrable (fun p : ℝ³ => ‖p‖ ^ 2 * (Work.OneBodyKin.profHat p) ^ 2) := by
  refine (Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow 2 (by norm_num)).congr ?_
  filter_upwards with p
  ring

/-! ## 2. Pointwise domination of the integrand -/

/-- **The pointwise bound.**  The truncated FS cut-off evaluated at the shifted momentum
`r = ‖q + ℓ⁻¹ • p‖` costs at most `4‖q‖² + 4ℓ⁻²‖p‖² + 2c²`:
`Ftrunc c n r ≤ [r−c]₊² ≤ (r−c)² ≤ 2r² + 2c²` and `r² ≤ 2‖q‖² + 2ℓ⁻²‖p‖²`. -/
private lemma Ftrunc_mul_profHat_sq_le {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ) (q p : ℝ³) :
    Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖ * (Work.OneBodyKin.profHat p) ^ 2
      ≤ (4 * ‖q‖ ^ 2 + 4 * (ℓ ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2)
          * (Work.OneBodyKin.profHat p) ^ 2 := by
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  set r : ℝ := ‖q + ℓ⁻¹ • p‖ with hr
  have hF : Work.OneBodyKin.Ftrunc c n r ≤ 2 * r ^ 2 + 2 * c ^ 2 := by
    calc Work.OneBodyKin.Ftrunc c n r ≤ fsKinCoeff c r :=
          Work.OneBodyKin.Ftrunc_le_fsKinCoeff c n r
      _ = (max (r - c) 0) ^ 2 := rfl
      _ ≤ (r - c) ^ 2 := by
          have h1 : max (r - c) 0 ≤ |r - c| := by
            rcases le_total 0 (r - c) with h | h
            · rw [max_eq_left h, abs_of_nonneg h]
            · rw [max_eq_right h]; exact abs_nonneg _
          calc (max (r - c) 0) ^ 2 ≤ |r - c| ^ 2 :=
                pow_le_pow_left₀ (le_max_right (r - c) 0) h1 2
            _ = (r - c) ^ 2 := sq_abs (r - c)
      _ ≤ 2 * r ^ 2 + 2 * c ^ 2 := by nlinarith [sq_nonneg (r + c)]
  have hr2 : r ^ 2 ≤ 2 * ‖q‖ ^ 2 + 2 * (ℓ ^ 2)⁻¹ * ‖p‖ ^ 2 := by
    have hsplit : r ≤ ‖q‖ + ℓ⁻¹ * ‖p‖ := by
      rw [hr]
      calc ‖q + ℓ⁻¹ • p‖ ≤ ‖q‖ + ‖ℓ⁻¹ • p‖ := norm_add_le _ _
        _ = ‖q‖ + ℓ⁻¹ * ‖p‖ := by
              rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ℓ⁻¹)]
    calc r ^ 2 ≤ (‖q‖ + ℓ⁻¹ * ‖p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsplit 2
      _ ≤ 2 * ‖q‖ ^ 2 + 2 * (ℓ⁻¹ * ‖p‖) ^ 2 := by
            nlinarith [sq_nonneg (‖q‖ - ℓ⁻¹ * ‖p‖)]
      _ = 2 * ‖q‖ ^ 2 + 2 * (ℓ ^ 2)⁻¹ * ‖p‖ ^ 2 := by rw [mul_pow, inv_pow]; ring
  nlinarith [hF, hr2]

/-! ## 3. The theorem -/

theorem symA_Ftrunc_quad_bound {ℓ c : ℝ} (hℓ : 0 < ℓ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (n : ℕ) (q : EuclideanSpace ℝ (Fin 3)),
      |Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q| ≤ A * ‖q‖ ^ 2 + B := by
  have hI0int : Integrable (fun p : ℝ³ => (Work.OneBodyKin.profHat p) ^ 2) :=
    integrable_profHat_sq
  have hI1int : Integrable (fun p : ℝ³ => ‖p‖ ^ 2 * (Work.OneBodyKin.profHat p) ^ 2) :=
    integrable_normSq_profHat_sq
  set I0 : ℝ := ∫ p : ℝ³, (Work.OneBodyKin.profHat p) ^ 2 with hI0def
  set I1 : ℝ := ∫ p : ℝ³, ‖p‖ ^ 2 * (Work.OneBodyKin.profHat p) ^ 2 with hI1def
  have hI0nn : 0 ≤ I0 := by
    rw [hI0def]
    exact integral_nonneg (fun p => sq_nonneg _)
  have hI1nn : 0 ≤ I1 := by
    rw [hI1def]
    exact integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hc0 : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  refine ⟨((2 * Real.pi) ^ 3)⁻¹ * (4 * I0),
    ((2 * Real.pi) ^ 3)⁻¹ * (2 * c ^ 2 * I0 + 4 * (ℓ ^ 2)⁻¹ * I1), ?_, ?_, ?_⟩
  · exact mul_nonneg hc0.le (by linarith [hI0nn])
  · refine mul_nonneg hc0.le (add_nonneg ?_ ?_)
    · exact mul_nonneg (by positivity) hI0nn
    · exact mul_nonneg (by positivity) hI1nn
  · intro n q
    -- the dominating function is integrable and independent of `n`
    have hgint : Integrable (fun p : ℝ³ =>
        (4 * ‖q‖ ^ 2 + 4 * (ℓ ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2)
          * (Work.OneBodyKin.profHat p) ^ 2) := by
      have h1 : Integrable (fun p : ℝ³ =>
          (4 * ‖q‖ ^ 2 + 2 * c ^ 2) * (Work.OneBodyKin.profHat p) ^ 2) :=
        hI0int.const_mul _
      have h2 : Integrable (fun p : ℝ³ =>
          (4 * (ℓ ^ 2)⁻¹) * (‖p‖ ^ 2 * (Work.OneBodyKin.profHat p) ^ 2)) :=
        hI1int.const_mul _
      refine (h1.add h2).congr ?_
      filter_upwards with p
      simp only [Pi.add_apply]
      ring
    -- `symA` is `(2π)⁻³` times a nonnegative `p`-integral, dominated pointwise
    have hmain : |Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q|
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
            (4 * ‖q‖ ^ 2 + 4 * (ℓ ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2)
              * (Work.OneBodyKin.profHat p) ^ 2 := by
      rw [Work.OneBodyKin.symA, abs_mul, abs_of_pos hc0]
      refine mul_le_mul_of_nonneg_left ?_ hc0.le
      have hb : ‖∫ p : ℝ³, Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖
            * (Work.OneBodyKin.profHat p) ^ 2‖
          ≤ ∫ p : ℝ³, (4 * ‖q‖ ^ 2 + 4 * (ℓ ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2)
              * (Work.OneBodyKin.profHat p) ^ 2 := by
        refine norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall (fun p => ?_))
        have hnn : (0 : ℝ) ≤ Work.OneBodyKin.Ftrunc c n ‖q + ℓ⁻¹ • p‖
            * (Work.OneBodyKin.profHat p) ^ 2 :=
          mul_nonneg (Work.OneBodyKin.Ftrunc_nonneg c n _) (sq_nonneg _)
        rw [Real.norm_of_nonneg hnn]
        exact Ftrunc_mul_profHat_sq_le hℓ n q p
      rwa [Real.norm_eq_abs] at hb
    -- linearity of the integral for the dominating function
    have hsplit : (∫ p : ℝ³, (4 * ‖q‖ ^ 2 + 4 * (ℓ ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2)
          * (Work.OneBodyKin.profHat p) ^ 2)
        = (4 * ‖q‖ ^ 2 + 2 * c ^ 2) * I0 + 4 * (ℓ ^ 2)⁻¹ * I1 := by
      have hcongr : (fun p : ℝ³ => (4 * ‖q‖ ^ 2 + 4 * (ℓ ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2)
            * (Work.OneBodyKin.profHat p) ^ 2)
          = fun p : ℝ³ => (4 * ‖q‖ ^ 2 + 2 * c ^ 2) * (Work.OneBodyKin.profHat p) ^ 2
              + (4 * (ℓ ^ 2)⁻¹) * (‖p‖ ^ 2 * (Work.OneBodyKin.profHat p) ^ 2) := by
        funext p; ring
      rw [hcongr, integral_add (hI0int.const_mul _) (hI1int.const_mul _),
        integral_const_mul, integral_const_mul, ← hI0def, ← hI1def]
    calc |Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q|
        ≤ ((2 * Real.pi) ^ 3)⁻¹
            * ((4 * ‖q‖ ^ 2 + 2 * c ^ 2) * I0 + 4 * (ℓ ^ 2)⁻¹ * I1) := by
          rw [← hsplit]; exact hmain
      _ = ((2 * Real.pi) ^ 3)⁻¹ * (4 * I0) * ‖q‖ ^ 2
            + ((2 * Real.pi) ^ 3)⁻¹ * (2 * c ^ 2 * I0 + 4 * (ℓ ^ 2)⁻¹ * I1) := by ring

end

end Work.BoseFixB1
