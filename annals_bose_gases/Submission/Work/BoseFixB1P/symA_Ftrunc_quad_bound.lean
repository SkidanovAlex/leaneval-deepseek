import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.TruncDefs
import Submission.Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1P.symA_Ftrunc_quad_bound` — quadratic growth of the truncated symbol

The unprojected family symbol with the truncated FS cut-off `Ftrunc c n` grows at most
quadratically in the momentum, *uniformly in the truncation parameter* `n`:

    `|symA ℓ (Ftrunc c n) q| ≤ A ‖q‖² + B`

with `A, B ≥ 0` depending on `ℓ` and `c` only.  This is the `symA`-half of the uniform
domination of the projected family-form symbol `famSym ℓ (Ftrunc c n)` used in the
dominated-convergence arguments of this chapter.

## The proof

Recall (`Work.OneBodyKin.Defs`)

    `symA ℓ F q = (2π)⁻³ ∫_p F‖q + ℓ⁻¹ • p‖ · profHat(p)² dp`.

* **Integrability of the two moments.**  `p ↦ profHat(p)² ‖p‖^k` is integrable for `k ≤ 2`
  (`Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow`, which squares the decay
  `|profHat p| ≤ C(1+‖p‖)^{-6}` of `Work.OneBodyKin.ProfHatDecay` and invokes
  `integrable_one_add_norm`).  Hence `I₀ = ∫ profHat²` and `I₁ = ∫ ‖p‖² profHat²` are finite
  and nonnegative.
* **Pointwise bound.**  `Ftrunc c n r ≤ [r−c]₊² ≤ 2r² + 2c²` and, with `r = ‖q + ℓ⁻¹•p‖`,
  `r² ≤ 2‖q‖² + 2ℓ⁻²‖p‖²`; so the integrand of `symA ℓ (Ftrunc c n) q` is dominated by
  `(4‖q‖² + 4ℓ⁻²‖p‖² + 2c²)·profHat(p)²`, a function integrable in `p` and *independent of `n`*.
* **Assembly.**  `‖∫‖ ≤ ∫‖·‖` and the two elementary integrals
  `∫ (4‖q‖² + 4ℓ⁻²‖p‖² + 2c²) profHat² = (4‖q‖² + 2c²) I₀ + 4ℓ⁻² I₁` give the claim with
  `A = (2π)⁻³·4 I₀` and `B = (2π)⁻³·(2c² I₀ + 4ℓ⁻² I₁)`, both nonnegative.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1P

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Integrability of the two moments of the bump profile -/

/-- `p ↦ profHat(p)²` is integrable.  This is the `k = 0` case of
`Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow`. -/
private lemma integrable_profHat_sq :
    MeasureTheory.Integrable (fun p : ℝ³ => (Work.OneBodyKin.profHat p) ^ 2) := by
  simpa using Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow 0 (by norm_num)

/-- `p ↦ ‖p‖² profHat(p)²` is integrable.  This is the `k = 2` case of
`Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow` (with the factors commuted). -/
private lemma integrable_normSq_profHat_sq :
    MeasureTheory.Integrable (fun p : ℝ³ => ‖p‖ ^ 2 * (Work.OneBodyKin.profHat p) ^ 2) := by
  refine (Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow 2 (by norm_num)).congr ?_
  filter_upwards with p
  ring

/-! ## 2. The pointwise domination of the integrand -/

/-- The truncated FS cut-off evaluated at the shifted momentum `‖q + ℓ⁻¹ • p‖` costs at most
`4‖q‖² + 4ℓ⁻²‖p‖² + 2c²`: `Ftrunc c n r ≤ [r−c]₊² ≤ (r−c)² ≤ 2r² + 2c²` and
`r² = ‖q + ℓ⁻¹•p‖² ≤ 2‖q‖² + 2ℓ⁻²‖p‖²`. -/
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

/-! ## 3. The bound -/

/-- Uniform-in-the-truncation quadratic growth of the unprojected family symbol:
`|symA ℓ (Ftrunc c n) q| ≤ A ‖q‖² + B` for all `n, q`, with `A, B ≥ 0` depending only on `ℓ, c`.
Since `Ftrunc c n ≤ fsKinCoeff c ≤ (1+|c|)²(1+·)²`, the intended constants are
`A = (2π)⁻³ · 4 · I₀` and `B = (2π)⁻³ · (4 ℓ⁻² I₁ + 2 c² I₀)` where
`I₀ = ∫_p profHat(p)²` and `I₁ = ∫_p ‖p‖² profHat(p)²`, both finite by the `(1+‖p‖)⁻⁶` decay of
`Work.OneBodyKin.ProfHatDecay` (whence `(1+‖p‖)² profHat(p)² ≤ C²(1+‖p‖)⁻¹⁰`, integrable in
dimension 3).  NOTE for the prover: `Submission/Work/OneBodyKin/symA_Ftrunc_bound.lean` and
`Submission/Work/BoseFixB1/symA_Ftrunc_quad_bound.lean` currently do NOT compile, so do not import
them -- prove this from scratch (`Work.OneBodyKin.ProfHatDecay`, `integrable_one_add_norm`,
`MeasureTheory.Integrable.mono'`, `norm_add_le`/`norm_smul`). -/
theorem symA_Ftrunc_quad_bound {ℓ c : ℝ} (hℓ : 0 < ℓ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (n : ℕ) (q : EuclideanSpace ℝ (Fin 3)),
      |Work.OneBodyKin.symA ℓ (Work.OneBodyKin.Ftrunc c n) q| ≤ A * ‖q‖ ^ 2 + B := by
  have hI0int : MeasureTheory.Integrable
      (fun p : ℝ³ => (Work.OneBodyKin.profHat p) ^ 2) := integrable_profHat_sq
  have hI1int : MeasureTheory.Integrable
      (fun p : ℝ³ => ‖p‖ ^ 2 * (Work.OneBodyKin.profHat p) ^ 2) :=
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
    have hgint : MeasureTheory.Integrable (fun p : ℝ³ =>
        (4 * ‖q‖ ^ 2 + 4 * (ℓ ^ 2)⁻¹ * ‖p‖ ^ 2 + 2 * c ^ 2)
          * (Work.OneBodyKin.profHat p) ^ 2) := by
      have h1 : MeasureTheory.Integrable (fun p : ℝ³ =>
          (4 * ‖q‖ ^ 2 + 2 * c ^ 2) * (Work.OneBodyKin.profHat p) ^ 2) :=
        hI0int.const_mul _
      have h2 : MeasureTheory.Integrable (fun p : ℝ³ =>
          (4 * (ℓ ^ 2)⁻¹) * (‖p‖ ^ 2 * (Work.OneBodyKin.profHat p) ^ 2)) :=
        hI1int.const_mul _
      refine (h1.add h2).congr ?_
      filter_upwards with p
      simp only [Pi.add_apply]
      ring
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

end Work.BoseFixB1P
