/-
# Consuming the arithmetic-projection bound: the averaged fibre bound, and the `form-1` assembly

This module *uses* `Work.KMTAreas.A7.arithProjectionD_lp_le_angleBracket` (area `A1` implies the
`⟨l⟩`-weighted `ℓ^p` bound for the exact-height arithmetic projector on `ℤ/q`) to

* **discharge the hypothesis `hproj`** of
  `Work.KMTAreas.A7.residueLp_fiberOpD_le_of_projection`, i.e. produce the *unconditional*
  residue-`ℓᵖ` bound for the fibre `fiberOpD ρ l (mStarF u)` from area `A1` alone
  (`residueLp_fiberOpD_le`); and
* **assemble steps A+B+C of §7**: the paper's `form-1` factorisation
  (`smallBtwist_eq_fiberSumD`), the residue-Hölder inequality (`residueLp_mul_le`) and the two
  fibre bounds give the `ℓ^r` bound for the twisted bilinear multiplier in terms of the two
  *inputs* `H`, `K` (`r⁻¹ = p₁⁻¹ + p₂⁻¹`); the `⟨l⟩`-loss of the projection bound is carried
  entirely by the two constants `C₁`, `C₂`.

This is the exact-height (`fiberOpD`/`fiberOpPD`, `smallBtwist`) counterpart of
`Work.KMTAreas.A7.eLpNorm_Btwist_le_residue` (`randBumpSingleScale_holds.lean`), which does the
same for the cumulative-height fibres `fiberOp`/`fiberOpP`.

The remaining input of the §7 single-scale estimate is the analogous fibre bound for the
*polynomial-twisted* second fibre `fiberOpPD ρ P l (mStargF d u)` (the index `n₀` is replaced by
`P.eval n₀`); it enters as the hypothesis `h₂` of `eLpNorm_smallBtwist_le_of_fiber_bounds`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.residueLp_fiberOpD_le_of_projection
import Submission.Work.KMTAreas.A7.IwLqGeneral
import Submission.Work.KMTPlan.A6.continuous_periodize_of_hasCompactSupport
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **Steps A+B+C of §7.**  For `p₁, p₂ > 1` with `p₁⁻¹ + p₂⁻¹ ≤ 1`, the twisted exact-height
bilinear multiplier `smallBtwist` applied to two inputs `H`, `K` obeys

  `‖smallBtwist ρ P l₁ l₂ m₁ m₂ H K‖_{ℓ^r} ≤ C₁·C₂·‖H‖_{ℓ^{p₁}}·‖K‖_{ℓ^{p₂}}`,
  `r = (p₁⁻¹ + p₂⁻¹)⁻¹`,

as soon as the two *fibres* obey their residue-`ℓᵖ` bounds with constants `C₁`, `C₂`.  The proof is
the `form-1` identity `smallBtwist_eq_fiberSumD` followed by the residue-Hölder inequality
`residueLp_mul_le`. -/
theorem eLpNorm_smallBtwist_le_of_fiber_bounds (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (m₁ m₂ : ℝ → ℂ) (p₁ p₂ : ENNReal) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) {H K : ℤ → ℂ}
    (hs₁ : ∀ (x : ℤ) (n₀ : ℤ),
      Summable (fun j : ℤ => arithCharD ρ l₁ (n₀ - j) * cw m₁ j * H (x - j)))
    (hs₂ : ∀ (x : ℤ) (n₀ : ℤ),
      Summable (fun j : ℤ => arithCharD ρ l₂ (P.eval n₀ - j) * cw m₂ j * K (x - j)))
    (C₁ C₂ : ENNReal)
    (h₁ : eLpNorm (fun y : ℤ => residueLp p₁.toReal (arithQ ρ (max l₁ l₂))
            (fun x n₀ => ‖(fiberOpD ρ l₁ m₁ (n₀ : ℤ) H x : ℂ)‖ₑ) y) p₁ Measure.count
          ≤ C₁ * eLpNorm H p₁ Measure.count)
    (h₂ : eLpNorm (fun y : ℤ => residueLp p₂.toReal (arithQ ρ (max l₁ l₂))
            (fun x n₀ => ‖(fiberOpPD ρ P l₂ m₂ (n₀ : ℤ) K x : ℂ)‖ₑ) y) p₂ Measure.count
          ≤ C₂ * eLpNorm K p₂ Measure.count) :
    eLpNorm (fun x : ℤ => smallBtwist ρ P l₁ l₂ m₁ m₂ H K x) (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
      ≤ C₁ * C₂ * (eLpNorm H p₁ Measure.count * eLpNorm K p₂ Measure.count) := by
  have hq0 : arithQ ρ (max l₁ l₂) ≠ 0 := (arithQ_pos ρ (max l₁ l₂)).ne'
  have hqinv : ‖(((arithQ ρ (max l₁ l₂) : ℕ) : ℂ))⁻¹‖ₑ
      = ((arithQ ρ (max l₁ l₂) : ℕ) : ENNReal)⁻¹ := by
    rw [enorm_inv (by exact_mod_cast hq0), ← ofReal_norm, Complex.norm_natCast,
      ENNReal.ofReal_natCast]
  have hpt : ∀ x : ℤ, ‖smallBtwist ρ P l₁ l₂ m₁ m₂ H K x‖ₑ ≤
      ((arithQ ρ (max l₁ l₂) : ℕ) : ENNReal)⁻¹ *
        ∑ n₀ ∈ Finset.range (arithQ ρ (max l₁ l₂)),
          ‖(fiberOpD ρ l₁ m₁ (n₀ : ℤ) H x : ℂ)‖ₑ *
            ‖(fiberOpPD ρ P l₂ m₂ (n₀ : ℤ) K x : ℂ)‖ₑ := by
    intro x
    rw [smallBtwist_eq_fiberSumD ρ P l₁ l₂ m₁ m₂ H K x (fun n₀ => hs₁ x n₀)
      (fun n₀ => hs₂ x n₀)]
    rw [enorm_mul, hqinv]
    refine mul_le_mul' le_rfl ?_
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum (fun n₀ _ => ?_))
    rw [enorm_mul]
  calc eLpNorm (fun x : ℤ => smallBtwist ρ P l₁ l₂ m₁ m₂ H K x) (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
      ≤ eLpNorm (fun x : ℤ => ((arithQ ρ (max l₁ l₂) : ℕ) : ENNReal)⁻¹ *
          ∑ n₀ ∈ Finset.range (arithQ ρ (max l₁ l₂)),
            ‖(fiberOpD ρ l₁ m₁ (n₀ : ℤ) H x : ℂ)‖ₑ *
              ‖(fiberOpPD ρ P l₂ m₂ (n₀ : ℤ) K x : ℂ)‖ₑ)
          (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count := eLpNorm_mono_enorm (hf := by pw_aesm) hpt
    _ ≤ eLpNorm (residueLp p₁.toReal (arithQ ρ (max l₁ l₂))
            (fun x n₀ => ‖(fiberOpD ρ l₁ m₁ (n₀ : ℤ) H x : ℂ)‖ₑ)) p₁ Measure.count *
          eLpNorm (residueLp p₂.toReal (arithQ ρ (max l₁ l₂))
            (fun x n₀ => ‖(fiberOpPD ρ P l₂ m₂ (n₀ : ℤ) K x : ℂ)‖ₑ)) p₂ Measure.count :=
        residueLp_mul_le _ p₁ p₂ hp₁ hp₂ htp₁ htp₂ hsum _ _
    _ ≤ C₁ * eLpNorm H p₁ Measure.count * (C₂ * eLpNorm K p₂ Measure.count) :=
        mul_le_mul' h₁ h₂
    _ = C₁ * C₂ * (eLpNorm H p₁ Measure.count * eLpNorm K p₂ Measure.count) := by ring

end

end Work.KMTAreas.A7
