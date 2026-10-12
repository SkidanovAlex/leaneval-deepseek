import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.weightedYoungB1` — the weighted Young (AM–GM) engine of the crux

FS `lm:appinteractionestimate` completes the square with the *operator* weights
`(n₀+1)^{1/2} ± (μ|B|)^{1/2}`; the one step of that chain which is elementary — and which
`Submission/Work/BoseFixB1S/NOTES_crux_FScompletion.md` §1 cites as "Cauchy–Schwarz in the
`W`-form + AM–GM" — is

    ∀ lam > 0, 2⟨u, W v⟩ ≥ −lam⟨u, W u⟩ − lam⁻¹⟨v, W v⟩          (W ≥ 0 self-adjoint)

whose proof is `⟨(√lam u + v/√lam), W (√lam u + v/√lam)⟩ ≥ 0`.  This module machine-checks that step in
the corpus's *integral* vocabulary, in the square-root-free form `0 ≤ ∫ W(lamu+v)²`
(multiply by `lam > 0` at the end).

**What this does and does not do.**  Having this lemma machine-checked, the *entire* remaining
content of the completion of squares is the identification of the two weights with
`Θ₊ = (√(n₀+1) + √c)²` and `Θ₋ = (√(n₀+1) − √c)²` (`c = μV`), i.e. the spectral decomposition of
`n₀ = ΣᵢP_{B,i}` (a finite sum of commuting orthogonal projections, so `g(n₀) = Σ_k g(k)Π_k` with
the Lagrange idempotents `Π_k`) together with the two hard estimates `(FS-P)` and `(CREDIT)` of
that note.  This lemma isolates the *elementary* half; nothing here touches the `√`.

`sorry`-free; `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

/-- Linearity of the box integral for two functions written with explicit applications. -/
private lemma integral_add_lambda' {N : ℕ} {ℓ : ℝ} {f g : X N → ℝ}
    (hf : IntegrableOn f (abox N ℓ) volume) (hg : IntegrableOn g (abox N ℓ) volume) :
    (∫ x in abox N ℓ, f x + g x) = (∫ x in abox N ℓ, f x) + (∫ x in abox N ℓ, g x) :=
  MeasureTheory.integral_add hf hg

/-- **Weighted Young / AM–GM inequality.**  For a nonnegative weight `W` and `lam > 0`,

    `2·∫ W·u·v ≥ −(lam·∫ W·u² + lam⁻¹·∫ W·v²)`  on `abox N ℓ`,

because `0 ≤ ∫ W(lamu + v)² = lam²∫Wu² + 2lam∫Wuv + ∫Wv²` and `lam⁻¹ > 0`.  This is the elementary step
of the completion of squares in FS `lm:appinteractionestimate`; see the module docstring. -/
theorem weighted_amgm_integral {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W u v : X N → ℝ} (hW : ∀ x, 0 ≤ W x) {lam : ℝ} (hlam : 0 < lam)
    (hWu2 : IntegrableOn (fun x : X N => W x * (u x) ^ 2) (abox N ℓ) volume)
    (hWv2 : IntegrableOn (fun x : X N => W x * (v x) ^ 2) (abox N ℓ) volume)
    (hWuv : IntegrableOn (fun x : X N => W x * (u x * v x)) (abox N ℓ) volume) :
    -(lam * (∫ x in abox N ℓ, W x * (u x) ^ 2)
        + lam⁻¹ * (∫ x in abox N ℓ, W x * (v x) ^ 2))
      ≤ 2 * (∫ x in abox N ℓ, W x * (u x * v x)) := by
  -- the manifest square is nonnegative after integration
  have hsq : (0 : ℝ) ≤ ∫ x in abox N ℓ, W x * (lam * u x + v x) ^ 2 :=
    integral_nonneg fun x => mul_nonneg (hW x) (sq_nonneg _)
  -- its expansion
  have hI1 : IntegrableOn (fun x : X N => lam ^ 2 * (W x * (u x) ^ 2)) (abox N ℓ) volume :=
    hWu2.const_mul (lam ^ 2)
  have hI2 : IntegrableOn (fun x : X N => (2 * lam) * (W x * (u x * v x))) (abox N ℓ) volume :=
    hWuv.const_mul (2 * lam)
  have hexp : (∫ x in abox N ℓ, W x * (lam * u x + v x) ^ 2)
      = lam ^ 2 * (∫ x in abox N ℓ, W x * (u x) ^ 2)
        + (2 * lam) * (∫ x in abox N ℓ, W x * (u x * v x))
        + (∫ x in abox N ℓ, W x * (v x) ^ 2) := by
    calc (∫ x in abox N ℓ, W x * (lam * u x + v x) ^ 2)
        = ∫ x in abox N ℓ, lam ^ 2 * (W x * (u x) ^ 2)
            + (2 * lam) * (W x * (u x * v x)) + W x * (v x) ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
      _ = (∫ x in abox N ℓ, (lam ^ 2 * (W x * (u x) ^ 2)
              + (2 * lam) * (W x * (u x * v x))))
            + (∫ x in abox N ℓ, W x * (v x) ^ 2) :=
          integral_add_lambda' (hI1.add hI2) hWv2
      _ = (lam ^ 2 * (∫ x in abox N ℓ, W x * (u x) ^ 2)
              + (2 * lam) * (∫ x in abox N ℓ, W x * (u x * v x)))
            + (∫ x in abox N ℓ, W x * (v x) ^ 2) := by
          rw [integral_add_lambda' hI1 hI2, MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]
      _ = lam ^ 2 * (∫ x in abox N ℓ, W x * (u x) ^ 2)
            + (2 * lam) * (∫ x in abox N ℓ, W x * (u x * v x))
            + (∫ x in abox N ℓ, W x * (v x) ^ 2) := by ring
  -- multiply by `lam⁻¹ > 0`
  have hkey : 0 ≤ lam⁻¹ * (∫ x in abox N ℓ, W x * (lam * u x + v x) ^ 2) :=
    mul_nonneg (le_of_lt (inv_pos.mpr hlam)) hsq
  have hmain : 0 ≤ lam * (∫ x in abox N ℓ, W x * (u x) ^ 2)
      + 2 * (∫ x in abox N ℓ, W x * (u x * v x))
      + lam⁻¹ * (∫ x in abox N ℓ, W x * (v x) ^ 2) := by
    have hrew : lam⁻¹ * (∫ x in abox N ℓ, W x * (lam * u x + v x) ^ 2)
        = lam * (∫ x in abox N ℓ, W x * (u x) ^ 2)
          + 2 * (∫ x in abox N ℓ, W x * (u x * v x))
          + lam⁻¹ * (∫ x in abox N ℓ, W x * (v x) ^ 2) := by
      rw [hexp]
      field_simp
    rw [hrew] at hkey
    exact hkey
  linarith [hmain]

end Work.BoseFixB1S
