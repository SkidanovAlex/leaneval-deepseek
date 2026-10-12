import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.q0word_localised_value` — the exact localised `Q₀`-word value

FS's potential splitting (`eq:potsplit`) writes the localised potential word as
`qLHSword = q0word + q1word + q2word + q3word + q4word`; the `A₀` (mean-field) analysis then
needs the **exact value of the condensate piece** `q0word` at the localised kernels
`w₁ = wSmall1Pair h M ℓ d u`, `w₂ = wSmallPair M ℓ d u (g₂ v h)` of the sliding box `B(u)`.

For *any* kernels integrable on `acube ℓ ×ˢ acube ℓ` (in particular for the localised ones,
which are only a.e.-measurable), the value is

    q0word ℓ μ w₁ w₂ Φ
      = ½·(ℓ³)⁻²·(∬ w₂)·cS2 ℓ Φ − μ·(ℓ³)⁻¹·(∬ w₁)·cS1 ℓ Φ ,

i.e. the condensate pair term is the *pair mass* `∬w₂` times the pair-condensate count `cS2`,
divided by the box volume squared, and the one-body term is `μ` times the *one-body mass*
`∬w₁` times `cS1` divided by the box volume.

**This is the statement to use in the localised `A₀` chain.**  Note what it does *not* need:
no lower bound on the masses.  The apparent need for "`∬w_{1,B(u)} ≥ c·(a v)·χMass`" (a per-`u`
mass lower bound) is a *dead end*: that statement is **false** on the band/corner
configurations of `goodSet`, where `χ_{B(u)}` is supported in a cap/sliver of the ball on which
`chiScale ℓ` lives and the ratio `∬w_{1,B(u)}/chiMass` degenerates (see
`FINDING_perBoxF_ledger.md` §1a).  Here the masses appear as *coefficients on both sides* of
FS's balance, so their *exact* values suffice, and the free error bracket of the per-box
statement absorbs the band (where both the masses and `χMass` degenerate).

The proof is the instantiation of the corpus's kernel-parametric identity
`Submission.BoseGases.q0_expect_ae` (in `Submission/AeValue.lean`), which is stated for
*arbitrary* kernels integrable on the box product — exactly the localised setting.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The exact localised `Q₀`-word value** (FS `eq:DefQ0` at the sliding box kernels):
`q0word ℓ μ w₁ w₂ Φ = ½(ℓ³)⁻²(∬w₂)·cS2 ℓ Φ − μ(ℓ³)⁻¹(∬w₁)·cS1 ℓ Φ`.

No regime hypotheses are needed: the identity is the kernel-parametric
`Submission.BoseGases.q0_expect_ae`, instantiated at the localised kernels. -/
theorem q0word_localised_value {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hw1i : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) MeasureTheory.volume)
    (hw2i : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) MeasureTheory.volume) :
    Submission.BoseGases.q0word (N := N) ℓ μ (Submission.BoseGases.wSmall1Pair h M ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ
      = (1 / 2) * (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹
          * (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
          * Submission.BoseGases.cS2 ℓ Φ
        - μ * (ℓ ^ 3)⁻¹
          * (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
          * Submission.BoseGases.cS1 ℓ Φ := by
  have hmain := Submission.BoseGases.q0_expect_ae (N := N) hℓ μ (Φ := Φ) hΦc hw1i hw2i
  simpa only [Submission.BoseGases.q0word, Submission.BoseGases.w1Fibre,
    Submission.BoseGases.cS1, Submission.BoseGases.cS2] using hmain

/-- **The lower-bound form consumed by the `A₀` algebra.**  Replacing the pair mass by *any*
lower bound `Wb` and the one-body mass by *any* upper bound `Wa` — the two directions in which
`q0word` is monotone — leaves the exact value from below.

This is stated with the two mass bounds as explicit hypotheses precisely because they fail on
the band: it is the *interior* statement, and the band is handled by the error bracket of the
per-box inequality. -/
theorem q0word_localised_lower {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hw1i : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) MeasureTheory.volume)
    (hw2i : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) MeasureTheory.volume)
    {Wa Wb : ℝ}
    (hmass_lo : Wb ≤ ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
    (hmass_up : (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2) ≤ Wa)
    (hμ : 0 ≤ μ) :
    (1 / 2) * (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * Wb * Submission.BoseGases.cS2 ℓ Φ
        - μ * (ℓ ^ 3)⁻¹ * Wa * Submission.BoseGases.cS1 ℓ Φ
      ≤ Submission.BoseGases.q0word (N := N) ℓ μ (Submission.BoseGases.wSmall1Pair h M ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) Φ := by
  have hℓ3 : (0 : ℝ) < ℓ ^ 3 := by positivity
  have hinv : 0 ≤ (ℓ ^ 3)⁻¹ := inv_nonneg.mpr hℓ3.le
  have hcS1 : 0 ≤ Submission.BoseGases.cS1 ℓ Φ := by
    simp only [Submission.BoseGases.cS1]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hcS2 : 0 ≤ Submission.BoseGases.cS2 ℓ Φ := by
    simp only [Submission.BoseGases.cS2]
    exact Finset.sum_nonneg fun p _ => integral_nonneg fun x => sq_nonneg _
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ :=
    mul_nonneg (mul_nonneg (by norm_num) hinv) hinv
  have hpair : (1 / 2) * (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ * Wb * Submission.BoseGases.cS2 ℓ Φ
      ≤ (1 / 2) * (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹
          * (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2)
          * Submission.BoseGases.cS2 ℓ Φ := by
    refine le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass_lo hcoef) hcS2) (le_of_eq ?_)
    ring
  have hone : μ * (ℓ ^ 3)⁻¹ * (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2) * Submission.BoseGases.cS1 ℓ Φ
      ≤ μ * (ℓ ^ 3)⁻¹ * Wa * Submission.BoseGases.cS1 ℓ Φ := by
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass_up (mul_nonneg hμ hinv)) hcS1)
    ring
  linarith [hpair, hone, q0word_localised_value (v := v) (M := M) (ℓ := ℓ) (d := d)
    (μ := μ) (N := N) (Φ := Φ) h hℓ u hΦc hw1i hw2i]

end Work.BoseFixB1
