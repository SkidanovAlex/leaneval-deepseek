import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.AprioriPieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.Local` — the vocabulary of the per-box integrated bound

This module (sorry-free) fixes the objects of `Work.BoseFixB1B.perBoxIntegratedPos` in a
readable form, so that

* the **per-box** analytic input (`Work.BoseFixB1B.PerBoxSmooth`) can be stated and dispatched
  without naming the frozen vocabulary at every turn, and
* the **assembly** (`∫_{I₋}` of the per-box bound, constants, error budget) can be written
  against the definitions below.

## What the target says

`Work.BoseFixB1B.perBoxIntegratedPos` is FS `thm:smallbox` (`final_v2.tex` l. 3907) *integrated
over the sliding interior* `I₋` (FS `final_v2.tex` l. 4120), in the frozen vocabulary of
`Submission/Work/BoseBoxFix/Defs.lean`:

    c₁·R_Ψ ≤ ∫_{I₋} H_{B(u)}(Φ) du + ½μ²(∫_{I₋}∬w_{1,B(u)})‖Φ‖² + C·μ²(a v)ℓ³K_B³(μ(a v)³)^{1/2}·‖Φ‖²

for every admissible `μ` and every low box state (`IsLowB`, `0 < normB`).

* `R_Ψ = ∫_{I₋} w1MassB(u)·∫_{abox n ℓ}Φ²·F(n_B(u)/|B(u)|)` with `F = psiWeight 1 μ` and the
  smooth local density `n_B(u) = nCountB u` normalised by the cutoff mass `chiMass u` — that is
  *definitionally* the `I₋`-integral of `fWeight` below (`rPsi_eq_integral_fWeight`).
* `∫_{I₋}H_{B(u)}(Φ) = ∫_{I₋} sbWord h μ u Φ` where `sbWord = tBwordBInd + qLHSwordB`
  (FS `eq:appTB` + `eq:HBU` at the localised kernels).

## The route, and the one open ingredient

The proof is FS's: **Piece 1** (`PerBoxSmooth`, FS `thm:smallbox` at the single box `B(u)`) plus
**Piece 2** (the `u`-bookkeeping: the mass normalisation `∫_u chiMass = ℓ³`
(`Work.SmallBoxSliding.integral_chiMass_eq`, proved), the measure of `I₋`, the FS parameter
regime `(R/(dℓ))² ≤ K_B³(μ(a v)³)^{1/2}`, integrability).  Piece 1 is the hard analytic input
(it contains the potential-side `A₀`/mean-field estimate at the localised kernels together with
the count ↔ density passage); it is dispatched as `Work.BoseFixB1B.PerBoxSmooth`.

The elementary half of the `F`-weight bookkeeping — FS's `F(t) ≤ μ(t+μ)`, `F(t) ≤ (t−μ)²`,
`F`` ≤ 8`, and the cut-off comparison `F(t) ≤ (8C+8)(F(s)+μ²)` for `t ≤ Cs` — is proved here.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The elementary `F`-weight bounds -/

/-- FS's weight is `F(t) = μ(t−μ)²/(t+μ)`. -/
lemma psiWeight_eq {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t = μ * (t - μ) ^ 2 / (t + μ) := by
  rw [Work.SmallBoxSliding.psiWeight, show (1 : ℝ) + t * μ⁻¹ = (t + μ) / μ by
    field_simp
    ring]
  rw [div_div_eq_mul_div]
  ring

/-- `F(t) ≤ μ (t + μ)`. -/
lemma psiWeight_le_mu_add {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ * (t + μ) := by
  rw [psiWeight_eq hμ ht]
  have hden : 0 < t + μ := by linarith
  have hsq : (t - μ) ^ 2 ≤ (t + μ) ^ 2 := by nlinarith [hμ, ht]
  calc μ * (t - μ) ^ 2 / (t + μ) ≤ μ * (t + μ) ^ 2 / (t + μ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (le_of_lt hμ)) (le_of_lt hden)
    _ = μ * (t + μ) := by field_simp

/-- `0 ≤ F(t)`. -/
lemma psiWeight_nonneg {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    0 ≤ Work.SmallBoxSliding.psiWeight 1 μ t := by
  rw [Work.SmallBoxSliding.psiWeight]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  exact div_nonneg (mul_nonneg zero_le_one (sq_nonneg _)) (le_of_lt hden)

/-- `F(t) ≤ (t − μ)²`. -/
lemma psiWeight_le_sq_sub {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ (t - μ) ^ 2 := by
  rw [Work.SmallBoxSliding.psiWeight]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [div_le_iff₀ hden]
  have hone : (1 : ℝ) ≤ 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  calc (1 : ℝ) * (t - μ) ^ 2 = (t - μ) ^ 2 := by ring
    _ ≤ (t - μ) ^ 2 * (1 + t * μ⁻¹) := le_mul_of_one_le_right (sq_nonneg _) hone

/-- **The convexity-and-growth lower bound**: `μ s/8 ≤ F(s)` once `2μ ≤ s`.  This is the
`F`` -type control (indeed `F`` = 8μ³/(t+μ)³ ≤ 8` and `F` is convex with minimum `0` at `t = μ`)
used to pass from a *small* density bound to a *large* one. -/
lemma psiWeight_lb {μ s : ℝ} (hμ : 0 < μ) (hs : 2 * μ ≤ s) :
    μ * s / 8 ≤ Work.SmallBoxSliding.psiWeight 1 μ s := by
  have hs0 : 0 < s := by linarith
  rw [psiWeight_eq hμ (le_of_lt hs0)]
  have hden : 0 < s + μ := by linarith
  rw [le_div_iff₀ hden]
  have hkey : 0 ≤ 7 * s ^ 2 - 17 * s * μ + 8 * μ ^ 2 := by
    have h1 : 0 ≤ (s - 2 * μ) * (7 * s - 3 * μ) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h1]
  nlinarith [hkey]

/-- **The cut-off comparison of the `F`-weights**: if `0 ≤ t ≤ C s` then
`F(t) ≤ (8C+8)(F(s) + μ²)`.  This is what lets a count-indexed bound be compared with the smooth
(local-density) `F`-weight of `R_Ψ`, and is the only real-analysis input of the count ↔ density
passage in the form used here. -/
lemma psiWeight_le_mul_add {μ t s C : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hC : 0 ≤ C) (hts : t ≤ C * s) :
    Work.SmallBoxSliding.psiWeight 1 μ t
      ≤ (8 * C + 8) * (Work.SmallBoxSliding.psiWeight 1 μ s + μ ^ 2) := by
  have hFs : 0 ≤ Work.SmallBoxSliding.psiWeight 1 μ s := psiWeight_nonneg hμ hs
  have hlin := psiWeight_le_mu_add (μ := μ) (t := t) hμ ht
  by_cases hs2 : s ≤ 2 * μ
  · have h1 : Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ * (C * (2 * μ) + μ) := by
      refine le_trans hlin ?_
      have : t ≤ C * (2 * μ) := by nlinarith
      exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hμ)
    have h2 : μ * (C * (2 * μ) + μ) = μ ^ 2 * (2 * C + 1) := by ring
    rw [h2] at h1
    nlinarith [h1, hFs, sq_nonneg μ, hC, hμ]
  · have hs2' : 2 * μ < s := not_le.mp hs2
    have hμs8 : μ * s ≤ 8 * Work.SmallBoxSliding.psiWeight 1 μ s := by
      have := psiWeight_lb hμ (le_of_lt hs2')
      linarith
    have hμ2 : μ ^ 2 ≤ 4 * Work.SmallBoxSliding.psiWeight 1 μ s := by
      nlinarith [hμs8, hμ, le_of_lt hs2']
    have ht' : Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ * (C * s + μ) := by
      refine le_trans hlin ?_
      exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hμ)
    have step : μ * (C * s + μ)
        ≤ (8 * C + 8) * (Work.SmallBoxSliding.psiWeight 1 μ s + μ ^ 2) := by
      nlinarith [hμs8, hμ2, hC, hFs]
    linarith [ht', step]

/-! ## 2. The objects of the target -/

/-- The per-`u` `F`-weight of FS's `R_Ψ` in the frozen vocabulary:
`w1MassB(u) · ∫_{abox n ℓ} Φ² F(n_B(u)/|B(u)|)`. -/
def fWeight (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u *
    (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (Work.BoseFixB1.nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x /
          Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u))

/-- FS's per-box error shape at `u`
(`μ²(a v)((R/(dℓ))² + K_B³(μ(a v)³)^{1/2})∫χ_{B(u)}² + μ(a v)`). -/
def boxErrShape (v : EuclideanSpace ℝ (Fin 3) → ℝ) (_h : Work.UBB.ScatSol v) (R μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  μ ^ 2 * (_root_.BoseGases.a v) *
      ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) *
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
        + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
      * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
    + μ * (_root_.BoseGases.a v)

/-- `R_Ψ` **is** the `I₋`-integral of the per-`u` weight (definitional). -/
lemma rPsi_eq_integral_fWeight (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (μ : ℝ) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) :
    Work.BoseFixB1.RPsi v h μ Φ
      = ∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ, fWeight v h μ Φ u := rfl

/-- **Piece 1** (FS `thm:smallbox`, `final_v2.tex` l. 3907, at the sliding box `B(u)`, in the
state-level smooth-count form): there are `ε₀ > 0`, `c₁ > 0`, `C ≥ 0` such that for every
admissible `μ`, every low box state and every `u ∈ I₋`, the localised word `sbWord h μ u Φ`
plus the background `½μ²(∬w_{1,B(u)})‖Φ‖²` dominates `c₁·fWeight`, up to FS's per-box error
`C·boxErrShape`.  This is the analytic heart of the chapter (the potential-side `A₀`/mean-field
estimate at the localised kernels plus the count ↔ density passage); it is strictly stronger than
`perBoxIntegratedPos`, which is its `I₋`-integral. -/
def PerBoxSmooth (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (R J : ℝ) : Prop :=
  ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → 0 < μ → ∀ (n : ℕ)
      (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ u ∈ Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
          c₁ * fWeight v h μ (Φ : Submission.BoseGases.X n → ℝ) u
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
              + (1 / 2) * μ ^ 2 *
                  (Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              + C * boxErrShape v h R μ u
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)

end Work.BoseFixB1B
