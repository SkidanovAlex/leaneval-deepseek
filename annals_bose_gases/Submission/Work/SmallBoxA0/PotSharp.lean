import ChallengeDeps
import Submission.Work.A0Bridge
import Submission.Work.QMassUpper
import Submission.Work.Step4SqrtFactorisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fixed-`n` smallbox block bound — the SHARP potential-side chain
(Work.SmallBoxA0, step 2)

This module assembles the potential-side words of the fixed-`n` smallbox
bound (`SmallBoxBlockBound.smallbox_state_block_bound`) from the CLOSED exact
identities of the corpus:

* `A0Bridge.q0word_w2_mass_sub` — the exact `∬w₂`-form of the q0-word
  (`q0word = ½V⁻¹(8π(av)+D)·cS2 − 8π(av)μ·cS1`, `D := g0w0Mass`);
* `Q0Convex.cS2_ge_sq_sub_self` — `cS2 ≥ cS1² − cS1`;
* `SmallBoxQ0.cS1_eq_nat_sub_cnPlus` — `cS1 = N̂ − n₊`;
* `Q3Q4Peel.q1_q3_q4_mass` + `Q3Q4Peel.q1_w1line_scalar_split` +
  `Q3Q4Peel.q1_cross_w1_cs_fs` — the exact w₁-line, its scalar split and the
  FS-shape (¼-coefficient) per-slot AM–GM;
* `A0Bridge.q2word_a2_split` + `FSGroupQ2.q2_T1_abs_le` +
  `QMassUpper.q2PairWord_nonneg` + `Step4SqrtFactorisation.qOneMass_le_fsqC1_mul_cnPlus`
  — the q2-word split keeping the `A₂ = q4PairWord` (Bogolubov) pairing and
  bounding the `T₁/T₂/T₃` masses by `n₊`-terms.

The output (`pot_sharp_summary`) is the potential-side inequality

    qLHSword ≥ ¼(x−μ)²·8π(av)s³ − ½μ²·8π(av)s³ + ½s⁻³D·cS2 + q4PairWord
                 − K·(av)μ·n₊ − 4π(av)μ − 2s⁻³·Corr ,

with `K := potNCoeff μ (av) = 64π(av)μ + 36C₁μ + 9μ(6C₁+C₂) + μC₁` and `Corr`
the (exact) word of `q1_w1line_scalar_split` (this summary lives in
`Submission/Work/SmallBoxA0/pot_sharp_summary.lean`).  The three residues are
precisely the ones the last stages consume: `½ℓ⁻³D·cS2` cancels the Bogolubov
`−½D(N̂+1)²/ℓ³` of `SmallBoxD1Final.lm_appbogolubov_pWord_holds`,
`K·n₊` is absorbed by the kinetic gap `KineticBound.kinWord_gap_cnPlus`
(`Regime.kinWord_absorbs_potNCoeff`), and `Corr` needs the FS operator-`√`
factorisation of `(n₀/V − μ)` (the corpus's `q1_cross_w1_cs_fs` is the
SCALAR-`(x−μ)` version; see the area `README.md` for this recorded gap).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxA0

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **`0 ≤ g0w0Mass`** (de-circularised copy of
`SmallBoxBogMainTerm.g0w0Mass_nonneg`; this area must not import
`SmallBoxBogMainTerm`, which (transitively) imports `SmallBoxBlockBound`). -/
lemma g0w0Mass_nonneg {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    0 ≤ g0w0Mass (v := v) h := by
  have hb := (chosen_gomega_integral_bounds (v := v) (R := R) hR hv_nonneg hvrad hv_supp h).1
  dsimp [g0w0Mass, g0]
  exact hb

/-! ## The pure-real A₀ completion (q0-side) -/

/-- **Pure-real A₀ completion.**  With `V > 0`, `μ, k, P ≥ 0`, `S := N̂ − P`,
`x := N̂/V ≤ 9μ`, the q0-part `½V⁻¹k(S²−S) − kμS` is at least
`½kV(x−μ)² − ½μ²kV − 8μk·P − (9/2)kμ`:

    the `½kV(x−μ)²`-coefficient is what the FS-shape AM–GM
    (`q1_cross_w1_cs_fs`, which costs `¼kV(x−μ)²`) needs, the `−8μkP` is the
    `n₊`-price of replacing the condensate density `S/V` by `x`, and `−½kμ`
    is the `μ(av)`-error. -/
lemma q0_sharp_arith (V μ k N P : ℝ) (hV : 0 < V) (hμ : 0 ≤ μ) (hk : 0 ≤ k)
    (hP0 : 0 ≤ P) (hwin : N / V ≤ 9 * μ) :
    (1 / 2 : ℝ) * V⁻¹ * k * ((N - P) ^ 2 - (N - P)) - k * μ * (N - P)
      ≥ (1 / 2 : ℝ) * ((N / V) - μ) ^ 2 * (k * V) - (1 / 2 : ℝ) * μ ^ 2 * (k * V)
        - (8 * μ * k) * P - (9 / 2 : ℝ) * k * μ := by
  have hid : (1 / 2 : ℝ) * V⁻¹ * k * ((N - P) ^ 2 - (N - P)) - k * μ * (N - P)
        - ((1 / 2 : ℝ) * ((N / V) - μ) ^ 2 * (k * V) - (1 / 2 : ℝ) * μ ^ 2 * (k * V))
      = - k * P * (N / V - μ) + (1 / 2 : ℝ) * k * V * (P / V) ^ 2
        - (1 / 2 : ℝ) * k * (N / V - P / V) := by
    field_simp [ne_of_gt hV]
    ring
  have hq0 : 0 ≤ P / V := by positivity
  have hxm : N / V - μ ≤ 8 * μ := by linarith
  have h1 : k * P * (N / V - μ) ≤ k * P * (8 * μ) :=
    mul_le_mul_of_nonneg_left hxm (by positivity)
  have h2 : 0 ≤ (1 / 2 : ℝ) * k * V * (P / V) ^ 2 := by positivity
  have h3 : N / V - P / V ≤ 9 * μ := by linarith
  have h4 : (1 / 2 : ℝ) * k * (N / V - P / V) ≤ (1 / 2 : ℝ) * k * (9 * μ) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  nlinarith [hid, h1, h2, h4]

/-! ## The q0-word in sharp form -/

/-- **Sharp q0-word bound.**  The exact `∬w₂`-form of the q0-word
(`A0Bridge.q0word_w2_mass_sub`) combined with `cS2 ≥ cS1²−cS1`
(`Q0Convex.cS2_ge_sq_sub_self`) and `cS1 = N̂ − n₊`: for a NORMALISED state in
the density window `N̂/ℓ³ ≤ 9μ`,

    q0word(g₀,g₂) ≥ ½(x−μ)²·8π(av)ℓ³ − ½μ²·8π(av)ℓ³ + ½ℓ⁻³·D·cS2
                      − 64π(av)μ·n₊ − 36π(av)μ ,

`x := N̂/ℓ³`, `D := g0w0Mass`.  The HALF-coefficient on `(x−μ)²` is exactly
what the FS-shape AM–GM (`q1_cross_w1_cs_fs`) subtracts (its `¼`-term), so
that the combined q0+q1 P-part produces the block-bound main term
`¼(x−μ)²·8π(av)ℓ³`. -/
theorem q0word_sharp {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 < μ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1)
    (hwin : (N : ℝ) / ℓ ^ 3 ≤ 9 * μ) :
    (1 / 2 : ℝ) * (((N : ℝ) / ℓ ^ 3) - μ) ^ 2 * (8 * π * (a v) * ℓ ^ 3)
      - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * (a v) * ℓ ^ 3)
      + (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 ℓ Φ
      - (64 * π * (a v) * μ) * cnPlus ℓ Φ - 36 * π * (a v) * μ
    ≤ q0word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ := by
  classical
  have hℓ3 : 0 < ℓ ^ 3 := by positivity
  have hq0 := q0word_w2_mass_sub (N := N) (v := v) (R := R) (ℓ := ℓ) hR hv_nonneg
    hvrad hv_supp h hℓ hRℓ μ (Φ := Φ) hΦc
  have hcS2 := cS2_ge_sq_sub_self (N := N) (ℓ := ℓ) hℓ hΦc hnorm
  have hS := cS1_eq_nat_sub_cnPlus hℓ hΦc hnorm
  have hDnn : 0 ≤ g0w0Mass (v := v) h :=
    g0w0Mass_nonneg (v := v) (R := R) hR hv_nonneg hvrad hv_supp h
  have hCnn : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
  have hC2nn : 0 ≤ cS2 ℓ Φ := cS2_nonneg
  have hann : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hcoef : (0 : ℝ) ≤ (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (8 * π * a v) := by positivity
  have hk8 : (0 : ℝ) ≤ 8 * π * a v := by positivity
  have hDc : (0 : ℝ) ≤ (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (g0w0Mass (v := v) h) * (cS2 ℓ Φ) := by
    have h1 : (0 : ℝ) ≤ (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (g0w0Mass (v := v) h) := by positivity
    exact mul_nonneg h1 hC2nn
  have harith := q0_sharp_arith (ℓ ^ 3) μ (8 * π * a v) (N : ℝ) (cnPlus ℓ Φ)
    hℓ3 (le_of_lt hμ) hk8 hCnn hwin
  have h1 : (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (8 * π * a v) * (cS1 ℓ Φ * cS1 ℓ Φ - cS1 ℓ Φ)
      ≤ (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (8 * π * a v) * cS2 ℓ Φ :=
    mul_le_mul_of_nonneg_left hcS2 hcoef
  have hq0' : q0word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
      = (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (8 * π * a v) * cS2 ℓ Φ
        + (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 ℓ Φ
        - (8 * π * a v) * μ * cS1 ℓ Φ := by
    rw [hq0]; ring
  have hstep : (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (8 * π * a v) * (((N : ℝ) - cnPlus ℓ Φ) ^ 2
          - ((N : ℝ) - cnPlus ℓ Φ))
        + (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 ℓ Φ
        - (8 * π * a v) * μ * ((N : ℝ) - cnPlus ℓ Φ)
      ≤ (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (8 * π * a v) * cS2 ℓ Φ
        + (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 ℓ Φ
        - (8 * π * a v) * μ * cS1 ℓ Φ := by
    rw [hS] at h1 ⊢
    nlinarith [h1]
  have hmain : (1 / 2 : ℝ) * (((N : ℝ) / ℓ ^ 3) - μ) ^ 2 * (8 * π * a v * ℓ ^ 3)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * a v * ℓ ^ 3)
        + (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 ℓ Φ
        - (64 * π * (a v) * μ) * cnPlus ℓ Φ - 36 * π * (a v) * μ
      ≤ (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (8 * π * a v) * (((N : ℝ) - cnPlus ℓ Φ) ^ 2
          - ((N : ℝ) - cnPlus ℓ Φ))
        + (1 / 2 : ℝ) * (ℓ ^ 3)⁻¹ * (g0w0Mass (v := v) h) * cS2 ℓ Φ
        - (8 * π * a v) * μ * ((N : ℝ) - cnPlus ℓ Φ) := by
    linarith [harith, hDc]
  rw [hq0']
  linarith [hstep, hmain]

/-! ## The q2-word in sharp form (keeping the A₂ pairing) -/

/-- **Sharp q2-word bound.**  From the exact split
`q2word = q1PairWord + q2PairWord − μ·qOneMass + q4PairWord`
(`A0Bridge.q2word_a2_split`), `q2PairWord ≥ 0`
(`QMassUpper.q2PairWord_nonneg`), `|q1PairWord| ≤ C₂ℓ⁻³N̂n₊`
(`FSGroupQ2.q2_T1_abs_le`) and `qOneMass ≤ C₁n₊`
(`Step4SqrtFactorisation.qOneMass_le_fsqC1_mul_cnPlus`):

    q2word ≥ q4PairWord − 2C₂ℓ⁻³N̂·n₊ − μC₁·n₊ ,

keeping the `A₂ = q4PairWord` pairing (the Bogolubov input) EXACT. -/
theorem q2word_sharp {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
      - (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ
      - μ * (fsqC1 (a v)) * cnPlus ℓ Φ
    ≤ q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ := by
  classical
  have hsplit := q2word_a2_split (N := N) (ℓ := ℓ) (μ := μ) (v := v) h (Φ := Φ)
  have hT1 := q2_T1_abs_le (N := N) (ℓ := ℓ) (v := v) hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hT2 := q2PairWord_nonneg (N := N) (ℓ := ℓ) (v := v) hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
  have hQ := qOneMass_le_fsqC1_mul_cnPlus (N := N) (ℓ := ℓ) (v := v) hℓ hv_nonneg hvrad
    hR hv_supp h hRℓ hΦc
  have hT1' : - ((fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ)
      ≤ q1PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) := by
    have hb := (abs_le.mp hT1).1
    simpa only [q1PairWord] using hb
  have hQ' : - (μ * (fsqC1 (a v)) * cnPlus ℓ Φ)
      ≤ - μ * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) := by
    have := mul_le_mul_of_nonneg_left hQ hμ
    linarith
  linarith [hsplit, hT1', hT2, hQ']


/-! ## The `n₊`-coefficient of the sharp chain -/

/-- The universal `n₊`-coefficient of the sharp potential-side chain:
`64π(av)μ + 36C₁μ + 9μ(6C₁+C₂) + μC₁` with `C₁ := fsqC1(av)`, `C₂ := fsqC2(av)`.
It is exactly what the kinetic gap (`KineticBound.kinWord_gap_cnPlus`,
`kinWord ≥ n₊/(36ℓ²)`) must absorb; the smallbox regime condition is
`potNCoeff μ (av) ≤ 1/(36ℓ²)`. -/
noncomputable def potNCoeff (μ a : ℝ) : ℝ :=
  64 * π * a * μ + 36 * (fsqC1 a) * μ + (6 * (fsqC1 a) + (fsqC2 a)) * 9 * μ
    + μ * (fsqC1 a)

end Work.SmallBoxA0
