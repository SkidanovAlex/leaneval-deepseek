import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.Interfaces` — the `J`-uniform interfaces of the count-window chain

This module holds the two predicates and the three bookkeeping lemmas that the count-window chain
(`Work.BoseFixB1S.LowCountWindowAllJ`) and its three chain modules
(`collectedUnifOfPerBox`, `aprioriUnifOfCollectedUnif`, `countWindowUnif_of_aprioriUnif`) share.

**Why it is a separate module.**  The chain modules are *stated* in the vocabulary of
`CollectedUnif` / `AprioriUnif`, so they must import the module that defines them.  With the
definitions living in `LowCountWindowAllJ.lean`, the target of that file could not import the chain
back (build cycle), and closing the target would have required inlining the whole chain.  Moving
the definitions here (upstream of both) makes the target *one line* away from its per-box inputs.

The declarations are verbatim the ones previously written in `LowCountWindowAllJ.lean` (same
names, same statements); nothing else changed.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBoxFix Work.BoseBox

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The two pieces of bookkeeping -/

/-- **`lhyC ≤ K_B³` under diluteness.**  At FS's parameters `K_B³ = (μa³)^{−18/323}`, so
`lhyC ≤ K_B³` as soon as `μa³ ≤ lhyC^{−323/18}` — attainable by choosing `ε₀` small.  This is
what lets the `J ≤ lhyC` cases be pulled back to `J = lhyC`. -/
lemma lhyC_le_KB_cube_of_dilute {v : E3 → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v)
    (hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ lhyC ^ (-(323 / 18 : ℝ))) :
    lhyC ≤ (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 :=
  Work.BoseBox.KB_cube_ge hμ hav lhyC_pos hdil

/-- **`IsLowB` is monotone in the threshold `J`.**  `Theta (a v) J μ` is increasing in `J`, so
raising the threshold enlarges the low class.  Hence the `∀ J ≤ K_B³` form of the count window is
*equivalent* to its `J = K_B³` instance, and the `J ≤ lhyC` cases reduce to `J = lhyC`. -/
lemma isLowB_mono {v : E3 → ℝ} {h : ScatSol v} {J J' μ : ℝ} {n : ℕ} {Φ : X n → ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hℓ : 0 ≤ sideAt μ (_root_.BoseGases.a v)) (hJJ : J ≤ J')
    (hlow : IsLowB v h J μ n Φ) : IsLowB v h J' μ n Φ := by
  rw [Work.BoseFixB1.isLowB_iff hav] at hlow ⊢
  have hA : 0 ≤ 4 * π * μ ^ 2 * (_root_.BoseGases.a v) * sideAt μ (_root_.BoseGases.a v) ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg μ)) hav.le) (pow_nonneg hℓ 3)
  have hs : 0 ≤ Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) := Real.sqrt_nonneg _
  have hstep : -(4 * π * μ ^ 2 * (_root_.BoseGases.a v) * sideAt μ (_root_.BoseGases.a v) ^ 3
        * (1 - J * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3)))
      ≤ -(4 * π * μ ^ 2 * (_root_.BoseGases.a v) * sideAt μ (_root_.BoseGases.a v) ^ 3
        * (1 - J' * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3))) := by
    have hprod : 0 ≤ (4 * π * μ ^ 2 * (_root_.BoseGases.a v) * sideAt μ (_root_.BoseGases.a v) ^ 3)
        * Real.sqrt (μ * (_root_.BoseGases.a v) ^ 3) * (J' - J) :=
      mul_nonneg (mul_nonneg hA hs) (sub_nonneg.mpr hJJ)
    nlinarith [hprod]
  exact le_trans hlow (mul_le_mul_of_nonneg_right hstep (Work.BoseFixB1.normB_nonneg Φ))

/-! ## 2. The `J`-uniform F-weight arithmetic

`arith_core` in `LowCountWindowB1` closes the F-weight chain

    c·((x−1)²/(1+x))·8πaℓ³μ² − 4πμ²aℓ³ − Cμ²aℓ³ − Cμa ≤ dg ≤ −4πμ²aℓ³(1 − J√(μa³))

with the constant `max 3 (8(4πJ + 2C)/(8πc))`, i.e. **linear in `J`**: it uses
`4πJ√(μa³) ≤ 4πJ` (valid for `J ≥ 0`, `μa³ ≤ 1`).  The hypothesis `J ≤ K_B³` upgrades this to
`4πJ√(μa³) ≤ 4πK_B³√(μa³) = 4π(μa³)^{287/646} ≤ 4π`, and the constant becomes `J`-free. -/
lemma fweight_count_uniform {μ a ℓ J c C dg x : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hℓ : 0 < ℓ)
    (hc : 0 < c) (hC : 0 ≤ C) (hx : 0 ≤ x) (hJt : J * Real.sqrt (μ * a ^ 3) ≤ 1)
    (htp : (μ * a ^ 3) ^ (166 / 323 : ℝ) ≤ 1)
    (hmul : μ * ℓ ^ 3 = (μ * a ^ 3) ^ (-(166 / 323) : ℝ))
    (h1 : (c * ((x * μ - μ) ^ 2 / (1 + (x * μ) / μ)) - (1 / 2) * μ ^ 2) * (8 * π * a * ℓ ^ 3)
        - C * μ ^ 2 * a * ℓ ^ 3 - C * μ * a ≤ dg)
    (h2 : dg ≤ -(4 * π * μ ^ 2 * a * ℓ ^ 3 * (1 - J * Real.sqrt (μ * a ^ 3)))) :
    x ≤ max 3 (8 * ((4 * π + 2 * C) / (8 * π * c))) := by
  have haℓ : 0 < a * ℓ ^ 3 := mul_pos ha (pow_pos hℓ 3)
  have hμ0 : 0 ≤ μ := hμ.le
  have htpos : (0 : ℝ) < μ * a ^ 3 := by positivity
  have hμ2pos : (0 : ℝ) < μ ^ 2 := by positivity
  have hden : (x * μ) / μ = x := by field_simp
  have hden0 : 0 < 1 + x := by linarith
  rw [hden] at h1
  have hstep : c * ((x - 1) ^ 2 * μ ^ 2 / (1 + x)) * (8 * π * a * ℓ ^ 3)
      ≤ μ ^ 2 * a * ℓ ^ 3 * (4 * π * (J * Real.sqrt (μ * a ^ 3)) + C) + C * μ * a := by
    have hexp : (c * ((x * μ - μ) ^ 2 / (1 + x)) - (1 / 2) * μ ^ 2) * (8 * π * a * ℓ ^ 3)
        = c * ((x - 1) ^ 2 * μ ^ 2 / (1 + x)) * (8 * π * a * ℓ ^ 3)
          - 4 * π * μ ^ 2 * a * ℓ ^ 3 := by ring
    have hexp2 : -(4 * π * μ ^ 2 * a * ℓ ^ 3 * (1 - J * Real.sqrt (μ * a ^ 3)))
        = -(4 * π * μ ^ 2 * a * ℓ ^ 3)
          + 4 * π * μ ^ 2 * a * ℓ ^ 3 * (J * Real.sqrt (μ * a ^ 3)) := by ring
    rw [hexp] at h1
    rw [hexp2] at h2
    nlinarith [h1, h2]
  have hmuℓ : μ / ℓ ^ 3 = μ ^ 2 * (μ * a ^ 3) ^ (166 / 323 : ℝ) := by
    rw [div_eq_iff (pow_ne_zero 3 (ne_of_gt hℓ))]
    have h1' : μ ^ 2 * (μ * a ^ 3) ^ (166 / 323 : ℝ) * ℓ ^ 3
        = μ * ((μ * a ^ 3) ^ (166 / 323 : ℝ) * (μ * ℓ ^ 3)) := by ring
    rw [h1', hmul, ← Real.rpow_add htpos,
      show (166 / 323 : ℝ) + -(166 / 323) = 0 by norm_num, Real.rpow_zero, mul_one]
  have hdiv : c * ((x - 1) ^ 2 * μ ^ 2 / (1 + x)) * (8 * π)
      ≤ μ ^ 2 * (4 * π * (J * Real.sqrt (μ * a ^ 3)) + C) + C * (μ / ℓ ^ 3) := by
    have hgoal : c * ((x - 1) ^ 2 * μ ^ 2 / (1 + x)) * (8 * π) * (a * ℓ ^ 3)
        ≤ (μ ^ 2 * (4 * π * (J * Real.sqrt (μ * a ^ 3)) + C) + C * (μ / ℓ ^ 3)) * (a * ℓ ^ 3) := by
      have hrhs : (μ ^ 2 * (4 * π * (J * Real.sqrt (μ * a ^ 3)) + C) + C * (μ / ℓ ^ 3))
            * (a * ℓ ^ 3)
          = μ ^ 2 * a * ℓ ^ 3 * (4 * π * (J * Real.sqrt (μ * a ^ 3)) + C) + C * μ * a := by
        have hℓ3ne : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
        field_simp
      rw [hrhs]
      have hre : c * ((x - 1) ^ 2 * μ ^ 2 / (1 + x)) * (8 * π) * (a * ℓ ^ 3)
          = c * ((x - 1) ^ 2 * μ ^ 2 / (1 + x)) * (8 * π * a * ℓ ^ 3) := by ring
      rw [hre]
      linarith [hstep]
    exact le_of_mul_le_mul_right hgoal haℓ
  rw [hmuℓ] at hdiv
  have hK : 4 * π * (J * Real.sqrt (μ * a ^ 3)) + C + C * (μ * a ^ 3) ^ (166 / 323 : ℝ)
      ≤ 4 * π + 2 * C := by
    have h1'' : 4 * π * (J * Real.sqrt (μ * a ^ 3)) ≤ 4 * π * 1 :=
      mul_le_mul_of_nonneg_left hJt (by positivity)
    have h2'' : C * (μ * a ^ 3) ^ (166 / 323 : ℝ) ≤ C * 1 := mul_le_mul_of_nonneg_left htp hC
    linarith
  have hF : c * ((x - 1) ^ 2 * μ ^ 2 / (1 + x)) * (8 * π) ≤ (4 * π + 2 * C) * μ ^ 2 := by
    have hdiv' : c * ((x - 1) ^ 2 * μ ^ 2 / (1 + x)) * (8 * π)
        ≤ μ ^ 2 * (4 * π * (J * Real.sqrt (μ * a ^ 3)) + C
            + C * (μ * a ^ 3) ^ (166 / 323 : ℝ)) := by
      calc c * ((x - 1) ^ 2 * μ ^ 2 / (1 + x)) * (8 * π)
          ≤ μ ^ 2 * (4 * π * (J * Real.sqrt (μ * a ^ 3)) + C)
            + C * (μ ^ 2 * (μ * a ^ 3) ^ (166 / 323 : ℝ)) := hdiv
        _ = μ ^ 2 * (4 * π * (J * Real.sqrt (μ * a ^ 3)) + C
              + C * (μ * a ^ 3) ^ (166 / 323 : ℝ)) := by ring
    have hfin : μ ^ 2 * (4 * π * (J * Real.sqrt (μ * a ^ 3)) + C
        + C * (μ * a ^ 3) ^ (166 / 323 : ℝ)) ≤ μ ^ 2 * (4 * π + 2 * C) :=
      mul_le_mul_of_nonneg_left hK (sq_nonneg μ)
    linarith [le_trans hdiv' hfin]
  set N : ℝ := (4 * π + 2 * C) / (8 * π * c) with hN
  have hN0 : 0 ≤ N := by
    rw [hN]
    have hnum : 0 ≤ 4 * π + 2 * C := by
      have : (0 : ℝ) ≤ 4 * π := by positivity
      linarith
    positivity
  have hkey : (x - 1) ^ 2 ≤ N * (1 + x) := by
    have h8 : (0 : ℝ) < 8 * π * c := by positivity
    have hunit : c * ((x - 1) ^ 2 * μ ^ 2 / (1 + x)) * (8 * π)
        = (((x - 1) ^ 2 / (1 + x)) * (8 * π * c)) * μ ^ 2 := by
      field_simp
    rw [hunit] at hF
    have hF' : ((x - 1) ^ 2 / (1 + x)) * (8 * π * c) ≤ 4 * π + 2 * C :=
      le_of_mul_le_mul_right hF hμ2pos
    have hF'' : (x - 1) ^ 2 / (1 + x) ≤ N := by
      rw [hN, le_div_iff₀ h8]
      linarith [hF']
    rwa [div_le_iff₀ hden0] at hF''
  by_cases hx3 : x ≤ 3
  · have h3 : x ≤ max 3 (8 * N) := le_trans hx3 (le_max_left _ _)
    linarith
  · have hx3' : 3 ≤ x := le_of_lt (lt_of_not_ge hx3)
    have hx0 : 0 < x := by linarith
    have hsq' : (x / 2) ^ 2 ≤ (x - 1) ^ 2 := by nlinarith [hx3']
    have hone : 1 + x ≤ 2 * x := by linarith
    have hstep2 : (x / 2) ^ 2 ≤ N * (2 * x) := by
      have h2' : N * (1 + x) ≤ N * (2 * x) := mul_le_mul_of_nonneg_left hone hN0
      linarith
    have hx8 : x ≤ 8 * N := by nlinarith [hstep2, hx0]
    have h8 : 8 * N ≤ max 3 (8 * N) := le_max_right _ _
    linarith

/-! ## 3. The interface: the collected per-box bound with a *single* constant for all `J`

`Work.BoseFixB1.SmallBoxCollectedC v h J` (the collected FS `thm:smallbox`, on disk as
`Work.BoseFixB1.smallBoxCollectedC_holds`) is *indexed* by `J` and hides its constants behind
`∃C`, so it cannot be composed into one `C` for the `∀ J` form of the count window.  The
predicate below is the *same* bound with the constants shared by every `J ≤ K_B³`.  Its
conclusion keeps FS's mean-field **background** `4πμ²(a v)ℓ³` — dropping it is *false*: the
per-box inputs give exactly

    c₁·R_Ψ ≤ ∫sbWord + 4πμ²(a v)ℓ³(1 + C₂κ)‖Φ‖² + (C₁+C₃)μ²(a v)ℓ³κ‖Φ‖² ,

and the background can only be cancelled against the low-state energy
(`wordB ≤ −4πμ²aℓ³(1−J√(μa³))‖Φ‖²`) *together with* `SlidingB` (`∫sbWord ≤ C_S·wordB`), which is
a hypothesis of the next step (`aprioriUnif_of_collectedUnif`), not of this one.  Its proof is
the (mechanical) re-run of `smallBoxCollectedC_holds`; its per-box inputs are
`Work.BoseFixB1B.perBoxIntegrated`'s (the F-weighted per-box bound, gated by
`perSectorBoundG_holds`) and `Work.BoseFixB1B.trimOffInterior`'s (gated by
`perBoxCrudeLower`), both currently `sorryAx`-tainted. -/
def CollectedUnif (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ C c : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ 0 < c ∧
    ∀ J : ℝ, ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
          0 ≤ Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) ∧
          c * Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ)
            ≤ (∫ u : E3, Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
              + 4 * π * μ ^ 2 * (_root_.BoseGases.a v)
                  * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                  * (1 + C * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)

/-! ## 4. The interface: the a-priori inequality with a *single* constant for all `J`

`Work.BoseFixB1.AprioriHLambdaIneq v h J` (FS `eq:aprioriRn+`) is *indexed* by `J` and hides
its constant behind `∃C`; the `J`-uniform form below exposes it, which is exactly what the
`∀ J` count window needs.  Its proof is the (mechanical) re-run of
`Work.BoseFixB1B.aprioriHLambdaIneq_from_slidingB`'s arithmetic at *fixed* constants, from the
proved `Work.BoseFixB1.SlidingB` and from `CollectedUnif` above. -/
def AprioriUnif (v : E3 → ℝ) (h : ScatSol v) : Prop :=
  ∃ C ε₀ : ℝ, 1 ≤ C ∧ 0 < ε₀ ∧
    ∀ J : ℝ, ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
          0 ≤ Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) ∧
          Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ)
            ≤ C * (μ ^ 2 * (_root_.BoseGases.a v)
                    * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                    * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                    * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) ∧
          ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
                / (2 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
              * Submission.BoseGases.cnPlus (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Φ : Submission.BoseGases.X n → ℝ)
            ≤ C * (μ ^ 2 * (_root_.BoseGases.a v)
                    * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
                    * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                    * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)

end Work.BoseFixB1S
