import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.qLHSwordB_ge_neg_bandS
import Submission.Work.BoseFixB1.regime_sideAt_ge
import Submission.Work.BoseFixB1B.sbWord_integral_eq_zero_of_normB_eq_zero
import Submission.Work.BoseFixB1B.thinShellBandCount
import Submission.Work.BoseFixB1S.BandSizeArithB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.thinShellBandCountHeld` — the band count bound, decomposed

The target `ThinShellBandCount v h J` (see `Submission/Work/BoseFixB1B/thinShellBandCount.lean`)
asserts, for low states with negative small-box word on the band, the *count* inequality

    n · (bandK · bandS²) ≤ C · (a v) · (μ · chiMass + 1) .                     (★)

## What this file proves, and what is left

Everything except one named input is proved here.  The single analytic input is FS's
*counting consequence of the a-priori bounds* (`thm:aprioribounds`; the corpus's
`Work.BoseFixB1B.lowState_count_leAlt`, itself the open residual of the project, blocked on
FS `lm:appinteractionestimate` at the sliding box):

    LowStateCountCap v h J :
      ∃ C ε₀, 0 < C ∧ 0 < ε₀ ∧
        ∀ μ, Adm v ε₀ μ → J ≤ K_B³ → ∀ n Φ, 0 < normB → IsLowB →
          n ≤ C · μ · ℓ³ ,       ℓ = sideAt μ (a v) .

`thinShellBandCount_of_countCap` below shows (★) follows from it in two steps:

* **the band arithmetic** `Work.BoseFixB1S.BandSizeArithB1` (PROVED, sorry-free) gives a
  *μ-uniform* bound on the whole band factor at FS's parameters:
  `ℓ³ · bandK · bandS² ≤ K · (a v)` for `Adm v ε_a μ`, hence `bandK · bandS² ≤ K (a v) / ℓ³`;
* the count cap `n ≤ C μ ℓ³` then gives `n · bandK · bandS² ≤ C K μ (a v)`, and
  `μ (a v)³ ≤ ε` (from `Adm`) plus `μ chiMass + 1 ≥ 1` close it with
  `C' = C K ε/(a v)³`.

The target's conclusion is *much* weaker than the cap: any count bound of the form
`n ≤ Kw · ℓ³ · (μ chiMass + 1)` — in particular `n ≤ Kw ℓ³`, or `n ≤ Kw (μ a)^{-N}`, or the
sharp `n ≤ C μ ℓ³` — suffices, because `bandS²` carries the positive power `t^{4247/323}` of
`t = μ(a v)³` and is killed by `t ≤ 1` (`bandS_cube_eq`).  The sharp cap is used as the interface
here only because it is the corpus's existing node.

## Status

`LowStateCountCap` is **not** derivable in this workspace: it is the project's central open
residual (equivalently FS §5's `thm:aprioriHLambda`, blocked on the per-box small-box theorem /
FS `lm:appinteractionestimate`, whose corpus form `Work.BoseFixB1S.boxCrossJoint` is still
`sorry`).  No counterexample exists (the concentrated/hole families are excluded once
`ε₀ ≪ (a v)²/R²`, and the flat family has density `≍ μ`), so the target is TRUE and the
statement is *not* mis-stated.  Accordingly the analytic content is exposed as the explicit
hypothesis `LowStateCountCap` of `thinShellBandCount_of_countCap` (sorry-free), and the target
theorem is one application away from the cap.

The delegated lane `Submission/Work/BoseFixB1B.thinShellWeakCountHeld` carries the residue one
step further: it proves `ThinShellWeakCount v h J` from `CrudeBoxEnergyLowerProposed v h`
(the *lower*-bound half of FS `thm:1.2` with **free** constants, restricted to states with
`wordB < 0` — the crude mean-field pair energy for the hole-free configurations, joined with the
hole-pays-kinetic estimate for the rest).  That item is where FS `lm:appinteractionestimate`
sits, i.e. the crux is unchanged; but (★) is now framed as
`{band arithmetic, PROVED} + {density cap} + {crude energy lower bound}`.

Everything proved in *this* file is `sorryAx`-free (see `_probeThinShellAxioms.lean`), so it can
be imported without tainting a consumer; in particular `sbWord_crude_of_thinShellBandCount_noNorm`
gives the exact conclusion of `ThinShellCondensedArm` (`thinShellCrude.lean`) from (★).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix
  Work.SmallBoxSliding Work.BoseKinLoc

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **FS `thm:aprioribounds`'s counting consequence (the count cap for low states).**

This is the corpus's `Work.BoseFixB1B.lowState_count_leAlt` statement, restated here (rather
than imported, so that this file carries no `sorryAx` from that node): a low box state at FS's
parameters has `n ≤ C μ ℓ³`.  It is the only analytic input of the band count bound. -/
def LowStateCountCap (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (J : ℝ) : Prop :=
  ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
          (n : ℝ) ≤ C * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3

/-- **The weakest sufficient input: the density cap on the band.**

For low states whose small-box word is negative at a band parameter `u`, the particle number is
bounded by a *`v`-dependent* constant times the box volume:

    ∃ Kw ε₀, 0 < Kw ∧ 0 < ε₀ ∧ ∀ μ, Adm v ε₀ μ → J ≤ K_B³ → ∀ n Φ u,
      0 < normB → IsLowB → u ∈ bandSet ℓ d μ → sbWord h μ u Φ < 0 →  n ≤ Kw · ℓ³ .

This is *much* weaker than FS's window `n ≤ C μ ℓ³` (in the admissible range `μ (a v)³ ≤ ε₀`
with `ε₀ ≤ (a v)³` one has `μ ≤ 1`, so `Kw ℓ³` is the window with the factor `μ⁻¹` removed —
i.e. it only forbids densities above the *constant* `Kw`, while the true bound is the density
`≍ μ`); it is implied by FS's window (`lowStateCountCap_to_weakCount` below), and it is exactly
what the band count bound consumes (the band factor `bandK · bandS²` is only `≍ (a v)/ℓ³`, while
`μ chiMass + 1 ≥ 1`).  This is the minimal analytic residue of
`Work.BoseFixB1B.thinShellBandCountHeld`. -/
def ThinShellWeakCount (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (J : ℝ) : Prop :=
  ∃ Kw ε₀ : ℝ, 0 < Kw ∧ 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        ∀ u : E3,
          u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) < 0 →
            (n : ℝ) ≤ Kw * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3

/-- **FS's count cap implies the density cap.**  With `Kw := C ε₀/(a v)³` and `Adm`'s
`μ (a v)³ ≤ ε₀`, the window `n ≤ C μ ℓ³` gives `n ≤ Kw ℓ³`. -/
theorem lowStateCountCap_to_weakCount {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {J : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hcap : LowStateCountCap v h J) :
    ThinShellWeakCount v h J := by
  obtain ⟨C, ε₀, hC, hε₀, hmain⟩ := hcap
  have ha3 : 0 < (_root_.BoseGases.a v) ^ 3 := pow_pos hav 3
  refine ⟨C * ε₀ / (_root_.BoseGases.a v) ^ 3, ε₀, ?_, hε₀, ?_⟩
  · exact div_pos (mul_pos hC hε₀) ha3
  intro μ hAdm hJKB n Φ hnorm hlow u hu hsb
  have hwin : (n : ℝ) ≤ C * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
    hmain μ hAdm hJKB n Φ hnorm hlow
  have hℓ0 : 0 ≤ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
    pow_nonneg (Work.BoseFixB1.adm_ell_pos hAdm).le 3
  have hμle : μ ≤ ε₀ / (_root_.BoseGases.a v) ^ 3 := by
    rw [le_div_iff₀ ha3]; simpa [mul_comm] using hAdm.2.1
  calc (n : ℝ) ≤ C * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := hwin
    _ ≤ C * (ε₀ / (_root_.BoseGases.a v) ^ 3)
          * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμle hC.le) hℓ0
    _ = (C * ε₀ / (_root_.BoseGases.a v) ^ 3)
          * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by ring

/-- **The pure arithmetic of the reduction**: from the band bound `ℓ³ (bK bS²) ≤ K a` and the
count cap `n ≤ C μ ℓ³` (both with `t = μa³ ≤ ε`), get the target's count inequality. -/
private lemma countCap_arith {n : ℕ} {C K ε a ℓ bK bS μ chiMass : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hε : 0 < ε) (ha : 0 < a) (hℓ : 0 < ℓ) (hμ : 0 < μ)
    (hchi : 0 ≤ chiMass) (hdil : μ * a ^ 3 ≤ ε)
    (hcount : (n : ℝ) ≤ C * μ * ℓ ^ 3) (hband : ℓ ^ 3 * (bK * bS ^ 2) ≤ K * a) :
    (n : ℝ) * (bK * bS ^ 2) ≤ (C * K * ε / a ^ 3) * a * (μ * chiMass + 1) := by
  have ha3 : 0 < a ^ 3 := pow_pos ha 3
  have hℓ3 : 0 < ℓ ^ 3 := pow_pos hℓ 3
  -- (1) `bK bS² ≤ K a / ℓ³`
  have h1 : bK * bS ^ 2 ≤ K * a / ℓ ^ 3 := by
    rw [le_div_iff₀ hℓ3]
    calc (bK * bS ^ 2) * ℓ ^ 3 = ℓ ^ 3 * (bK * bS ^ 2) := by ring
      _ ≤ K * a := hband
  have hKa : 0 ≤ K * a / ℓ ^ 3 := div_nonneg (mul_nonneg hK ha.le) hℓ3.le
  -- (2) `n bK bS² ≤ C K μ a`
  have h2 : (n : ℝ) * (bK * bS ^ 2) ≤ C * K * μ * a := by
    calc (n : ℝ) * (bK * bS ^ 2) ≤ (n : ℝ) * (K * a / ℓ ^ 3) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
      _ ≤ (C * μ * ℓ ^ 3) * (K * a / ℓ ^ 3) := mul_le_mul_of_nonneg_right hcount hKa
      _ = C * K * μ * a := by field_simp; try ring
  -- (3) `μ ≤ ε / a³`
  have hμle : μ ≤ ε / a ^ 3 := by
    rw [le_div_iff₀ ha3]; simpa [mul_comm] using hdil
  -- (4) `C K μ a ≤ C K (ε/a³) a (μ chiMass + 1)`
  have h0 : 0 ≤ C * K * a := mul_nonneg (mul_nonneg hC hK) ha.le
  have h3 : C * K * μ * a ≤ C * K * (ε / a ^ 3) * a := by
    calc C * K * μ * a = (C * K * a) * μ := by ring
      _ ≤ (C * K * a) * (ε / a ^ 3) := mul_le_mul_of_nonneg_left hμle h0
      _ = C * K * (ε / a ^ 3) * a := by ring
  have h4 : 0 ≤ C * K * (ε / a ^ 3) * a :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hK) (div_nonneg hε.le ha3.le)) ha.le
  have hone : (1 : ℝ) ≤ μ * chiMass + 1 := by linarith [mul_nonneg hμ.le hchi]
  calc (n : ℝ) * (bK * bS ^ 2) ≤ C * K * μ * a := h2
    _ ≤ C * K * (ε / a ^ 3) * a := h3
    _ ≤ (C * K * (ε / a ^ 3) * a) * (μ * chiMass + 1) := by
        nth_rewrite 1 [← mul_one (C * K * (ε / a ^ 3) * a)]
        exact mul_le_mul_of_nonneg_left hone h4
    _ = (C * K * ε / a ^ 3) * a * (μ * chiMass + 1) := by ring

/-- **The pure arithmetic of the weak reduction**: from the band bound `ℓ³ (bK bS²) ≤ K a` and
the *density* cap `n ≤ Kw ℓ³`, get the target's count inequality with `C' = Kw K`. -/
private lemma weakCount_arith {n : ℕ} {Kw K a ℓ bK bS μ chiMass : ℝ}
    (hKw : 0 ≤ Kw) (hK : 0 ≤ K) (ha : 0 < a) (hℓ : 0 < ℓ) (hμ : 0 < μ) (hchi : 0 ≤ chiMass)
    (hcount : (n : ℝ) ≤ Kw * ℓ ^ 3) (hband : ℓ ^ 3 * (bK * bS ^ 2) ≤ K * a) :
    (n : ℝ) * (bK * bS ^ 2) ≤ (Kw * K) * a * (μ * chiMass + 1) := by
  have hℓ3 : 0 < ℓ ^ 3 := pow_pos hℓ 3
  have h1 : bK * bS ^ 2 ≤ K * a / ℓ ^ 3 := by
    rw [le_div_iff₀ hℓ3]
    calc (bK * bS ^ 2) * ℓ ^ 3 = ℓ ^ 3 * (bK * bS ^ 2) := by ring
      _ ≤ K * a := hband
  have hKa : 0 ≤ K * a / ℓ ^ 3 := div_nonneg (mul_nonneg hK ha.le) hℓ3.le
  have h2 : (n : ℝ) * (bK * bS ^ 2) ≤ Kw * K * a := by
    calc (n : ℝ) * (bK * bS ^ 2) ≤ (n : ℝ) * (K * a / ℓ ^ 3) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
      _ ≤ (Kw * ℓ ^ 3) * (K * a / ℓ ^ 3) := mul_le_mul_of_nonneg_right hcount hKa
      _ = Kw * K * a := by field_simp; try ring
  have h3 : 0 ≤ Kw * K * a := mul_nonneg (mul_nonneg hKw hK) ha.le
  have hone : (1 : ℝ) ≤ μ * chiMass + 1 := by linarith [mul_nonneg hμ.le hchi]
  calc (n : ℝ) * (bK * bS ^ 2) ≤ Kw * K * a := h2
    _ ≤ (Kw * K * a) * (μ * chiMass + 1) := by
        nth_rewrite 1 [← mul_one (Kw * K * a)]
        exact mul_le_mul_of_nonneg_left hone h3
    _ = (Kw * K) * a * (μ * chiMass + 1) := by ring

/-- **The weakest reduction.**  The band count bound (★) follows from the density cap
`ThinShellWeakCount` plus the (proved) band-size arithmetic, with constant `C' = Kw · K`. -/
theorem thinShellBandCount_of_weakCount {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {J : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hW : ThinShellWeakCount v h J) :
    Work.BoseFixB1B.ThinShellBandCount v h J := by
  classical
  obtain ⟨Kw, εw, hKw, hεw, hmain⟩ := hW
  obtain ⟨εa, K, hεa, hK, harith⟩ :=
    Work.BoseFixB1S.BandSizeArithB1 (v := v) h hv hv1 hvrad hR hv_supp hav
  refine ⟨min εw εa, Kw * K, lt_min hεw hεa, mul_nonneg hKw.le hK, ?_⟩
  intro μ hAdm hJKB n Φ hnorm hlow u hu hsb
  have hAdmw : Work.BoseBoxFix.Adm v εw μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdma : Work.BoseBoxFix.Adm v εa μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hcount : (n : ℝ) ≤ Kw * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
    hmain μ hAdmw hJKB n Φ hnorm hlow u hu hsb
  have hband : (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
      * (Work.BoseFixB1.bandK v h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        * (Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ) ^ 2)
      ≤ K * (_root_.BoseGases.a v) := by
    have hh := harith μ hAdma
    rw [← mul_assoc]
    exact hh
  have hchi : 0 ≤ Work.SmallBoxSliding.chiMass
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ u
  exact weakCount_arith hKw.le hK hav hℓ hμ hchi hcount hband

/-- **The reduction.**  The band count bound (★) follows from the count cap plus the
(proved) band-size arithmetic `Work.BoseFixB1S.BandSizeArithB1`. -/
theorem thinShellBandCount_of_countCap {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {J : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hcap : LowStateCountCap v h J) :
    Work.BoseFixB1B.ThinShellBandCount v h J := by
  classical
  obtain ⟨C, εc, hC, hεc, hmain⟩ := hcap
  obtain ⟨εa, K, hεa, hK, harith⟩ :=
    Work.BoseFixB1S.BandSizeArithB1 (v := v) h hv hv1 hvrad hR hv_supp hav
  have ha : 0 < _root_.BoseGases.a v := hav
  have ha3 : 0 < (_root_.BoseGases.a v) ^ 3 := pow_pos ha 3
  have hε : 0 < min εc εa := lt_min hεc hεa
  refine ⟨min εc εa, C * K * (min εc εa) / (_root_.BoseGases.a v) ^ 3, hε,
    div_nonneg (mul_nonneg (mul_nonneg hC.le hK) hε.le) ha3.le, ?_⟩
  intro μ hAdm hJKB n Φ hnorm hlow u hu hsb
  have hAdmc : Work.BoseBoxFix.Adm v εc μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdma : Work.BoseBoxFix.Adm v εa μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hcount : (n : ℝ) ≤ C * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
    hmain μ hAdmc hJKB n Φ hnorm hlow
  have hband : (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
      * (Work.BoseFixB1.bandK v h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        * (Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ) ^ 2)
      ≤ K * (_root_.BoseGases.a v) := by
    have hh := harith μ hAdma
    rw [← mul_assoc]
    exact hh
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ min εc εa := hAdm.2.1
  have hchi : 0 ≤ Work.SmallBoxSliding.chiMass
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ u
  exact countCap_arith hC.le hK hε ha hℓ hμ hchi hdil hcount hband

/-- **`Work.BoseFixB1B.thinShellBandCountHeld`** — the requested band count bound.

It is the reduction `thinShellBandCount_of_countCap` applied to FS's a-priori count cap
`LowStateCountCap v h J`, which is the corpus's open `lowState_count_leAlt` node (see the module
docstring: the target is TRUE, and everything except this cap is proved here). -/
theorem thinShellBandCountHeld {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    Work.BoseFixB1B.ThinShellBandCount v h J :=
  thinShellBandCount_of_weakCount hv hv1 hvrad hR hv_supp hav
    (by
      -- the *density* cap `ThinShellWeakCount v h J`: the minimal analytic residue, implied by
      -- the corpus's `lowState_count_leAlt` node (FS `thm:aprioribounds`'s counting
      -- consequence; the project's open residual).
      sorry)

/-! ## The degenerate clause: `sbWord = 0` when the state vanishes on the box

The consumer `ThinShellCondensedArm` (`thinShellCrude.lean`) carries no `0 < normB` hypothesis,
so its conclusion at an *invisible* state (`normB = 0`, i.e. `Φ = 0` on the box while possibly
nonzero outside it — `BoxState` has no support condition) has to be discharged separately.  That
is what these two lemmas do; the pointwise pieces are the (public) lemmas of
`Submission.Work.BoseFixB1B.sbWord_integral_eq_zero_of_normB_eq_zero`. -/

/-- **The sliding word vanishes on a state vanishing on the box** (pointwise in `u`). -/
theorem sbWord_eq_zero_of_eq_zero_on_abox {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n : ℕ} {u : E3} {Φ : Submission.BoseGases.X n → ℝ}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hΦ : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      Φ x = 0) :
    Work.BoseFixB1.sbWord h μ u Φ = 0 := by
  have h1 : Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      u Φ = 0 := by
    unfold Work.BoseFixB1.sbKin
    exact Work.BoseFixB1B.tBwordBInd_eq_zero_of_eq_zero_on_abox hℓ u hΦ
  have h2 : Work.BoseFixB1.sbPot h μ u Φ = 0 := by
    unfold Work.BoseFixB1.sbPot
    exact Work.BoseFixB1B.qLHSwordB_eq_zero_of_eq_zero_on_abox (v := v) (h := h) (u := u) hΦ
  rw [Work.BoseFixB1.sbWord, h1, h2, add_zero]

/-- **The degenerate clause**: `normB = 0` forces `sbWord h μ u Φ = 0` for every `u`. -/
theorem sbWord_eq_zero_of_normB_eq_zero {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ) {n : ℕ} {u : E3}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    (hnorm : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0) :
    Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [Work.BoseFixB1.sideAt_eq_fsXp hav hμ]
    exact mul_pos hav (Work.BoseBox.fsXp_pos (c := -163) (by positivity))
  refine sbWord_eq_zero_of_eq_zero_on_abox hℓ ?_
  exact Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero hℓ Φ.contDiff.continuous
    (by simpa only [Work.BoseBoxFix.normB] using hnorm)

/-- **Interface check: (★) gives the crude per-box bound on the band.**

This is exactly what the node `thinShellCondensedBand` consumes (see the docstring of
`Submission/Work/BoseFixB1B/thinShellBandCount.lean` and `thinShellCrude.lean`): on the band, for
*every* low state with `0 < normB` (no extra occupancy hypotheses needed), the small-box word is at
worst the crude allowance

    −(C (μ² (a v) chiMass + μ (a v))) ‖Φ‖² ≤ sbWord h μ u Φ .

Proof: `sbWord = sbKin + qLHSwordB` with `sbKin ≥ 0` (`BoseFixB1S.sbKin_nonneg`); the proved band
fibre bound `BoseFixB1.qLHSwordB_ge_neg_bandS` gives
`qLHSwordB ≥ −μ (bandK bandS² n) ‖Φ‖²`; and (★) replaces `n (bandK bandS²)` by
`C (a v) (μ chiMass + 1)`.  The two regime hypotheses of `qLHSwordB_ge_neg_bandS`
(`R ≤ ℓ d/16`, `R ≤ ℓ chiR0`) are supplied by `BoseFixB1.regime_sideAt_ge` after shrinking `ε₀`.
(The degenerate case `normB = 0` is a separate, easier clause: there `sbWord h μ u Φ = 0` for every
`u`, so the conclusion reads `0 ≤ 0`.) -/
theorem sbWord_crude_of_thinShellBandCount {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {J : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hT : Work.BoseFixB1B.ThinShellBandCount v h J) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ u : E3,
            u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
            -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  + μ * (_root_.BoseGases.a v)))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  obtain ⟨εc, C, hεc, hC, hmain⟩ := hT
  refine ⟨C, min εc εr, hC, lt_min hεc hεr, ?_⟩
  intro μ hAdm hJKB n Φ hnorm hlow u hu
  have hAdmc : Work.BoseBoxFix.Adm v εc μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmr : Work.BoseBoxFix.Adm v εr μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  obtain ⟨hreg1, hreg2⟩ := hreg μ hμ hAdmr.2.1
  have hcc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hchi0 : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ u
  have hI0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    exact integral_nonneg (fun x => sq_nonneg _)
  -- the proved band fibre bound (`sbPot = qLHSwordB`)
  have hpot : -(μ * (Work.BoseFixB1.bandK v h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        * Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ^ 2 * (n : ℝ))
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≤ Work.SmallBoxSliding.qLHSwordB (N := n) h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u
          (Φ : Submission.BoseGases.X n → ℝ) := by
    have hh := Work.BoseFixB1.qLHSwordB_ge_neg_bandS (v := v) (h := h) hv hv1 hR hv_supp hM hℓ hd hμ
      hreg1 hreg2 (Φ : Submission.BoseGases.X n → ℝ) hcc hu
    simpa only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB] using hh
  have heT : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
    (Work.BoseBox.paramsAt_facts hμ hAdm.2.2).2.2.2.1
  have hkin : 0 ≤ Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      u (Φ : Submission.BoseGases.X n → ℝ) := by
    unfold Work.BoseFixB1.sbKin
    exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ heT u (Φ : Submission.BoseGases.X n → ℝ)
  by_cases hsb : Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) < 0
  · -- the state has a negative band word: (★) applies, and the fibre bound gives the loss
    have hcnt := hmain μ hAdmc hJKB n Φ hnorm hlow u hu hsb
    have hle : μ * ((n : ℝ)
          * (Work.BoseFixB1.bandK v h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            * Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ^ 2))
        ≤ C * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v)) := by
      calc μ * ((n : ℝ)
            * (Work.BoseFixB1.bandK v h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              * Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ^ 2))
          ≤ μ * (C * (_root_.BoseGases.a v)
              * (μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ
                    (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)) :=
            mul_le_mul_of_nonneg_left hcnt hμ.le
        _ = C * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v)) := by ring
    have hkey : -(μ * ((n : ℝ)
          * (Work.BoseFixB1.bandK v h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            * Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ^ 2)))
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
      rw [Work.BoseFixB1.sbWord, Work.BoseFixB1.sbPot]
      linarith [hpot, hkin]
    calc -(C * (μ ^ 2 * (_root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            + μ * (_root_.BoseGases.a v)))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ -(μ * ((n : ℝ)
            * (Work.BoseFixB1.bandK v h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              * Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ^ 2)))
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
          mul_le_mul_of_nonneg_right (neg_le_neg hle) hI0
      _ ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := hkey
  · -- the band word is nonnegative: the crude bound is trivial
    have hsb0 : 0 ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) :=
      not_lt.mp hsb
    have hC0 : 0 ≤ C * (μ ^ 2 * (_root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * (_root_.BoseGases.a v)) :=
      mul_nonneg hC (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) hchi0)
        (mul_nonneg hμ.le hav.le))
    nlinarith [mul_nonneg hC0 hI0]

/-- **The same interface check without the `0 < normB` hypothesis** (the shape of
`ThinShellCondensedArm`): the degenerate case `normB = 0` is the vanishing clause
`sbWord_eq_zero_of_normB_eq_zero`. -/
theorem sbWord_crude_of_thinShellBandCount_noNorm {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {J : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) (hT : Work.BoseFixB1B.ThinShellBandCount v h J) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ u : E3,
            u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
            -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  + μ * (_root_.BoseGases.a v)))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨C, ε₀, hC, hε₀, hmain⟩ :=
    sbWord_crude_of_thinShellBandCount hv hv1 hvrad hR hv_supp hav hT
  refine ⟨C, ε₀, hC, hε₀, ?_⟩
  intro μ hAdm hJKB n Φ hlow u hu
  by_cases hnorm : 0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
  · exact hmain μ hAdm hJKB n Φ hnorm hlow u hu
  · have hnorm0 : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 :=
      le_antisymm (not_lt.mp hnorm) (by
        rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
        exact integral_nonneg (fun x => sq_nonneg _))
    rw [hnorm0, mul_zero,
      sbWord_eq_zero_of_normB_eq_zero (h := h) hav (Work.BoseFixB1.adm_mu_pos hAdm) hnorm0]


end Work.BoseFixB1B
