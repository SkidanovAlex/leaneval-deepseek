import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixB1.Cube.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.Cube.Assembly` — the Appendix at the matched (cube) window

`aprioriHLambdaIneq_of_piecesCube`: FS's `eq:aprioriRn+` (`Work.BoseFixB1.AprioriHLambdaIneq`)
follows from the two named pieces of the Appendix `SmallBoxes` **at the single cube cutoff**:

* `Work.BoseFixB1B.SlidingBCube` — FS `eq:BSsliding2` (Bratteli–Solovej Thm 3.10) with the matched
  word `sbWordCube = sbKinCube + sbPot`;
* `Work.BoseFixB1.SmallBoxCollectedCube` — FS `thm:smallbox` integrated over the small boxes,
  at the same cutoff.

This is the frozen `Work.BoseFixB1.aprioriHLambdaIneq_of_pieces` with the single substitution
`sbWord ↦ sbWordCube` (and the correspondingly substituted two hypotheses): the arithmetic is FS's
and uses no property of the word beyond those two inequalities, so nothing else changes.  The
target `AprioriHLambdaIneq` itself is **window-independent** — it mentions only `RPsi` (already
`chiSmallB`-based in both chapters), `cnPlus`, `wordB` and `normB`, and no small-box word at all.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- **FS `eq:aprioriRn+` from the two Appendix pieces, at the matched cube window.** -/
theorem aprioriHLambdaIneq_of_piecesCube {v : ℝ³ → ℝ} {h : ScatSol v} {J : ℝ}
    (hav : 0 < a v) (hS : Work.BoseFixB1B.SlidingBCube v h) (hC : SmallBoxCollectedCube v h J) :
    AprioriHLambdaIneq v h J := by
  obtain ⟨εS, CS, hCS1, hεS, hS'⟩ := hS
  obtain ⟨εC, CC, hCC0, hεC, hC'⟩ := hC
  refine ⟨4 * π * (CS + CC) + 1, min εS (min εC 1), ?_, ?_, ?_⟩
  · have hone : (0 : ℝ) ≤ CS + CC := by linarith
    nlinarith [Real.pi_pos, hone]
  · exact lt_min hεS (lt_min hεC one_pos)
  · intro μ hAdm hJK n Φ hlow
    obtain ⟨hμ, hdil, hPOK⟩ := hAdm
    have hAdmS : Adm v εS μ := ⟨hμ, le_trans hdil (min_le_left _ _), hPOK⟩
    have hAdmC : Adm v εC μ :=
      ⟨hμ, le_trans hdil (le_trans (min_le_right _ _) (min_le_left _ _)), hPOK⟩
    have hNN : 0 ≤ normB v μ n Φ := normB_nonneg Φ
    have htt : 0 ≤ (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
    have hcn : 0 ≤ cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := cnPlus_nonneg _
    have hCSpos : 0 < CS := lt_of_lt_of_le one_pos hCS1
    have hell : 0 < sideAt μ (a v) := adm_ell_pos ⟨hμ, hdil, hPOK⟩
    have hQQ : 0 ≤ ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
        * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) :=
      mul_nonneg (div_nonneg (le_of_lt (paramsAt_b_pos μ (a v)))
        (by positivity)) hcn
    have hSapp := hS' μ hAdmS n Φ
    obtain ⟨hRnn, hCapp⟩ := hC' μ hAdmC hJK n Φ hlow
    have hL := (isLowB_iff hav).mp hlow
    rw [Real.sqrt_eq_rpow] at hL
    -- (1) `Q + (1/CS)·∫ ≤ W` gives `∫ ≤ CS·(W − Q)`
    have h2 : (1 / CS) * (∫ u : ℝ³, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
        ≤ wordB v h μ n Φ - ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
            * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by linarith [hSapp]
    have hmul : CS * ((1 / CS) * (∫ u : ℝ³, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)))
        = (∫ u : ℝ³, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) := by
      field_simp
    have h1 : (∫ u : ℝ³, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
        ≤ CS * (wordB v h μ n Φ - ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
            * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_left h2 (le_of_lt hCSpos)
    -- (2) combine with the collected per-box bound and cancel the `(b/2ℓ²)⟨n₊⟩`
    have hsplit : CS * (wordB v h μ n Φ
          - ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
              * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
        = CS * wordB v h μ n Φ
          - CS * (((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
              * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)) := by ring
    have hCSQ : CS * (((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
            * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
        = ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
            * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          + (CS - 1) * (((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
              * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)) := by ring
    have hCSQnn : 0 ≤ (CS - 1) * (((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
          * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)) :=
      mul_nonneg (by linarith) hQQ
    have h2' : RPsi v h μ Φ
          + ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
              * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ CS * wordB v h μ n Φ
          + 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
              * (1 + CC * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * normB v μ n Φ := by
      have hBG := hCapp
      have hA : RPsi v h μ Φ + ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
            * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ (∫ u : ℝ³, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
            + 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
                * (1 + CC * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n Φ
            + ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
                * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by linarith [hBG]
      have hB : (∫ u : ℝ³, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
          ≤ CS * wordB v h μ n Φ
            - CS * (((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
                * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)) := by linarith [h1, hsplit]
      have hCc : CS * wordB v h μ n Φ
            - CS * (((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
                * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
            + 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
                * (1 + CC * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n Φ
            + ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
                * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ CS * wordB v h μ n Φ
            + 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
                * (1 + CC * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
                * normB v μ n Φ := by linarith [hCSQ, hCSQnn]
      linarith [hA, hB, hCc]
    -- (3) the background cancels against the low-state hypothesis
    have hCSW : CS * wordB v h μ n Φ
        ≤ CS * (-(4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
            * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) * normB v μ n Φ) :=
      mul_le_mul_of_nonneg_left hL (le_of_lt hCSpos)
    have hstep : RPsi v h μ Φ
          + ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
              * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ CS * (-(4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
              * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) * normB v μ n Φ)
          + 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
              * (1 + CC * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * normB v μ n Φ := by linarith [h2', hCSW]
    have heq : CS * (-(4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
              * (1 - J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))) * normB v μ n Φ)
          + 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
              * (1 + CC * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * normB v μ n Φ
        = 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * normB v μ n Φ
            * ((1 - CS) + CS * J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
                + CC * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
      ring
    have hKB1 : 1 ≤ (paramsAt μ (a v)).KB :=
      one_le_KB hμ (adm_a_pos ⟨hμ, hdil, hPOK⟩)
        (le_trans hdil (le_trans (min_le_right _ _) (min_le_right εC 1)))
    have hKB3nn : 0 ≤ (paramsAt μ (a v)).KB ^ 3 := by positivity
    have hbr : (1 - CS) + CS * J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
          + CC * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
        ≤ (CS + CC) * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := by
      have hJb : J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
          ≤ (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hJK htt
      nlinarith [hJb, hCS1, hCC0, htt, hKB3nn, mul_nonneg (le_of_lt hCSpos) htt,
        mul_nonneg (le_of_lt hCSpos) (mul_nonneg hKB3nn htt),
        mul_nonneg hCC0 (mul_nonneg hKB3nn htt)]
    have h7 : RPsi v h μ Φ
          + ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
              * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * (CS + CC)
            * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
            * normB v μ n Φ := by
      have heqT : 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * (CS + CC)
            * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) * normB v μ n Φ
          = 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * normB v μ n Φ
              * ((CS + CC) * (paramsAt μ (a v)).KB ^ 3
                  * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by ring
      have hnn : 0 ≤ 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * normB v μ n Φ := by
        have h1 : 0 < 4 * π := by nlinarith [Real.pi_gt_three]
        positivity
      rw [heqT]
      calc RPsi v h μ Φ
            + ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2))
                * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * normB v μ n Φ
              * ((1 - CS) + CS * J * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
                  + CC * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) := by
            rw [← heq]; exact hstep
        _ ≤ 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * normB v μ n Φ
              * ((CS + CC) * (paramsAt μ (a v)).KB ^ 3
                  * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hbr hnn
    -- the two target constants
    have h9 : 4 * π * (CS + CC) ≤ 4 * π * (CS + CC) + 1 := by linarith
    have h10 := mul_le_mul_of_nonneg_right h9
      (by positivity : (0 : ℝ) ≤ μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
      * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) * normB v μ n Φ)
    have h11 : 4 * π * (CS + CC) * (μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
        * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) * normB v μ n Φ)
      = 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * (CS + CC)
        * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) * normB v μ n Φ := by
      ring
    have h12 : (4 * π * (CS + CC) + 1) * (μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
        * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) * normB v μ n Φ)
      = (4 * π * (CS + CC) + 1) * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
        * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
        * normB v μ n Φ := by ring
    have h8 : 4 * π * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3 * (CS + CC)
        * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) * normB v μ n Φ
      ≤ (4 * π * (CS + CC) + 1) * μ ^ 2 * (a v) * sideAt μ (a v) ^ 3
          * (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ)
          * normB v μ n Φ := by
      linarith [h10, h11.le, h11.ge, h12.le, h12.ge]
    refine ⟨hRnn, ?_, ?_⟩
    · exact le_trans (le_add_of_nonneg_right hQQ) (le_trans h7 h8)
    · exact le_trans (le_add_of_nonneg_left hRnn) (le_trans h7 h8)

end Work.BoseFixB1
