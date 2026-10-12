import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.bqPotsplit
import Submission.Work.BoseFixB1B.matchedWindowDefs
import Submission.Work.BoseFixB1S.a0A2PaymentAdm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.matchedChainedBound` — the **matched-window** chained bound

Holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.  Decision (B) of the lead; the
vocabulary is `Submission/Work/BoseFixB1B/matchedWindowDefs.lean` (`sbKinCube`, `sbWordCube`).

## What this module adds, and why the frozen versions do not suffice

The frozen word `sbWord = sbKin + sbPot` mixes FS's two cutoffs: its **kinetic** slot
`sbKin = tBwordBend … (chiB …)` carries the *ball* window `chiB`, while its potential slot
`sbPot = qLHSwordB` carries the *cube* kernels `wSmall1Pair`/`wSmallPair` (window `chiSmallB`).
The proved Bogoliubov port `Work.BoseFixB1B.SlidingBogPort`
(`slidingBogPort_holds.lean` / `slidingBogPortProved.lean`) pays the pairing **at the cube
window** (`bSpectralCube + bA2`), so consuming it against the frozen `sbKin` needs the window
comparison `tBwordKinInd (chiSmallB) ≤ C · tBwordKinInd (chiB)`, which is **FALSE**: at every
admissible `u ∈ goodSet` whose two balls `ball(0,ℓ/2)`, `ball((ℓd)u, ℓd/2)` are disjoint one has
`chiB ≡ 0` while `chiSmallB > 0` on the box, so the frozen `sbKin` collapses to its gap row while
the port's spectral slot stays alive (`FINDING_perBoxFTotal_session2.md`, §2 of that note).

Running the chapter at the **single cube cutoff** (FS's own modelling, `eq:chiBdefinition`)
removes the comparison: the kinetic slot becomes `sbKinCube = bGapCoeff·n₊ + cubeSpectral` whose
window is exactly the port's.  This module supplies the first three *word-level* bricks of that
chapter — the exact matched-window analogues of

* `Work.BoseFixB1.perBoxF_pieces.sbKin_ge_gapPart`,
* `Work.BoseFixB1.perBoxF_pieces.sbKin_ge_mu_av_cnPlus` (FS `eq:appgapestimate`),
* `Work.BoseFixB1S.sbWord_ge_a0Main_add_boxA2` (the payment assembly),

with `sbKin ↦ sbKinCube` and `sbWord ↦ sbWordCube`, and **nothing else changed**.  All three are
window-generic *at the level of the payout*: the payment `Work.BoseFixB1S.a0A2PaymentAdm_holds`
(`PayProp`) and the potential split `Work.BoseFixB1.bqPotsplit` speak only about `qLHSwordB`
(i.e. `sbPot`), which the matched vocabulary does not touch, so the frozen proofs transcribe
verbatim.

The fourth brick the chapter needs — the **localisation** `SlidingBCube` (FS `eq:BSsliding2` /
Bratteli–Solovej Thm 3.10 at the cube cutoff, on record in `matchedWindowDefs.lean`) — is the
open analytic input and is *not* addressed here.

## Status

All three declarations below are `sorry`-free; see the module's FINDING for the axiom check.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix
  Work.SmallBoxSliding

/-! ## §1  The gap row of the matched word -/

/-- **The gap part of `sbKinCube`** — the matched-window analogue of
`Work.BoseFixB1.perBoxF_pieces.sbKin_ge_gapPart`: the gap coefficient times the excited count of
the sliding box is at most `sbKinCube`, because the spectral slot of `sbKinCube`
(`cubeSpectral`, FS `eq:appTB`'s second term at the cube cutoff) is a sum of `‖·‖²`-integrals
against a nonnegative symbol (`Work.BoseFixB1.tBwordKinInd_nonneg`). -/
lemma sbKinCube_ge_gapPart {v : E3 → ℝ} {μ : ℝ} {M : ℕ} {u : E3} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    Work.SmallBoxTBWord.tbGapCoeff ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      * Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ
      ≤ sbKinCube v μ u Φ := by
  have hgc : Work.BoseFixB1.bGapCoeff v μ
      = Work.SmallBoxTBWord.tbGapCoeff ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
    rw [Work.BoseFixB1.bGapCoeff, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, mul_comm]
  rw [sbKinCube, cubeSpectral, hgc]
  simp only [Work.BoseFixB1.bSide, Work.BoseFixB1.bA, Work.BoseFixB1.bV, Work.BoseFixB1.bM,
    Work.BoseFixB1.bD]
  have hnn : 0 ≤ Work.UBBInputs8.tBwordKinInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ :=
    Work.BoseFixB1.tBwordKinInd_nonneg Φ
  linarith

/-- **FS `eq:appgapestimate` in the matched vocabulary**: in the regime
`ε_T ≥ 2(1+π⁻²)(dℓ C'√(μ(a v)))²`, the excited count `n₊(B)` of the sliding box is paid by
`sbKinCube` at the coefficient `C'²μ(a v)`.  This is
`Work.BoseFixB1.perBoxF_pieces.sbKin_ge_mu_av_cnPlus` with `sbKin ↦ sbKinCube` (the `hker`
hypothesis is discharged internally by `sbKinCube_ge_gapPart`). -/
lemma sbKinCube_ge_mu_av_cnPlus {v : ℝ³ → ℝ} {μ c' : ℝ} {M : ℕ} {u : ℝ³} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ)
    (hav : 0 ≤ _root_.BoseGases.a v) (hμ : 0 ≤ μ) (hC' : 0 ≤ c')
    (hs : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hε : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (hreg : 2 * (1 + (Real.pi ^ 2)⁻¹)
        * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * c'
            * Real.sqrt (μ * (_root_.BoseGases.a v))) ^ 2
        ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT) :
    c' ^ 2 * μ * (_root_.BoseGases.a v)
      * Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ
      ≤ sbKinCube v μ u Φ := by
  have hgap : c' ^ 2 * μ * (_root_.BoseGases.a v) ≤ Work.SmallBoxTBWord.tbGapCoeff
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT :=
    Work.SmallBoxTBWord.gapCoeff_absorbs hav hμ hC' hε hs hreg
  have hnn : 0 ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ := by
    rw [Work.UBBInputs8.cnPlusBoxInd]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  calc c' ^ 2 * μ * (_root_.BoseGases.a v)
        * Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ
      ≤ Work.SmallBoxTBWord.tbGapCoeff ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        * Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ :=
        mul_le_mul_of_nonneg_right hgap hnn
    _ ≤ sbKinCube v μ u Φ := sbKinCube_ge_gapPart (v := v) (μ := μ) (M := M) (u := u) Φ

/-! ## §2  The matched-window chained bound (the payment assembly) -/

/-- **The matched-window assembly**: at FS's parameters, `Adm`-level, the *matched* sliding word
`sbWordCube = sbKinCube + sbPot` dominates the mean-field credit plus the pairing minus the
excitation credit — i.e. `Work.BoseFixB1S.sbWord_ge_a0Main_add_boxA2` with `sbKin ↦ sbKinCube`
and `sbWord ↦ sbWordCube`.  The proof is the frozen one verbatim: the payment
`Work.BoseFixB1S.a0A2PaymentAdm_holds` and the split `Work.BoseFixB1.bqPotsplit` speak only
about `qLHSwordB = sbPot`, which the matched vocabulary leaves untouched. -/
theorem sbWordCube_ge_a0Main_add_boxA2 {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : E3),
          0 < Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u →
          (1 : ℝ) ≤ μ * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u →
          (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1 →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
            (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 →
              ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
          0 ≤ Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
          Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h)) →
          0 ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
              * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
            - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1.a0MainLocBox (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) μ
              (Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u))
              (Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ))
            + Work.BoseFixB1.boxA2 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ)
            + sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ)
            - C * (_root_.BoseGases.a v)
                * (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
                    / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) (Φ : Submission.BoseGases.X n → ℝ)
          ≤ sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨εp, C, hεp, hC, hpay⟩ := Work.BoseFixB1S.a0A2PaymentAdm_holds h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εg, hεg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min εp εg, C, lt_min hεp hεg, hC, ?_⟩
  intro μ hAdm n Φ u hvol hμv hnorm hsupp hM1nn hM2 hPcnn hcS2
  have hAdmp : Work.BoseBoxFix.Adm v εp μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmg : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  obtain ⟨hR16, hRχ⟩ := hreg μ hAdm.1 (Work.BoseFixB1.adm_dilute hAdmg)
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hMv : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hpay' := hpay μ hAdmp n Φ u hvol hμv hnorm hsupp hM1nn hM2 hPcnn hcS2
  have hpot := Work.BoseFixB1.bqPotsplit (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
    (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hMv
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μ)
    hℓ hd hR16 hRχ u hvol (N := n) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff.continuous
  rw [sbWordCube, Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB]
  linarith [hpay', hpot]

end Work.BoseFixB1B
