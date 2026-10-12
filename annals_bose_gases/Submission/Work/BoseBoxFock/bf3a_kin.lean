import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.bf3a_cnplus
import Submission.Work.BoseBoxFock.bf3a_fibre
import Submission.Work.BoseFixB2.DvApriori.KinOffdiag.pieces_integrableOn_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.bf3a_kin` — BF3a, the kinetic rows

FS §8 `prop:Hamilton2ndQuant`'s kinetic comparison, isolated: the first-quantised `H_Λ^{2nd}`
kinetic word

`W2kinB v μ n Φ = kinTauB + (b/2ℓ²)·cnPlus + (ε_Tb/2d²ℓ²)·nPlusHB`

is dominated by the *sharp* box kinetic word `kinFormB`, for every box state `Φ` at admissible
`μ`, with `C = 0` (the requested error term is not needed: the *sharp* `mainWord` row of
`kinFormB` already dominates the smoothed `τ̃`-row, and the full Neumann/large-momentum gaps
dominate their halves).

The proof is the slot-sum bookkeeping:

* per slot `i` and per configuration `x`, `bsOneBody ℓ (tauSmRad …) 0 (fibreᵢ Φ x)`
  is dominated by `mainWord` (`bf3a_fibre`, the one-body symbol comparison
  `τ̃ ≤ τ`: `tauProf ≤ (· − 1)₊²`);
* `kinFormB = ℓ⁻³ Σᵢ ∫ 1_{Λ}(xᵢ)·fsT(fibreᵢ)` with `fsT = neuWord + gapWord + momWord + mainWord`,
  all four pieces nonnegative in FS's regime (`fsT_nonneg_of_continuous`, `gapWord_nonneg`,
  `momWord_nonneg`, `mainWord_nonneg`, plus `neuWord_nonneg_of_continuous`);
* the slot integrands are integrable on the box (`integrableOn_fsT_fibre_smooth` for `fsT`,
  `pieces_integrableOn_fibre` for the gap/momentum rows compared), so the slot integrals
  linearise;
* `Σᵢ ∫ 1_{Λ}(xᵢ)·gapBare(fibreᵢ) = ℓ³·cnPlus` (`bf3a_cnplus`), and the analogous identity for
  `momForm`/`nPlusHB` is the definition, so the halves match `(b/2ℓ²)cnPlus` and
  `(ε_Tb/2d²ℓ²)nPlusHB`.
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Metric Filter

namespace Work.BoseBoxFock

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix
open Work.BoseKinLoc Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. Nonnegativity of the Neumann word for continuous states -/

/-- The Neumann word is nonnegative for a merely continuous one-body state (the box
`Λ(u)` is compact, so the mean-free square of the state is integrable there). -/
lemma neuWord_nonneg_of_continuous {ℓ d eT : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (heT0 : 0 ≤ eT) {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) :
    0 ≤ neuWord ℓ d eT 0 ψ := by
  have hdℓ : 0 < d * ℓ := mul_pos hd hℓ
  have hcont : Continuous (Qfree ℓ 0 ψ) := hψ.sub continuous_const
  have hI : Integrable (fun z : ℝ³ => (Qfree ℓ 0 ψ z) ^ 2)
      (volume.restrict (lamBox ℓ 0)) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (ℓ • (0 : ℝ³)) (2 * (|ℓ| + 1)))
      (hcont.pow 2).continuousOn).mono_set
        (Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ 0)
  have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg hdℓ.le _
  have hn := Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2 ℓ ((d * ℓ) ^ (-2 : ℤ)) ha2 0
    (Qfree ℓ 0 ψ) hI
  unfold neuWord
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) heT0) ha2) hn

/-! ## 2. The per-slot inequality -/

private lemma slot_le {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (hd : 0 < d)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hb : 0 ≤ b)
    {n : ℕ} (i : Fin n) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∫ x in abox n ℓ, indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x))
      + (1 / 2) * (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))
      + (1 / 2) * (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))
    ≤ ∫ x in abox n ℓ, indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x) := by
  have hfib : ∀ x : Submission.BoseGases.X n, ContDiff ℝ (⊤ : ℕ∞) (fibre n i Φ x) :=
    fun x => hΦ.comp (contDiff_update (⊤ : ℕ∞) x i)
  obtain ⟨hIgap, hImom, -, -⟩ :=
    Work.BoseFixB2.DvApriori.KinOffdiag.pieces_integrableOn_fibre (ℓ := ℓ) (d := d) (s := s)
      (εT := eT) (b := b) hℓ i hΦ
  have hIfs :=
    Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s)
      (εT := eT) (b := b) hℓ i hΦ
  -- integrability of the dominating "difference" integrand
  have hDint : Integrable (fun x : Submission.BoseGases.X n =>
      indU ℓ 0 (x i) * (fsT ℓ d s eT b 0 (fibre n i Φ x) - gapWord ℓ b 0 (fibre n i Φ x)
        - momWord ℓ d eT b 0 (fibre n i Φ x))) (volume.restrict (abox n ℓ)) := by
    refine ((hIfs.sub hIgap).sub hImom).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  -- the `τ̃`-row is dominated by the difference integrand
  have hmono : (∫ x in abox n ℓ,
        indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x))
      ≤ ∫ x in abox n ℓ, indU ℓ 0 (x i) *
          (fsT ℓ d s eT b 0 (fibre n i Φ x) - gapWord ℓ b 0 (fibre n i Φ x)
            - momWord ℓ d eT b 0 (fibre n i Φ x)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hDint ?_
    · filter_upwards with x
      simp only [Pi.zero_apply]
      exact mul_nonneg (Word.kinFormB_indU_nonneg ℓ 0 (x i))
        (bsOneBody_nonneg (fun r => tauSmRad_nonneg heT0 heT1 r) 0 (fibre n i Φ x))
    · filter_upwards with x
      have hnd : 0 ≤ indU ℓ 0 (x i) := Word.kinFormB_indU_nonneg ℓ 0 (x i)
      have hK := bf3a_fibre hℓ hs hd heT0 heT1 (fibre n i Φ x) (hfib x)
      have hneu := neuWord_nonneg_of_continuous hℓ hd heT0 (hfib x).continuous
      have hcore' : bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x)
          ≤ fsT ℓ d s eT b 0 (fibre n i Φ x) - gapWord ℓ b 0 (fibre n i Φ x)
            - momWord ℓ d eT b 0 (fibre n i Φ x) := by
        rw [fsT_eq_sum]
        linarith
      exact mul_le_mul_of_nonneg_left hcore' hnd
  -- the difference integral linearises
  have hsub1 : (∫ x in abox n ℓ,
        (indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x)
          - indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)))
      = (∫ x in abox n ℓ, indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x))
        - (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)) :=
    MeasureTheory.integral_sub hIfs hIgap
  have hsub2 : (∫ x in abox n ℓ,
        (indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x)
          - indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)
          - indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)))
      = (∫ x in abox n ℓ,
          (indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x)
            - indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)))
        - (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)) :=
    MeasureTheory.integral_sub (hIfs.sub hIgap) hImom
  have hcongr : (∫ x in abox n ℓ, indU ℓ 0 (x i) *
        (fsT ℓ d s eT b 0 (fibre n i Φ x) - gapWord ℓ b 0 (fibre n i Φ x)
          - momWord ℓ d eT b 0 (fibre n i Φ x)))
      = ∫ x in abox n ℓ,
          (indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x)
            - indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)
            - indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)) :=
    MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hlin : (∫ x in abox n ℓ, indU ℓ 0 (x i) *
        (fsT ℓ d s eT b 0 (fibre n i Φ x) - gapWord ℓ b 0 (fibre n i Φ x)
          - momWord ℓ d eT b 0 (fibre n i Φ x)))
      = (∫ x in abox n ℓ, indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x))
        - (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))
        - (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)) :=
    hcongr.trans (hsub2.trans (congrArg₂ (· - ·) hsub1 rfl))
  -- nonnegativity of the two gap integrals
  have hgap0 : 0 ≤ ∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x) :=
    integral_nonneg fun x => mul_nonneg (Word.kinFormB_indU_nonneg ℓ 0 (x i))
      (gapWord_nonneg hb hℓ.le 0 (fibre n i Φ x))
  have hmom0 : 0 ≤ ∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x) :=
    integral_nonneg fun x => mul_nonneg (Word.kinFormB_indU_nonneg ℓ 0 (x i))
      (momWord_nonneg hb heT0 (mul_nonneg hd.le hℓ.le) 0 (fibre n i Φ x))
  linarith [hmono, hlin, hgap0, hmom0]

/-! ## 3. The kinetic-row bound `W2kinB ≤ kinFormB` -/

/-- **BF3a, kinetic rows.**  `W2kinB` is dominated by the box kinetic word `kinFormB`. -/
private lemma W2kinB_le_kinFormB {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (hd : 0 < d)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hb : 0 ≤ b)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    kinTauB n ℓ d s eT Φ + (b / 2) * ℓ ^ (-2 : ℤ) * cnPlus ℓ Φ
        + (eT * b / (2 * d ^ 2 * ℓ ^ 2)) * nPlusHB ℓ d Φ
      ≤ kinFormB n ℓ d s eT b Φ := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  -- the power identities `ℓ⁻³ ℓ³ = 1` and `ℓ³ ℓ⁻³ = 1`
  have hz : ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 := by
    rw [← zpow_natCast ℓ 3, ← zpow_add₀ hℓne]
    norm_num
  have hz' : ℓ ^ 3 * ℓ ^ (-3 : ℤ) = 1 := by
    rw [← zpow_natCast ℓ 3, ← zpow_add₀ hℓne]
    norm_num
  -- `kinTauB` as a slot sum
  have hA : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        (∫ x in abox n ℓ, indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x)))
      = kinTauB n ℓ d s eT Φ := by
    simp only [kinTauB, slotFormB]
  -- `kinFormB` as a slot sum
  have hD : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        (∫ x in abox n ℓ, indU ℓ 0 (x i) * fsT ℓ d s eT b 0 (fibre n i Φ x)))
      = kinFormB n ℓ d s eT b Φ := by
    rw [kinFormB, ← Finset.mul_sum]
  -- the gap slot sum: pull `b ℓ⁻²` out of each slot integral, then peel (`bf3a_cnplus`)
  have hgapSum : (∑ i : Fin n, ∫ x in abox n ℓ,
        indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))
      = b * ℓ ^ (-2 : ℤ) * (ℓ ^ 3 * cnPlus ℓ Φ) := by
    have h1 : ∀ i : Fin n, (∫ x in abox n ℓ,
          indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))
        = (b * ℓ ^ (-2 : ℤ)) * (∫ x in abox n ℓ,
            indU ℓ 0 (x i) * gapBare ℓ 0 (fibre n i Φ x)) := by
      intro i
      have hpt : ∀ x : Submission.BoseGases.X n,
          indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)
            = (b * ℓ ^ (-2 : ℤ)) * (indU ℓ 0 (x i) * gapBare ℓ 0 (fibre n i Φ x)) := by
        intro x
        simp only [Work.BoseKinLoc.gapWord]
        ring
      calc (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))
          = ∫ x in abox n ℓ,
              (b * ℓ ^ (-2 : ℤ)) * (indU ℓ 0 (x i) * gapBare ℓ 0 (fibre n i Φ x)) :=
            MeasureTheory.integral_congr_ae (Eventually.of_forall hpt)
        _ = (b * ℓ ^ (-2 : ℤ)) *
              (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapBare ℓ 0 (fibre n i Φ x)) :=
            MeasureTheory.integral_const_mul _ _
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum, bf3a_cnplus hℓ hΦ]
  have hB : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)))
      = b * ℓ ^ (-2 : ℤ) * cnPlus ℓ Φ := by
    rw [← Finset.mul_sum, hgapSum]
    rw [show ℓ ^ (-3 : ℤ) * (b * ℓ ^ (-2 : ℤ) * (ℓ ^ 3 * cnPlus ℓ Φ))
        = (ℓ ^ (-3 : ℤ) * ℓ ^ 3) * (b * ℓ ^ (-2 : ℤ) * cnPlus ℓ Φ) by ring, hz, one_mul]
  -- the momentum slot sum: pull the coefficient out, then use the definition of `nPlusHB`
  have hmomSum : (∑ i : Fin n, ∫ x in abox n ℓ,
        indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))
      = b * eT * (d * ℓ) ^ (-2 : ℤ) * (ℓ ^ 3 * nPlusHB ℓ d Φ) := by
    have h1 : ∀ i : Fin n, (∫ x in abox n ℓ,
          indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))
        = (b * eT * (d * ℓ) ^ (-2 : ℤ)) * (∫ x in abox n ℓ,
            indU ℓ 0 (x i) * momForm ℓ d 0 (fibre n i Φ x)) := by
      intro i
      have hpt : ∀ x : Submission.BoseGases.X n,
          indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)
            = (b * eT * (d * ℓ) ^ (-2 : ℤ)) *
                (indU ℓ 0 (x i) * momForm ℓ d 0 (fibre n i Φ x)) := by
        intro x
        simp only [Work.BoseKinLoc.momWord]
        ring
      calc (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))
          = ∫ x in abox n ℓ,
              (b * eT * (d * ℓ) ^ (-2 : ℤ)) *
                (indU ℓ 0 (x i) * momForm ℓ d 0 (fibre n i Φ x)) :=
            MeasureTheory.integral_congr_ae (Eventually.of_forall hpt)
        _ = (b * eT * (d * ℓ) ^ (-2 : ℤ)) *
              (∫ x in abox n ℓ, indU ℓ 0 (x i) * momForm ℓ d 0 (fibre n i Φ x)) :=
            MeasureTheory.integral_const_mul _ _
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.mul_sum]
    congr 1
    have hS : nPlusHB ℓ d Φ = ℓ ^ (-3 : ℤ) *
        (∑ i : Fin n, ∫ x in abox n ℓ, indU ℓ 0 (x i) * momForm ℓ d 0 (fibre n i Φ x)) := rfl
    rw [hS, ← mul_assoc, hz', one_mul]
  have hC : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)))
      = b * eT * (d * ℓ) ^ (-2 : ℤ) * nPlusHB ℓ d Φ := by
    rw [← Finset.mul_sum, hmomSum]
    rw [show ℓ ^ (-3 : ℤ) * (b * eT * (d * ℓ) ^ (-2 : ℤ) * (ℓ ^ 3 * nPlusHB ℓ d Φ))
        = (ℓ ^ (-3 : ℤ) * ℓ ^ 3) * (b * eT * (d * ℓ) ^ (-2 : ℤ) * nPlusHB ℓ d Φ) by ring,
      hz, one_mul]
  -- the summed slot inequality, with the left side distributed
  have hsum0 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (slot_le (ℓ := ℓ) (d := d) (s := s) (eT := eT) (b := b) hℓ hs hd heT0 heT1 hb i hΦ)
      (zpow_nonneg hℓ.le (-3 : ℤ)))
  have hstep : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        ((∫ x in abox n ℓ, indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x))
          + (1 / 2) * (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))
          + (1 / 2) * (∫ x in abox n ℓ,
              indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))))
      = ∑ i : Fin n, (ℓ ^ (-3 : ℤ) *
              (∫ x in abox n ℓ, indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x))
          + (1 / 2) * (ℓ ^ (-3 : ℤ) *
              (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)))
          + (1 / 2) * (ℓ ^ (-3 : ℤ) *
              (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x)))) :=
    Finset.sum_congr rfl fun i _ => by ring
  have hL : (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
        ((∫ x in abox n ℓ, indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x))
          + (1 / 2) * (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))
          + (1 / 2) * (∫ x in abox n ℓ,
              indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))))
      = (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
            (∫ x in abox n ℓ, indU ℓ 0 (x i) * bsOneBody ℓ (tauSmRad eT s d ℓ) 0 (fibre n i Φ x)))
        + (1 / 2) * (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
            (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x)))
        + (1 / 2) * (∑ i : Fin n, ℓ ^ (-3 : ℤ) *
            (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))) := by
    rw [hstep, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.mul_sum (s := Finset.univ)
          (f := fun i : Fin n => ℓ ^ (-3 : ℤ) *
            (∫ x in abox n ℓ, indU ℓ 0 (x i) * gapWord ℓ b 0 (fibre n i Φ x))) (a := 1 / 2),
      ← Finset.mul_sum (s := Finset.univ)
          (f := fun i : Fin n => ℓ ^ (-3 : ℤ) *
            (∫ x in abox n ℓ, indU ℓ 0 (x i) * momWord ℓ d eT b 0 (fibre n i Φ x))) (a := 1 / 2)]
  rw [hL] at hsum0
  rw [hA, hB, hC, hD] at hsum0
  -- rewrite the coefficients into the `W2kinB` shape
  have e1 : (1 / 2) * (b * ℓ ^ (-2 : ℤ) * cnPlus ℓ Φ) = (b / 2) * ℓ ^ (-2 : ℤ) * cnPlus ℓ Φ := by
    ring
  have hcoef : b * eT * (d * ℓ) ^ (-2 : ℤ) = eT * b / (d ^ 2 * ℓ ^ 2) := by
    field_simp
  have e2 : (1 / 2) * (b * eT * (d * ℓ) ^ (-2 : ℤ) * nPlusHB ℓ d Φ)
      = (eT * b / (2 * d ^ 2 * ℓ ^ 2)) * nPlusHB ℓ d Φ := by
    rw [hcoef]
    ring
  rw [e1, e2] at hsum0
  exact hsum0

/-! ## 4. The target -/

theorem bf3a_kin (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) {R : ℝ} (hav : 0 < BoseGases.a v) :
    ∃ C ε₀ : ℝ, 0 ≤ C ∧ 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          Work.BoseBoxFock.W2kinB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              - C * Work.BoseBoxFock.errB v R μ * Work.BoseBoxFix.normB v μ n Φ
            ≤ Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
                (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
                (Φ : Submission.BoseGases.X n → ℝ) := by
  refine ⟨0, 1, le_rfl, one_pos, ?_⟩
  intro μ hAdm n Φ _
  obtain ⟨hμ, ht1, _⟩ := hAdm
  have ha : 0 < BoseGases.a v := hav
  have hμa : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  let P : Work.BoseBox.FSParams := Work.BoseBox.paramsAt μ (BoseGases.a v)
  let ℓ : ℝ := Work.BoseBox.sideAt μ (BoseGases.a v)
  have hpar : P = Work.BoseBox.fsParams (μ * (BoseGases.a v) ^ 3) := rfl
  have hs : 0 < P.s := by
    rw [hpar]; exact Work.BoseBox.fsXp_pos hμa
  have hd : 0 < P.d := by
    rw [hpar]; exact Work.BoseBox.fsXp_pos hμa
  have hKl : 0 < P.Kl := by
    rw [hpar]; exact Work.BoseBox.fsXp_pos hμa
  have heT0 : 0 ≤ P.eT := by
    rw [hpar]
    exact le_of_lt (Work.BoseBox.fsXp_pos hμa)
  have heT1 : P.eT ≤ 1 := by
    rw [hpar]
    exact Work.BoseBox.fsXp_le_one hμa ht1 (by norm_num)
  have hb : 0 ≤ P.b := by
    rw [hpar]
    simp only [Work.BoseBox.fsParams, Work.BoseBox.bValue]
    norm_num
  have hℓpos : 0 < ℓ := by
    show 0 < Work.BoseBox.sideAt μ (BoseGases.a v)
    rw [Work.BoseBox.sideAt, Work.BoseBox.boxSide]
    exact mul_pos hKl (Real.rpow_pos_of_pos (by positivity) _)
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff
  have hexp : W2kinB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      = kinTauB n ℓ P.d P.s P.eT (Φ : Submission.BoseGases.X n → ℝ)
        + (P.b / 2) * ℓ ^ (-2 : ℤ) * cnPlus ℓ (Φ : Submission.BoseGases.X n → ℝ)
        + (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)) * nPlusHB ℓ P.d
            (Φ : Submission.BoseGases.X n → ℝ) := rfl
  rw [hexp]
  have hmain := W2kinB_le_kinFormB (ℓ := ℓ) (d := P.d) (s := P.s) (eT := P.eT) (b := P.b)
    hℓpos hs hd heT0 heT1 hb hΦ
  have hzero : (0 : ℝ) * errB v R μ * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 :=
    by ring
  linarith [hmain, hzero]

end Work.BoseBoxFock
