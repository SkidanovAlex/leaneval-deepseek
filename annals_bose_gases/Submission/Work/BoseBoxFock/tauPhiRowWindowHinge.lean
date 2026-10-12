import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.deficit_window_bounds
import Submission.Work.BoseBoxFock.ledgerParen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tauPhiRowWindowHinge` — the χ_Λ-windowed spine: the hinge row implies the
windowed row

The corpus's route to the general row is

    `tauPhi_row`  ⟸  `tauPhi_row_of_hinge`  +  `hingeRow`   ( ⟸ `sTailRow`, open ) ,

where `hingeRow` (`hingeRow.lean`) is *proved* from the open tail row `sTailRow`.  This file adds
the **windowed** stretch of the chain, i.e. the one that runs through the χ_Λ-class

    `g = χ_Λ·h`  (`h` smooth, compactly supported, `tsupport h ⊆ boxL ℓ`),

which is exactly the class the corpus's `deficitAlias_*` machinery
(`deficitAlias_shiftstab`, `kinFirst_sub_latMoment_eq_imageSplit`, `deficitAlias_touching_image_le`,
`farImageSum_le_eighth_kinFirst`) is stated for:

* **`tauPhi_row_of_hingeSmooth`** — the hinge inequality implies the tauPhi row for every
  `C^∞`-smooth compactly supported `g`, with **no support hypothesis at all** (the open-ball
  hypothesis of `Work.BoseBoxFock.tauPhi_row_of_hinge` is not used anywhere in its proof; only
  the pointwise domination `c²·tauPhi(r/c) ≤ (max 0 (r − 5c/4))²` and the quadratic summability
  are, and both are support-free);
* **`windowed_contDiff`, `windowed_hasCompactSupport`, `windowed_tsupport_subset`** — the
  class-closure facts: a windowed state is `C^∞`, compactly supported, and supported in
  `closedBall 0 (ℓ/2)`;
* **`tauPhiRowWindow_of_hingeWindow`** — hence the χ_Λ-windowed row follows from the *windowed*
  hinge row.  So a proof of `sTailRow`-type statement restricted to the windowed class closes
  `Work.BoseBoxFock.tauPhiRowWindow` (and, through `tauPhi_row_of_windowed` +
  `chiLamFactorLift`, the general `tauPhi_row` as well).

Note the support facts are the ones the windowed class *does* give: `closedBall`, not `ball`
(§7 of `FINDING_kinRow_lattice_tauPhi_session4.md` shows the open ball is not available here —
the window can only force `h = ψ − m` on the open ball, and the six face midpoints obstruct the
open-ball support).  That is why `tauPhi_row_of_hingeSmooth` is stated support-free.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

/-- `χ_Λ` is smooth (`corpusBox.chiLam ℓ = chiScale ℓ`). -/
lemma chiLam_contDiff' {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ContDiff ℝ (⊤ : ENat) (Work.BoseK15.corpusBox.chiLam ℓ) := by
  have h : Work.BoseK15.corpusBox.chiLam ℓ = Submission.BoseGases.chiScale ℓ := rfl
  rw [h]
  exact Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)

/-- `χ_Λ` is supported in the closed ball of radius `ℓ/2`. -/
lemma chiLam_tsupport_subset' {ℓ : ℝ} (hℓ : 0 < ℓ) :
    tsupport (Work.BoseK15.corpusBox.chiLam ℓ) ⊆ Metric.closedBall 0 (ℓ / 2) := by
  have h : Function.support (Work.BoseK15.corpusBox.chiLam ℓ) ⊆ Metric.closedBall 0 (ℓ / 2) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Submission.BoseGases.chiScale_support_le hℓ hx
  exact closure_minimal h Metric.isClosed_closedBall

/-- **The hinge row implies the tauPhi row**, with no support hypothesis on `g` (only `C^∞` and
compact support, which is what the quadratic summability needs).  This is the minimal-hypothesis
form of `Work.BoseBoxFock.tauPhi_row_of_hinge`. -/
theorem tauPhi_row_of_hingeSmooth {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hhinge : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (max 0 (‖kmomInt ℓ n‖ - 5 * c / 4)) ^ 2 *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  -- the hinge is controlled by a quadratic
  have hquad : ∀ r : ℝ, 0 ≤ r → (max 0 (r - 5 * c / 4)) ^ 2 ≤ 2 * r ^ 2 + (25 / 8) * c ^ 2 := by
    intro r _
    have h1 : (max 0 (r - 5 * c / 4)) ^ 2 ≤ (r - 5 * c / 4) ^ 2 := by
      have hm : max 0 (r - 5 * c / 4) ≤ |r - 5 * c / 4| :=
        max_le (abs_nonneg _) (le_abs_self _)
      have h0 : 0 ≤ max 0 (r - 5 * c / 4) := le_max_left _ _
      calc (max 0 (r - 5 * c / 4)) ^ 2 ≤ |r - 5 * c / 4| ^ 2 :=
            pow_le_pow_left₀ h0 hm 2
        _ = (r - 5 * c / 4) ^ 2 := by rw [sq_abs]
    have h2 : (r - 5 * c / 4) ^ 2 ≤ 2 * r ^ 2 + (25 / 8) * c ^ 2 := by
      have key : 2 * r ^ 2 + (25 / 8) * c ^ 2 - (r - 5 * c / 4) ^ 2
          = (r + 5 * c / 4) ^ 2 := by ring
      linarith [sq_nonneg (r + 5 * c / 4)]
    linarith
  have hF0 : ∀ r : ℝ, 0 ≤ (max 0 (r - 5 * c / 4)) ^ 2 := fun r => sq_nonneg _
  have hHsum : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ *
      (max 0 (‖kmomInt ℓ n‖ - 5 * c / 4)) ^ 2 *
      ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) :=
    summable_of_quad_growth (ℓ := ℓ) (A := 2) (B := (25 / 8) * c ^ 2)
      (F := fun r : ℝ => (max 0 (r - 5 * c / 4)) ^ 2) hℓ hg hgc hF0 hquad
  have hG0 : ∀ r : ℝ, 0 ≤ c ^ 2 * tauPhi (r / c) :=
    fun r => mul_nonneg (sq_nonneg c) (tauPhi_nonneg _)
  have hGquad : ∀ r : ℝ, 0 ≤ r → c ^ 2 * tauPhi (r / c)
      ≤ 2 * r ^ 2 + ((25 / 8) * c ^ 2) :=
    fun r hr => le_trans (rescaled_tauPhi_le_conv hc hr) (hquad r hr)
  have hGsum : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c))
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) :=
    summable_of_quad_growth (ℓ := ℓ) (A := 2) (B := (25 / 8) * c ^ 2)
      (F := fun r : ℝ => c ^ 2 * tauPhi (r / c)) hℓ hg hgc hG0 hGquad
  -- the pointwise domination `τ̃_c ≤ (· − 5c/4)₊²`
  have hpt : ∀ n : Fin 3 → ℤ,
      (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c))
          * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        ≤ (ℓ ^ 3)⁻¹ * (max 0 (‖kmomInt ℓ n‖ - 5 * c / 4)) ^ 2
          * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
    intro n
    have h1 : c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)
        ≤ (max 0 (‖kmomInt ℓ n‖ - 5 * c / 4)) ^ 2 :=
      rescaled_tauPhi_le_conv hc (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity))
      (sq_nonneg _)
  exact le_trans (hGsum.tsum_le_tsum hpt hHsum) hhinge

/-! ## The class-closure facts for the χ_Λ-windowed class -/

/-- A windowed state is smooth. -/
lemma windowed_contDiff {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hclass : ∃ h : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ (⊤ : ENat) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ Work.BoseK15.corpusBox.boxL ℓ ∧
        (∀ z, g z = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * h z)) :
    ContDiff ℝ (⊤ : ENat) g := by
  obtain ⟨h, hh, -, -, hgeq⟩ := hclass
  have h1 : ContDiff ℝ (⊤ : ENat)
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (chiLam_contDiff' hℓ)
  have h2 := h1.mul hh
  rw [show g = fun z => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * h z from
    funext hgeq]
  exact h2

/-- A windowed state has compact support. -/
lemma windowed_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hclass : ∃ h : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ (⊤ : ENat) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ Work.BoseK15.corpusBox.boxL ℓ ∧
        (∀ z, g z = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * h z)) :
    HasCompactSupport g := by
  obtain ⟨h, -, -, -, hgeq⟩ := hclass
  have hcs : HasCompactSupport (Work.BoseK15.corpusBox.chiLam ℓ) := by
    have h : Work.BoseK15.corpusBox.chiLam ℓ = Submission.BoseGases.chiScale ℓ := rfl
    rw [h]
    exact Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)
  have hsub : tsupport g ⊆ tsupport (Work.BoseK15.corpusBox.chiLam ℓ) := by
    rw [tsupport, tsupport]
    refine closure_mono fun z hz => ?_
    intro hzero
    simp only [Function.mem_support] at hz
    rw [hgeq z, hzero, Complex.ofReal_zero, zero_mul] at hz
    exact hz rfl
  exact hcs.of_isClosed_subset (isClosed_tsupport _) hsub

/-- A windowed state is supported in the closed ball of radius `ℓ/2`. -/
lemma windowed_tsupport_subset {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hclass : ∃ h : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ (⊤ : ENat) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ Work.BoseK15.corpusBox.boxL ℓ ∧
        (∀ z, g z = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * h z)) :
    tsupport g ⊆ Metric.closedBall 0 (ℓ / 2) := by
  have hsub : tsupport g ⊆ tsupport (Work.BoseK15.corpusBox.chiLam ℓ) := by
    obtain ⟨h, -, -, -, hgeq⟩ := hclass
    rw [tsupport, tsupport]
    refine closure_mono fun z hz => ?_
    intro hzero
    simp only [Function.mem_support] at hz
    rw [hgeq z, hzero, Complex.ofReal_zero, zero_mul] at hz
    exact hz rfl
  exact hsub.trans (chiLam_tsupport_subset' hℓ)

/-- **The χ_Λ-windowed row follows from the *windowed* hinge row.** -/
theorem tauPhiRowWindow_of_hingeWindow {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hclass : ∃ h : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ (⊤ : ENat) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ Work.BoseK15.corpusBox.boxL ℓ ∧
        (∀ z, g z = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * h z))
    (hhinge : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (max 0 (‖kmomInt ℓ n‖ - 5 * c / 4)) ^ 2 *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
  tauPhi_row_of_hingeSmooth hℓ hc (windowed_contDiff hℓ hclass)
    (windowed_hasCompactSupport hℓ hclass) hhinge

/-! ## The deficit-language entry point for the windowed class

The corpus's route `tauPhi_row ⟸ tauPhi_row_of_deficit + hdef` is stated at the **open** ball
(`tsupport g ⊆ Metric.ball 0 (ℓ/2)`), and its proof converts that to the *closed* ball before
calling the PROVED `tauPhi_row_lattice_of_deficit` — which takes the closed ball directly.  The
windowed class supplies exactly the closed ball (`windowed_tsupport_subset`), so the deficit route
applies to it verbatim.  This matters because the corpus's *proved* exact evaluations
(`latDeficit_eq_regions`, `deficit_window_bounds`, `nu_tauTheta_eq_truncated`, `latDeficit_ge_window`,
`row_of_window`) are all stated in this deficit language, i.e. on precisely this class. -/

/-- **The χ_Λ-windowed row follows from the *windowed* deficit form** `hdef` (the same
`deficit`/`tauPsi`/`tauTheta` inequality that `Work.BoseBoxFock.tauPhi_row_of_deficit` consumes). -/
theorem tauPhiRowWindow_of_deficitWindow {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hclass : ∃ h : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ (⊤ : ENat) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ Work.BoseK15.corpusBox.boxL ℓ ∧
        (∀ z, g z = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * h z))
    (hdef : c * (3 * (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
              * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
            - 2 * (((2 * Real.pi) ^ 3)⁻¹
              * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2))
          + (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
              * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
          - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2
        ≥ (5 / 4 + tauC0phi) * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹
            * ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
  tauPhi_row_lattice_of_deficit hℓ hc (windowed_contDiff hℓ hclass)
    (windowed_hasCompactSupport hℓ hclass) (windowed_tsupport_subset hℓ hclass) hdef

/-! ## (WIN) at the windowed class: the third entry point

`row_of_window` (`row_of_window.lean`, PROVED) shows that the **window-samples** inequality

    (WIN)   2c·(C(‖·‖) − L(‖·‖))  ≤  Σ_{c<‖kₙ‖<2c} ℓ⁻³((‖kₙ‖−c)² − [‖kₙ‖−5c/4]₊²)‖ĉ(kₙ)‖²
                                    + lowGain ℓ c g

implies the row, via `latDeficit_ge_window` + the canonical ledger identity
`ledger_eq_deficitForm_paren` + `tauPhi_row_of_sharpAlias`.  Reading those proofs: the support
hypothesis `tsupport g ⊆ Metric.ball 0 (ℓ/2)` they all carry is *never used* —

* `latDeficit_ge_window` is flagged `set_option linter.unusedVariables false` and its body only uses
  `hg`, `hgc` (`deficit_window_bounds`, `summable_latDeficit`);
* the ledger identity's body passes the *converted* (closed-ball) containment to
  `latDeficit_add_latTheta`, which takes **no support argument at all**.

The windowed class supplies exactly that closed ball (`windowed_tsupport_subset`), so (WIN) is
usable there too.  This is the third, and sharpest, entry point into `tauPhiRowWindow`: (WIN) is
*strictly stronger* than the row, but its payers are the explicit window samples, which is where
the proved `latDeficit_eq_regions` / `deficit_window_bounds` / `nu_tauTheta_eq_truncated` live. -/

/-- `latDeficit_ge_window` **without the support hypothesis** (which its proof does not use). -/
theorem latDeficit_ge_window_smooth {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    (∑' n : Fin 3 → ℤ, if c < ‖kmomInt ℓ n‖ ∧ ‖kmomInt ℓ n‖ < 2 * c then
          (ℓ ^ 3)⁻¹ * ((‖kmomInt ℓ n‖ - c) ^ 2 - (max 0 (‖kmomInt ℓ n‖ - 5 * c / 4)) ^ 2)
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        else (0 : ℝ))
      ≤ latDeficit ℓ c g := by
  classical
  have hpt : ∀ n : Fin 3 → ℤ,
      (if c < ‖kmomInt ℓ n‖ ∧ ‖kmomInt ℓ n‖ < 2 * c then
          (ℓ ^ 3)⁻¹ * ((‖kmomInt ℓ n‖ - c) ^ 2 - (max 0 (‖kmomInt ℓ n‖ - 5 * c / 4)) ^ 2)
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        else (0 : ℝ))
      ≤ (ℓ ^ 3)⁻¹ * deficit c ‖kmomInt ℓ n‖
          * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
    intro n
    by_cases h : c < ‖kmomInt ℓ n‖ ∧ ‖kmomInt ℓ n‖ < 2 * c
    · rw [if_pos h]
      have hr : 0 ≤ ‖kmomInt ℓ n‖ := norm_nonneg _
      have hwin := (deficit_window_bounds hc hr).1
      have hmax : (max (‖kmomInt ℓ n‖ - c) 0) ^ 2 = (‖kmomInt ℓ n‖ - c) ^ 2 := by
        rw [max_eq_left (by linarith [h.1] : (0 : ℝ) ≤ ‖kmomInt ℓ n‖ - c)]
      rw [hmax] at hwin
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hwin (by positivity)) (sq_nonneg _)
    · rw [if_neg h]
      exact mul_nonneg (mul_nonneg (by positivity)
        (deficit_nonneg hc (norm_nonneg _))) (sq_nonneg _)
  have hFnn : ∀ n : Fin 3 → ℤ,
      0 ≤ (if c < ‖kmomInt ℓ n‖ ∧ ‖kmomInt ℓ n‖ < 2 * c then
          (ℓ ^ 3)⁻¹ * ((‖kmomInt ℓ n‖ - c) ^ 2 - (max 0 (‖kmomInt ℓ n‖ - 5 * c / 4)) ^ 2)
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        else (0 : ℝ)) := by
    intro n
    by_cases h : c < ‖kmomInt ℓ n‖ ∧ ‖kmomInt ℓ n‖ < 2 * c
    · rw [if_pos h]
      have ham : 0 ≤ max 0 (‖kmomInt ℓ n‖ - 5 * c / 4) := le_max_left _ _
      have hle : max 0 (‖kmomInt ℓ n‖ - 5 * c / 4) ≤ ‖kmomInt ℓ n‖ - c :=
        max_le (by linarith) (by linarith [h.1])
      have hsq := pow_le_pow_left₀ ham hle 2
      have hX : 0 ≤ (‖kmomInt ℓ n‖ - c) ^ 2
          - (max 0 (‖kmomInt ℓ n‖ - 5 * c / 4)) ^ 2 := by linarith
      exact mul_nonneg (mul_nonneg (by positivity) hX) (sq_nonneg _)
    · rw [if_neg h]
  have hFs : Summable (fun n : Fin 3 → ℤ =>
      if c < ‖kmomInt ℓ n‖ ∧ ‖kmomInt ℓ n‖ < 2 * c then
          (ℓ ^ 3)⁻¹ * ((‖kmomInt ℓ n‖ - c) ^ 2 - (max 0 (‖kmomInt ℓ n‖ - 5 * c / 4)) ^ 2)
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        else (0 : ℝ)) :=
    Summable.of_nonneg_of_le hFnn hpt (summable_latDeficit hℓ hc hg hgc)
  rw [latDeficit]
  exact hFs.tsum_le_tsum hpt (summable_latDeficit hℓ hc hg hgc)

/-- The **canonical ledger identity** with the closed-ball support hypothesis (the form the
windowed class supplies); same proof as `ledger_eq_deficitForm_paren`, whose open-ball hypothesis is
only used to produce this closed ball. -/
theorem ledger_eq_deficitForm_closed {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    latDeficit ℓ c g + lowGain ℓ c g - 2 * c * (tauContPow 1 g - tauLatPow ℓ 1 g)
      = c * (3 * tauLatPow ℓ 1 g - 2 * tauContPow 1 g)
        + (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        - ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3),
            tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        - (5 / 4 + tauC0phi) * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹
            * ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hcore := latDeficit_add_latTheta hℓ hc hg hgc hgsupp
  have hΘ : (∫ p : EuclideanSpace ℝ (Fin 3),
        tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      = ∫ p : EuclideanSpace ℝ (Fin 3), thetaSym c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards with p
    rw [thetaSym_eq_tauTheta]
  rw [hΘ, lowGain]
  linear_combination hcore

/-- **(WIN) at the windowed class ⟹ the tauPhi row.**  Same three-step assembly as
`Work.BoseBoxFock.row_of_window` (`latDeficit_ge_window` + the canonical ledger identity), transcribed
to the χ_Λ-windowed class.

⚠ **VACUOUS — kept as documentation only.**  The hypothesis `hwin` is *false* in general: the
window sum `W` satisfies `W ≤ latDeficit ℓ c g` (PROVED `latDeficit_ge_window_smooth`), and the
ledger identity gives `(★) ⟺ 2cD ≤ latDeficit + lowGain`, so `(WIN) ⟹ (★)` *strictly*, with slack
`latDeficit − W = Σ_{‖kₙ‖≥2c}ℓ⁻³(c‖kₙ‖−(5/4+c₀)c²)‖ĉ(kₙ)‖² ≥ 0`, which is positive whenever the
state has lattice mass above `2c`.  Review produced a concrete admissible counterexample at
`ℓ = 1, c = 4π` (`FINDING_tauPhiRowWindowHinge.md`, ADDENDUM 2).  The *useful* content here is the
pair of support-free/closed-ball lemmas below, not this arrow. -/
theorem tauPhiRowWindow_of_winWindow {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hclass : ∃ h : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ (⊤ : ENat) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ Work.BoseK15.corpusBox.boxL ℓ ∧
        (∀ z, g z = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * h z))
    (hwin : 2 * c * (tauContPow 1 g - tauLatPow ℓ 1 g)
      ≤ (∑' n : Fin 3 → ℤ, (if c < ‖kmomInt ℓ n‖ ∧ ‖kmomInt ℓ n‖ < 2 * c then
              (ℓ ^ 3)⁻¹ * ((‖kmomInt ℓ n‖ - c) ^ 2
                  - (max 0 (‖kmomInt ℓ n‖ - 5 * c / 4)) ^ 2)
                * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
            else (0 : ℝ)))
        + lowGain ℓ c g) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hg := windowed_contDiff hℓ hclass
  have hgc := windowed_hasCompactSupport hℓ hclass
  have hgs := windowed_tsupport_subset hℓ hclass
  have hw := latDeficit_ge_window_smooth hℓ hc hg hgc
  have hstar : 2 * c * (tauContPow 1 g - tauLatPow ℓ 1 g)
      ≤ latDeficit ℓ c g + lowGain ℓ c g := by
    linarith
  have hdef : c * (3 * (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
              * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
            - 2 * (((2 * Real.pi) ^ 3)⁻¹
              * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2))
          + (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
              * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
          - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2
        ≥ (5 / 4 + tauC0phi) * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹
            * ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
    have hled := ledger_eq_deficitForm_closed hℓ hc hg hgc hgs
    simp only [tauLatPow, tauContPow, pow_one] at hled hstar ⊢
    linarith
  exact tauPhiRowWindow_of_deficitWindow hℓ hc hclass hdef

/-! ## The pinned residual

`tauPhiRowWindow_of_deficitWindow` reduces `tauPhiRowWindow` to the inequality `hdef` below.  That
inequality is **the residual obligation of the windowed stretch** (it is equivalent to the crux
`(★) ⟺ 2cD ≤ latDeficit + lowGain` via the PROVED canonical ledger identity), so it is pinned here
as a named `Prop` and its reduction to the row is restated for it.  Naming it matters: it is the
object the fleet's in-flight nodes bear on, and it is *not* to be re-filed under a new name. -/

/-- **The windowed deficit residual.**  `windowedDeficitResidual ℓ c g` is *exactly* the `hdef`
hypothesis of `tauPhi_row_lattice_of_deficit` / `tauPhiRowWindow_of_deficitWindow`; via the PROVED
ledger identity `ledger_eq_deficitForm_paren` it is equivalent to the canonical form
`(★)  2c·(R₁ − S₁) ≤ latDeficit ℓ c g + lowGain ℓ c g`
(with `R₁ = tauContPow 1 g`, `S₁ = tauLatPow ℓ 1 g`, `D = R₁ − S₁`). -/
def windowedDeficitResidual (ℓ c : ℝ) (g : EuclideanSpace ℝ (Fin 3) → ℂ) : Prop :=
  c * (3 * (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
          - 2 * (((2 * Real.pi) ^ 3)⁻¹
            * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2))
        + (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2
      ≥ (5 / 4 + tauC0phi) * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹
          * ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2)

/-- **The pinned residual implies the tauPhi row** for χ_Λ-windowed `g`
(immediate repackaging of `tauPhiRowWindow_of_deficitWindow`). -/
theorem tauPhiRowWindow_of_windowedDeficitResidual {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hclass : ∃ h : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ (⊤ : ENat) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ Work.BoseK15.corpusBox.boxL ℓ ∧
        (∀ z, g z = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * h z))
    (hres : windowedDeficitResidual ℓ c g) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
  tauPhiRowWindow_of_deficitWindow hℓ hc hclass hres

end Work.BoseBoxFock
