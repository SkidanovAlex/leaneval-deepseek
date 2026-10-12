import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.W2Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.bf3a_fibre` — the fibre-wise `τ̃`-kinetic row of BF3a

The box side of the bridge (BF3a / FS `prop:Hamilton2ndQuant`) carries the kinetic row
`Σ_k τ̃(k)a_k†a_k` with the **smoothed** symbol `τ̃ = tauSm` of `W2Defs`, against the
box kinetic word `kinFormB`, whose main piece is `mainWord = (1−ε_T)[√−Δ−½(sℓ)⁻¹]₊²
+ ε_T[√−Δ−½(dsℓ)⁻¹]₊²` (FS `eq:T'u`).  Fibre by fibre (one slot, `u = 0`) the comparison
is exactly

    `bsOneBody ℓ (tauSmRad eT s d ℓ) 0 ψ ≤ mainWord ℓ d s eT 0 ψ`,

i.e. the `τ̃`-one-body quadratic form is dominated by the two-cutoff `eq:T'u` word.

This module proves that statement.  The engine is the smoothing inequality
`τ̃ ≤ τ`: the profile `tauProf` of `exists_tauProf` satisfies
`tauProf r ≤ (max 0 (r−1))²`, so for every `c > 0`

    `c² · tauProf(r/c) ≤ [r − c]₊² = fsKinCoeff c r`,

which applied at `c = (2sℓ)⁻¹` and `c = (2dsℓ)⁻¹` gives the pointwise symbol bound
`tauSmRad eT s d ℓ ≤ (1−ε_T)·fsKinCoeff (2sℓ)⁻¹ + ε_T·fsKinCoeff (2dsℓ)⁻¹`.  The
`p`-integral is then monotone because both integrands are dominated by the integrable
`fsKinCoeff`-weighted masses (`integrable_fsKinCoeff_mul_bsPsi_sq`), using the
transported form `bsOneBody = (2π)⁻³·bsW` of the shifted state.
-/

noncomputable section

open MeasureTheory Filter
open Work.BSKinetic.Decomp

namespace Work.BoseBoxFock

set_option linter.unusedVariables false

/-! ## 1. The kinetic profile: nonnegativity and the smoothing bound -/

/-- `tauProf` is nonnegative (it dominates `(r−2)₊²`). -/
lemma tauProf_nonneg (r : ℝ) : 0 ≤ tauProf r := by
  have h : (max 0 (r - 2)) ^ 2 ≤ tauProf r :=
    tauProf_spec.2.2.1 r
  exact le_trans (sq_nonneg _) h

/-- **The smoothing inequality** `c²·tauProf(r/c) ≤ [r−c]₊²` for `c > 0`: the profile
`tauProf` sits below the kink `(·₊)²`, so the rescaled profile is dominated by the
`fsKinCoeff c r = (max 0 (r−c))²` cutoff. -/
lemma mul_tauProf_le_fsKinCoeff {c r : ℝ} (hc : 0 < c) :
    c ^ 2 * tauProf (r / c) ≤ Submission.BoseGases.fsKinCoeff c r := by
  have hle : tauProf (r / c) ≤ (max 0 (r / c - 1)) ^ 2 :=
    tauProf_spec.2.2.2.1 (r / c)
  have h1 : c * (r / c - 1) = r - c := by
    rw [mul_sub, mul_div_cancel₀ r (ne_of_gt hc), mul_one]
  have h2 : c * max 0 (r / c - 1) = max 0 (r - c) := by
    rw [mul_max_of_nonneg (0:ℝ) (r / c - 1) hc.le, h1, mul_zero]
  rw [Submission.BoseGases.fsKinCoeff, max_comm (r - c) 0]
  calc c ^ 2 * tauProf (r / c) ≤ c ^ 2 * (max 0 (r / c - 1)) ^ 2 :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (c * max 0 (r / c - 1)) ^ 2 := by ring
    _ = (max 0 (r - c)) ^ 2 := by rw [h2]

/-- `tauSmRad` is nonnegative (sum of nonnegative rescaled profiles). -/
lemma tauSmRad_nonneg {s d ℓ eT : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (r : ℝ) :
    0 ≤ tauSmRad eT s d ℓ r := by
  have h1 : 0 ≤ (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * tauProf (r / (2 * s * ℓ)⁻¹) :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (tauProf_nonneg _)
  have h2 : 0 ≤ eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * tauProf (r / (2 * d * s * ℓ)⁻¹) :=
    mul_nonneg (mul_nonneg heT0 (sq_nonneg _)) (tauProf_nonneg _)
  simp only [tauSmRad]
  linarith

/-! ## 2. The pointwise symbol bound `tauSmRad ≤ (1−ε_T)·fsKinCoeff + ε_T·fsKinCoeff` -/

/-- **The `τ̃ ≤ τ` symbol bound**: the smoothed symbol `tauSmRad` is dominated by the two
kinked cutoffs of `eq:T'u` at the cut-off momenta `(2sℓ)⁻¹` and `(2dsℓ)⁻¹`. -/
lemma tauSmRad_le_fsKinCoeff {ℓ s d eT : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (hd : 0 < d)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (r : ℝ) :
    tauSmRad eT s d ℓ r ≤
      (1 - eT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r
        + eT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r := by
  have hA : ((2 * s * ℓ)⁻¹) ^ 2 * tauProf (r / (2 * s * ℓ)⁻¹)
      ≤ Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r := by
    rw [show (2 * s * ℓ)⁻¹ = (2 * (s * ℓ))⁻¹ from by congr 1; ring]
    exact mul_tauProf_le_fsKinCoeff (r := r)
      (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * (s * ℓ)))
  have hB : ((2 * d * s * ℓ)⁻¹) ^ 2 * tauProf (r / (2 * d * s * ℓ)⁻¹)
      ≤ Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r := by
    rw [show (2 * d * s * ℓ)⁻¹ = (2 * (d * s * ℓ))⁻¹ from by congr 1; ring]
    exact mul_tauProf_le_fsKinCoeff (r := r)
      (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * (d * s * ℓ)))
  have h1 : (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2 * tauProf (r / (2 * s * ℓ)⁻¹))
      ≤ (1 - eT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r :=
    mul_le_mul_of_nonneg_left hA (by linarith)
  have h2 : eT * (((2 * d * s * ℓ)⁻¹) ^ 2 * tauProf (r / (2 * d * s * ℓ)⁻¹))
      ≤ eT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r :=
    mul_le_mul_of_nonneg_left hB heT0
  simp only [tauSmRad]
  nlinarith [h1, h2]

/-! ## 3. Linearity of `bsW` in the symbol -/

/-- `bsW` is linear in the symbol: `bsW (c·F) h = c·bsW F h`. -/
lemma bsW_const_mul {c : ℝ} {F : ℝ → ℝ} {h : ℝ³ → ℝ}
    (hInt : Integrable (fun p : ℝ³ => F ‖p‖ * ‖bsPsi h p‖ ^ 2)) :
    bsW (fun r => c * F r) h = c * bsW F h := by
  rw [bsW, bsW, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun p => by ring)

/-- `bsW` is additive on symbol combinations:
`bsW (c₁F + c₂G) h = c₁·bsW F h + c₂·bsW G h`. -/
lemma bsW_lincomb {c₁ c₂ : ℝ} {F G : ℝ → ℝ} {h : ℝ³ → ℝ}
    (hF : Integrable (fun p : ℝ³ => F ‖p‖ * ‖bsPsi h p‖ ^ 2))
    (hG : Integrable (fun p : ℝ³ => G ‖p‖ * ‖bsPsi h p‖ ^ 2)) :
    bsW (fun r => c₁ * F r + c₂ * G r) h = c₁ * bsW F h + c₂ * bsW G h := by
  have h1 : ∫ p : ℝ³, (c₁ * F ‖p‖ + c₂ * G ‖p‖) * ‖bsPsi h p‖ ^ 2
      = ∫ p : ℝ³, c₁ * (F ‖p‖ * ‖bsPsi h p‖ ^ 2) + c₂ * (G ‖p‖ * ‖bsPsi h p‖ ^ 2) :=
    integral_congr_ae (Eventually.of_forall fun p => by ring)
  rw [bsW, bsW, bsW, h1, integral_add (hF.const_mul c₁) (hG.const_mul c₂),
    integral_const_mul, integral_const_mul]

/-! ## 4. The `bsW` inequality at the shifted state -/

/-- **The shifted-state form of the fibre bound**: for a smooth compactly supported one-body
state `h`, the `tauSmRad`-weighted `p`-form is dominated by the two `fsKinCoeff`-weighted
forms with the FS cut-offs. -/
lemma bsW_tauSmRad_le {ℓ s d eT : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (hd : 0 < d)
    (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) {h : ℝ³ → ℝ}
    (hdh : ContDiff ℝ (⊤ : ℕ∞) h) (hch : HasCompactSupport h) :
    bsW (tauSmRad eT s d ℓ) h
      ≤ (1 - eT) * bsW (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) h
        + eT * bsW (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) h := by
  have hInta : Integrable (fun p : ℝ³ =>
      Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ * ‖bsPsi h p‖ ^ 2) :=
    integrable_fsKinCoeff_mul_bsPsi_sq (c := (2 * (s * ℓ))⁻¹) hdh hch
  have hIntb : Integrable (fun p : ℝ³ =>
      Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ * ‖bsPsi h p‖ ^ 2) :=
    integrable_fsKinCoeff_mul_bsPsi_sq (c := (2 * (d * s * ℓ))⁻¹) hdh hch
  -- the dominating integrand is a sum of two integrable pieces
  have hDint : Integrable (fun p : ℝ³ =>
      ((1 - eT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖
        + eT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖)
        * ‖bsPsi h p‖ ^ 2) := by
    have h1 : Integrable (fun p : ℝ³ =>
        ((1 - eT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖)
          * ‖bsPsi h p‖ ^ 2) :=
      (hInta.const_mul (1 - eT)).congr (Eventually.of_forall fun p => by ring)
    have h2 : Integrable (fun p : ℝ³ =>
        (eT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖)
          * ‖bsPsi h p‖ ^ 2) :=
      (hIntb.const_mul eT).congr (Eventually.of_forall fun p => by ring)
    exact (h1.add h2).congr (Eventually.of_forall fun p => by simp only [Pi.add_apply]; ring)
  have key := integral_mono_of_nonneg
    (Eventually.of_forall fun p => mul_nonneg (tauSmRad_nonneg heT0 heT1 ‖p‖) (sq_nonneg _))
    hDint
    (Eventually.of_forall fun p =>
      mul_le_mul_of_nonneg_right (tauSmRad_le_fsKinCoeff hℓ hs hd heT0 heT1 ‖p‖)
        (sq_nonneg _))
  rw [← bsW_lincomb hInta hIntb]
  rw [bsW, bsW]
  exact key

/-! ## 5. The target: the fibre bound for `bsOneBody` -/

theorem bf3a_fibre {ℓ s d eT : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s) (hd : 0 < d) (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : Work.BSKinetic.bsOneBody ℓ (Work.BoseBoxFock.tauSmRad eT s d ℓ) 0 ψ ≤ Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := by
  have hdψ : ContDiff ℝ (⊤ : ℕ∞) (bsShift ℓ ψ 0) := contDiff_bsShift hℓ hψ 0
  have hcψ : HasCompactSupport (bsShift ℓ ψ 0) := hasCompactSupport_bsShift (ne_of_gt hℓ) 0
  have key := bsW_tauSmRad_le hℓ hs hd heT0 heT1 hdψ hcψ
  have hC : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
  calc Work.BSKinetic.bsOneBody ℓ (Work.BoseBoxFock.tauSmRad eT s d ℓ) 0 ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * bsW (Work.BoseBoxFock.tauSmRad eT s d ℓ) (bsShift ℓ ψ 0) :=
        bsOneBody_eq_bsW_shift hℓ _ 0 ψ
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          ((1 - eT) * bsW (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) (bsShift ℓ ψ 0)
            + eT * bsW (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹))
                (bsShift ℓ ψ 0)) :=
        mul_le_mul_of_nonneg_left key hC
    _ = (1 - eT) * Work.BSKinetic.bsOneBody ℓ
            (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) 0 ψ
          + eT * Work.BSKinetic.bsOneBody ℓ
            (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) 0 ψ := by
        rw [bsOneBody_eq_bsW_shift hℓ, bsOneBody_eq_bsW_shift hℓ]
        ring
    _ = Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ := by
        rw [Work.BoseKinLoc.mainWord]

end Work.BoseBoxFock
