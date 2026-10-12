import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseFixB2.DvApriori.bsOneBody_polar
import Submission.Work.BoseFixB2.DvApriori.integrable_fsKinCoeff_polar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.Analysis.BoseBand.polar_mainWord_fibre`

The kinetic word `mainWord` (FS `eq:DefT`'s fourth term) is the *quadratic* form

  `mainWord ℓ d s ε_T 0 ψ
    = (1−ε_T)·bsOneBody ℓ [·−(2sℓ)⁻¹]₊² 0 ψ + ε_T·bsOneBody ℓ [·−(2dsℓ)⁻¹]₊² 0 ψ`,

and `bsOneBody ℓ F 0 ψ = (2π)⁻³∫_p F(‖p‖)·‖kinFT(χ₀·Q₀ψ)(p)‖²`, so it is the diagonal of the
sesquilinear form `(f,g) ↦ (2π)⁻³∫_p F(‖p‖)·Re(star(kinFT(χ₀Q₀f)(p))·kinFT(χ₀Q₀g)(p))`.

Polarising the pointwise identity `‖z+w‖²−‖z−w‖² = 4·Re(star z · w)` and translating the
windowed Fourier transform through the slot-fibre dictionary

  `kinFT (χ₀·Q₀(fibre_j Ψ x)) p = tBamp χ₀ p (Q_jΨ) j x`

gives the pointwise (in the configuration `x`) identity of the theorem: the difference of
`mainWord` at the sum and the difference of two slot-`j` fibres is four times the polarisation,
written with the localised amplitude `tBamp` of the *mean-free slot states* `Q_jΨ`, `Q_jΨ'`.

## Contents

* `contDiff_fibre_smooth`, `Qfree_fibre_eq`, `kinFT_win_Qfree_fibre` — the slot-fibre dictionary;
* `tPair` — the polarised `tBamp` pairing;
* `mainWord_fibre_polar` — the polarisation identity for arbitrary smooth slot states `W`, `V`;
* `polar_mainWord_fibre` — the requested statement (`W = Ψ`, `V = Ψ'`).

The one-body polarisation `bsOneBody_polar` and the integrability of the polarised integrand
`integrable_fsKinCoeff_polar` are the two analytic inputs; everything else is the dictionary and
the assembly of the two `bsOneBody` differences into one `p`-integral.
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory ContDiff

namespace Work.Analysis.BoseBand

set_option maxHeartbeats 1000000

/-! ## 1. The slot-fibre dictionary -/

/-- The slot-`j` fibre of a smooth `n`-body state is smooth (the fibre is the composition of the
state with the smooth map `z ↦ x_{j←z}`). -/
lemma contDiff_fibre_smooth {n : ℕ} {W : Submission.BoseGases.X n → ℝ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (j : Fin n) (x : Submission.BoseGases.X n) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.fibre n j W x) :=
  hW.comp (contDiff_update (𝕜 := ℝ) (⊤ : ℕ∞) x j)

/-- **The mean-free part of a slot-`j` fibre is the fibre of the mean-free state:**

`Q_{Λ}(fibre_j W x) = fibre_j (Q_jW) x`, i.e.
`Qfree ℓ 0 (fibre n j W x) = fibre n j (aQ ℓ j W) x`.

Both sides are `W(x_j ← z) − |Λ|⁻¹∫_{Λ}W(x_j ← z')dz'` (the mean is independent of `z`). -/
lemma Qfree_fibre_eq {ℓ : ℝ} {n : ℕ} (j : Fin n) {W : Submission.BoseGases.X n → ℝ}
    (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j W x)
      = Work.BoseKinLoc.fibre n j (Submission.BoseGases.aQ ℓ j W) x := by
  funext z
  simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, Work.BSKinetic.bsMean,
    Work.BoseKinLoc.fibre, Submission.BoseGases.aQ, Submission.BoseGases.aP,
    smul_zero, zero_add, one_div]
  have hme : (∫ y in Submission.BoseGases.acube ℓ,
      W (Function.update (Function.update x j z) j y))
      = ∫ y in Submission.BoseGases.acube ℓ, W (Function.update x j y) := by
    congr 1
    ext y
    rw [Function.update_idem]
  rw [hme]

/-- **The windowed fibre dictionary.**

The windowed Fourier transform of the mean-free slot-`j` fibre is the `tBamp` amplitude of the
mean-free slot state:

`kinFT (χ · Q_{Λ}(fibre_j W x)) p = tBamp χ p (Q_jW) j x`. -/
lemma kinFT_win_Qfree_fibre {ℓ : ℝ} {n : ℕ} (j : Fin n) (χ : ℝ³ → ℝ) (p : ℝ³)
    {W : Submission.BoseGases.X n → ℝ} (x : Submission.BoseGases.X n) :
    Submission.BoseGases.kinFT
        (fun z : ℝ³ => (χ z : ℂ) *
          (Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j W x) z : ℂ)) p
      = Work.SmallBoxTBWord.tBamp χ p (Submission.BoseGases.aQ ℓ j W) j x := by
  simp only [Submission.BoseGases.kinFT, Work.SmallBoxTBWord.tBamp]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  have h : Work.BoseKinLoc.fibre n j (Submission.BoseGases.aQ ℓ j W) x z
      = Submission.BoseGases.aQ ℓ j W (Function.update x j z) := rfl
  rw [Qfree_fibre_eq j x, h]
  ring

/-! ## 2. The polarisation identity -/

/-- **The polarised `tBamp` pairing.**  `tPair ℓ W V j p x` is the bilinear form in which the
polarisation of the windowed spectral word `mainWord` is written:
`Re(star(tBamp χ₀ p W j x)·tBamp χ₀ p V j x)` with `χ₀ = bsWin ℓ 0`. -/
def tPair {n : ℕ} (ℓ : ℝ) (W V : Submission.BoseGases.X n → ℝ) (j : Fin n)
    (p : ℝ³) (x : Submission.BoseGases.X n) : ℝ :=
  (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
    Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re

/-- **The polarisation of `mainWord` at a fixed slot and configuration.**  For smooth slot states
`W`, `V`,

`mainWord (fibre_j(W+V) x) − mainWord (fibre_j(W−V) x)`
`  = 4(2π)⁻³∫_p ((1−ε_T)[‖p‖−(2sℓ)⁻¹]₊² + ε_T[‖p‖−(2dsℓ)⁻¹]₊²)·tPair ℓ (Q_jW) (Q_jV) j p x`.

The proof: `mainWord` is the combination `(1−ε_T)·bsOneBody(c₁) + ε_T·bsOneBody(c₂)` of two
one-body spectral words; each polarises by `bsOneBody_polar`, the polarised `p`-integrand is
integrable (`integrable_fsKinCoeff_polar`), the two `p`-integrals combine by additivity of the
Bochner integral, and the resulting integrand is regrouped by `ring`. -/
theorem mainWord_fibre_polar {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    (x : Submission.BoseGases.X n) {W V : Submission.BoseGases.X n → ℝ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    Work.BoseKinLoc.mainWord ℓ d s εT 0
        (fun z => Work.BoseKinLoc.fibre n j W x z + Work.BoseKinLoc.fibre n j V x z)
      - Work.BoseKinLoc.mainWord ℓ d s εT 0
        (fun z => Work.BoseKinLoc.fibre n j W x z - Work.BoseKinLoc.fibre n j V x z)
    = 4 * ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : ℝ³,
          ((1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖
            + εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖) *
          tPair ℓ (Submission.BoseGases.aQ ℓ j W) (Submission.BoseGases.aQ ℓ j V) j p x := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.fibre n j W x) := contDiff_fibre_smooth hW j x
  have hg : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.fibre n j V x) := contDiff_fibre_smooth hV j x
  -- integrability of the polarised `p`-integrand, in the `tBamp` form
  have hInt : ∀ c : ℝ, MeasureTheory.Integrable (fun p : ℝ³ =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ *
        tPair ℓ (Submission.BoseGases.aQ ℓ j W) (Submission.BoseGases.aQ ℓ j V) j p x) := by
    intro c
    refine (Work.BoseFixB2.DvApriori.integrable_fsKinCoeff_polar (ℓ := ℓ) (c := c)
      hℓ hf hg).congr ?_
    filter_upwards with p
    rw [kinFT_win_Qfree_fibre, kinFT_win_Qfree_fibre]
    rfl
  -- the polarisation of each of the two `bsOneBody`s
  have hpol : ∀ c : ℝ,
      Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
          (fun z => Work.BoseKinLoc.fibre n j W x z + Work.BoseKinLoc.fibre n j V x z)
        - Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) 0
          (fun z => Work.BoseKinLoc.fibre n j W x z - Work.BoseKinLoc.fibre n j V x z)
      = ∫ p : ℝ³, (4 * ((2 * Real.pi) ^ 3)⁻¹) *
          (Submission.BoseGases.fsKinCoeff c ‖p‖ *
            tPair ℓ (Submission.BoseGases.aQ ℓ j W) (Submission.BoseGases.aQ ℓ j V) j p x) := by
    intro c
    rw [Work.BoseFixB2.DvApriori.bsOneBody_polar (ℓ := ℓ) (c := c) hℓ hf hg]
    simp only [kinFT_win_Qfree_fibre]
    rw [← MeasureTheory.integral_const_mul (4 * ((2 * Real.pi) ^ 3)⁻¹)
      (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff c ‖p‖ *
        (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p
            (Submission.BoseGases.aQ ℓ j W) j x)
          * Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p
            (Submission.BoseGases.aQ ℓ j V) j x).re)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    simp only [tPair]
  -- group the difference of the two `bsOneBody` differences
  have hgroup : Work.BoseKinLoc.mainWord ℓ d s εT 0
        (fun z => Work.BoseKinLoc.fibre n j W x z + Work.BoseKinLoc.fibre n j V x z)
      - Work.BoseKinLoc.mainWord ℓ d s εT 0
        (fun z => Work.BoseKinLoc.fibre n j W x z - Work.BoseKinLoc.fibre n j V x z)
      = (1 - εT) * (Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) 0
              (fun z => Work.BoseKinLoc.fibre n j W x z + Work.BoseKinLoc.fibre n j V x z)
            - Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹)) 0
              (fun z => Work.BoseKinLoc.fibre n j W x z - Work.BoseKinLoc.fibre n j V x z))
        + εT * (Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) 0
              (fun z => Work.BoseKinLoc.fibre n j W x z + Work.BoseKinLoc.fibre n j V x z)
            - Work.BSKinetic.bsOneBody ℓ
              (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹)) 0
              (fun z => Work.BoseKinLoc.fibre n j W x z - Work.BoseKinLoc.fibre n j V x z)) := by
    simp only [Work.BoseKinLoc.mainWord]
    ring
  rw [hgroup, hpol ((2 * (s * ℓ))⁻¹), hpol ((2 * (d * s * ℓ))⁻¹)]
  -- move the coefficients `(1−ε_T)`, `ε_T` inside their integrals
  rw [← MeasureTheory.integral_const_mul (1 - εT)
        (fun p : ℝ³ => (4 * ((2 * Real.pi) ^ 3)⁻¹) *
          (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖ *
            tPair ℓ (Submission.BoseGases.aQ ℓ j W) (Submission.BoseGases.aQ ℓ j V) j p x)),
    ← MeasureTheory.integral_const_mul εT
        (fun p : ℝ³ => (4 * ((2 * Real.pi) ^ 3)⁻¹) *
          (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖ *
            tPair ℓ (Submission.BoseGases.aQ ℓ j W) (Submission.BoseGases.aQ ℓ j V) j p x))]
  -- combine the two integrals
  rw [← MeasureTheory.integral_add
        (((hInt ((2 * (s * ℓ))⁻¹)).const_mul (4 * ((2 * Real.pi) ^ 3)⁻¹)).const_mul (1 - εT))
        (((hInt ((2 * (d * s * ℓ))⁻¹)).const_mul (4 * ((2 * Real.pi) ^ 3)⁻¹)).const_mul εT)]
  -- move the constant of the right-hand side inside its integral
  rw [← MeasureTheory.integral_const_mul (4 * ((2 * Real.pi) ^ 3)⁻¹)
        (fun p : ℝ³ =>
          ((1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖
            + εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖) *
          tPair ℓ (Submission.BoseGases.aQ ℓ j W) (Submission.BoseGases.aQ ℓ j V) j p x)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  ring

/-! ## 3. The requested statement -/

theorem polar_mainWord_fibre {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Ψ Ψ' : Submission.BoseGases.X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨ' : ContDiff ℝ (⊤ : ℕ∞) Ψ') (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.mainWord ℓ d s εT 0
        (fun z => Work.BoseKinLoc.fibre n j Ψ x z + Work.BoseKinLoc.fibre n j Ψ' x z)
      - Work.BoseKinLoc.mainWord ℓ d s εT 0
        (fun z => Work.BoseKinLoc.fibre n j Ψ x z - Work.BoseKinLoc.fibre n j Ψ' x z)
    = 4 * ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : EuclideanSpace ℝ (Fin 3),
          ((1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖
            + εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖) *
          (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p
              (Submission.BoseGases.aQ ℓ j Ψ) j x)
            * Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p
              (Submission.BoseGases.aQ ℓ j Ψ') j x).re := by
  simpa only [tPair] using
    mainWord_fibre_polar (ℓ := ℓ) (d := d) (s := s) (εT := εT) hℓ j x hΨ hΨ'

end Work.Analysis.BoseBand
