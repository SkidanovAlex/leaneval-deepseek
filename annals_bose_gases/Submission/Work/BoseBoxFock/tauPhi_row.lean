import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.hingeRow
import Submission.Work.BoseBoxFock.summable_of_quad_growth
import Submission.Work.BoseBoxFock.tauPhiRowWindow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tauPhi_row` — the lattice-vs-continuum row at the *explicit* profile

Target (below, unchanged): for `ℓ > 0`, `c > 0` with `c ℓ ≥ 4π` and `g : ℝ³ → ℂ` smooth of
compact support in the *open* ball `B(0, ℓ/2)`,

    Σ_n ℓ⁻³ · c²·τ̃(‖k_n‖/c) · ‖ĝ(k_n)‖²   ≤   (2π)⁻³ ∫_p [‖p‖−c]₊² · ‖ĝ(p)‖² dp ,

`k_n = kmomInt ℓ n = (2π/ℓ)·n`, `τ̃ = tauPhi`, `ĝ = kinFT g`.

## Structure of the proof (this file)

Everything in this file is elementary and proved.  Write `C₀ = ∫ t² K(t) dt ≥ 0` for the
constant of the profile (`K = tauKer`), so that

* `tauPhi s = 0` for `s ≤ 5/4` (`rescaled_tauPhi_eq_zero`),
* `tauPhi s ≤ (max 0 (s−1))²` and `tauPhi s ≤ (max 0 (s−5/4))²` (`TauProf.tauPhi_le`,
  `rescaled_tauPhi_le_conv`),
* `tauPhi s ≤ (s−3/2)² + C₀` for **every** `s` (`TauProf.tauPhi_le_quad`),
* `tauPhi s = (s−3/2)² + C₀` for `s ≥ 2` (`TauProf.tauPhi_quad`).

Rescaled by `c` (so that `τ̃_c(r) := c²·tauPhi (r/c)`), and with

    δ_c(r) := [r−c]₊² − τ̃_c(r)   (the *profile deficit*, which is `≥ 0`),

these give the two facts on which every route to the target rests:

* `rescaled_tauPhi_le_sharp` : `τ̃_c ≤ fsKinCoeff c = [· − c]₊²` (pointwise domination);
* `deficit_ge_linear` : `δ_c(r) ≥ c·r − (5/4 + C₀)c²` for `r ≤ 2c`, and
  `rescaled_tauPhi_eq_tail` : `δ_c(r) = c·r − (5/4 + C₀)c²` for `r ≥ 2c`.

## The remaining content (open)

Writing `L(h) = Σ_n ℓ⁻³ h(‖k_n‖)‖ĝ(k_n)‖²` and `C(h) = (2π)⁻³∫ h(‖p‖)‖ĝ(p)‖²dp` for a radial
symbol `h`, the two *moment identities* `L(1) = C(1)` (`frame_lattice_ball` + `kinFT_plancherel`)
and `L((·)²) = C((·)²)` (`moment2Lattice*`) turn the target into an identity involving only the
*aliasing* of the deficit symbols: with `ν(h) := L(h) − C(h)` and `D := C(‖·‖) − L(‖·‖)` the
target is **equivalent** to

    (★)   L(δ_c) + ν(Θ_c) ≥ 2·c·D ,      Θ_c := (c−·)₊² .

Equivalently, with `Σ(r) := δ_c(r) − (c·r − (5/4+C₀)c²)` (supported in frequency on `r ≤ 2c`),

    (★★)  c·(3L(‖·‖) − 2C(‖·‖)) + L(Σ) + ν(Θ_c) ≥ (5/4 + C₀)·c²·L(1) ,

i.e. the *low-frequency lattice gain* `ν(Θ_c)` together with the *window slack* `L(Σ)` (which is
essentially its continuum value `C(Σ)`, `Σ` being `C^∞` with compact frequency support) must pay
the *aliasing deficit* `2cD` of the sharp symbol.  Numerically (see the accompanying FINDING note)
the margin of `(★★)` is small but positive, `≈ 5·10⁻³`–`10⁻³` of `c²L(1)`; the identity `(★)`
is the sharp form of the statement and is what a proof has to establish.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

/-- The constant `C₀ = ∫ t² K(t) dt` of the explicit profile `tauPhi`
(`K = tauKer` is the smoothing kernel). -/
noncomputable def tauPhiC0 : ℝ := ∫ t, t ^ 2 * tauKer t

lemma tauPhiC0_nonneg : 0 ≤ tauPhiC0 := tauKer_moment2_nonneg

lemma tauPhiC0_le : tauPhiC0 ≤ 1 / 16 := tauKer_moment2_le

/-- **The profile at the rescaled argument vanishes below `5/4·c`.**  The kernel `tauKer` is
supported in `[−1/4,1/4]`, so `tauPhi s = ∫ (max 0 (s − 3/2 − t))²K(t)dt = 0` as soon as
`s ≤ 5/4`. -/
theorem rescaled_tauPhi_eq_zero {c r : ℝ} (hc : 0 < c) (hr : r ≤ 5 * c / 4) :
    c ^ 2 * tauPhi (r / c) = 0 := by
  have hs : r / c ≤ 5 / 4 := by
    rw [div_le_iff₀ hc]; linarith
  have hzero : tauPhi (r / c) = 0 := by
    rw [tauPhi_eq_integral]
    have hpt : ∀ t : ℝ, tauH (r / c - 3 / 2 - t) * tauKer t = 0 := by
      intro t
      rcases eq_or_ne (tauKer t) 0 with h0 | h0
      · rw [h0, mul_zero]
      · have ht : -(1 / 4) < t := (abs_lt.mp (tauKer_abs_lt t h0)).1
        have hx : r / c - 3 / 2 - t < 0 := by linarith
        rw [tauH_eq_zero_of_nonpos hx.le, zero_mul]
    rw [show (∫ t, tauH (r / c - 3 / 2 - t) * tauKer t)
        = ∫ _t : ℝ, (0 : ℝ) from integral_congr_ae (Filter.Eventually.of_forall hpt)]
    simp
  rw [hzero, mul_zero]

/-- **The pointwise domination `τ̃_c ≤ [·−c]₊²`.** -/
theorem rescaled_tauPhi_le_sharp {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    c ^ 2 * tauPhi (r / c) ≤ Submission.BoseGases.fsKinCoeff c r := by
  have h := tauPhi_le (r / c)
  have hmul : c ^ 2 * tauPhi (r / c) ≤ c ^ 2 * (max 0 (r / c - 1)) ^ 2 :=
    mul_le_mul_of_nonneg_left h (sq_nonneg c)
  have hkey : c ^ 2 * (max 0 (r / c - 1)) ^ 2 = (max (r - c) 0) ^ 2 := by
    have h1 : c * (r / c - 1) = r - c := by field_simp
    rcases le_or_gt r c with hle | hlt
    · have hz : r / c - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_one hc]; exact hle
      rw [max_eq_left hz, max_eq_right (by linarith : r - c ≤ 0)]
      ring
    · have hp : 0 ≤ r / c - 1 := by
        rw [le_sub_iff_add_le, le_div_iff₀ hc]
        linarith
      rw [max_eq_right hp, max_eq_left (by linarith : (0 : ℝ) ≤ r - c),
        show c ^ 2 * (r / c - 1) ^ 2 = (c * (r / c - 1)) ^ 2 from by ring, h1]
  rw [hkey] at hmul
  simpa [Submission.BoseGases.fsKinCoeff, max_comm] using hmul

/-- **The convolution-support bound**: `τ̃_c(r) ≤ (max 0 (r − 5c/4))²`. -/
theorem rescaled_tauPhi_le_conv {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    c ^ 2 * tauPhi (r / c) ≤ (max 0 (r - 5 * c / 4)) ^ 2 := by
  have hint : tauPhi (r / c) ≤ (max 0 (r / c - 5 / 4)) ^ 2 := by
    rw [tauPhi_eq_integral]
    have hpt : ∀ t : ℝ, tauH (r / c - 3 / 2 - t) * tauKer t
        ≤ (max 0 (r / c - 5 / 4)) ^ 2 * tauKer t := by
      intro t
      rcases eq_or_ne (tauKer t) 0 with h0 | h0
      · rw [h0, mul_zero, mul_zero]
      · have ht : |t| < 1 / 4 := tauKer_abs_lt t h0
        have ht' : -1 / 4 ≤ t := by
          have h : -t < 1 / 4 := by
            have := abs_lt.mp ht
            linarith [this.2]
          linarith
        have hx : r / c - 3 / 2 - t ≤ r / c - 5 / 4 := by linarith
        have hmono := tauH_mono hx
        have hval : tauH (r / c - 5 / 4) = (max 0 (r / c - 5 / 4)) ^ 2 := rfl
        rw [hval] at hmono
        exact mul_le_mul_of_nonneg_right hmono (tauKer_nonneg t)
    have hInt1 : Integrable (fun t => tauH (r / c - 3 / 2 - t) * tauKer t) volume :=
      tauKer_mul_integrable _ (tauH_continuous.comp (by fun_prop))
    have hInt2 : Integrable (fun t => (max 0 (r / c - 5 / 4)) ^ 2 * tauKer t) volume :=
      tauKer_integrable.const_mul _
    calc ∫ t, tauH (r / c - 3 / 2 - t) * tauKer t
        ≤ ∫ t, (max 0 (r / c - 5 / 4)) ^ 2 * tauKer t := integral_mono hInt1 hInt2 hpt
      _ = (max 0 (r / c - 5 / 4)) ^ 2 * ∫ t, tauKer t := integral_const_mul _ _
      _ = (max 0 (r / c - 5 / 4)) ^ 2 := by rw [tauKer_integral, mul_one]
  have hmul := mul_le_mul_of_nonneg_left hint (sq_nonneg c)
  have hkey : c ^ 2 * (max 0 (r / c - 5 / 4)) ^ 2 = (max 0 (r - 5 * c / 4)) ^ 2 := by
    have h1 : c * (r / c - 5 / 4) = r - 5 * c / 4 := by field_simp
    rcases le_or_gt r (5 * c / 4) with hle | hlt
    · have hz : r / c - 5 / 4 ≤ 0 := by
        have : r / c ≤ 5 / 4 := by rw [div_le_iff₀ hc]; linarith
        linarith
      rw [max_eq_left hz, max_eq_left (by linarith : r - 5 * c / 4 ≤ 0)]; ring
    · have hp : 0 ≤ r / c - 5 / 4 := by
        have : 5 / 4 ≤ r / c := by rw [le_div_iff₀ hc]; linarith
        linarith
      rw [max_eq_right hp, max_eq_right (by linarith : (0 : ℝ) ≤ r - 5 * c / 4),
        show c ^ 2 * (r / c - 5 / 4) ^ 2 = (c * (r / c - 5 / 4)) ^ 2 from by ring, h1]
  linarith [hmul, hkey.le]

/-- **The profile in the quadratic tail, rescaled**: for `r ≥ 2c`,
`τ̃_c(r) = (r − 3c/2)² + C₀c²`. -/
theorem rescaled_tauPhi_eq_tail {c r : ℝ} (hc : 0 < c) (hr : 2 * c ≤ r) :
    c ^ 2 * tauPhi (r / c) = (r - 3 * c / 2) ^ 2 + tauPhiC0 * c ^ 2 := by
  have hs : 2 ≤ r / c := by rw [le_div_iff₀ hc]; linarith
  unfold tauPhiC0
  rw [tauPhi_quad (r / c) hs, mul_add]
  have h2 : c ^ 2 * (r / c - 3 / 2) ^ 2 = (r - 3 * c / 2) ^ 2 := by
    rw [show c ^ 2 * (r / c - 3 / 2) ^ 2 = (c * (r / c - 3 / 2)) ^ 2 from by ring]
    congr 1
    field_simp
  rw [h2]
  ring

/-- **The deficit is bounded below by its linear tail**: for `0 < c` and `0 ≤ r`,

    δ_c(r) = [r−c]₊² − τ̃_c(r) ≥ c·r − (5/4 + C₀)c² .

The inequality is elementary (it needs only `tauPhi_le_quad`); for `r ≥ 2c` it is an *equality*
(`rescaled_tauPhi_eq_tail`). -/
theorem deficit_ge_linear {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    c * r - (5 / 4 + tauPhiC0) * c ^ 2
      ≤ Submission.BoseGases.fsKinCoeff c r - c ^ 2 * tauPhi (r / c) := by
  unfold tauPhiC0
  rcases le_or_gt r c with hle | hlt
  · have hz : tauPhi (r / c) = 0 :=
      tauPhi_zero_of_le_one (r / c) (by rw [div_le_one hc]; exact hle)
    have hs : Submission.BoseGases.fsKinCoeff c r = 0 := by
      rw [Submission.BoseGases.fsKinCoeff, max_eq_right (by linarith : r - c ≤ 0)]; ring
    rw [hz, mul_zero, hs, sub_zero]
    have h1 : c * r ≤ c ^ 2 := by nlinarith
    have h2 : c ^ 2 ≤ (5 / 4 + ∫ t, t ^ 2 * tauKer t) * c ^ 2 := by
      have := tauKer_moment2_nonneg
      nlinarith
    linarith
  · have hq := tauPhi_le_quad (r / c)
    have hsq : c ^ 2 * tauPhi (r / c)
        ≤ (r - 3 * c / 2) ^ 2 + c ^ 2 * ∫ t, t ^ 2 * tauKer t := by
      have h := mul_le_mul_of_nonneg_left hq (sq_nonneg c)
      rw [mul_add] at h
      have h2 : c ^ 2 * (r / c - 3 / 2) ^ 2 = (r - 3 * c / 2) ^ 2 := by
        rw [show c ^ 2 * (r / c - 3 / 2) ^ 2 = (c * (r / c - 3 / 2)) ^ 2 from by ring]
        congr 1
        field_simp
      linarith [h, h2.le]
    have hsh : Submission.BoseGases.fsKinCoeff c r = (r - c) ^ 2 := by
      rw [Submission.BoseGases.fsKinCoeff, max_eq_left (by linarith : (0 : ℝ) ≤ r - c)]
    rw [hsh]
    have hident : (r - 3 * c / 2) ^ 2 = (r - c) ^ 2 - (c * r - 5 * c ^ 2 / 4) := by ring
    linarith [hsq, hident.le, hident.ge]

/-- **The target reduced to the corpus's canonical deficit inequality `(D)`.**

The bridge `Work.BoseBoxFock.tauPhi_row_lattice_of_deficit` (PROVED, axiom-clean) is exactly
`(D) ⟹ Row` for the *closed*-ball class; the present target's class is the *open* ball of radius
`ℓ/2`, which is contained in the closed one, so the reduction applies verbatim.  `(D)` is

    (D)   c·(3·S₁ − 2·R₁) + L(τ̃Ψ_c) − C(Θ_c) ≥ (5/4 + c₀)·c²·R₀ ,

with `S₁ = Σₙℓ⁻³‖kₙ‖‖ĝ(kₙ)‖²`, `R₁ = (2π)⁻³∫‖p‖‖ĝ(p)‖²`, `R₀ = (2π)⁻³∫‖ĝ‖²`,
`Ψ_c = τ̃ρ_c − τ̃_c ≥ 0` the convexity defect (`tauGapDefs.tauPsi`),
`Θ_c = (c−r)₊²` (`tauGapDefs.tauTheta`) and `c₀ = tauC0phi`; `L`, `C` are the lattice and
continuum forms.  By `row_of_deficit` + `deficit_inputs` (both PROVED) `(D)` is *equivalent* to
the row, and it is the corpus's long-open quantitative aliasing crux (`deficitAlias` /
`heatSampling_le`) in a state-adapted form; see `FINDING_tauPhi_row_lattice.md` §6–§7 for its two
halves.  So this lemma isolates the *only* open input of `Work.BoseBoxFock.tauPhi_row`. -/
theorem tauPhi_row_of_deficit {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2))
    (hdef : c * (3 * (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖
              * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
            - 2 * (((2 * Real.pi) ^ 3)⁻¹
              * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2))
          + (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Work.BoseBoxFock.tauPsi c
                ‖Work.BoseBoxFock.kmomInt ℓ n‖
              * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
          - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseBoxFock.tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2
        ≥ (5 / 4 + Work.BoseBoxFock.tauC0phi) * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹
            * ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
  tauPhi_row_lattice_of_deficit hℓ hc hg hgc (hgsupp.trans Metric.ball_subset_closedBall) hdef

/-- **Assembly step** (`FINDING_tauPhi_row.md` §4 item 0): the *windowed* row
`Work.BoseBoxFock.tauPhiRowWindow` gives the target's inequality for every state that admits a
`χ_Λ`-factorisation `g = χ_Λ·h` with `h` smooth of compact support in `boxL ℓ`.  By
`Work.BoseBoxFock.chiLamFactorLift` (delegated) *every* state of the target's class admits such a
factorisation, so the target itself will be
`tauPhi_row_of_windowed hℓ hc hcℓ hg hgc hgsupp (chiLamFactorLift hℓ hg hgc hgsupp)`
once the windowed row is proved. -/
theorem tauPhi_row_of_windowed {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2))
    (hf : ∃ h : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ (⊤ : ENat) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ Work.BoseK15.corpusBox.boxL ℓ ∧
        (∀ z, g z = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * h z)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
  tauPhiRowWindow hℓ hc hcℓ hf

/-- **The row follows from the elementary hinge residual `Work.BoseBoxFock.hingeRow`.**

This is the *cleanest* reduction of the target: by the PROVED pointwise domination
`rescaled_tauPhi_le_conv` (`c²·tauPhi (r/c) ≤ (max 0 (r − 5c/4))²`), the smoothed profile is below
the **hinge** at `5c/4`; the row is therefore dominated termwise by the lattice hinge series, and
`hingeRow` bounds the latter by the continuum integral at the sharp symbol
`fsKinCoeff c r = (max 0 (r−c))²`.

Both series are summable by `summable_of_quad_growth` (the two symbols grow at most like
`2r² + (25/8)c²`), so the comparison is `Summable.tsum_le_tsum`.  (`hcℓ` and `hgsupp` are not used:
all the analytic content sits in `hhinge`.) -/
theorem tauPhi_row_of_hinge {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2))
    (hhinge : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (max 0 (‖Work.BoseBoxFock.kmomInt ℓ n‖ - 5 * c / 4)) ^ 2 *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
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
      (max 0 (‖Work.BoseBoxFock.kmomInt ℓ n‖ - 5 * c / 4)) ^ 2 *
      ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) :=
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

theorem tauPhi_row_of_sTailLambda {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2))
    (hlam : sTailLat ℓ (5 * c / 4) g ≤
      ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p in {p : EuclideanSpace ℝ (Fin 3) | 5 * c / 4 ≤ ‖p‖},
          (‖p‖ - c) ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  refine tauPhi_row_of_hinge hℓ hc hcℓ hg hgc hgsupp ?_
  have h1 : sTailLat ℓ (5 * c / 4) g
      = ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * (max 0 (‖Work.BoseBoxFock.kmomInt ℓ n‖ - 5 * c / 4)) ^ 2
          * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 := by
    rw [sTailLat]
    refine tsum_congr (fun n => ?_)
    rw [Submission.BoseGases.fsKinCoeff, max_comm]
  rw [h1] at hlam
  have hInt : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
    have hcont : Continuous (Submission.BoseGases.kinFT g) :=
      Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable
        (hg.continuous.integrable_of_hasCompactSupport (μ := volume) hgc)
    have hcontfs : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      simp only [Submission.BoseGases.fsKinCoeff]
      exact ((continuous_norm.sub continuous_const).max continuous_const).pow 2
    refine (Work.BoseBoxFock.SqrtKin.kinFT_weight2_integrable hg hgc).mono'
      (hcontfs.mul (hcont.norm.pow 2)).aestronglyMeasurable ?_
    filter_upwards with p
    rw [Real.norm_of_nonneg
      (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (by positivity))]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [Submission.BoseGases.fsKinCoeff]
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith [norm_nonneg p]) (norm_nonneg p)) 2
  have hset : (∫ p in {p : EuclideanSpace ℝ (Fin 3) | 5 * c / 4 ≤ ‖p‖},
        (‖p‖ - c) ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      = ∫ p in {p : EuclideanSpace ℝ (Fin 3) | 5 * c / 4 ≤ ‖p‖},
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
    refine setIntegral_congr_fun (measurableSet_le measurable_const measurable_norm)
      (fun p hp => ?_)
    have hp' : 5 * c / 4 ≤ ‖p‖ := hp
    have hcp : c ≤ ‖p‖ := by linarith [hp', hc]
    rw [Submission.BoseGases.fsKinCoeff, max_eq_left (by linarith : (0 : ℝ) ≤ ‖p‖ - c)]
  rw [hset] at hlam
  refine le_trans hlam (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact setIntegral_le_integral hInt
    (Filter.Eventually.of_forall (fun p => mul_nonneg
      (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _)))

theorem tauPhi_row {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
  tauPhi_row_of_hinge hℓ hc hcℓ hg hgc hgsupp (hingeRow hℓ hc hcℓ hg hgc hgsupp)
