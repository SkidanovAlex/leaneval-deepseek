import Mathlib
import Submission.Work.KMTAreas.A7.fiberOpVarNonFareyBounded
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## The `ℓ^q` step of the fibre variational estimate, from a kernel-mass bound

The pointwise Young inequality `fiberOpVarYoungExact` bounds the variational norm of the fibre
`n ↦ fiberOp ρ l (mStarF U) n₀ (w n)` at a point `x` by the `ℓ¹`-weighted sum
`∑'_j ‖κ_{n₀} j‖ · V^r(w)(x - j)` of the *shifted* input variational norms, with kernel
`κ_{n₀} j = (∑_{α ∈ (ℚ/ℤ)_{≤l}} e(α (n₀ - j))) · cw (mStarF U) j`.  Taking `ℓ^q` of that bound is
Young's (Minkowski's) inequality for the lattice convolution with the counting measure, and it
costs exactly the `ℓ¹`-mass `∑'_j ‖κ_{n₀} j‖` of the kernel.

This module isolates that analytic step in the form needed downstream: **if the kernel mass is at
most `C`, then the fibre does not increase the `ℓ^q(ℤ; V^r)`-norm, with constant `C`** — no
hypothesis on `n₀`, on `l`, on the scale `U`, or on the family `w`.  The arithmetic input (a bound
on the kernel mass) is the subject of the sibling modules. -/

/-- **Minkowski/Young for `ℝ≥0∞`-valued functions on the counting measure of `ℤ`.**  For `q ≥ 1`,
`K : ℤ → ℂ` and `W : ℤ → ℝ≥0∞`,

  `‖ x ↦ ∑'_j ‖K j‖ · W (x - j) ‖_{ℓ^q} ≤ (∑'_j ‖K j‖) · ‖W‖_{ℓ^q}`.

(Reproduced from `Work.KMTAreas.A7Hi.FiberOpCutBoundLevelOne` / `Work.KMTAreas.A7.fiberOpVarNonFareyBounded`,
where the same argument is private, so that this module is self-contained.) -/
private theorem eLpNorm_tsum_enorm_mul_sub_le (q : ℝ) (hq : 1 ≤ q) (K : ℤ → ℂ)
    (W : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => ∑' j : ℤ, ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
      ≤ (∑' j : ℤ, ‖K j‖ₑ) * eLpNorm W (ENNReal.ofReal q) Measure.count := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hmink := eLpNorm_tsum_le_tsum_eLpNorm (μ := Measure.count) (p := ENNReal.ofReal q)
    (ENNReal.one_le_ofReal.mpr hq) (f := fun j : ℤ => fun x : ℤ => ‖K j‖ₑ * W (x - j))
    (fun j => (measurable_of_countable (fun x : ℤ => ‖K j‖ₑ * W (x - j))).aemeasurable)
  have hconst : ∀ j : ℤ,
      eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
        = ‖K j‖ₑ * eLpNorm W (ENNReal.ofReal q) Measure.count := by
    intro j
    rw [show eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
        = eLpNorm (fun x : ℤ => ‖K j‖ₑ * W x) (ENNReal.ofReal q) Measure.count from
        Commons.Analysis.Convolution.eLpNorm_sub_right_ennreal (fun y : ℤ => ‖K j‖ₑ * W y) j hq0]
    exact Commons.Analysis.Convolution.eLpNorm_const_mul_ennreal_of_pos
      (f := W) (measurable_of_countable W).aemeasurable (‖K j‖ₑ) hq0
  refine hmink.trans_eq ?_
  rw [tsum_congr hconst, ENNReal.tsum_mul_right]

/-- **The `ℓ^q` fibre bound from a kernel-mass bound.**  If the fibre kernel of the bump `mStarF U`
at the level `l`,
`j ↦ (∑_{α ∈ (ℚ/ℤ)_{≤l}} e(α (n₀ - j))) · cw (mStarF U) j`, has total `ℓ¹`-mass at most `C`, then the
fibre `fiberOp ρ l (mStarF U) n₀` does not increase the `ℓ^q(ℤ; V^r)`-norm of any family
`n ↦ w n`, with constant `C`. -/
theorem eLpNorm_varNorm_fiberOp_le_of_mass (r : NNReal) (hr : 1 ≤ r) (ρ : ℝ) (l U : ℕ)
    (n₀ : ℤ) (w : ℕ → ℤ → ℂ) {C : ℝ} (hC : 0 ≤ C) {q : ℝ} (hq : 1 ≤ q)
    (hmass : (∑' j : ℤ, ‖(∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
        fourier (T := 1) (n₀ - j) α) * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖ₑ)
      ≤ ENNReal.ofReal C) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStarF U) n₀ (w n) x))
      (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x))
        (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  set W : ℤ → ℝ≥0∞ := fun x => variationalNorm r (fun n : ℕ => w n x) with hW
  -- Step 1: Young's inequality for the variational norm of the fibre, pointwise in `x`.
  have hpt : ∀ x : ℤ, variationalNorm r (fun n : ℕ =>
        Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStarF U) n₀ (w n) x)
      ≤ ∑' j : ℤ, ‖(∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
            fourier (T := 1) (n₀ - j) α) * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖ₑ
          * W (x - j) := by
    intro x
    exact Work.KMTAreas.A7.fiberOpVarYoungExact ρ l (Work.KMTAreas.A7.mStarF U) n₀ w r hr x
  -- Step 2: monotonicity of `eLpNorm`, Minkowski/Young in `ℓ^q`, then the kernel-mass bound.
  have h1 : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStarF U) n₀ (w n) x))
        (ENNReal.ofReal q) Measure.count
      ≤ eLpNorm (fun x : ℤ => ∑' j : ℤ,
            ‖(∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
              fourier (T := 1) (n₀ - j) α)
              * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖ₑ * W (x - j))
          (ENNReal.ofReal q) Measure.count := by
    refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)
    simpa only [enorm_eq_self] using hpt x
  have h2 := eLpNorm_tsum_enorm_mul_sub_le q hq
    (fun j : ℤ => (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      fourier (T := 1) (n₀ - j) α) * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j) W
  exact h1.trans (h2.trans (mul_le_mul' hmass le_rfl))

end Work.KMTAreas.A7
