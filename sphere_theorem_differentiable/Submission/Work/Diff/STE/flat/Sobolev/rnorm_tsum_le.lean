import Mathlib
import Submission.Work.Diff.STE.flat.Sobolev

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `L^q` triangle inequality for `rnorm` (Minkowski for series)

`Work.Diff.STE.flat.rnorm q g = (∫_{unitCube} ‖g x‖ ^ q) ^ (1/q)` is the `L^q` (semi)norm of `g`
on the unit cube.  This file proves the countable Minkowski inequality
`rnorm q (Σ' g m) ≤ Σ' rnorm q (g m)` for `q ≥ 1`.

The proof goes through Mathlib's `eLpNorm` (which is the honest `L^q` seminorm, i.e. never
junk-zero while the integral is infinite):

* `rnorm eq eLpNorm.toReal` (always, for an `AEStronglyMeasurable` function), and in the
  `MemLp` case the two are exactly related by `ofReal` (`eLpNorm_eq_ofReal_rnorm`);
* `eLpNorm` is lower semicontinuous under a.e. convergence (`Lp.eLpNorm_le_of_ae_tendsto`),
  which combined with the finite-sum triangle inequality `eLpNorm_sum_le` gives Fatou's lemma
  for series;
* the a.e. convergence of the partial sums uses
  `MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top`.
-/

noncomputable section

open MeasureTheory ENNReal Filter
open scoped Topology

namespace Work.Diff.STE.flat.Sobolev

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The measure of the unit cube, i.e. the measure appearing in `rnorm`. -/
noncomputable abbrev cubeMeasure (ι : Type*) [Fintype ι] : MeasureTheory.Measure (ι → ℝ) :=
  MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))

/-- For a function in `L^q` the honest `L^q` seminorm `eLpNorm` and `rnorm` agree, the first being
the image of the second under `ENNReal.ofReal`. -/
lemma eLpNorm_eq_ofReal_rnorm {ι : Type*} [Fintype ι] (q : ℝ) (hq : 1 ≤ q)
    {g : (ι → ℝ) → ℂ} (hm : MemLp g (ENNReal.ofReal q) (cubeMeasure ι)) :
    eLpNorm g (ENNReal.ofReal q) (cubeMeasure ι)
      = ENNReal.ofReal (Work.Diff.STE.flat.rnorm q g) := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hp0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hptop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [hm.eLpNorm_eq_integral_rpow_norm hp0 hptop, ENNReal.toReal_ofReal hq0,
    Work.Diff.STE.flat.rnorm, one_div]

/-- `rnorm` is the real part of the honest `L^q` seminorm `eLpNorm` (`ENNReal.toReal`); this holds
for every almost everywhere strongly measurable function, the value `0` of the `toReal` of `⊤`
matching the junk value `0` of the Bochner integral of a non-integrable function. -/
lemma rnorm_eq_toReal_eLpNorm {ι : Type*} [Fintype ι] (q : ℝ) (hq : 1 ≤ q)
    {g : (ι → ℝ) → ℂ} (hg : AEStronglyMeasurable g (cubeMeasure ι)) :
    Work.Diff.STE.flat.rnorm q g = (eLpNorm g (ENNReal.ofReal q) (cubeMeasure ι)).toReal := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have hp0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hptop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0
  have hmeas : AEStronglyMeasurable (fun x : ι → ℝ => ‖g x‖ ^ q) (cubeMeasure ι) :=
    (hg.norm.aemeasurable.pow_const q).aestronglyMeasurable
  have hL : ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q) ∂(cubeMeasure ι)
      = ∫⁻ x, ‖g x‖ₑ ^ q ∂(cubeMeasure ι) := by
    refine MeasureTheory.lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0, ofReal_norm]
  have hInt : ∫ x, ‖g x‖ ^ q ∂(cubeMeasure ι)
      = (∫⁻ x, ‖g x‖ₑ ^ q ∂(cubeMeasure ι)).toReal := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖g x‖ ^ q)
      (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg (g x)) q) hmeas, hL]
  have heLp : eLpNorm g (ENNReal.ofReal q) (cubeMeasure ι)
      = (∫⁻ x, ‖g x‖ₑ ^ q ∂(cubeMeasure ι)) ^ (1 / q) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hg, hqr]
  show (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ q) ^ (1 / q) = _
  calc (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ q) ^ (1 / q)
      = ((∫⁻ x, ‖g x‖ₑ ^ q ∂(cubeMeasure ι)).toReal) ^ (1 / q) := by
        rw [show (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖g x‖ ^ q)
              = ∫ x, ‖g x‖ ^ q ∂(cubeMeasure ι) from rfl, hInt]
    _ = ((∫⁻ x, ‖g x‖ₑ ^ q ∂(cubeMeasure ι)) ^ (1 / q)).toReal :=
        ENNReal.toReal_rpow _ _
    _ = (eLpNorm g (ENNReal.ofReal q) (cubeMeasure ι)).toReal := by rw [heLp]

theorem rnorm_tsum_le {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℝ) (hq : 1 ≤ q)
    {g : ℕ → (ι → ℝ) → ℂ} {f : (ι → ℝ) → ℂ}
    (hm : ∀ m : ℕ, MeasureTheory.MemLp (g m) (ENNReal.ofReal q)
        (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))))
    (hf : AEMeasurable f
        (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))))
    (hfg : ∀ x : ι → ℝ, f x = ∑' m : ℕ, g m x)
    (hsum : Summable fun m : ℕ => Work.Diff.STE.flat.rnorm q (g m)) :
    Work.Diff.STE.flat.rnorm q f ≤ ∑' m : ℕ, Work.Diff.STE.flat.rnorm q (g m) := by
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  have hS : 0 ≤ ∑' m : ℕ, Work.Diff.STE.flat.rnorm q (g m) :=
    tsum_nonneg fun m => Work.Diff.STE.flat.rnorm_nonneg q (g m)
  -- the `L^q` norm of each term, in terms of `rnorm`
  have hE : ∀ m : ℕ, eLpNorm (g m) (ENNReal.ofReal q) (cubeMeasure ι)
      = ENNReal.ofReal (Work.Diff.STE.flat.rnorm q (g m)) :=
    fun m => eLpNorm_eq_ofReal_rnorm q hq (hm m)
  have htsum : ∑' m : ℕ, eLpNorm (g m) (ENNReal.ofReal q) (cubeMeasure ι)
      = ENNReal.ofReal (∑' m : ℕ, Work.Diff.STE.flat.rnorm q (g m)) := by
    simp only [hE]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun m => Work.Diff.STE.flat.rnorm_nonneg q (g m)) hsum).symm
  -- the norms of the terms are almost everywhere summable
  have hae : ∀ᵐ x ∂(cubeMeasure ι), Summable fun m : ℕ => ‖g m x‖ :=
    MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top hp1
      (by rw [htsum]; exact ENNReal.ofReal_ne_top)
  -- hence the partial sums converge almost everywhere to `f`
  have hconv : ∀ᵐ x ∂(cubeMeasure ι),
      Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n, g m) x) atTop (𝓝 (f x)) := by
    filter_upwards [hae] with x hx
    have h2 : Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n, g m) x) atTop
        (𝓝 (∑' m : ℕ, g m x)) := by
      simpa using hx.of_norm.hasSum.tendsto_sum_nat
    rwa [← hfg x] at h2
  -- the uniform bound on the `L^q` norms of the partial sums, from Minkowski
  have hbound : ∀ n : ℕ, eLpNorm (∑ m ∈ Finset.range n, g m)
        (ENNReal.ofReal q) (cubeMeasure ι)
      ≤ ENNReal.ofReal (∑' m : ℕ, Work.Diff.STE.flat.rnorm q (g m)) := by
    intro n
    have h1 : eLpNorm (∑ m ∈ Finset.range n, g m) (ENNReal.ofReal q) (cubeMeasure ι)
        ≤ ∑ m ∈ Finset.range n, eLpNorm (g m) (ENNReal.ofReal q) (cubeMeasure ι) :=
      MeasureTheory.eLpNorm_sum_le hp1
    have h2 : ∑ m ∈ Finset.range n, eLpNorm (g m) (ENNReal.ofReal q) (cubeMeasure ι)
        = ENNReal.ofReal (∑ m ∈ Finset.range n, Work.Diff.STE.flat.rnorm q (g m)) := by
      simp only [hE]
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun i _ => Work.Diff.STE.flat.rnorm_nonneg q (g i))).symm
    have h3 : ∑ m ∈ Finset.range n, Work.Diff.STE.flat.rnorm q (g m)
        ≤ ∑' m : ℕ, Work.Diff.STE.flat.rnorm q (g m) :=
      Summable.sum_le_tsum (Finset.range n)
        (fun i _ => Work.Diff.STE.flat.rnorm_nonneg q (g i)) hsum
    calc eLpNorm (∑ m ∈ Finset.range n, g m) (ENNReal.ofReal q) (cubeMeasure ι)
        ≤ ∑ m ∈ Finset.range n, eLpNorm (g m) (ENNReal.ofReal q) (cubeMeasure ι) := h1
      _ = ENNReal.ofReal (∑ m ∈ Finset.range n, Work.Diff.STE.flat.rnorm q (g m)) := h2
      _ ≤ ENNReal.ofReal (∑' m : ℕ, Work.Diff.STE.flat.rnorm q (g m)) :=
          ENNReal.ofReal_le_ofReal h3
  -- Fatou
  have hmain : eLpNorm f (ENNReal.ofReal q) (cubeMeasure ι)
      ≤ ENNReal.ofReal (∑' m : ℕ, Work.Diff.STE.flat.rnorm q (g m)) :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall hbound)
      (fun n => Finset.aestronglyMeasurable_sum _ fun m _ => (hm m).aestronglyMeasurable)
      hf.aestronglyMeasurable hconv
  -- pass from `eLpNorm` back to `rnorm`
  have hfin : ENNReal.ofReal (Work.Diff.STE.flat.rnorm q f)
      ≤ eLpNorm f (ENNReal.ofReal q) (cubeMeasure ι) :=
    calc ENNReal.ofReal (Work.Diff.STE.flat.rnorm q f)
        = ENNReal.ofReal ((eLpNorm f (ENNReal.ofReal q) (cubeMeasure ι)).toReal) := by
          rw [rnorm_eq_toReal_eLpNorm q hq hf.aestronglyMeasurable]
      _ ≤ eLpNorm f (ENNReal.ofReal q) (cubeMeasure ι) := ENNReal.ofReal_toReal_le
  exact (ENNReal.ofReal_le_ofReal_iff hS).mp (le_trans hfin hmain)

end Work.Diff.STE.flat.Sobolev
