import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.QC

open MeasureTheory Complex Function Filter
open scoped ENNReal Convolution Topology

/-!
## The total derivative is controlled by the two Wirtinger derivatives

For `f : ℂ → ℂ` with real Fréchet derivative `Df = fderiv ℝ f`, the two Wirtinger
derivatives of `Work.MRMT` are

`dz f z = (Df z 1 - I * Df z I)/2`,  `dzbar f z = (Df z 1 + I * Df z I)/2`,

so that `Df z 1 = dz f z + dzbar f z` and `Df z I = (dzbar f z - dz f z)/I`.

Since `{1, I}` spans `ℂ` over `ℝ`, the operator norm of `Df z` is controlled by its
values on `1` and `I`; each of those is a combination of the two Wirtinger
derivatives, giving the pointwise bound

`‖Df z‖ ≤ 2 * (‖dz f z‖ + ‖dzbar f z‖)`.

Integrating this pointwise bound with the `L²` triangle inequality yields the
`L²` statement.  No integrability hypothesis is needed: both sides are extended
nonnegative `L²` seminorms (`⊤` if the relevant function is not a.e. strongly
measurable), and `fderiv` of *any* function is Borel measurable, hence a.e.
strongly measurable.
-/

/-- The operator norm of a real-linear map `ℂ → ℂ` is bounded by the sum of the norms
of its values on the real basis `1, I` of `ℂ`. -/
lemma opNorm_le_norm_apply_one_add_I (T : ℂ →L[ℝ] ℂ) :
    ‖T‖ ≤ ‖T 1‖ + ‖T Complex.I‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  have hT : T v = v.re • T 1 + v.im • T Complex.I := by
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul]
  calc
    ‖T v‖ = ‖v.re • T 1 + v.im • T Complex.I‖ := by rw [hT]
    _ ≤ ‖v.re • T 1‖ + ‖v.im • T Complex.I‖ := norm_add_le _ _
    _ = |v.re| * ‖T 1‖ + |v.im| * ‖T Complex.I‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖v‖ * ‖T 1‖ + ‖v‖ * ‖T Complex.I‖ := by
          gcongr
          · exact Complex.abs_re_le_norm v
          · exact Complex.abs_im_le_norm v
    _ = (‖T 1‖ + ‖T Complex.I‖) * ‖v‖ := by ring

/-- For a real-linear map `T : ℂ → ℂ`, the sum of the norms of `T 1` and `T I` is
bounded by twice the sum of the norms of the two Wirtinger combinations
`(T 1 ∓ I * T I)/2`. -/
lemma norm_apply_one_add_I_le_two_mul (T : ℂ →L[ℝ] ℂ) :
    ‖T 1‖ + ‖T Complex.I‖ ≤
      2 * (‖(T 1 - Complex.I * T Complex.I)/2‖ + ‖(T 1 + Complex.I * T Complex.I)/2‖) := by
  set d := (T 1 - Complex.I * T Complex.I)/2 with hd'
  set e := (T 1 + Complex.I * T Complex.I)/2 with he'
  have hd : T 1 = d + e := by rw [hd', he']; ring
  have hed : e - d = Complex.I * T Complex.I := by rw [hd', he']; ring
  have hb : T Complex.I = -Complex.I * (e - d) := by
    rw [hed]; ring_nf; simp
  have hA : ‖T 1‖ ≤ ‖d‖ + ‖e‖ := by rw [hd]; exact norm_add_le _ _
  have hB : ‖T Complex.I‖ ≤ ‖d‖ + ‖e‖ := by
    rw [hb]
    have h3 : ‖-Complex.I * (e - d)‖ = ‖e - d‖ := by simp
    rw [h3]
    have h4 := norm_sub_le e d
    linarith
  linarith

/-- Pointwise form of the inequality: the operator norm of the real Fréchet derivative
is at most twice the sum of the moduli of the two Wirtinger derivatives. -/
lemma norm_fderiv_le_two_mul_add (f : ℂ → ℂ) (z : ℂ) :
    ‖fderiv ℝ f z‖ ≤ 2 * (‖Work.MRMT.dz f z‖ + ‖Work.MRMT.dzbar f z‖) := by
  refine (opNorm_le_norm_apply_one_add_I (fderiv ℝ f z)).trans ?_
  have h := norm_apply_one_add_I_le_two_mul (fderiv ℝ f z)
  have hde : (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I)/2 = Work.MRMT.dz f z := by
    simp [Work.MRMT.dz]
  have hee : (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)/2 = Work.MRMT.dzbar f z := by
    simp [Work.MRMT.dzbar]
  rwa [hde, hee] at h

/-- Measurability of the Wirtinger derivative `dz`, as a continuous combination of the
(everywhere defined, Borel measurable) real Fréchet derivative. -/
lemma measurable_dz (f : ℂ → ℂ) : Measurable (Work.MRMT.dz f) := by
  have h1 : Measurable fun z => fderiv ℝ f z (1 : ℂ) := measurable_fderiv_apply_const ℝ f 1
  have h2 : Measurable fun z => fderiv ℝ f z Complex.I :=
    measurable_fderiv_apply_const ℝ f Complex.I
  exact ((h1.sub (measurable_const.mul h2)).div_const 2)

/-- Measurability of the Wirtinger derivative `dzbar`. -/
lemma measurable_dzbar (f : ℂ → ℂ) : Measurable (Work.MRMT.dzbar f) := by
  have h1 : Measurable fun z => fderiv ℝ f z (1 : ℂ) := measurable_fderiv_apply_const ℝ f 1
  have h2 : Measurable fun z => fderiv ℝ f z Complex.I :=
    measurable_fderiv_apply_const ℝ f Complex.I
  exact ((h1.add (measurable_const.mul h2)).div_const 2)

theorem eLpNorm_fderiv_le_two_mul_add (f : ℂ → ℂ) :
    eLpNorm (fderiv ℝ f) 2 volume ≤
      2 * (eLpNorm (Work.MRMT.dz f) 2 volume + eLpNorm (Work.MRMT.dzbar f) 2 volume) := by
  have hf : AEStronglyMeasurable (fderiv ℝ f) volume :=
    (measurable_fderiv ℝ f).aestronglyMeasurable
  have hdz : AEStronglyMeasurable (Work.MRMT.dz f) volume :=
    (measurable_dz f).aestronglyMeasurable
  have hdzbar : AEStronglyMeasurable (Work.MRMT.dzbar f) volume :=
    (measurable_dzbar f).aestronglyMeasurable
  calc
    eLpNorm (fderiv ℝ f) 2 volume
        ≤ eLpNorm (fun z => 2 * (‖Work.MRMT.dz f z‖ + ‖Work.MRMT.dzbar f z‖)) 2 volume :=
          eLpNorm_mono_real hf (norm_fderiv_le_two_mul_add f)
    _ = 2 * eLpNorm (fun z => ‖Work.MRMT.dz f z‖ + ‖Work.MRMT.dzbar f z‖) 2 volume := by
          have h : (fun z => 2 * (‖Work.MRMT.dz f z‖ + ‖Work.MRMT.dzbar f z‖))
              = (2 : ℝ) • (fun z => ‖Work.MRMT.dz f z‖ + ‖Work.MRMT.dzbar f z‖) := by
            ext z; simp [smul_eq_mul]
          rw [h, eLpNorm_const_smul, enorm_eq_nnnorm]
          norm_num
    _ ≤ 2 * (eLpNorm (fun z => ‖Work.MRMT.dz f z‖) 2 volume
              + eLpNorm (fun z => ‖Work.MRMT.dzbar f z‖) 2 volume) := by
          gcongr
          exact eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ = 2 * (eLpNorm (Work.MRMT.dz f) 2 volume + eLpNorm (Work.MRMT.dzbar f) 2 volume) := by
          rw [eLpNorm_norm _ hdz, eLpNorm_norm _ hdzbar]

end Work.MRMT.QC
