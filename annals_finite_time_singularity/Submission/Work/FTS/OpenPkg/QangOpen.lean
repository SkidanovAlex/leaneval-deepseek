
/-
# `OpenPkg/QangOpen` — the open-quadrant migration of the `Qang` chain

The delivered chain `Work.FTS.H2.QangAux` → `QangBox` → `Qang_sq_leQ` → `QangDiff` →
`N4Fields.Qang_sq_w_sq_integral` → `N4Fields.DzdIter_Qang_ae` proves, in the *interior* class
`SmoothQuad g` (`C^∞` on `z > -1`), the primitive identity

  `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`   (`j ≤ 3`, `z, z₀ > 0`)

for the angular moments `Qang g j z = ∫_θ Kθ(θ)·(D_z^j g)(z,θ) dθ`, and hence
`D_z^i (Qang g 0) = Qang g i` almost everywhere (`i ≤ 4`) and
`∫_z (Qang g i z)² w(z)² dz ≤ (∫_θ Kθ²)·HkSq α 4 g`.

The open-quadrant class of the vocabulary `Work.FTS.VocabO` (`HQo`) only supplies
`Work.FTS.EllipticEst.SmoothOpen g` (smoothness on `z > 0`, no hypothesis on the strip
`-1 < z ≤ 0`) together with `HkMem α 4 g`.  Every proof of the delivered chain, however, only
ever uses the *open-quadrant* facts `SmoothOpen.DzIter`, `SmoothOpen.curry_θ` and the `θ`-slice
continuity at `z > 0`, plus the Fubini/Lebesgue-differentiation arguments which take place on
compact subintervals of `(0,∞)`.  This module is the faithful re-run of that chain with the
hypothesis weakened from `SmoothQuad` to `SmoothOpen`; the proofs are those of the sibling
modules, with `SmoothQuad.toSmoothOpen` deleted (the hypothesis *is* `SmoothOpen`).

`Good`/`fkH_field` consumes `Qang_sq_w_sq_integral_open` and `DzdIter_Qang_ae_open` to identify
the angular moment `FK g = Qang g 0` of a datum `g` of the open class as an `ℋ⁴`-function.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.H2.QangAux
import Submission.Work.FTS.H2.QangBox
import Submission.Work.FTS.H2.Qang_sq_leQ
import Submission.Work.FTS.H2.QangDiff
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.DzIter_slice_FTC_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.QangOpen

open Work.FTS.H2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The primitive formula along a `z`-slice.**  For `g` of class `SmoothQuad`, every
`j : ℕ`, every `z, z₀ > 0` and every `θ ∈ (0,π/2)`,

  `D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^{z} D_z^{j+1} g x θ / x dx`. -/
theorem QangSliceFTC_open {g : ℝ → ℝ → ℝ} (hO : Work.FTS.EllipticEst.SmoothOpen g) (j : ℕ)
    {z z₀ θ : ℝ} (hz : 0 < z) (hz₀ : 0 < z₀) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ
      = ∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x := by
  -- the derivative of the `θ`-slice of `D_z^j g`, in divided form
  have hderiv : ∀ r : ℝ, r ∈ Set.uIcc z₀ z →
      Work.Spaces.pz (Work.Spaces.DzIter j g) r θ
        = Work.Spaces.DzIter (j + 1) g r θ / r := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le (lt_min hz₀ hz) hr.1
    have h1 : Work.Spaces.DzIter (j + 1) g r θ
        = r * Work.Spaces.pz (Work.Spaces.DzIter j g) r θ := rfl
    rw [h1, mul_comm r, mul_div_cancel_right₀ _ (ne_of_gt hrpos)]
  rcases le_total z₀ z with hle | hle
  · have hF := Work.FTS.EllipticEst.DzIter_slice_FTC_open hO j hz₀ hle hθ
    rw [hF]
    refine intervalIntegral.integral_congr (a := z₀) (b := z)
      (f := fun r => Work.Spaces.pz (Work.Spaces.DzIter j g) r θ)
      (g := fun r => Work.Spaces.DzIter (j + 1) g r θ / r) (fun r hr => hderiv r hr)
  · have hF := Work.FTS.EllipticEst.DzIter_slice_FTC_open hO j hz hle hθ
    have hF' : Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ
        = -∫ r in z..z₀, Work.Spaces.pz (Work.Spaces.DzIter j g) r θ := by
      linarith [hF]
    rw [hF']
    rw [intervalIntegral.integral_congr (a := z) (b := z₀)
      (f := fun r => Work.Spaces.pz (Work.Spaces.DzIter j g) r θ)
      (g := fun r => Work.Spaces.DzIter (j + 1) g r θ / r)
      (fun r hr => hderiv r (by rwa [Set.uIcc_comm]))]
    rw [intervalIntegral.integral_symm, neg_neg]

/-! ## Integrability of the angular slice of `Ktheta · D_z^j g` -/

/-- The pair `(z,θ) ↦ Ktheta θ · D_z^j g z θ` is continuous on the open quadrant. -/
theorem continuousOn_Ktheta_DzIter_open {g : ℝ → ℝ → ℝ} (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
      * Work.Spaces.DzIter j g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hK : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
        = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
      ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hO.DzIter j).continuousOn
  refine (hD.mul hK).congr (fun p hp => ?_)
  exact mul_comm _ _

/-- **The angular slice `θ ↦ Ktheta θ · D_z^j g z θ` is integrable on `Iθ`** for `z > 0` and
`j ≤ 4`, in the interior class `SmoothQuad g + HkMem α 4 g`. -/
theorem QangSliceIntegrable_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
      Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_Ktheta_DzIter_open hO j) hz
  have hmaj : MeasureTheory.Integrable (fun θ : ℝ =>
      3 * (Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.Integrable (fun θ : ℝ =>
        Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hmem.1 z (Set.mem_Ici.mpr hz.le)).div_const _
    have h2 : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ)) (by
        rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    exact (h1.add h2).const_mul 3
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  rw [show (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) from by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hKh := abs_Ktheta_le_three θ
  have hDh := sq_DzIter_le_HkIntegrand_div_w_sq α 4 g j hj hz hθ
  have hsq : |Work.Spaces.DzIter j g z θ| ≤ (Work.Spaces.DzIter j g z θ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|Work.Spaces.DzIter j g z θ| - 1),
      sq_abs (Work.Spaces.DzIter j g z θ), abs_nonneg (Work.Spaces.DzIter j g z θ)]
  have hDnn : 0 ≤ |Work.Spaces.DzIter j g z θ| := abs_nonneg _
  have hDh' : |Work.Spaces.DzIter j g z θ|
      ≤ Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1 :=
    le_trans hsq (by linarith)
  calc |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ|
      ≤ 3 * |Work.Spaces.DzIter j g z θ| := mul_le_mul_of_nonneg_right hKh hDnn
    _ ≤ 3 * (Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left hDh' (by norm_num)


/-- The uncurried `ℋ⁴`-integrand of a `SmoothQuad` function is a.e. strongly measurable for the
product of the restrictions of Lebesgue measure. -/
theorem aesm_joint_HkIntegrand_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (hO.continuousOn_HkIntegrand α 4)

/-- **`HkIntegrand α 4 g` is jointly integrable on the quadrant** for
`SmoothQuad g + HkMem α 4 g`, by Tonelli: both iterated integrals are the two halves of
`HkMem α 4 g`. -/
theorem HkIntegrand_joint_integrable_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have haesm := aesm_joint_HkIntegrand_open (α := α) hO
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact hmem.1 z hz
  have houter : MeasureTheory.Integrable
      (fun z => ∫ θ, Work.Spaces.HkIntegrand α 4 g z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  exact (Work.Spaces.integrable_prod_of_iterated hnn haesm hslice houter).1

/-! ## Joint integrability of the square of a `D_z`-iterate -/

/-- **`(D_zⁱ g)²` is jointly integrable on the quadrant** for `i ≤ 4`: it is dominated by
`HkIntegrand α 4 g` because `w ≥ 1` on `z > 0`. -/
theorem DzIter_sq_joint_integrable_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {i : ℕ} (hi : i ≤ 4) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono' (HkIntegrand_joint_integrable_open hO hmem) ?_ ?_
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((hO.DzIter i).continuousOn).pow 2
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  · refine ae_prod_quad (fun z θ hz hθ1 hθ2 => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 := sq_DzIter_le_HkIntegrand_div_w_sq α 4 g i hi hz ⟨hθ1, hθ2⟩
    have h2 : Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
      rw [div_le_iff₀ (pow_pos (w_pos hz) 2)]
      have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (one_le_w hz) 2
        simpa using h
      nlinarith [Work.Spaces.HkIntegrand_nonneg α 4 g z θ, hw2]
    linarith

/-! ## The joint integrand of the angular moment on a box -/

/-- The joint integrand `(x,θ) ↦ Kθ(θ)·D_z^{j+1} g x θ / x` is continuous on the open
quadrant. -/
theorem continuousOn_Ktheta_DzIter_div_open {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
      * Work.Spaces.DzIter j g p.1 p.2 / p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  (continuousOn_Ktheta_DzIter_open hO j).div continuousOn_fst (fun p hp => ne_of_gt hp.1)

/-- **Joint integrability on a box, and of its `θ`-integral.**  For `0 < a ≤ b` and `j ≤ 3`,

* the joint integrand `(x,θ) ↦ Kθ(θ)·D_z^{j+1} g x θ / x` is integrable on the box
  `uIoc a b ×ˢ uIoc 0 (π/2)` (this is the Fubini hypothesis);
* its `θ`-integral `x ↦ Qang g (j+1) x / x` is integrable on `uIoc a b`. -/
theorem QangBoxIntegrable_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {j : ℕ} (hj : j ≤ 3) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2)) ∧
      MeasureTheory.IntegrableOn (fun x : ℝ => Work.Elliptic.Qang g (j + 1) x / x)
        (Set.uIoc a b) := by
  have hsub1 : Set.uIoc a b ⊆ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.uIoc_of_le hab]
    exact fun x hx => le_of_lt (lt_trans ha hx.1)
  have hsub2 : Set.uIoc 0 (π / 2) ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    exact fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  have hle : (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono (Set.prod_mono hsub1 hsub2) le_rfl
  have hD2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter (j + 1) g p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    (DzIter_sq_joint_integrable_open hO hmem (by omega)).mono_measure hle
  have hconst : MeasureTheory.Integrable (fun _ : ℝ × ℝ => (1 : ℝ))
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) := by
    have hne : ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) Set.univ ≠ ⊤ := by
      rw [← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod,
        MeasureTheory.Measure.restrict_apply_univ, MeasureTheory.Measure.restrict_apply_univ,
        Set.uIoc_of_le hab, Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2),
        Real.volume_Ioc, Real.volume_Ioc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    simpa only [MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_univ] using
      (MeasureTheory.integrableOn_const (μ := (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) (s := Set.univ) (C := (1 : ℝ)) hne)
  -- the a.e. domination of the joint integrand
  have haesmF : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_Ktheta_DzIter_div_open hO (j + 1))).mono_measure hle
  have hdom : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
      (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))),
      ‖Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1‖
        ≤ (3 / a) * ((Work.Spaces.DzIter (j + 1) g p.1 p.2) ^ 2 + 1) := by
    refine ae_prod_box hab (fun z θ hz hθ1 hθ2 => ?_)
    have hzpos : 0 < z := by
      rw [Set.uIoc_of_le hab] at hz
      exact lt_trans ha hz.1
    have haz : a ≤ z := by
      rw [Set.uIoc_of_le hab] at hz
      exact hz.1.le
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hzpos, abs_mul]
    have hD1 : |Work.Spaces.DzIter (j + 1) g z θ|
        ≤ (Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|Work.Spaces.DzIter (j + 1) g z θ| - 1),
        sq_abs (Work.Spaces.DzIter (j + 1) g z θ),
        abs_nonneg (Work.Spaces.DzIter (j + 1) g z θ)]
    have hDnn : 0 ≤ |Work.Spaces.DzIter (j + 1) g z θ| := abs_nonneg _
    have h1 : |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter (j + 1) g z θ| / z
        ≤ 3 * |Work.Spaces.DzIter (j + 1) g z θ| / z :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (abs_Ktheta_le_three θ) hDnn) hzpos.le
    have h2 : 3 * |Work.Spaces.DzIter (j + 1) g z θ| / z
        ≤ 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / z :=
      div_le_div_of_nonneg_right (by linarith) hzpos.le
    have h3 : 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / z
        ≤ 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / a :=
      div_le_div_of_nonneg_left (by positivity) ha haz
    have h4 : 3 * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) / a
        = (3 / a) * ((Work.Spaces.DzIter (j + 1) g z θ) ^ 2 + 1) := by ring
    linarith [h1, h2, h3, h4.le, h4.ge]
  have hFbox : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
        (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2)))) :=
    MeasureTheory.Integrable.mono' ((hD2.add hconst).const_mul (3 / a)) haesmF hdom
  refine ⟨?_, ?_⟩
  · have hvol : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2))
        = (MeasureTheory.volume.restrict (Set.uIoc a b)).prod
          (MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2))) := by
      rw [MeasureTheory.Measure.prod_restrict]
      rfl
    show MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1)
      ((MeasureTheory.volume : Measure (ℝ × ℝ)).restrict
        (Set.uIoc a b ×ˢ Set.uIoc 0 (π / 2)))
    rw [hvol]
    exact hFbox
  · have h1 : MeasureTheory.Integrable
        (fun x : ℝ => ∫ θ, (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
            * Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1) (x, θ)
          ∂(MeasureTheory.volume.restrict (Set.uIoc 0 (π / 2))))
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
      MeasureTheory.Integrable.integral_prod_left hFbox
    have hset : Set.uIoc 0 (π / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ := by
      rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ π / 2), Work.Spaces.Iθ]
      exact MeasureTheory.Ioc_ae_eq_Icc
    refine h1.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun x hx => ?_)
    have hxpos : 0 < x := by
      rw [Set.uIoc_of_le hab] at hx
      exact lt_trans ha hx.1
    change (∫ θ in Set.uIoc 0 (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ / x)
      = Work.Elliptic.Qang g (j + 1) x / x
    rw [MeasureTheory.setIntegral_congr_set hset, MeasureTheory.integral_div]
    rfl


/-- Cauchy–Schwarz in `θ` for the angular moment, in the interior class: for
`SmoothQuad g`, `HkMem α 4 g`, `j ≤ 4` and `z > 0`,

  `(Qang g j z)² ≤ (∫_θ Ktheta θ²)·(∫_θ (D_z^j g z θ)²)`,

`Qang g j z = ∫_θ Ktheta θ · D_z^j g z θ dθ`.  This is `Work.Elliptic.Qang_sq_le` with the
analyticity hypothesis `Work.Spaces.SmoothNbhd g` replaced by `SmoothQuad g`: both `θ`-slices are
measurable on `Iθ` (they are continuous on the open interval, `SmoothQuad` +
`Work.Spaces.aesm_slice_of_continuousOn_Qd`) and square-integrable there (`Ktheta` is continuous
on the compact `Iθ`; `(D_z^j g z ·)²` is dominated by `HkIntegrand α 4 g z ·` by
`Work.Spaces.sq_le_HkIntegrand_z` and `hmem.1`, on the full-measure open interval `Ioo 0 (π/2)`),
so the inequality is the standard Cauchy–Schwarz for the Bochner integral
(`MeasureTheory.integral_mul_le_Lp_mul_Lq`, or a version of
`Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` for functions merely continuous on the open
interval); no continuity at the angular endpoints `θ = 0, π/2` is needed.  The hypothesis
`j ≤ 4` is needed: `sq_le_HkIntegrand_z` gives the domination only for `j ≤ 4`, and that is what
makes the second factor finite. -/
theorem Qang_sq_leQ_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.Qang g j z) ^ 2 ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
  -- `Iθ = Icc 0 (π/2)` and the open interval `Ioo 0 (π/2)` differ by the two endpoints, a null
  -- set: every integral below can be taken over the open interval, where the `θ`-slice of
  -- `D_z^j g` is continuous (`SmoothQuad` only gives smoothness on the *open* quadrant).
  have hIoo : (Set.Icc (0 : ℝ) (π / 2)) =ᵐ[volume] (Set.Ioo (0 : ℝ) (π / 2)) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hQeq : Work.Elliptic.Qang g j z
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ := by
    rw [Work.Elliptic.Qang]
    exact MeasureTheory.setIntegral_congr_set hIoo
  have hKeq : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  have hAeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIoo
  -- the `θ`-slice of `D_z^j g` at `z > 0` is continuous on `(0,π/2)`
  have hzIoi : (0 : ℝ) < z := hz
  have hAcont : ContinuousOn (fun θ => Work.Spaces.DzIter j g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hO.DzIter j).curry_θ hzIoi).continuousOn
  -- `Ktheta` is continuous everywhere (hence on `Iθ` and on `Ioo 0 (π/2)`)
  have hKcont : Continuous (fun θ => Work.Elliptic.Ktheta θ) := by
    unfold Work.Elliptic.Ktheta
    fun_prop
  -- integrability of `Ktheta²` on the open interval (continuity on the compact closure)
  have hK2int : IntegrableOn (fun θ => Work.Elliptic.Ktheta θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    ((hKcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  -- integrability of `HkIntegrand α 4 g z ·`, transported from `hmem` to the open interval
  have hHkint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    change Integrable (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    rw [← MeasureTheory.Measure.restrict_congr_set hIoo]
    simpa only [Work.Spaces.Iθ, IntegrableOn] using hmem.1 z (le_of_lt hz)
  -- a.e. strong measurability of the `θ`-slice
  have hAesm : AEStronglyMeasurable (fun θ => |Work.Spaces.DzIter j g z θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using (hAcont.aestronglyMeasurable measurableSet_Ioo).norm
  -- integrability of `(D_z^j g z ·)²`: dominated by the `ℋ⁴`-integrand on the open interval
  have hA2int : IntegrableOn (fun θ => |Work.Spaces.DzIter j g z θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine hHkint.mono' (hAesm.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_abs]
    exact Work.Elliptic.sq_DzIter_le_HkIntegrand_Qd α g hj hz hθ.1 hθ.2
  have hKesm : AEStronglyMeasurable (fun θ => |Work.Elliptic.Ktheta θ|)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    simpa only [Real.norm_eq_abs] using hKcont.aestronglyMeasurable.norm
  have hKabs : IntegrableOn (fun θ => |Work.Elliptic.Ktheta θ| ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    simpa only [sq_abs] using hK2int
  -- `L²`-membership of the two factors (`p = q = 2`)
  have hKmem : MemLp (fun θ => |Work.Elliptic.Ktheta θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hKesm).mpr hKabs
  have hAmem : MemLp (fun θ => |Work.Spaces.DzIter j g z θ|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
    exact (MeasureTheory.memLp_two_iff_integrable_sq hAesm).mpr hA2int
  -- Cauchy–Schwarz for the Bochner integral (`p = q = 2`, both factors nonnegative)
  have hcs := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
    (p := 2) (q := 2) (f := fun θ => |Work.Elliptic.Ktheta θ|)
    (g := fun θ => |Work.Spaces.DzIter j g z θ|)
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun θ => abs_nonneg _)
    (Filter.Eventually.of_forall fun θ => abs_nonneg _) hKmem hAmem
  have hnQ : |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Set.Ioo (0 : ℝ) (π / 2)))
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ)
    simpa only [Real.norm_eq_abs, abs_mul] using h
  have hKIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Elliptic.Ktheta θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hAIsq : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ))
      = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by
      simp only [Real.rpow_two, sq_abs])
  have hK0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hA0 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hmain : (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
        Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
    calc (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
          Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ) ^ 2
        = |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
            Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ| ^ 2 := by rw [sq_abs]
      _ ≤ (Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
            * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                (Work.Spaces.DzIter j g z θ) ^ 2)) ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _)
          calc |∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ|
              ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                  |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g z θ| := hnQ
            _ ≤ (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Elliptic.Ktheta θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
                * (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    |Work.Spaces.DzIter j g z θ| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hcs
            _ = Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
                * Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) (π / 2),
                    (Work.Spaces.DzIter j g z θ) ^ 2) := by
                rw [hKIsq, hAIsq, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      _ = (∫ θ in Set.Ioo (0 : ℝ) (π / 2), Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter j g z θ) ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt hA0]
  rw [hQeq, hKeq, hAeq]
  exact hmain


/-- **The primitive identity for `z₀ ≤ z`.**  For every `j ≤ 3` and `0 < z₀ ≤ z`,

  `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`.

The proof integrates the slice formula
`D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^{z} D_z^{j+1} g x θ / x dx`
(`QangSliceFTC_open`) against `Ktheta` and swaps the two integrations with Fubini on the box
`uIoc z₀ z ×ˢ uIoc 0 (π/2)`, whose joint integrability is `QangBoxIntegrable_open`. -/
theorem Qang_primitive_le_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) {z z₀ : ℝ} (hz : 0 < z)
    (hz₀ : 0 < z₀) (hle : z₀ ≤ z) :
    Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
  -- integral integrability of the two angular slices over `0..π/2`
  have hslice : ∀ {w : ℝ}, 0 < w →
      IntervalIntegrable (fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g w θ)
        volume 0 (π/2) := by
    intro w hw
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ π / 2)]
    refine (QangSliceIntegrable_open hO hmem (by omega : j ≤ 4) hw).mono_set ?_
    rw [Work.Spaces.Iθ]
    exact Set.Ioc_subset_Icc_self
  have hIi_z := hslice hz
  have hIi_z₀ := hslice hz₀
  -- Step 1: split the difference of the two θ-integrals
  have h1 : Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ
          - Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z₀ θ) := by
    rw [Qang_eq_intervalIntegral g j z, Qang_eq_intervalIntegral g j z₀]
    exact (intervalIntegral.integral_sub hIi_z hIi_z₀).symm
  -- Step 2: factor out the angular weight
  have h2 : (∫ θ in (0 : ℝ)..(π / 2), (Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z θ
        - Work.Elliptic.Ktheta θ * Work.Spaces.DzIter j g z₀ θ))
      = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
          * (Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    ring
  -- Step 3: the slice formula
  have h3 : (∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
        * (Work.Spaces.DzIter j g z θ - Work.Spaces.DzIter j g z₀ θ))
      = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
          * (∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine ae_imp_uIoc (fun θ hθ1 hθ2 => ?_)
    rw [QangSliceFTC_open hO j hz hz₀ ⟨hθ1, hθ2⟩]
  -- Step 4: pull the angular weight inside the inner integral
  have h4 : (∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ
        * (∫ x in z₀..z, Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ θ in (0 : ℝ)..(π / 2), ∫ x in z₀..z,
          Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    exact (intervalIntegral.integral_const_mul (Work.Elliptic.Ktheta θ)
      (fun x => Work.Spaces.DzIter (j + 1) g x θ / x)).symm
  -- Step 5: Fubini on the box
  have hFbox : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * (Work.Spaces.DzIter (j + 1) g p.1 p.2 / p.1))
      (Set.uIoc z₀ z ×ˢ Set.uIoc 0 (π / 2)) :=
    (QangBoxIntegrable_open hO hmem hj hz₀ hle).1.congr_fun (fun p _ => by ring)
      ((measurableSet_uIoc).prod measurableSet_uIoc)
  have h5 : (∫ θ in (0 : ℝ)..(π / 2), ∫ x in z₀..z,
        Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ x in z₀..z, ∫ θ in (0 : ℝ)..(π / 2),
          Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x) :=
    (MeasureTheory.intervalIntegral_intervalIntegral_swap
      (F := fun x θ => Work.Elliptic.Ktheta θ
        * (Work.Spaces.DzIter (j + 1) g x θ / x)) hFbox).symm
  -- Step 6: identify the inner integral with `Qang g (j+1) x / x`
  have h6 : (∫ x in z₀..z, ∫ θ in (0 : ℝ)..(π / 2),
        Work.Elliptic.Ktheta θ * (Work.Spaces.DzIter (j + 1) g x θ / x))
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have hq : Work.Elliptic.Qang g (j + 1) x
        = ∫ θ in (0 : ℝ)..(π / 2), Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ :=
      Qang_eq_intervalIntegral g (j + 1) x
    have hfun : (fun θ : ℝ => Work.Elliptic.Ktheta θ
          * (Work.Spaces.DzIter (j + 1) g x θ / x))
        = fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter (j + 1) g x θ / x := by
      funext θ; ring
    rw [hfun, hq, intervalIntegral.integral_div]
  rw [h1, h2, h3, h4, h5, h6]

/-- **The primitive identity.**  For every `j ≤ 3` and every `z, z₀ > 0`,

  `Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`. -/
theorem Qang_primitive_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) {z z₀ : ℝ} (hz : 0 < z)
    (hz₀ : 0 < z₀) :
    Work.Elliptic.Qang g j z - Work.Elliptic.Qang g j z₀
      = ∫ x in z₀..z, Work.Elliptic.Qang g (j + 1) x / x := by
  rcases le_total z₀ z with hle | hle
  · exact Qang_primitive_le_open α g hO hmem hj hz hz₀ hle
  · have h := Qang_primitive_le_open α g hO hmem hj hz₀ hz hle
    rw [intervalIntegral.integral_symm z₀ z] at h
    linarith [h]

/-- `z ↦ Qang g (j+1) z / z` is continuous at every `z > 0`, for `j ≤ 2`: this is the
integrand of the primitive identity, and it is continuous because `Qang g (j+1)` is
(`j + 1 ≤ 3`) and `z ≠ 0`. -/
theorem continuousAt_Qang_div {g : ℝ → ℝ → ℝ} {j : ℕ} {z : ℝ}
    (hcont : ContinuousOn (fun w => Work.Elliptic.Qang g (j + 1) w) (Set.Ioi 0))
    (hz : 0 < z) :
    ContinuousAt (fun x => Work.Elliptic.Qang g (j + 1) x / x) z :=
  (hcont.continuousAt (isOpen_Ioi.mem_nhds hz)).div continuousAt_id (ne_of_gt hz)

/-- `Qang g j` is continuous on `(0,∞)` for `j ≤ 3`: it is (a constant plus) the primitive of
`x ↦ Qang g (j+1) x / x`, which is integrable on every compact subinterval of `(0,∞)`. -/
theorem continuousOn_Qang_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 3) :
    ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) := by
  intro z hz
  have hzpos : 0 < z := hz
  have hz2pos : 0 < z / 2 := by linarith
  have hle1 : z / 2 ≤ 2 * z := by linarith
  -- integrability of the integrand on a closed interval around `z`
  obtain ⟨-, hint⟩ := QangBoxIntegrable_open hO hmem hj hz2pos hle1
  have hintIcc : MeasureTheory.IntegrableOn (fun x => Work.Elliptic.Qang g (j + 1) x / x)
      (Set.uIcc (z / 2) (2 * z)) := by
    rw [Set.uIcc_of_le hle1]
    refine (integrableOn_Icc_iff_integrableOn_Ioc (a := z / 2)
      (f := fun x => Work.Elliptic.Qang g (j + 1) x / x)).mpr ?_
    rwa [Set.uIoc_of_le hle1] at hint
  have hcont := intervalIntegral.continuousOn_primitive_interval hintIcc
  -- the primitive is `Qang g j · - Qang g j (z/2)` on the interval
  have hcongr : Set.EqOn (fun x => ∫ t in z / 2..x, Work.Elliptic.Qang g (j + 1) t / t)
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2))
      (Set.uIcc (z / 2) (2 * z)) := by
    intro x hx
    have hxpos : 0 < x := by
      rw [Set.uIcc_of_le hle1] at hx
      linarith [hx.1]
    exact (Qang_primitive_open α g hO hmem hj hxpos hz2pos).symm
  have hcont2 : ContinuousOn
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2))
      (Set.uIcc (z / 2) (2 * z)) := hcont.congr hcongr.symm
  have hnhds : Set.uIcc (z / 2) (2 * z) ∈ 𝓝 z := by
    rw [Set.uIcc_of_le hle1]
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hcat : ContinuousAt
      (fun x => Work.Elliptic.Qang g j x - Work.Elliptic.Qang g j (z / 2)) z :=
    hcont2.continuousAt hnhds
  exact ((hcat.add_const (Work.Elliptic.Qang g j (z / 2))).congr
    (Filter.Eventually.of_forall (fun x => by ring))).continuousWithinAt

/-- **`Qang g j` is differentiable on `(0,∞)` for `j ≤ 2`, with derivative
`Qang g (j+1) z / z`**: the primitive identity exhibits it as the primitive of a function
which is continuous at `z` (`continuousOn_Qang_open` at level `j + 1 ≤ 3`). -/
theorem hasDerivAt_Qang_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hO : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g) {j : ℕ} (hj : j ≤ 2) {z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn (fun w => Work.Elliptic.Qang g (j + 1) w) (Set.Ioi 0)) :
    HasDerivAt (fun z => Work.Elliptic.Qang g j z)
      (Work.Elliptic.Qang g (j + 1) z / z) z := by
  have hz2pos : 0 < z / 2 := by linarith
  have hle1 : z / 2 ≤ z := by linarith
  obtain ⟨-, hint⟩ := QangBoxIntegrable_open hO hmem (by omega : j ≤ 3) hz2pos hle1
  have hInt : IntervalIntegrable (fun x => Work.Elliptic.Qang g (j + 1) x / x) volume
      (z / 2) z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle1]
    rwa [Set.uIoc_of_le hle1] at hint
  have hcontAt := continuousAt_Qang_div hcont hz
  have hcontOn : ContinuousOn (fun x => Work.Elliptic.Qang g (j + 1) x / x) (Set.Ioi 0) :=
    hcont.div continuousOn_id (fun x hx => ne_of_gt hx)
  have hsmAt := ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi hcontOn z hz
  have hprim : HasDerivAt (fun u => ∫ x in z / 2..u, Work.Elliptic.Qang g (j + 1) x / x)
      (Work.Elliptic.Qang g (j + 1) z / z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt hsmAt hcontAt
  have heq : (fun u => Work.Elliptic.Qang g j u - Work.Elliptic.Qang g j (z / 2))
      =ᶠ[𝓝 z] (fun u => ∫ x in z / 2..u, Work.Elliptic.Qang g (j + 1) x / x) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
    exact Qang_primitive_open α g hO hmem (by omega : j ≤ 3) hu hz2pos
  have h1 := hprim.congr_of_eventuallyEq heq
  have h2 := h1.add_const (Work.Elliptic.Qang g j (z / 2))
  exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => by ring))

/-- `z`-differentiation of the angular moments `Qang g j z = ∫_θ Ktheta θ · D_z^j g z θ dθ`
in the interior class `SmoothQuad g + HkMem α 4 g` (no analyticity/`SmoothNbhd`):
`Qang g j` is continuous on `(0,∞)` for `j ≤ 3`, and for `j ≤ 2` it is differentiable at every
`z > 0` with `∂_z (Qang g j) z = Qang g (j+1) z / z`.

Route.  For each `θ ∈ (0,π/2)` the slice `z ↦ D_z^j g z θ` is `C^∞` on `Ioi (-1)`
(`Work.FTS.LocData.SmoothQuad.curry_z`), and `z·∂_z(D_z^j g) = D_z^{j+1} g`, so the primitive
formula (FTC) on `z₀..z` gives
`D_z^j g z θ - D_z^j g z₀ θ = ∫_{z₀}^z D_z^{j+1} g x θ / x dx` for every `θ ∈ (0,π/2)`.
Multiply by `Ktheta θ` and integrate in `θ`: the difference of the two `θ`-integrals is the
`θ`-integral of the difference (each `θ ↦ Ktheta θ · D_z^j g z θ` is integrable on `Iθ` for
`z > 0`, by Cauchy–Schwarz with `∫_θ (D_z^j g z θ)² < ∞`; the latter follows from `hmem.1` and
the pointwise domination of `(D_z^j g)²` by the `j`-th summand of `HkIntegrand α 4 g`, which is
`Work.Spaces.sq_le_HkIntegrand_z`).  Then Fubini/Tonelli on the box
`[min z z₀, max z z₀] × Iθ`: the joint integrand `(x,θ) ↦ Ktheta θ · D_z^{j+1} g x θ / x` is
integrable there because `|Ktheta| ≤ 3` and Cauchy–Schwarz bounds it by
`(∫∫ (D_z^{j+1} g)²/x²)^{1/2}`, while on the box `1/x² ≤ C·w(x)²·sin(2θ)^{-η}`
(`w ≥ w_min > 0` since `x ≥ min z z₀ > 0`, and `sin(2θ)^{-η} ≥ 1`) and the `(j+1)`-th pure
`D_z` slot of `HkIntegrand α 4 g` is integrable over `Iz × Iθ` by `hmem`; continuity of the
joint integrand on the box gives measurability.  This yields, for all `z, z₀ > 0`,
`Qang g j z - Qang g j z₀ = ∫_{z₀}^z Qang g (j+1) x / x dx`, and also that
`x ↦ Qang g (j+1) x / x` is integrable on each compact subinterval of `(0,∞)`.
Consequently `Qang g j` is continuous on `(0,∞)` (it is a primitive plus a constant), and for
`j ≤ 2` the right-hand integrand `x ↦ Qang g (j+1) x / x` is continuous at `z` (continuity of
`Qang g (j+1)`, obtained at the level `j+1 ≤ 3`), so
`HasDerivAt (Qang g j) (Qang g (j+1) z / z) z`.
(`j ≤ 3` in the continuity part is sharp: continuity of `Qang g 3` uses the Fubini identity at
level 3, hence the 4-th pure `D_z` slot of `HkMem α 4 g`.)
Useful existing siblings (all with the analyticity hypothesis `Spaces.SmoothNbhd`, which must
NOT be used): `Work.Elliptic.Qang_deriv_mul`, `Work.Elliptic.L12Iterate` (and
`Work.EllipticEst.Blocks.L12Gen.L12Iterate_k`), `Work.Elliptic.L12k0`. -/
theorem QangDiff_open (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        HasDerivAt (Work.Elliptic.Qang g j) (Work.Elliptic.Qang g (j + 1) z / z) z) ∧
      (∀ j : ℕ, j ≤ 3 → ContinuousOn (Work.Elliptic.Qang g j) (Set.Ioi 0)) := by
  have hcont : ∀ j : ℕ, j ≤ 3 → ContinuousOn (fun z => Work.Elliptic.Qang g j z) (Set.Ioi 0) :=
    fun j hj => continuousOn_Qang_open α g hO hmem hj
  refine ⟨?_, hcont⟩
  intro j hj z hz
  exact hasDerivAt_Qang_open α g hO hmem hj hz (hcont (j + 1) (by omega))


/-- The `z = 0`-slice of `Iz = [0,∞)` is null, so every almost-everywhere statement on
`Iz` may be proved on the open half-line. -/
private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- The two angular endpoints of `Iθ = [0,π/2]` are null. -/
private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- **The pure `D_z`-slot domination with the full weight.**  For `z > 0` and
`0 < θ < π/2`, the square of the weighted iterate is dominated by the `ℋ⁴`-integrand:

  `(D_z^i g z θ)² w(z)² ≤ HkIntegrand α 4 g z θ`   (`i ≤ 4`).

This is `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` (which gives
`(D_z^i g)² ≤ HkIntegrand/w²`) multiplied by `w² > 0`. -/
private theorem DzIter_sq_w_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {i : ℕ} (hi : i ≤ 4)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α 4 g i hi hz hθ
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Work.Spaces.w z))
  rwa [div_mul_cancel₀ _
    (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hz)))] at h2

/-- The radial weight `w` squared is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

theorem Qang_sq_w_sq_integral_open {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {i : ℕ} (hi : i ≤ 4) :
    MeasureTheory.IntegrableOn (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α 4 g := by
  -- the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro z hz
    -- Cauchy–Schwarz in `θ`
    have hCS := Qang_sq_leQ_open α g hO hmem i hi hz
    -- the `θ`-slice domination, with the weight `w z` on the left
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => DzIter_sq_w_sq_le_HkIntegrand α g hi hz hθ)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 z (le_of_lt hz)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    calc (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hCS (sq_nonneg _)
      _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) :=
          mul_le_mul_of_nonneg_left hslice
            (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
  -- the bound holds almost everywhere on `Iz`
  have hle : (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)) := by
    rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt
  -- a.e. strong measurability of the left-hand side
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hQ : AEStronglyMeasurable (fun z => Work.Elliptic.Qang g i z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h := (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i g p.1 p.2)
        (continuousOn_Ktheta_DzIter_open hO i)).integral_prod_right'
      simpa only [Work.Elliptic.Qang] using h
    have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
      exact continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi
    exact (hQ.pow 2).mul hw
  -- the dominating function is integrable
  have hdom : MeasureTheory.Integrable
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul _
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [hle] with z hz
    rwa [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  · have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      hdom hle
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono.trans (le_of_eq rfl)


/-! ## The iterated `z ∂_z`-identity from a primitive relation -/

/-- If `u = Φ 0` and `Φ j` has derivative `Φ (j+1) z / z` at every `z > 0` (for `j ≤ 2`), then
`DzdIter i u = Φ i` on `(0,∞)` for every `i ≤ 3`.

This is the pointwise half of the main theorem, stated for an abstract pair `(u, Φ)` so that
the induction is independent of `Qang`.  The hypothesis `j ≤ 2` is what makes
`z * ∂_z(Φ j) z = Φ (j+1) z` hold: `DzdIter i u` agrees with `Φ i` on the open half-line, so
their derivatives at `z > 0` agree, and the divided derivative `Φ (j+1) z / z` is undone by the
multiplication by `z`. -/
private theorem DzdIter_eq_of_hasDerivAt {u : ℝ → ℝ} {Φ : ℕ → ℝ → ℝ}
    (h0 : ∀ z, u z = Φ 0 z)
    (hder : ∀ j ≤ 2, ∀ z, 0 < z → HasDerivAt (Φ j) (Φ (j + 1) z / z) z) :
    ∀ i ≤ 3, ∀ z, 0 < z → Work.Elliptic.DzdIter i u z = Φ i z := by
  intro i
  induction i with
  | zero => intro _ z _; exact h0 z
  | succ i ih =>
    intro _ z hz
    have hprev : Work.Elliptic.DzdIter i u =ᶠ[𝓝 z] Φ i := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact ih (by omega) w hw
    rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
    rw [hprev.deriv_eq, (hder i (by omega) z hz).deriv]
    rw [mul_comm z, div_mul_cancel₀ _ (ne_of_gt hz)]

/-! ## The main identity -/

theorem DzdIter_Qang_ae_open {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ᵐ z ∂(MeasureTheory.volume), 0 < z → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z := by
  -- the divided derivative of `Qang g j` for `j ≤ 2` (continuity of `Qang g (j+1)`, `j+1 ≤ 3`)
  have hder2 : ∀ j ≤ 2, ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.Qang g j z) (Work.Elliptic.Qang g (j + 1) z / z) z := by
    intro j hj z hz
    exact hasDerivAt_Qang_open α g hO hmem hj hz
      (continuousOn_Qang_open α g hO hmem (by omega))
  -- the pointwise identity for `i ≤ 3`
  have hpoint : ∀ i ≤ 3, ∀ z, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z :=
    DzdIter_eq_of_hasDerivAt (fun z => rfl) hder2
  -- the integrand `x ↦ Qang g 4 x / x` is interval integrable on every compact subinterval of
  -- `(0,∞)`: this is the `j = 3` instance of the Fubini/box integrability
  have hφint : ∀ n : ℕ, IntervalIntegrable (fun x => Work.Elliptic.Qang g 4 x / x) volume
      (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro n
    have ha : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact intervalIntegrable_iff.mpr
      (QangBoxIntegrable_open hO hmem (j := 3) le_rfl ha hab).2
  -- the Lebesgue differentiation theorem on each piece of the countable cover
  have hldt : ∀ᵐ z ∂volume, ∀ n : ℕ, (z ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) →
      ∀ c ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2),
        HasDerivAt (fun y => ∫ t in c..y, Work.Elliptic.Qang g 4 t / t)
          (Work.Elliptic.Qang g 4 z / z) z) :=
    MeasureTheory.ae_all_iff.mpr fun n => (hφint n).ae_hasDerivAt_integral
  -- every `z > 0` lies in one of the pieces of the cover
  have hcover : ∀ z : ℝ, 0 < z → ∃ n : ℕ, z ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / z) z)
    refine ⟨n, ?_⟩
    have hnz : z < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hn1 : 1 / z < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hzn : 1 < z * (n : ℝ) := by
      rw [div_lt_iff₀ hz] at hn1
      linarith
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [Set.uIcc_of_le hab, Set.mem_Icc]
    exact ⟨by
      rw [div_le_iff₀ (by positivity)]
      nlinarith, by linarith⟩
  -- `1` lies in every piece of the cover, so the primitive can be taken from `1`
  have h1mem : ∀ n : ℕ, (1 : ℝ) ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro n
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [Set.uIcc_of_le hab, Set.mem_Icc]
    exact ⟨by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)],
      by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  -- a.e. differentiability of the primitive `y ↦ ∫_1^y Qang g 4 t / t`
  have hprim : ∀ᵐ z ∂volume, 0 < z →
      HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, Work.Elliptic.Qang g 4 t / t)
        (Work.Elliptic.Qang g 4 z / z) z := by
    filter_upwards [hldt] with z hz hzpos
    obtain ⟨n, hn⟩ := hcover z hzpos
    exact hz n hn 1 (h1mem n)
  -- hence `Qang g 3` is differentiable a.e. with the divided derivative `Qang g 4 z / z`
  have hderiv3 : ∀ᵐ z ∂volume, 0 < z →
      HasDerivAt (fun y => Work.Elliptic.Qang g 3 y) (Work.Elliptic.Qang g 4 z / z) z := by
    filter_upwards [hprim] with z hz hzpos
    have hev : (fun y => Work.Elliptic.Qang g 3 y) =ᶠ[𝓝 z]
        (fun y => (∫ t in (1 : ℝ)..y, Work.Elliptic.Qang g 4 t / t)
          + Work.Elliptic.Qang g 3 1) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with y hy
      have h := Qang_primitive_open α g hO hmem (j := 3) (by norm_num) hy
        (by norm_num : (0 : ℝ) < 1)
      linarith
    exact ((hz hzpos).add_const _).congr_of_eventuallyEq hev
  -- the fourth iterate
  have h4 : ∀ᵐ z ∂volume, 0 < z →
      Work.Elliptic.DzdIter 4 (fun z => Work.Elliptic.Qang g 0 z) z
        = Work.Elliptic.Qang g 4 z := by
    filter_upwards [hderiv3] with z hz3 hzpos
    have h3eq : Work.Elliptic.DzdIter 3 (fun z => Work.Elliptic.Qang g 0 z) =ᶠ[𝓝 z]
        (fun w => Work.Elliptic.Qang g 3 w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with w hw
      exact hpoint 3 le_rfl w hw
    have hd : deriv (Work.Elliptic.DzdIter 3 (fun z => Work.Elliptic.Qang g 0 z)) z
        = Work.Elliptic.Qang g 4 z / z := by
      rw [h3eq.deriv_eq, (hz3 hzpos).deriv]
    rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd, hd]
    rw [mul_comm z, div_mul_cancel₀ _ (ne_of_gt hzpos)]
  filter_upwards [h4] with z hz4 hz i hi
  have hi4 : i ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rcases Nat.lt_or_ge i 4 with hlt | hge
  · exact hpoint i (by omega) z hz
  · have hieq : i = 4 := by omega
    subst hieq
    exact hz4 hz


end Work.FTS.OpenPkg.QangOpen
