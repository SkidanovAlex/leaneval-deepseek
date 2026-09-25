import Mathlib
import Submission.Work.CR.Flat.Cauchy.pompeiu
import Submission.Work.CR.Flat.Cauchy.dbarC_mul
import Submission.Work.CR.Flat.Cauchy.dbarC_cauchyTransform
import Submission.Work.NN.Core.fiberPot

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Work.NN.Core.TelTwoDF

/-! ## Elementary gluing lemmas for `C¹` functions with support in an open set -/

/-- The complex-plane version of `contDiff_mul_of_contDiffOn_of_tsupport_subset`: if `χ` is `C^m`
and `A` is `C^m` on the open set `U ⊇ tsupport χ`, then `χ * A` is `C^m` on all of `ℂ`
(the product is `0` near every point outside `tsupport χ`). -/
theorem contDiff_mul_of_contDiffOn_of_tsupport_subset_complex {m : ℕ} {U : Set ℂ}
    (hU : IsOpen U) {χ A : ℂ → ℂ} (hχ : ContDiff ℝ m χ) (hχU : tsupport χ ⊆ U)
    (hA : ContDiffOn ℝ m A U) : ContDiff ℝ m (fun z => χ z * A z) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact (hχ.contDiffAt).mul (hA.contDiffAt (hU.mem_nhds (hχU hx)))
  · have hev : (fun z => χ z * A z) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev

/-- Continuous version of the previous gluing lemma: if `χ` is continuous with
`tsupport χ ⊆ U` and `A` is continuous on the open set `U`, then `χ * A` is continuous. -/
theorem continuous_mul_of_continuousOn_of_tsupport_subset_complex {U : Set ℂ} (hU : IsOpen U)
    {χ A : ℂ → ℂ} (hχ : Continuous χ) (hχU : tsupport χ ⊆ U) (hA : ContinuousOn A U) :
    Continuous (fun z => χ z * A z) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact (hχ.continuousAt).mul (hA.continuousAt (hU.mem_nhds (hχU hx)))
  · have hev : (fun z => χ z * A z) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact (continuousAt_const (x := x) : ContinuousAt (fun _ : ℂ => (0 : ℂ)) x).congr_of_eventuallyEq hev

/-- The topological support of `∂̄f` is contained in that of `f`: outside `tsupport f` the
function `f` vanishes identically near the point, hence so does its (real) derivative. -/
lemma tsupport_dbarC_subset (f : ℂ → ℂ) :
    tsupport (Work.CR.Flat.dbarC f) ⊆ tsupport f := by
  intro x hx
  by_contra hxf
  have hcomp : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hxf
  have hev : Work.CR.Flat.dbarC f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [hcomp] with y hy
    rw [Work.CR.Flat.dbarC, fderiv_of_notMem_tsupport (𝕜 := ℝ) hy]
    simp
  exact absurd hx ((notMem_tsupport_iff_eventuallyEq).mpr hev)

/-- `∂̄A` is continuous on the open set `U` when `A` is `C¹` there. -/
lemma continuousOn_dbarC_of_contDiffOn {U : Set ℂ} (hU : IsOpen U) {A : ℂ → ℂ}
    (hA : ContDiffOn ℝ 1 A U) : ContinuousOn (Work.CR.Flat.dbarC A) U := by
  intro x hx
  have hx' : ContDiffAt ℝ 1 A x := hA.contDiffAt (hU.mem_nhds hx)
  have hfd : ContinuousAt (fun y : ℂ => fderiv ℝ A y) x := hx'.continuousAt_fderiv one_ne_zero
  have h1 : ContinuousAt (fun y : ℂ => fderiv ℝ A y (1 : ℂ)) x := hfd.clm_apply continuousAt_const
  have h2 : ContinuousAt (fun y : ℂ => fderiv ℝ A y Complex.I) x := hfd.clm_apply continuousAt_const
  have h3 : ContinuousAt (fun y : ℂ =>
      (1 / 2 : ℂ) * (fderiv ℝ A y (1 : ℂ) + Complex.I * fderiv ℝ A y Complex.I)) x :=
    continuousAt_const.mul (h1.add (continuousAt_const.mul h2))
  exact h3.continuousWithinAt

/-- **The product rule for `∂̄` at every point**, for a cut-off `χ` supported inside the open
set `U` on which `A` is `C¹`.  Outside `U` both sides vanish: `χ` is eventually `0` there, hence
so are `∂̄χ` and `∂̄(χA)`. -/
lemma dbarC_mul_of_tsupport_subset {U : Set ℂ} (hU : IsOpen U) {χ A : ℂ → ℂ}
    (hχ : ContDiff ℝ 1 χ) (hχU : tsupport χ ⊆ U) (hA : ContDiffOn ℝ 1 A U) (w : ℂ) :
    Work.CR.Flat.dbarC (fun z => χ z * A z) w
      = Work.CR.Flat.dbarC χ w * A w + χ w * Work.CR.Flat.dbarC A w := by
  by_cases hw : w ∈ U
  · exact Work.CR.Flat.Cauchy.dbarC_mul χ A w (hχ.differentiable one_ne_zero w)
      ((hA.contDiffAt (hU.mem_nhds hw)).differentiableAt one_ne_zero)
  · have hwt : w ∉ tsupport χ := fun h => hw (hχU h)
    have hev : χ =ᶠ[𝓝 w] (fun _ => (0 : ℂ)) := (notMem_tsupport_iff_eventuallyEq.mp hwt)
    have hχw : χ w = 0 := image_eq_zero_of_notMem_tsupport hwt
    have hdχ : Work.CR.Flat.dbarC χ w = 0 := by
      rw [Work.CR.Flat.dbarC, fderiv_of_notMem_tsupport (𝕜 := ℝ) hwt]
      simp
    have hev2 : (fun z => χ z * A z) =ᶠ[𝓝 w] (fun _ => (0 : ℂ)) := by
      filter_upwards [hev] with y hy
      rw [hy, zero_mul]
    have hdg : Work.CR.Flat.dbarC (fun z => χ z * A z) w = 0 := by
      have h0 : w ∉ tsupport (fun z => χ z * A z) :=
        (notMem_tsupport_iff_eventuallyEq).mpr hev2
      rw [Work.CR.Flat.dbarC, fderiv_of_notMem_tsupport (𝕜 := ℝ) h0]
      simp
    rw [hdg, hdχ, hχw]
    ring

/-- Integrability of `w ↦ g w / (w - a)` on a disc, for a *continuous* `g`: the shifted Cauchy
kernel is integrable and `g` is bounded on the disc. -/
lemma integrableOn_div_sub_of_continuous {g : ℂ → ℂ} (hg : Continuous g) (R : ℝ) (a : ℂ) :
    IntegrableOn (fun w : ℂ => g w / (w - a)) (Metric.ball (0 : ℂ) R) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hg.continuousOn
  have hbound : IntegrableOn (fun w : ℂ => (max C 0) * ‖(w - a)⁻¹‖) (Metric.ball (0 : ℂ) R) :=
    ((Work.NN.Core.integrableOn_sub_inv_ball R a).norm).const_mul (max C 0)
  refine hbound.mono'
    ((hg.measurable.div (measurable_id.sub measurable_const)).aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with w hw
  rw [div_eq_mul_inv, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact le_trans (hC w (Metric.ball_subset_closedBall hw)) (le_max_left C 0)

/-- **The fibre-cut identity.**  Let `0 < R`, let `χ : ℂ → ℂ` be `C¹` with compact support and
topological support inside the open set `U`, with `χ = 0` on the circle of radius `R`, and let
`A : ℂ → ℂ` be `C¹` on `U`.  If `‖a‖ < R` and `χ ≡ 1` on a neighbourhood of `a` (of radius `ρ`),
then

  `∫ w in ball 0 R, χ w * ∂̄A w / (w - a) = -π * A a - ∫ w in ball 0 R, ∂̄χ w * A w / (w - a)`.

Route: the product rule `∂̄(χ A) = (∂̄χ) A + χ (∂̄A)` (combine `Work.CR.Flat.Cauchy.dbarC_mul`
with linearity), and the point-`a` Pompeiu formula applied to `χ · A`, whose support lies in
`ball 0 R` and which is `C¹` because `tsupport χ ⊆ U` and `A` is `C¹` on the open `U`:

  `-π⁻¹ * ∫ w in ball 0 R, ∂̄(χ A) w / (w - a) = (χ · A) a = A a`.

Equivalently `∫ w in ball 0 R, ∂̄(χ A) w / (w - a) = -π * A a`.  The other two integrands are
absolutely integrable: `1/(w - a)` is locally integrable and `∂̄A` is locally bounded near `a`
(because `a ∈ tsupport χ ⊆ U`), while `(∂̄χ) A` is supported away from `a` (χ is constant near
`a`, hence `∂̄χ = 0` there). -/
theorem integral_cut_dbarC_div {R : ℝ} (hR : 0 < R) {U : Set ℂ} (hU : IsOpen U)
    {χ A : ℂ → ℂ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hA : ContDiffOn ℝ 1 A U) (hχU : tsupport χ ⊆ U)
    (hsuppR : ∀ w : ℂ, R ≤ ‖w‖ → χ w = 0)
    {a : ℂ} (ha : ‖a‖ < R) {ρ : ℝ} (hρ : 0 < ρ) (hχ1 : ∀ w : ℂ, ‖w - a‖ < ρ → χ w = 1) :
    (∫ w in Metric.ball (0 : ℂ) R, χ w * Work.CR.Flat.dbarC A w / (w - a))
      = -(Real.pi : ℂ) * A a
        - ∫ w in Metric.ball (0 : ℂ) R, Work.CR.Flat.dbarC χ w * A w / (w - a) := by
  -- `χ` is compactly supported; the proof below in fact uses only `tsupport χ ⊆ U`
  -- and the continuity of `χ`, but the compact support is part of the interface.
  have _ := hχc
  set g : ℂ → ℂ := fun w => χ w * A w with hgdef
  have hgC : ContDiff ℝ 1 g := by
    rw [hgdef]
    exact contDiff_mul_of_contDiffOn_of_tsupport_subset_complex hU hχ hχU hA
  have hgsupp : Work.CR.Flat.SupportedInBall R g := by
    intro w hw
    rw [hgdef]
    show χ w * A w = 0
    rw [hsuppR w hw, zero_mul]
  have hga : g a = A a := by
    rw [hgdef]
    show χ a * A a = A a
    rw [hχ1 a (by simpa using hρ), one_mul]
  have hpom := Work.CR.Flat.Cauchy.pompeiu hR hgC hgsupp ha
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  -- the Pompeiu formula, solved for the integral
  have hI : (∫ ζ in Metric.ball (0 : ℂ) R, Work.CR.Flat.dbarC g ζ / (ζ - a))
      = -(Real.pi : ℂ) * A a := by
    have h2 := congrArg (fun t => (-(Real.pi : ℂ)) * t) (hpom.trans hga)
    rw [← mul_assoc, neg_inv, mul_inv_cancel₀ (neg_ne_zero.mpr hpi), one_mul] at h2
    exact h2
  -- the two summands are continuous, hence their quotients are integrable
  have hcont1 : Continuous (fun w : ℂ => Work.CR.Flat.dbarC χ w * A w) :=
    continuous_mul_of_continuousOn_of_tsupport_subset_complex hU
      (Work.CR.Flat.Cauchy.continuous_dbarC hχ) ((tsupport_dbarC_subset χ).trans hχU) hA.continuousOn
  have hcont2 : Continuous (fun w : ℂ => χ w * Work.CR.Flat.dbarC A w) :=
    continuous_mul_of_continuousOn_of_tsupport_subset_complex hU hχ.continuous hχU
      (continuousOn_dbarC_of_contDiffOn hU hA)
  have hint1 : IntegrableOn (fun w : ℂ => Work.CR.Flat.dbarC χ w * A w / (w - a))
      (Metric.ball (0 : ℂ) R) := integrableOn_div_sub_of_continuous hcont1 R a
  have hint2 : IntegrableOn (fun w : ℂ => χ w * Work.CR.Flat.dbarC A w / (w - a))
      (Metric.ball (0 : ℂ) R) := integrableOn_div_sub_of_continuous hcont2 R a
  -- the product rule, integrated over the disc
  have hpoint : ∀ w : ℂ, Work.CR.Flat.dbarC g w
      = Work.CR.Flat.dbarC χ w * A w + χ w * Work.CR.Flat.dbarC A w := by
    intro w
    rw [hgdef]
    exact dbarC_mul_of_tsupport_subset hU hχ hχU hA w
  have hcongr : (∫ ζ in Metric.ball (0 : ℂ) R, Work.CR.Flat.dbarC g ζ / (ζ - a))
      = ∫ ζ in Metric.ball (0 : ℂ) R,
          (Work.CR.Flat.dbarC χ ζ * A ζ / (ζ - a) + χ ζ * Work.CR.Flat.dbarC A ζ / (ζ - a)) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro ζ _
    show Work.CR.Flat.dbarC g ζ / (ζ - a)
        = Work.CR.Flat.dbarC χ ζ * A ζ / (ζ - a) + χ ζ * Work.CR.Flat.dbarC A ζ / (ζ - a)
    rw [hpoint ζ, add_div]
  have hsplit : (∫ ζ in Metric.ball (0 : ℂ) R,
          (Work.CR.Flat.dbarC χ ζ * A ζ / (ζ - a) + χ ζ * Work.CR.Flat.dbarC A ζ / (ζ - a)))
      = (∫ ζ in Metric.ball (0 : ℂ) R, Work.CR.Flat.dbarC χ ζ * A ζ / (ζ - a))
        + ∫ ζ in Metric.ball (0 : ℂ) R, χ ζ * Work.CR.Flat.dbarC A ζ / (ζ - a) :=
    integral_add hint1 hint2
  have hkey : (∫ ζ in Metric.ball (0 : ℂ) R, Work.CR.Flat.dbarC χ ζ * A ζ / (ζ - a))
      + (∫ ζ in Metric.ball (0 : ℂ) R, χ ζ * Work.CR.Flat.dbarC A ζ / (ζ - a))
      = -(Real.pi : ℂ) * A a := by
    rw [← hsplit, ← hcongr]
    exact hI
  rw [eq_sub_iff_add_eq, add_comm]
  exact hkey

end Work.NN.Core.TelTwoDF
