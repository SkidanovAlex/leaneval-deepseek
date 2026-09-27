import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLCompLeaf.measurable_nu
import Submission.Work.EKLCompLeaf.measurable_apply_inter_isCompact
import Submission.Work.EKLCompLeaf.measurable_lintegral_kernel_prod_right_of_finite

/-!
# Measurability of the leaf mass `x ↦ (leafMass ν S R x).toReal`

`leafMass ν S R x = ν_x (ballU h01 R ∩ {g | g • x ∈ S})` is the integral of the jointly
measurable function `(x, g) ↦ 1_{ballU R}(g) · 1_S(g • x)` against the leafwise measure `ν x`.

Because `ballU h01 R` is *compact*, only the values of `ν x` on that compact set are needed, and
these depend measurably on `x`:

* `Work.EKLCompLeaf.measurable_apply_inter_isCompact` (proved from the weak measurability field
  `IsLeafwise.measurable` and finiteness on compacts) shows that `x ↦ ν x (B ∩ K)` is measurable
  for every Borel `B` and compact `K`;
* hence `x ↦ (ν x).restrict K` is a measurable family of measures, i.e. a kernel `κ` on `X₃ × SL₃`,
  with `κ x` finite for every `x` (as `(ν x) K < ∞`);
* `Work.EKLCompLeaf.measurable_lintegral_kernel_prod_right_of_finite` — the pointwise-finite
  (rather than Mathlib's s-finite) version of `Measurable.lintegral_kernel_prod_right` — then gives
  measurability of `x ↦ ∫⁻ g, 1_K(g) · 1_S(g • x) ∂(κ x)`, and that integral is `leafMass ν S R x`.
-/

set_option linter.style.haveILetI false

open MeasureTheory Filter Topology ProbabilityTheory Function
open scoped ENNReal

namespace Work.EKLCompLeaf

theorem measurable_leafMass {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij Work.EKLComp.h01) ν X')
    (hν : ∀ x : Work.EKLContract.X3, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (S : Set Work.EKLContract.X3) (hS : MeasurableSet S) (R : ℝ) :
    Measurable fun x => (Work.EKLComp.leafMass ν S R x).toReal := by
  classical
  set K : Set Work.EKLContract.SL3 := Work.EKLContract.ballU Work.EKLComp.h01 R with hKdef
  have hKc : IsCompact K := by rw [hKdef]; exact Work.EKLComp.isCompact_ballU R
  have hKmeas : MeasurableSet K := hKc.measurableSet
  -- measurability of the coefficients of `ν` on the compact set `K`
  have hcoef : ∀ B : Set Work.EKLContract.SL3, MeasurableSet B →
      Measurable fun x => ν x (B ∩ K) :=
    fun B hB => measurable_apply_inter_isCompact hL.measurable hν hKc B hB
  -- the leafwise measures restricted to `K` form a kernel
  let κ : ProbabilityTheory.Kernel Work.EKLContract.X3 Work.EKLContract.SL3 :=
    ⟨fun x => (ν x).restrict K, by
      refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
      simpa only [Measure.restrict_apply hs] using hcoef s hs⟩
  have hκfin : ∀ x, IsFiniteMeasure (κ x) := fun x => ⟨by
      haveI : IsFiniteMeasureOnCompacts (ν x) := hν x
      change (ν x).restrict K Set.univ < ∞
      rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact hKc⟩
  -- the joint integrand
  let F : Work.EKLContract.X3 → Work.EKLContract.SL3 → ENNReal := fun x g =>
    Set.indicator K (fun _ => (1 : ENNReal)) g * Set.indicator S (fun _ => (1 : ENNReal)) (g • x)
  have hF : Measurable (fun p : Work.EKLContract.X3 × Work.EKLContract.SL3 => F p.1 p.2) := by
    have h1 : Measurable fun p : Work.EKLContract.X3 × Work.EKLContract.SL3 =>
        Set.indicator K (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) p.2 :=
      ((measurable_const : Measurable fun _ : Work.EKLContract.SL3 => (1 : ENNReal)).indicator
        hKmeas).comp measurable_snd
    have h2 : Measurable fun p : Work.EKLContract.X3 × Work.EKLContract.SL3 =>
        Set.indicator S (fun _ : Work.EKLContract.X3 => (1 : ENNReal)) (p.2 • p.1) :=
      ((measurable_const : Measurable fun _ : Work.EKLContract.X3 => (1 : ENNReal)).indicator
        hS).comp (by fun_prop)
    have h3 : Measurable fun p : Work.EKLContract.X3 × Work.EKLContract.SL3 =>
        Set.indicator K (fun _ : Work.EKLContract.SL3 => (1 : ENNReal)) p.2 *
        Set.indicator S (fun _ : Work.EKLContract.X3 => (1 : ENNReal)) (p.2 • p.1) :=
      h1.mul h2
    simpa only [F] using h3
  have hmain : Measurable fun x => ∫⁻ g, F x g ∂(κ x) :=
    measurable_lintegral_kernel_prod_right_of_finite hκfin hF
  -- the integral is the leaf mass
  have key : ∀ x, (∫⁻ g, F x g ∂(κ x)) = Work.EKLComp.leafMass ν S R x := by
    intro x
    have hκx : κ x = (ν x).restrict K := rfl
    unfold Work.EKLComp.leafMass
    rw [hκx, ← hKdef]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem hKmeas] with g hg
    simp only [F, Set.indicator_of_mem hg, one_mul]
  have heq : ∀ x, (∫⁻ g, F x g ∂(κ x)).toReal =
      (Work.EKLComp.leafMass ν S R x).toReal :=
    fun x => congrArg ENNReal.toReal (key x)
  simpa only [heq] using hmain.ennreal_toReal

end Work.EKLCompLeaf
