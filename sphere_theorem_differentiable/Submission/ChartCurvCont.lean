import Submission.ChartCurv

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the derivative of the Christoffel symbol in the base point

This file contains the continuity statements needed for the **second variation** of the energy
(`Submission/IndexForm.lean`): the object `dB cov x₀ p v a b` (the derivative of the chart
Christoffel symbol `chrB` in the *base point* `p`, in the direction `v`, evaluated on the
coordinate vectors `a`, `b`) must depend continuously on `(p, v, a, b)`.

## Contents

* `mvfderiv_frameVector_eq_fderiv`: the **chart formula for `mvfderiv`**.  For a function
  `g : M → E` differentiable at `p`, and `v : E`, the derivative of `g` at `p` in the direction of
  the tangent vector whose *coordinates in the chart at `x₀`* are `v` equals the ordinary
  (`fderiv`) derivative at `(extChartAt I x₀) p` of the coordinate representative
  `x ↦ g ((extChartAt I x₀).symm x)`, applied to `v`.  (This is the fact that `mfderiv` is
  computed in the preferred chart at `p`, while `frameVector` uses the chart at `x₀`; the two are
  related by the derivative of the chart transition.)
* `chrEntryModel` and `contDiffOn_chrEntryModel`: the coordinate model of a Christoffel entry,
  `x ↦ gammaEntry cov x₀ i j ((extChartAt I x₀).symm x)`, is `C^∞` on the chart target.
* `continuousAt_dB_prod` / `continuousOn_dB_prod`: joint continuity of `dB`.

The file needs `[I.Boundaryless]` (so that chart targets are open) and `[T2Space M]`
(the latter because `contMDiffOn_gammaEntry` of `Submission/ChartCurv.lean` does).
-/

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Commons.Geometry.Manifold.VectorBundle.CovariantDerivative
open Commons.Geometry.Manifold.Tangent

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Submission.ChartCurvCont

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **The chart formula for `mvfderiv`.**  If `g : M → E` is differentiable at `p` and `v : E`,
then the derivative of `g` at `p` in the direction of the tangent vector with coordinates `v` in
the chart at `x₀` is the derivative of the coordinate representative `x ↦ g ((extChartAt I x₀).symm x)`
at `(extChartAt I x₀) p`, applied to `v`. -/
theorem mvfderiv_frameVector_eq_fderiv [I.Boundaryless] (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) {g : M → E}
    (hg : MDifferentiableAt I 𝓘(ℝ,E) g p) (v : E) :
    mvfderiv I g p (frameVector (I := I) x₀ p v)
      = fderiv ℝ (fun x : E => g ((extChartAt I x₀).symm x)) ((extChartAt I x₀) p) v := by
  have hpsrc : p ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hp
  have hytgt : (extChartAt I x₀) p ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hpsrc
  have hyrange : (extChartAt I x₀) p ∈ range I := extChartAt_target_subset_range x₀ hytgt
  have hΦd : MDifferentiableAt 𝓘(ℝ,E) I (fun x : E => (extChartAt I x₀).symm x)
      ((extChartAt I x₀) p) :=
    (mdifferentiableWithinAt_extChartAt_symm (I := I) hytgt).mdifferentiableAt
      (Filter.mem_of_superset ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hytgt)
        (extChartAt_target_subset_range x₀))
  have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) p) = p := (extChartAt I x₀).left_inv hpsrc
  have hg' : MDifferentiableAt I 𝓘(ℝ,E) g
      ((fun x : E => (extChartAt I x₀).symm x) ((extChartAt I x₀) p)) := by
    rw [show (fun x : E => (extChartAt I x₀).symm x) ((extChartAt I x₀) p) = p from hleft]
    exact hg
  have hcomp : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g ∘ fun x : E => (extChartAt I x₀).symm x)
        ((extChartAt I x₀) p)
      = (mfderiv I 𝓘(ℝ,E) g p) ∘L
        (mfderiv 𝓘(ℝ,E) I (fun x : E => (extChartAt I x₀).symm x) ((extChartAt I x₀) p)) := by
    have h := mfderiv_comp ((extChartAt I x₀) p) hg' hΦd
    rw [hleft] at h
    exact h
  have hmvf : mvfderiv 𝓘(ℝ,E) (g ∘ fun x : E => (extChartAt I x₀).symm x) ((extChartAt I x₀) p)
      = mvfderiv I g p ∘L
        (mfderiv 𝓘(ℝ,E) I (fun x : E => (extChartAt I x₀).symm x) ((extChartAt I x₀) p)) := by
    rw [mvfderiv, mvfderiv, hcomp]
    simp only [Function.comp_apply]
    rw [hleft]
    rfl
  have hmodel : mvfderiv 𝓘(ℝ,E) (g ∘ fun x : E => (extChartAt I x₀).symm x)
      ((extChartAt I x₀) p) = fderiv ℝ (g ∘ fun x : E => (extChartAt I x₀).symm x)
        ((extChartAt I x₀) p) := by
    rw [mvfderiv, mfderiv_eq_fderiv]; rfl
  have hdΦ : mfderiv 𝓘(ℝ,E) I (fun x : E => (extChartAt I x₀).symm x) ((extChartAt I x₀) p)
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ p := by
    have h1 : mfderiv[range I] (fun x : E => (extChartAt I x₀).symm x) ((extChartAt I x₀) p)
        = mfderiv 𝓘(ℝ,E) I (fun x : E => (extChartAt I x₀).symm x) ((extChartAt I x₀) p) :=
      mfderivWithin_eq_mfderiv (I.uniqueMDiffOn _ hyrange) hΦd
    rw [← h1]
    simpa only using (TangentBundle.symmL_trivializationAt (I := I) hp).symm
  have hfin : mvfderiv I g p (frameVector (I := I) x₀ p v)
      = (mvfderiv I g p ∘L mfderiv 𝓘(ℝ,E) I (fun x : E => (extChartAt I x₀).symm x)
          ((extChartAt I x₀) p)) v := by
    rw [hdΦ]
    rfl
  rw [hfin, ← hmvf, hmodel]
  rw [show (g ∘ fun x : E => (extChartAt I x₀).symm x)
      = (fun x : E => g ((extChartAt I x₀).symm x)) from rfl]
  rfl

/-- The coordinate model of the Christoffel entry `gammaEntry cov x₀ i j`. -/
noncomputable def chrEntryModel (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) : E → E :=
  fun x => gammaEntry cov x₀ i j ((extChartAt I x₀).symm x)

/-- The coordinate model of a Christoffel entry is `C^∞` on the chart target. -/
theorem contDiffOn_chrEntryModel [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞] (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ 1 (chrEntryModel cov x₀ i j) (extChartAt I x₀).target := by
  have h1 : ContMDiffOn I 𝓘(ℝ,E) ∞ (gammaEntry cov x₀ i j) (chartAt H x₀).source :=
    contMDiffOn_gammaEntry (cov := cov) x₀ i j
  have h2 : ContMDiffOn 𝓘(ℝ,E) I ∞ (fun x : E => (extChartAt I x₀).symm x)
      (extChartAt I x₀).target := contMDiffOn_extChartAt_symm x₀
  have h3 : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (chrEntryModel cov x₀ i j)
      (extChartAt I x₀).target := by
    refine h1.comp h2 ?_
    intro x hx
    rw [Set.mem_preimage]
    have hx' : (extChartAt I x₀).symm x ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hx
    rw [extChartAt_source] at hx'
    exact hx'
  have h4 : ContDiffOn ℝ ∞ (chrEntryModel cov x₀ i j) (extChartAt I x₀).target := h3.contDiffOn
  exact h4.of_le (by simp : ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω))

/-- **Joint continuity of `dB`** (the derivative of the Christoffel symbol in the base point) in
`(p, v, a, b)`, at a point of the chart. -/
theorem continuousAt_dB_prod [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞] (x₀ : M)
    {p₀ : M} (hp₀ : p₀ ∈ (chartAt H x₀).source) (v₀ a₀ b₀ : E) :
    ContinuousAt (fun q : M × E × E × E => dB cov x₀ q.1 q.2.1 q.2.2.1 q.2.2.2)
      (p₀, v₀, a₀, b₀) := by
  classical
  have hsrc_nhds : (chartAt H x₀).source ∈ 𝓝 p₀ := (chartAt H x₀).open_source.mem_nhds hp₀
  have hq1 : ContinuousAt (fun q : M × E × E × E => q.1) (p₀, v₀, a₀, b₀) := continuousAt_fst
  have hq21 : ContinuousAt (fun q : M × E × E × E => q.2.1) (p₀, v₀, a₀, b₀) :=
    continuousAt_fst.comp continuousAt_snd
  have hq221 : ContinuousAt (fun q : M × E × E × E => q.2.2.1) (p₀, v₀, a₀, b₀) :=
    continuousAt_fst.comp (continuousAt_snd.comp continuousAt_snd)
  have hq222 : ContinuousAt (fun q : M × E × E × E => q.2.2.2) (p₀, v₀, a₀, b₀) :=
    continuousAt_snd.comp (continuousAt_snd.comp continuousAt_snd)
  have hev : ∀ᶠ q : M × E × E × E in 𝓝 (p₀, v₀, a₀, b₀),
      q.1 ∈ (chartAt H x₀).source := hq1.tendsto hsrc_nhds
  have hcongr : (fun q : M × E × E × E =>
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).coord i) q.2.2.1 * ((Module.finBasis ℝ E).coord j) q.2.2.2) •
            fderiv ℝ (chrEntryModel cov x₀ i j) ((extChartAt I x₀) q.1) q.2.1)
      =ᶠ[𝓝 (p₀, v₀, a₀, b₀)]
      (fun q : M × E × E × E => dB cov x₀ q.1 q.2.1 q.2.2.1 q.2.2.2) := by
    filter_upwards [hev] with q hq
    rw [dB, mvfderiv_chrB_apply (cov := cov) x₀ q.1 q.2.2.1 q.2.2.2 q.2.1 hq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mvfderiv_frameVector_eq_fderiv (I := I) x₀ hq
      (mdifferentiableAt_gammaEntry (cov := cov) x₀ i j hq) q.2.1]
    rfl
  refine ContinuousAt.congr ?_ hcongr
  refine tendsto_finsetSum Finset.univ fun i _ => tendsto_finsetSum Finset.univ fun j _ => ?_
  have hxcont : ContinuousAt (fun q : M × E × E × E => (extChartAt I x₀) q.1)
      (p₀, v₀, a₀, b₀) :=
    ((continuousOn_extChartAt (I := I) x₀).continuousAt
      (by rw [extChartAt_source]; exact hsrc_nhds)).comp hq1
  have hL : ContinuousAt (fun q : M × E × E × E => fderiv ℝ (chrEntryModel cov x₀ i j)
      ((extChartAt I x₀) q.1)) (p₀, v₀, a₀, b₀) :=
    ContinuousAt.comp'
      (g := fun x : E => fderiv ℝ (chrEntryModel cov x₀ i j) x)
      (f := fun q : M × E × E × E => (extChartAt I x₀) q.1)
      (((ContDiffOn.continuousOn_fderiv_of_isOpen (contDiffOn_chrEntryModel (cov := cov) x₀ i j)
          (isOpen_extChartAt_target (I := I) x₀) le_rfl).continuousAt
        ((isOpen_extChartAt_target (I := I) x₀).mem_nhds
          ((extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hp₀)))))
      hxcont
  have hci : ContinuousAt (fun q : M × E × E × E =>
      ((Module.finBasis ℝ E).coord i) q.2.2.1) (p₀, v₀, a₀, b₀) :=
    ((((Module.finBasis ℝ E).coord i : E →ₗ[ℝ] ℝ).continuous_of_finiteDimensional).continuousAt.comp
      hq221)
  have hcj : ContinuousAt (fun q : M × E × E × E =>
      ((Module.finBasis ℝ E).coord j) q.2.2.2) (p₀, v₀, a₀, b₀) :=
    ((((Module.finBasis ℝ E).coord j : E →ₗ[ℝ] ℝ).continuous_of_finiteDimensional).continuousAt.comp
      hq222)
  exact (hci.mul hcj).smul (hL.clm_apply hq21)

/-- **Joint continuity of `dB`** on the chart source. -/
theorem continuousOn_dB_prod [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ContinuousOn (fun q : M × E × E × E => dB cov x₀ q.1 q.2.1 q.2.2.1 q.2.2.2)
      ((chartAt H x₀).source ×ˢ (Set.univ : Set (E × E × E))) :=
  fun _q hq => (continuousAt_dB_prod (cov := cov) (I := I) x₀ hq.1 _ _ _).continuousWithinAt

end

end Submission.ChartCurvCont
