import Submission.Work.RiemLib.VariationJacobi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The variation field on an arbitrary time window

`Submission/VariationJacobi.lean` extracts the V1/V2 computation of `Submission/FlowJacobi.lean`
as a statement about an arbitrary smooth family `Φ : ℝ × ℝ → E × E` of *chart geodesics*: the
`t`-variation field `Yp Φ` together with `Ufun x₀ Φ` solves the chart Jacobi system.  Both the
hypotheses and the conclusion, however, are stated on the *fixed* windows `Ioo (-2) 2` (family) and
`Icc (-1) 1` (conclusion).

For the globalisation of the variation argument along a geodesic ray (§83 of the roadmap) one needs
the statement on an *arbitrary* time window: the chart in which the ray is analysed is only
guaranteed to host the ray over an interval of some positive but unknown length, and the family must
be read in the chart's own time coordinate.  This file copies the four lemmas of
`Submission/FlowJacobi.lean`'s `Variation` section and the extraction lemma of
`Submission/VariationJacobi.lean` with the fixed constants `2, 1` replaced by a parameter `R > 0`
(the family window is `Ioo (-R) R` and the conclusion is drawn on `Icc (-R/2) (R/2)`).

Nothing else changes: the proofs are the same, the constants being used only to name the intervals.

## Contents

* `tgt_eventually_gen`, `hasDerivAt_variation_gen`, `hasDerivAt_variation_vel_gen`,
  `deriv_chartGeodesicVectorField_gen` — the four lemmas, with an interval parameter `R`;
* **`variationField_satisfies_jacobiSys_gen`** — the extraction on `Icc (-R/2) (R/2)`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Commons.Analysis.Calculus
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.JacobiTensor
open Submission.Rauch
open Submission.SecondVariation
open Submission.SecondVar2
open Submission.FlowJacobi
open Submission.VariationJacobi

namespace Submission.FlowJacobiGen

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

section Variation

variable {x₀ : M} {δ R c : ℝ} {Φ : ℝ × ℝ → E × E}

lemma tgt_eventually_gen (hδ : 0 < δ)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (c - R) (c + R), (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    {s : ℝ} (hs : s ∈ Ioo (c - R) (c + R)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), (Φ (s, t)).1 ∈ (extChartAt I x₀).target := by
  filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)]
    with t ht
  exact hTGT t ht s hs

lemma hasDerivAt_variation_gen (hδ : 0 < δ)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (c - R) (c + R), (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (c - R) (c + R),
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (c - R) (c + R), ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0))
    {s : ℝ} (hs : s ∈ Ioo (c - R) (c + R)) :
    HasDerivAt (Yp Φ) (Zp Φ s) s := by
  have hF1 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (Φ p).1) (s, 0) :=
    (ContinuousLinearMap.fst ℝ E E).contDiff.contDiffAt.comp (s, 0)
      ((hSM s hs).of_le (by decide))
  have h := hasDerivAt_deriv_partial_swap (F := fun p : ℝ × ℝ => (Φ p).1) hF1
  have hev : (fun t : ℝ => deriv (fun σ : ℝ => (Φ (σ, t)).1) s) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => (Φ (s, t)).2) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)]
      with t ht
    exact (Submission.Gauss.hasDerivAt_fst (hODE t ht s hs)).deriv
  rw [hev.deriv_eq] at h
  exact h

lemma hasDerivAt_variation_vel_gen (hδ : 0 < δ)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (c - R) (c + R), (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (c - R) (c + R),
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (c - R) (c + R), ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0))
    {s : ℝ} (hs : s ∈ Ioo (c - R) (c + R)) :
    HasDerivAt (Zp Φ) (deriv (fun t : ℝ => chartGeodesicVectorField cov x₀ (Φ (s, t))) 0) s := by
  have hF2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (Φ p).2) (s, 0) :=
    (ContinuousLinearMap.snd ℝ E E).contDiff.contDiffAt.comp (s, 0)
      ((hSM s hs).of_le (by decide))
  have h := hasDerivAt_deriv_partial_swap (F := fun p : ℝ × ℝ => (Φ p).2) hF2
  have hev : (fun t : ℝ => deriv (fun σ : ℝ => (Φ (σ, t)).2) s) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => chartGeodesicVectorField cov x₀ (Φ (s, t))) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)]
      with t ht
    exact (Submission.Gauss.hasDerivAt_snd (hODE t ht s hs)).deriv
  rw [hev.deriv_eq] at h
  exact h

/-- **The derivative of the geodesic vector field along the variation** — the linearised geodesic
equation, on an arbitrary window. -/
lemma deriv_chartGeodesicVectorField_gen (hδ : 0 < δ)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (c - R) (c + R), (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (c - R) (c + R),
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (c - R) (c + R), ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0))
    {s : ℝ} (hs : s ∈ Ioo (c - R) (c + R)) :
    deriv (fun t : ℝ => chartGeodesicVectorField cov x₀ (Φ (s, t))) 0
      = - (dB cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) (Yp Φ s) (gv Φ s) (gv Φ s)
            + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) (Zp Φ s) (gv Φ s)
            + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) (gv Φ s) (Zp Φ s)) := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hcomp : ContDiffAt ℝ ∞ (fun t : ℝ => Φ (s, t)) 0 :=
    (hSM s hs).comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hdt : DifferentiableAt ℝ (fun t : ℝ => Φ (s, t)) 0 := hcomp.differentiableAt (by norm_num)
  have hu : HasDerivAt (fun t : ℝ => (Φ (s, t)).1) (Yp Φ s) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (Φ (s, t)).1) (deriv (fun t : ℝ => (Φ (s, t)).1) 0) 0 :=
      hdt.fst.hasDerivAt
    exact h1
  have ha : HasDerivAt (fun t : ℝ => (Φ (s, t)).2) (Zp Φ s) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (Φ (s, t)).2) (deriv (fun t : ℝ => (Φ (s, t)).2) 0) 0 :=
      hdt.snd.hasDerivAt
    exact h1
  have htgt : (Φ (s, 0)).1 ∈ (extChartAt I x₀).target := hTGT 0 h0 s hs
  have hstay : ∀ᶠ t in 𝓝 (0 : ℝ), (Φ (s, t)).1 ∈ (extChartAt I x₀).target :=
    tgt_eventually_gen (x₀ := x₀) hδ hTGT hs
  have hchr := hasDerivAt_chrB_curve (cov := cov) hu ha ha htgt hstay
  have hfun : (fun t : ℝ => chartGeodesicVectorField cov x₀ (Φ (s, t)))
      = (fun t : ℝ => - chrB cov x₀ ((extChartAt I x₀).symm ((Φ (s, t)).1)) ((Φ (s, t)).2)
          ((Φ (s, t)).2)) := by
    funext t; rfl
  rw [hfun]
  exact hchr.neg.deriv

end Variation

/-- **The variation field of a smooth family of chart geodesics solves the chart Jacobi system**,
on an arbitrary time window.  Let `Φ : ℝ × ℝ → E × E` be a family such that, for every `t` near
`0`, the curve `s ↦ Φ (s,t)` is a chart geodesic (with velocity `(Φ (s,t)).2`) staying inside the
chart target, and suppose `Φ` is jointly `C^∞` near `(s,0)` for `s ∈ (-R,R)`.  Then the pair
`(Yp Φ, Ufun x₀ Φ)` satisfies the linear Jacobi system on `[-R/2, R/2]`.

No hypothesis relates the family to the centre of the chart: this is the form needed when the chart
is taken at a point along a long geodesic. -/
theorem variationField_satisfies_jacobiSys_gen (htor : cov.torsion = 0) {x₀ : M} {δ R c : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) {Φ : ℝ × ℝ → E × E}
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (c - R) (c + R),
      (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (c - R) (c + R),
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s)
    (hSM : ∀ s ∈ Ioo (c - R) (c + R), ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0)) :
    ∀ t ∈ Icc (c - R/2) (c + R/2),
      HasDerivAt (fun r : ℝ => (Yp Φ r, Ufun (cov := cov) x₀ Φ r))
        (jacobiSysVec (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t, Ufun (cov := cov) x₀ Φ t)) t := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hsub : Icc (c - R/2) (c + R/2) ⊆ Ioo (c - R) (c + R) :=
    fun t ht => ⟨by linarith [ht.1, hR], by linarith [ht.2, hR]⟩
  intro t ht
  have ht2 : t ∈ Ioo (c - R) (c + R) := hsub ht
  have hsrc : (extChartAt I x₀).symm ((Φ (t, 0)).1) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) (x₀ := x₀) (u := fun _ => (Φ (t, 0)).1) (t := 0)
      (hTGT 0 h0 t ht2)
  have hu : HasDerivAt (gc Φ) (gv Φ t) t := Submission.Gauss.hasDerivAt_fst (hODE 0 h0 t ht2)
  have hw : HasDerivAt (gv Φ) (chartGeodesicVectorField cov x₀ (Φ (t, 0))) t :=
    Submission.Gauss.hasDerivAt_snd (hODE 0 h0 t ht2)
  have hGCtarget : gc Φ t ∈ (extChartAt I x₀).target := hTGT 0 h0 t ht2
  have hGCtarget_ev : ∀ᶠ r in 𝓝 t, gc Φ r ∈ (extChartAt I x₀).target := by
    filter_upwards [isOpen_Ioo.mem_nhds ht2] with r hr
    exact hTGT 0 h0 r hr
  have hy : HasDerivAt (Yp Φ) (Zp Φ t) t :=
    hasDerivAt_variation_gen (cov := cov) hδ hTGT hODE hSM ht2
  have hz := hasDerivAt_variation_vel_gen (cov := cov) hδ hTGT hODE hSM ht2
  have hzval := deriv_chartGeodesicVectorField_gen (cov := cov) hδ hTGT hODE hSM ht2
  have hchr : HasDerivAt
      (fun r : ℝ => chrB cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) (Yp Φ r) (gv Φ r))
      (dB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (Yp Φ t) (gv Φ t)
        + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Zp Φ t) (gv Φ t)
        + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t)
            (chartGeodesicVectorField cov x₀ (Φ (t, 0)))) t :=
    hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀) (u := gc Φ) (a := Yp Φ) (b := gv Φ)
      (v := gv Φ t) (a' := Zp Φ t) (b' := chartGeodesicVectorField cov x₀ (Φ (t, 0)))
      hu hy hw hGCtarget hGCtarget_ev
  have hUderiv : HasDerivAt (Ufun (cov := cov) x₀ Φ)
      (deriv (fun r : ℝ => chartGeodesicVectorField cov x₀ (Φ (t, r))) 0
        + (dB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (Yp Φ t) (gv Φ t)
          + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Zp Φ t) (gv Φ t)
          + chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t)
              (chartGeodesicVectorField cov x₀ (Φ (t, 0))))) t := by
    have h := hz.add hchr
    exact h
  have hgam : gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t)
      = chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t) (gv Φ t) :=
    gammaOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc (Yp Φ t)
  have hgamU : gammaOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Ufun (cov := cov) x₀ Φ t)
      = chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1))
          (Ufun (cov := cov) x₀ Φ t) (gv Φ t) :=
    gammaOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc
      (Ufun (cov := cov) x₀ Φ t)
  have hcurv : curvOp (cov := cov) x₀ (gc Φ) (gv Φ) t (Yp Φ t)
      = chartCurv cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (Yp Φ t) (gv Φ t) :=
    curvOp_apply (cov := cov) (x₀ := x₀) (u := gc Φ) (w := gv Φ) (t := t) hsrc (Yp Φ t)
  have hbase := hy.prodMk hUderiv
  rw [jacobiSysVec_apply]
  refine hbase.congr_deriv ?_
  refine Prod.ext ?_ ?_
  · simp only [hgam, Ufun_apply]
    abel
  · have hgv : chartGeodesicVectorField cov x₀ (Φ (t, 0))
        = - chrB cov x₀ ((extChartAt I x₀).symm ((Φ (t, 0)).1)) (gv Φ t) (gv Φ t) := rfl
    have hid := linearization_identity (cov := cov) htor x₀ hsrc (Yp Φ t) (Zp Φ t) (gv Φ t)
    rw [hzval, hgamU, hcurv, hgv, Ufun_apply, hid]

end

end Submission.FlowJacobiGen
