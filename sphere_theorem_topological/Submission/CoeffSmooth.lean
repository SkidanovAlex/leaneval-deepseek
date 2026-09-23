import Submission.JacobiGen
import Submission.GeodesicGlobal

import Submission.JacobiGen
import Submission.GeodesicGlobal

/-!
# Smoothness of the Christoffel operator along a smooth chart curve

The Jacobi system along a chart geodesic, `y' = z - Γ̂_t y`, `z' = -Γ̂_t z - R̂_t y`, is a linear
ODE system.  To bootstrap *smoothness* of its solutions (via
`Commons.Analysis.ODE.contDiffOn_of_hasDerivAt_of_contDiffOn`, requested as
`Commons.Analysis.ODE.contDiffOn_of_linearODE_pair`) one needs the coefficient operators `Γ̂_t` and
`R̂_t` to be `C^∞` in the parameter `t`.  For a chart geodesic this reduces to smoothness of the
Christoffel operator along the curve, which is what this file supplies.

The proofs are transcriptions of the continuity counterparts in `Submission/JacobiGen.lean`,
upgrading `ContinuousOn` to `ContDiffOn`.  The one ingredient that makes this cheap is the
**polarization identity** `Submission.Geodesic.christoffelEval_polarize`: the polarized Christoffel
symbol is a fixed linear combination of the chart spray evaluated at `(u t, a + w t)`,
`(u t, a)` and `(u t, w t)`, and the chart spray is `C^∞`
(`Submission.GeodesicGlobal.contDiffOn_chartSpray'`).

* `contDiffOn_christoffelEval_entry_Ioo` — one entry `t ↦ Γ(σ_a, w t)` is `C^∞` in `t`;
* `contDiffOn_christoffelLM_along_Ioo` — the operator `t ↦ Γ̂_t` is `C^∞` in `t`;
* **`contDiffOn_christoffelEval_joint`** — the **joint** smoothness of `(q, a, b) ↦ christoffelEval
  cov x₀ q a (frameVector x₀ q b)` on the chart, again by the polarization identity but now with the
  second coordinate slot free.  This is the ingredient the *curvature* half of the coefficients needs:
  `chartCurv` is built from `dB` and `chrB`, and both are derivatives/values of this joint form.

Gotchas of this file: `ContDiffOn.prod` does **not** exist (use `ContDiffOn.prodMk`); `ContDiffOn.comp`
returns a `Function.comp` (normalise with `ContDiffOn.congr (… := rfl)` or `rfl`); `ContDiffOn.congr h
h'` wants `h' : f₁ x = f x` with `h : ContDiffOn f s`, i.e. the *goal* is `f₁`; `E × E × E` parses as
`(E × E) × E` — write `E × (E × E)` and `A ×ˢ (B ×ˢ C)` when the projections matter; and
`mem_source_chartCurve` needs its `x₀`/`u`/`t` supplied explicitly when the goal does not exhibit them.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi

namespace Submission.Coeff

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **Smoothness of the Christoffel symbol along a smooth chart curve.**  This is the `ContDiffOn`
counterpart of `Submission.JacobiGen.continuousOn_christoffelEval_entry_Ioo`: the Christoffel
symbol evaluated at the chart curve, with a fixed coordinate vector `a` in its first slot and the
curve's velocity in its second, is `C^∞` in the curve parameter.

The proof is the polarization identity of `christoffelEval_polarize`: the polarized Christoffel
symbol is a fixed linear combination of the chart spray evaluated at `(u t, a + w t)`,
`(u t, a)` and `(u t, w t)`, and those are compositions of the (`C^∞`) spray with (`C^∞`) curve
data. -/
lemma contDiffOn_christoffelEval_entry_Ioo [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {A B : ℝ}
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ContDiffOn ℝ ∞ u (Ioo A B)) (hw : ContDiffOn ℝ ∞ w (Ioo A B))
    (a : E) :
    ContDiffOn ℝ ∞ (fun t : ℝ => christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (Ioo A B) := by
  have hspray : ContDiffOn ℝ ∞ (fun z : E × E => chartGeodesicVectorField cov x₀ z)
      ((extChartAt I x₀).target ×ˢ (univ : Set E)) :=
    Submission.GeodesicGlobal.contDiffOn_chartSpray' (cov := cov) x₀
  have hc1 : ContDiffOn ℝ ∞ (fun t : ℝ => chartGeodesicVectorField cov x₀ (u t, a + w t))
      (Ioo A B) :=
    (hspray.comp (hu.prodMk (contDiffOn_const.add hw))
      (fun t ht => ⟨hstay t ht, Set.mem_univ _⟩)).congr
      (fun t _ => rfl)
  have hc2 : ContDiffOn ℝ ∞ (fun t : ℝ => chartGeodesicVectorField cov x₀ (u t, a)) (Ioo A B) :=
    (hspray.comp (hu.prodMk contDiffOn_const) (fun t ht => ⟨hstay t ht, Set.mem_univ _⟩)).congr
      (fun t _ => rfl)
  have hc3 : ContDiffOn ℝ ∞ (fun t : ℝ => chartGeodesicVectorField cov x₀ (u t, w t))
      (Ioo A B) :=
    (hspray.comp (hu.prodMk hw) (fun t ht => ⟨hstay t ht, Set.mem_univ _⟩)).congr
      (fun t _ => rfl)
  have hcomb : ContDiffOn ℝ ∞ (fun t : ℝ => (1/2 : ℝ) • (- chartGeodesicVectorField cov x₀
        (u t, a + w t) + chartGeodesicVectorField cov x₀ (u t, a)
        + chartGeodesicVectorField cov x₀ (u t, w t))) (Ioo A B) :=
    (((hc1.neg).add hc2).add hc3).const_smul ((1/2 : ℝ))
  have key : ∀ t ∈ Ioo A B,
      christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        = (1/2 : ℝ) • (- chartGeodesicVectorField cov x₀ (u t, a + w t)
            + chartGeodesicVectorField cov x₀ (u t, a)
            + chartGeodesicVectorField cov x₀ (u t, w t)) := by
    intro t ht
    have hp : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (hstay t ht)
    have hpol := christoffelEval_polarize (cov := cov) htor hp a (w t)
    have hstep : christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        = (1/2 : ℝ) • (christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (a + w t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (a + w t))
          - christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) a)
          - christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (w t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) := by
      rw [← hpol]; module
    rw [hstep]
    simp only [chartGeodesicVectorField]
    module
  exact ContDiffOn.congr hcomb (fun t ht => key t ht)

/-- **Smoothness of the Christoffel *operator* along a smooth chart curve.**  The `ContDiffOn`
counterpart of `Submission.JacobiGen.continuousOn_christoffelLM_along_Ioo`. -/
lemma contDiffOn_christoffelLM_along_Ioo [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {A B : ℝ}
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ContDiffOn ℝ ∞ u (Ioo A B)) (hw : ContDiffOn ℝ ∞ w (Ioo A B)) :
    ContDiffOn ℝ ∞ (fun t : ℝ => christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (Ioo A B) := by
  have hsum : ∀ t : ℝ, christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
      = ∑ i : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
            (christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) ((Module.finBasis ℝ E) i)
              (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) :=
    fun t => rfl
  simp only [hsum]
  refine ContDiffOn.sum (fun i _ => ?_)
  exact (ContinuousLinearMap.smulRightL ℝ E E
      (((Module.finBasis ℝ E).coord i).toContinuousLinearMap)).contDiff.comp_contDiffOn
    (contDiffOn_christoffelEval_entry_Ioo (cov := cov) htor hstay hu hw ((Module.finBasis ℝ E) i))

/-- **Joint smoothness of the Christoffel symbol on the chart.**  The Christoffel symbol
`(q, a, b) ↦ Γ(q; a, σ_b)` is `C^∞` jointly on the chart.  Again the polarization identity turns it
into a combination of the (jointly `C^∞`) chart spray, now with the *second* coordinate slot free as
well — which is what the curvature term of the Jacobi equation needs. -/
lemma contDiffOn_christoffelEval_joint [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (x₀ : M) :
    ContDiffOn ℝ ∞ (fun p : E × (E × E) => christoffelEval cov x₀ ((extChartAt I x₀).symm p.1)
      p.2.1 (frameVector (I := I) x₀ ((extChartAt I x₀).symm p.1) p.2.2))
      ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) := by
  have hspray : ContDiffOn ℝ ∞ (fun z : E × E => chartGeodesicVectorField cov x₀ z)
      ((extChartAt I x₀).target ×ˢ (univ : Set E)) :=
    Submission.GeodesicGlobal.contDiffOn_chartSpray' (cov := cov) x₀
  have hfst : ContDiffOn ℝ ∞ (fun p : E × (E × E) => p.1)
      ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) := contDiffOn_fst
  have hs1 : ContDiffOn ℝ ∞ (fun p : E × (E × E) => p.2.1)
      ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) :=
    (contDiffOn_fst.comp contDiffOn_snd (fun p _ => Set.mem_univ _)).congr (fun p _ => rfl)
  have hs2 : ContDiffOn ℝ ∞ (fun p : E × (E × E) => p.2.2)
      ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) :=
    (contDiffOn_snd.comp contDiffOn_snd (fun p _ => Set.mem_univ _)).congr (fun p _ => rfl)
  have hmap1 : ContDiffOn ℝ ∞ (fun p : E × (E × E) => (p.1, p.2.1 + p.2.2))
      ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) :=
    hfst.prodMk (hs1.add hs2)
  have hmap2 : ContDiffOn ℝ ∞ (fun p : E × (E × E) => (p.1, p.2.1))
      ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) := hfst.prodMk hs1
  have hmap3 : ContDiffOn ℝ ∞ (fun p : E × (E × E) => (p.1, p.2.2))
      ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) := hfst.prodMk hs2
  have hc1 : ContDiffOn ℝ ∞ (fun p : E × (E × E) =>
      chartGeodesicVectorField cov x₀ (p.1, p.2.1 + p.2.2))
      ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) :=
    (hspray.comp hmap1 (fun p hp => ⟨hp.1, Set.mem_univ _⟩)).congr (fun p _ => rfl)
  have hc2 : ContDiffOn ℝ ∞ (fun p : E × (E × E) =>
      chartGeodesicVectorField cov x₀ (p.1, p.2.1))
      ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) :=
    (hspray.comp hmap2 (fun p hp => ⟨hp.1, Set.mem_univ _⟩)).congr (fun p _ => rfl)
  have hc3 : ContDiffOn ℝ ∞ (fun p : E × (E × E) =>
      chartGeodesicVectorField cov x₀ (p.1, p.2.2))
      ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) :=
    (hspray.comp hmap3 (fun p hp => ⟨hp.1, Set.mem_univ _⟩)).congr (fun p _ => rfl)
  have hcomb : ContDiffOn ℝ ∞ (fun p : E × (E × E) => (1/2 : ℝ) •
      (- chartGeodesicVectorField cov x₀ (p.1, p.2.1 + p.2.2)
        + chartGeodesicVectorField cov x₀ (p.1, p.2.1)
        + chartGeodesicVectorField cov x₀ (p.1, p.2.2)))
      ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) :=
    (((hc1.neg).add hc2).add hc3).const_smul ((1/2 : ℝ))
  have key : ∀ p : E × (E × E), p ∈ ((extChartAt I x₀).target ×ˢ (univ ×ˢ univ)) →
      christoffelEval cov x₀ ((extChartAt I x₀).symm p.1) p.2.1
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm p.1) p.2.2)
        = (1/2 : ℝ) • (- chartGeodesicVectorField cov x₀ (p.1, p.2.1 + p.2.2)
            + chartGeodesicVectorField cov x₀ (p.1, p.2.1)
            + chartGeodesicVectorField cov x₀ (p.1, p.2.2)) := by
    intro p hp
    have hp1 : p.1 ∈ (extChartAt I x₀).target := hp.1
    have hsrc : (extChartAt I x₀).symm p.1 ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (x₀ := x₀) (u := fun _ : ℝ => p.1) (t := 0) hp1
    have hpol := christoffelEval_polarize (cov := cov) htor hsrc p.2.1 p.2.2
    have hstep : christoffelEval cov x₀ ((extChartAt I x₀).symm p.1) p.2.1
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm p.1) p.2.2)
        = (1/2 : ℝ) • (christoffelEval cov x₀ ((extChartAt I x₀).symm p.1) (p.2.1 + p.2.2)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm p.1) (p.2.1 + p.2.2))
          - christoffelEval cov x₀ ((extChartAt I x₀).symm p.1) p.2.1
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm p.1) p.2.1)
          - christoffelEval cov x₀ ((extChartAt I x₀).symm p.1) p.2.2
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm p.1) p.2.2)) := by
      rw [← hpol]; module
    rw [hstep]
    simp only [chartGeodesicVectorField]
    module
  exact ContDiffOn.congr hcomb (fun p hp => key p hp)

end

end Submission.Coeff


