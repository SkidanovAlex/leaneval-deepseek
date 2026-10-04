import Submission.CoeffSmooth
import Submission.ChartCurvCont
import Submission.JacobiTensor
import Submission.FlowJacobi
import Submission.Commons.Analysis.ODE.contDiffOn_of_linearODE_pair

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the curvature coefficients of the Jacobi system

`Submission/CoeffSmooth.lean` upgraded the *Christoffel* coefficients of the Jacobi system
(`Γ̂_t = gammaOp`) to `C^∞` in the parameter.  This file does the *curvature* half: it upgrades the
coefficient operators `dB`, `chartCurv`, `curvOp` to `C^∞` in `t`, along a `C^∞` chart curve, and
then bootstraps the solutions of the Jacobi system to `C^∞` via the fleet lemma
`Commons.Analysis.ODE.contDiffOn_of_linearODE_pair`.

Contents:

* `contDiffOn_chrEntryModel_infty` — the coordinate model of a Christoffel entry is `C^∞`
  (upgrade of `Submission.ChartCurvCont.contDiffOn_chrEntryModel` from `C^1`);
* `contDiffOn_chrB_along_Ioo` — `t ↦ Γ(γ(t); a(t), σ_{b(t)})` is `C^∞`;
* `contDiffOn_dB_along_Ioo` — `t ↦ ∂B(γ(t); v(t))(a(t), b(t))` is `C^∞`;
* `contDiffOn_chartCurv_curve` — `t ↦ chartCurv(γ(t); X(t), Y(t))` is `C^∞`;
* `contDiffOn_gammaOp_along_Ioo` — the Christoffel operator `t ↦ Γ̂_t` is `C^∞`;
* `contDiffOn_curvOp_along_Ioo` — the curvature operator `t ↦ R̂_t` is `C^∞`;
* **`contDiffOn_of_jacobiSolution`** — the coordinate functions of a solution of the Jacobi system
  along a `C^∞` chart curve are `C^∞`.

The route for `dB` is the basis expansion `mvfderiv_chrB_apply` (writing the derivative in the base
point as a combination of `fderiv`s of the *fixed* coordinate models `chrEntryModel`) followed by
`ContDiffOn.fderiv_of_isOpen`.  No joint smoothness of the *manifold-valued* `dB` is needed.
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
open Submission.ChartCurv
open Submission.ChartCurvCont
open Submission.JacobiTensor
open Submission.Coeff
open Submission.Rauch

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

/-- The coordinate model of a Christoffel entry is `C^∞` (upgrade of
`Submission.ChartCurvCont.contDiffOn_chrEntryModel`). -/
theorem contDiffOn_chrEntryModel_infty [ContMDiffCovariantDerivative cov ∞] (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chrEntryModel cov x₀ i j) (extChartAt I x₀).target := by
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
  exact h3.contDiffOn

/-- **Smoothness of `chrB` along a smooth chart curve.** -/
lemma contDiffOn_chrB_along_Ioo [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {u a b : ℝ → E} {A₀ B₀ : ℝ}
    (hstay : ∀ t ∈ Ioo A₀ B₀, u t ∈ (extChartAt I x₀).target)
    (hu : ContDiffOn ℝ ∞ u (Ioo A₀ B₀)) (ha : ContDiffOn ℝ ∞ a (Ioo A₀ B₀))
    (hb : ContDiffOn ℝ ∞ b (Ioo A₀ B₀)) :
    ContDiffOn ℝ ∞ (fun t : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (u t)) (a t) (b t))
      (Ioo A₀ B₀) := by
  have hJ := contDiffOn_christoffelEval_joint (cov := cov) htor x₀
  have hmap : ContDiffOn ℝ ∞ (fun t : ℝ => (u t, (a t, b t))) (Ioo A₀ B₀) :=
    hu.prodMk (ha.prodMk hb)
  refine (hJ.comp hmap (fun t ht => ⟨hstay t ht, Set.mem_univ _, Set.mem_univ _⟩)).congr
    (fun t ht => rfl)

/-- **Smoothness of `dB` along a smooth chart curve.** -/
lemma contDiffOn_dB_along_Ioo [ContMDiffCovariantDerivative cov ∞]
    {x₀ : M} {u v a b : ℝ → E} {A₀ B₀ : ℝ}
    (hstay : ∀ t ∈ Ioo A₀ B₀, u t ∈ (extChartAt I x₀).target)
    (hu : ContDiffOn ℝ ∞ u (Ioo A₀ B₀)) (hv : ContDiffOn ℝ ∞ v (Ioo A₀ B₀))
    (ha : ContDiffOn ℝ ∞ a (Ioo A₀ B₀)) (hb : ContDiffOn ℝ ∞ b (Ioo A₀ B₀)) :
    ContDiffOn ℝ ∞
      (fun t : ℝ => dB cov x₀ ((extChartAt I x₀).symm (u t)) (v t) (a t) (b t)) (Ioo A₀ B₀) := by
  classical
  have hkey : ∀ t ∈ Ioo A₀ B₀,
      dB cov x₀ ((extChartAt I x₀).symm (u t)) (v t) (a t) (b t)
        = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (((Module.finBasis ℝ E).coord i) (a t) * ((Module.finBasis ℝ E).coord j) (b t)) •
              fderiv ℝ (chrEntryModel cov x₀ i j) (u t) (v t) := by
    intro t ht
    have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (x₀ := x₀) (u := u) (t := t) (hstay t ht)
    rw [dB, mvfderiv_chrB_apply (cov := cov) x₀ _ (a t) (b t) (v t) hsrc]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mvfderiv_frameVector_eq_fderiv (I := I) x₀ hsrc
      (mdifferentiableAt_gammaEntry (cov := cov) x₀ i j hsrc) (v t)]
    rw [show (extChartAt I x₀) ((extChartAt I x₀).symm (u t)) = u t from
      (extChartAt I x₀).right_inv (hstay t ht)]
    rfl
  refine ContDiffOn.congr ?_ (fun t ht => hkey t ht)
  refine ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => ?_))
  have hfj : ContDiffOn ℝ ∞ (fun x : E => fderiv ℝ (chrEntryModel cov x₀ i j) x)
      (extChartAt I x₀).target :=
    (contDiffOn_chrEntryModel_infty (cov := cov) x₀ i j).fderiv_of_isOpen
      (isOpen_extChartAt_target (I := I) x₀) (le_of_eq (by simp))
  have h1 : ContDiffOn ℝ ∞ (fun t : ℝ => fderiv ℝ (chrEntryModel cov x₀ i j) (u t))
      (Ioo A₀ B₀) := hfj.comp hu (fun t ht => hstay t ht)
  have h2 : ContDiffOn ℝ ∞
      (fun t : ℝ => fderiv ℝ (chrEntryModel cov x₀ i j) (u t) (v t)) (Ioo A₀ B₀) :=
    h1.clm_apply hv
  have h3 : ContDiffOn ℝ ∞ (fun t : ℝ => ((Module.finBasis ℝ E).coord i) (a t)) (Ioo A₀ B₀) :=
    (((Module.finBasis ℝ E).coord i).toContinuousLinearMap.contDiff).comp_contDiffOn ha
  have h4 : ContDiffOn ℝ ∞ (fun t : ℝ => ((Module.finBasis ℝ E).coord j) (b t)) (Ioo A₀ B₀) :=
    (((Module.finBasis ℝ E).coord j).toContinuousLinearMap.contDiff).comp_contDiffOn hb
  exact (h3.mul h4).smul h2

/-- **Smoothness of `chartCurv` along a smooth chart curve.** -/
lemma contDiffOn_chartCurv_curve [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {u X Y : ℝ → E} {A₀ B₀ : ℝ}
    (hstay : ∀ t ∈ Ioo A₀ B₀, u t ∈ (extChartAt I x₀).target)
    (hu : ContDiffOn ℝ ∞ u (Ioo A₀ B₀)) (hX : ContDiffOn ℝ ∞ X (Ioo A₀ B₀))
    (hY : ContDiffOn ℝ ∞ Y (Ioo A₀ B₀)) :
    ContDiffOn ℝ ∞ (fun t : ℝ =>
      chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (X t) (Y t)) (Ioo A₀ B₀) := by
  have h1 := contDiffOn_dB_along_Ioo (cov := cov) (v := X) (a := Y) (b := Y) hstay hu hX hY hY
  have h2 := contDiffOn_dB_along_Ioo (cov := cov) (v := Y) (a := Y) (b := X) hstay hu hY hY hX
  have hYin : ContDiffOn ℝ ∞
      (fun t : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (Y t)) (Ioo A₀ B₀) :=
    contDiffOn_chrB_along_Ioo (cov := cov) htor hstay hu hY hY
  have hXin : ContDiffOn ℝ ∞
      (fun t : ℝ => chrB cov x₀ ((extChartAt I x₀).symm (u t)) (Y t) (X t)) (Ioo A₀ B₀) :=
    contDiffOn_chrB_along_Ioo (cov := cov) htor hstay hu hY hX
  have h3 := contDiffOn_chrB_along_Ioo (cov := cov) htor hstay hu hYin hX
  have h4 := contDiffOn_chrB_along_Ioo (cov := cov) htor hstay hu hXin hY
  refine ((h1.sub h2).add h3).sub h4 |>.congr fun t _ => ?_
  simp only [chartCurv]

/-- **Smoothness of the Christoffel operator `gammaOp` along a smooth chart curve.** -/
lemma contDiffOn_gammaOp_along_Ioo [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {u w : ℝ → E} {A₀ B₀ : ℝ}
    (hstay : ∀ t ∈ Ioo A₀ B₀, u t ∈ (extChartAt I x₀).target)
    (hu : ContDiffOn ℝ ∞ u (Ioo A₀ B₀)) (hw : ContDiffOn ℝ ∞ w (Ioo A₀ B₀)) :
    ContDiffOn ℝ ∞ (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Ioo A₀ B₀) := by
  have hsum : ∀ t : ℝ, gammaOp (cov := cov) x₀ u w t
      = ∑ i : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
            (chrB cov x₀ ((extChartAt I x₀).symm (u t)) ((Module.finBasis ℝ E) i) (w t)) :=
    fun t => rfl
  simp only [hsum]
  refine ContDiffOn.sum (fun i _ => ?_)
  exact (ContinuousLinearMap.smulRightL ℝ E E
      (((Module.finBasis ℝ E).coord i).toContinuousLinearMap)).contDiff.comp_contDiffOn
    (contDiffOn_chrB_along_Ioo (cov := cov) htor hstay hu contDiffOn_const hw)

/-- **Smoothness of the curvature operator `curvOp` along a smooth chart curve.** -/
lemma contDiffOn_curvOp_along_Ioo [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {u w : ℝ → E} {A₀ B₀ : ℝ}
    (hstay : ∀ t ∈ Ioo A₀ B₀, u t ∈ (extChartAt I x₀).target)
    (hu : ContDiffOn ℝ ∞ u (Ioo A₀ B₀)) (hw : ContDiffOn ℝ ∞ w (Ioo A₀ B₀)) :
    ContDiffOn ℝ ∞ (fun t : ℝ => curvOp (cov := cov) x₀ u w t) (Ioo A₀ B₀) := by
  change ContDiffOn ℝ ∞ (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E),
    (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
      (chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) ((Module.finBasis ℝ E) i) (w t)))
    (Ioo A₀ B₀)
  refine ContDiffOn.sum (fun i _ => ?_)
  exact (ContinuousLinearMap.smulRightL ℝ E E
      (((Module.finBasis ℝ E).coord i).toContinuousLinearMap)).contDiff.comp_contDiffOn
    (contDiffOn_chartCurv_curve (cov := cov) htor hstay hu contDiffOn_const hw)

/-- **The coordinate functions of a solution of the Jacobi system are `C^∞`.** -/
theorem contDiffOn_of_jacobiSolution [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    {x₀ : M} {u w y z : ℝ → E} {A₀ B₀ a b : ℝ} (hab : a < b)
    (habt : Icc a b ⊆ Ioo A₀ B₀)
    (hstay : ∀ t ∈ Ioo A₀ B₀, u t ∈ (extChartAt I x₀).target)
    (hu : ContDiffOn ℝ ∞ u (Ioo A₀ B₀)) (hw : ContDiffOn ℝ ∞ w (Ioo A₀ B₀))
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (z t - gammaOp (cov := cov) x₀ u w t (y t)) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (-(gammaOp (cov := cov) x₀ u w t (z t))
      - curvOp (cov := cov) x₀ u w t (y t)) t)
    (hyc : ContinuousOn y (Icc a b)) (hzc : ContinuousOn z (Icc a b)) :
    ContDiffOn ℝ ∞ y (Icc a b) ∧ ContDiffOn ℝ ∞ z (Icc a b) :=
  Commons.Analysis.ODE.contDiffOn_of_linearODE_pair (A := gammaOp (cov := cov) x₀ u w)
    (B := curvOp (cov := cov) x₀ u w) hab
    ((contDiffOn_gammaOp_along_Ioo (cov := cov) htor hstay hu hw).mono habt)
    ((contDiffOn_curvOp_along_Ioo (cov := cov) htor hstay hu hw).mono habt)
    hy hz hyc hzc

end

end Submission.Coeff
