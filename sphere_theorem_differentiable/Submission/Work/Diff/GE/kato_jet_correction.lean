import Mathlib
import Submission.Work.Diff.GE.kato_deps

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- (as in `Submission/Work/Diff/GE/EvolB/kato_jet_correction_B.lean`, from which this proof is
-- copied: the `rw` steps below match through `LinearMap`/`Function` coercions)
set_option backward.isDefEq.respectTransparency false

/-!
# The jet correction: a section with prescribed value and vanishing covariant derivative

`Work.Diff.GE.kato_jet_correction`: for a covariant derivative `cov` (no compatibility or torsion
hypothesis is needed) and a tangent vector `u` at `x`, there is a globally `C^∞` section `Y` with
`Y x = u` and `cov Y x = 0`.

This is the only input of the (already written) proof of `Work.Diff.GE.kato_geodesic_frame`: the
geodesic orthonormal frame is obtained from it by Gram–Schmidt.

The proof here is the one of `Submission/Work/Diff/GE/EvolB/kato_jet_correction_B.lean` (where it is
stated in the `EvolB` namespace and against the `EvolB` import gate); it is reproduced in this file
so that `kato_geodesic_frame` can be proved from it *without* `sorryAx` (the `EvolB` copy cannot be
imported here — `Work.Diff.GE.EvolB.Lib` already imports `kato_geodesic_frame`, so the import would
create a cycle).

Route.  Write `Y := ∑ᵢ fᵢ • σᵢ` with `σᵢ := smoothExt x eᵢ` for a basis `(eᵢ)` of `TₓM` and smooth
functions `fᵢ`.  The Leibniz rule for the covariant derivative of a finite sum gives
`cov Y x v = ∑ᵢ fᵢ x • (cov σᵢ x v) + ∑ᵢ (mvfderiv I fᵢ x v) • eᵢ`, so the *only* data of the `fᵢ`
that enter are their values and their first derivatives at `x`; choosing the values `Aᵢ` as the
coordinates of `u` makes `Y x = u`, and then the functionals `mvfderiv I fᵢ x` are chosen freely
(within the set of realisable derivatives, which is everything, by `kato_exists_jet_functional`) to
cancel the Christoffel term `∑ᵢ Aᵢ • cov σᵢ x v`.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- The manifold derivative of the affine chart-coordinate function `y ↦ ℓ (χ y - χ x)`, with
`χ = extChartAt I x`, is `ℓ` composed with the chart derivative at `x`. -/
theorem kato_mvfderiv_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) (ℓ : E →L[ℝ] ℝ) :
    mvfderiv I (fun y : M => ℓ ((extChartAt I x) y - (extChartAt I x) x)) x
      = ℓ.comp (mfderiv I 𝓘(ℝ,E) (extChartAt I x) x) := by
  have hχ : MDifferentiableAt I 𝓘(ℝ,E) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  set c : E := (extChartAt I x) x with hc
  have hphi : (fun w : E => ℓ (w - c)) = ((fun w : E => ℓ w) - fun _ : E => ℓ c) := by
    ext w; rw [Pi.sub_apply, map_sub]
  have hsplit : (fun y : M => ℓ ((extChartAt I x) y - (extChartAt I x) x))
      = (fun w : E => ℓ (w - c)) ∘ (extChartAt I x) := rfl
  have hdphi : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ)
      (fun w : E => ℓ (w - c)) c := by
    rw [hphi]
    exact ((ContinuousLinearMap.contMDiff (n := ⊤) ℓ).sub contMDiff_const).mdifferentiableAt
      (by simp)
  rw [hsplit, mvfderiv_comp x hdphi hχ]
  have hclm : mvfderiv (modelWithCornersSelf ℝ E) (fun w : E => ℓ (w - c)) c = ℓ := by
    rw [hphi]
    have hd1 : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ)
        (fun w : E => ℓ w) c :=
      (ContinuousLinearMap.contMDiff (n := ⊤) ℓ).mdifferentiableAt (by simp)
    have hd2 : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ)
        (fun _ : E => ℓ c) c := mdifferentiableAt_const (c := ℓ c)
    rw [mvfderiv_sub hd1 hd2, mvfderiv_const, sub_zero]
    rw [mvfderiv_eq_fderiv]
    exact (ContinuousLinearMap.hasFDerivAt ℓ).fderiv
  rw [hclm]

/-- **A global `C^∞` function with prescribed first derivative.**  For `x : M` and a continuous
linear functional `L : TₓM →L[ℝ] ℝ` there is a globally `C^∞` `g : M → ℝ` with `g x = 0` and
`mvfderiv I g x = L`. -/
theorem kato_exists_jet_functional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) (L : TangentSpace I x →L[ℝ] ℝ) :
    ∃ g : M → ℝ, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ g ∧ g x = 0 ∧
      mvfderiv I g x = L := by
  classical
  set D : TangentSpace I x →L[ℝ] E := mfderiv I 𝓘(ℝ,E) (extChartAt I x) x with hD
  have hDinv : D.IsInvertible := isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)
  set ℓ : E →L[ℝ] ℝ := L.comp D.inverse with hℓ
  set g : M → ℝ := fun y => ℓ ((extChartAt I x) y - (extChartAt I x) x) with hg
  have hgx : g x = 0 := by simp [hg]
  have hgd : mvfderiv I g x = L := by
    rw [hg, kato_mvfderiv_affine, ← hD]
    ext v
    simp only [ContinuousLinearMap.comp_apply, hℓ]
    rw [ContinuousLinearMap.IsInvertible.inverse_apply_self hDinv v]
  obtain ⟨ψ, -, hψsupp⟩ : ∃ ψ : SmoothBumpFunction I x,
      True ∧ tsupport (ψ : M → ℝ) ⊆ (chartAt H x).source :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  have hgOn : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ g (chartAt H x).source := by
    have h1 : ContMDiffOn I 𝓘(ℝ,E) ∞ (fun y : M => (extChartAt I x) y - (extChartAt I x) x)
        (chartAt H x).source :=
      (contMDiffOn_extChartAt (I := I) (x := x)).sub_const _
    exact (ℓ.contMDiff).comp_contMDiffOn h1
  have hgsm : ContMDiff I 𝓘(ℝ,ℝ) ∞ (fun y : M => (ψ : M → ℝ) y * g y) := by
    simpa only [smul_eq_mul] using ψ.contMDiff_smul hgOn
  have hgd' : MDifferentiableAt I 𝓘(ℝ,ℝ) g x :=
    ((hgOn x (mem_chart_source H x)).contMDiffAt
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))).mdifferentiableAt (by simp)
  have hψd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M => (ψ : M → ℝ) y) x :=
    ψ.contMDiff.mdifferentiableAt (by simp)
  refine ⟨fun y => (ψ : M → ℝ) y * g y, hgsm, ?_, ?_⟩
  · show (ψ : M → ℝ) x * g x = 0
    rw [SmoothBumpFunction.eq_one, hgx, mul_zero]
  · rw [mvfderiv_fun_mul hψd hgd', hgd, SmoothBumpFunction.eq_one, hgx, one_smul, zero_smul,
      add_zero]

/-- **The jet correction.**  For a covariant derivative `cov` (no compatibility or torsion
hypothesis needed) and a vector `u` at `x` there is a globally `C^∞` section `Y` with `Y x = u`
whose covariant derivative vanishes at `x`. -/
theorem kato_jet_correction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x : M) (u : TangentSpace I x) :
    ∃ Y : Π y : M, TangentSpace I y,
      CMDiff ∞ (T% Y) ∧ Y x = u ∧ cov Y x = 0 := by
  classical
  -- A basis `e` of `TₓM` and the expansion of every vector in it.
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let e : Fin (Module.finrank ℝ E) → TangentSpace I x := fun i => ((b i : E) : TangentSpace I x)
  have hexp : ∀ w : TangentSpace I x, ∑ i, b.coord i ((w : E)) • e i = w := by
    intro w
    rw [show (∑ i, b.coord i ((w : E)) • e i)
        = ∑ i, b.repr ((w : E)) i • e i from
      Finset.sum_congr rfl (fun i _ => by rw [Module.Basis.coord_apply])]
    exact Module.Basis.sum_repr b (w : E)
  -- Smooth fields with the basis vectors as values at `x`, and their covariant derivatives.
  let σ : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun i => Submission.Diff.smoothExt x (e i)
  have hσsm : ∀ i, ContMDiff I I.tangent ∞ (T% (σ i)) :=
    fun i => Work.Diff.GE.smoothExt_cmdiff x (e i)
  have hσx : ∀ i, σ i x = e i := fun i => Work.Diff.GE.smoothExt_apply x (e i)
  -- The coordinates of `u` in the basis, and the correction functionals.
  let A : Fin (Module.finrank ℝ E) → ℝ := fun i => b.coord i ((u : E))
  have hYx : ∑ i, A i • e i = u := hexp u
  let L : Fin (Module.finrank ℝ E) → TangentSpace I x →L[ℝ] ℝ := fun j =>
    - ∑ i, A i • ((b.coord j).toContinuousLinearMap.comp (cov (σ i) x))
  -- Smooth functions whose first derivative at `x` is the prescribed functional.
  have hjet : ∀ j, ∃ g : M → ℝ, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ g ∧ g x = 0 ∧
      mvfderiv I g x = L j := fun j => kato_exists_jet_functional x (L j)
  choose g hgsm hgx hgv using hjet
  -- Add the prescribed values at `x`.
  let f : Fin (Module.finrank ℝ E) → M → ℝ := fun j y => A j + g j y
  have hfsm : ∀ j, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (f j) := by
    intro j
    have hdec : f j = (fun _ : M => A j) + g j := rfl
    rw [hdec]
    exact contMDiff_const.add (hgsm j)
  have hfx : ∀ j, f j x = A j := by intro j; simp [f, hgx j]
  have hfv : ∀ j, mvfderiv I (f j) x = L j := by
    intro j
    have hdec : f j = (fun _ : M => A j) + g j := rfl
    rw [hdec, mvfderiv_add (mdifferentiableAt_const (c := A j))
      ((hgsm j).mdifferentiableAt (by simp)), mvfderiv_const, zero_add]
    exact hgv j
  -- The corrected field.
  let Y : Π y : M, TangentSpace I y := fun y => ∑ i, f i y • σ i y
  have hYsm : CMDiff ∞ (T% Y) := by
    have hterm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ,E)) ∞ (T% (f i • σ i)) :=
      fun i => (hfsm i).smul_section (hσsm i)
    have hsum := ContMDiff.sum_section (𝕜 := ℝ) (F := E) (V := TangentSpace I) (I := I) (n := ∞)
      (s := Finset.univ) (t := fun i => f i • σ i) (fun i _ => hterm i)
    simpa [Y] using hsum
  refine ⟨Y, hYsm, ?_, ?_⟩
  · show (∑ i, f i x • σ i x) = u
    rw [show (∑ i, f i x • σ i x) = ∑ i, A i • e i from
      Finset.sum_congr rfl (fun i _ => by rw [hfx i, hσx i])]
    exact hYx
  · -- The covariant derivative: the Christoffel terms contain the `A i` and the Leibniz terms
    -- the chosen functionals `L i`, which were *defined* to cancel them.
    ext v
    rw [Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise
      (s := Finset.univ) (f := f) (σ := σ) (Z := Y) (x := x) (v := v)
      hYsm.contMDiffAt (fun i => (hσsm i).contMDiffAt) (fun i => (hfsm i).contMDiffAt)
      (Filter.EventuallyEq.refl _ _)]
    simp only [hfx, hfv, hσx, zero_apply]
    have hsplit : (∑ i, A i • cov (σ i) x v)
        = ∑ j, (∑ i, A i * b.coord j ((cov (σ i) x v : E))) • e j := by
      calc ∑ i, A i • cov (σ i) x v
          = ∑ i, A i • (∑ j, b.coord j ((cov (σ i) x v : E)) • e j) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [hexp (cov (σ i) x v)]
        _ = ∑ i, ∑ j, (A i * b.coord j ((cov (σ i) x v : E))) • e j := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [smul_smul]
        _ = ∑ j, (∑ i, A i * b.coord j ((cov (σ i) x v : E))) • e j := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.sum_smul]
    have hLv : ∀ j, (L j) v = - (∑ i, A i * b.coord j ((cov (σ i) x v : E))) := by
      intro j
      simp only [L, neg_apply, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
        LinearMap.coe_toContinuousLinearMap', smul_eq_mul]
      rfl
    rw [hsplit]
    have hsum2 : (∑ j, (L j) v • e j)
        = - (∑ j, (∑ i, A i * b.coord j ((cov (σ i) x v : E))) • e j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hLv j, neg_smul]
    rw [hsum2, add_neg_cancel]

end Work.Diff.GE
