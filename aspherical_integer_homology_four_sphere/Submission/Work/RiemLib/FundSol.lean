import Submission.Work.RiemLib.ParallelRoom

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The chart-level fundamental solution of the parallel equation, and its positive determinant

This is **Stage 1** of the determinant theorem `det P = 1` for the holonomy of a closed curve
(Roadmap §115).  It isolates the *analytic* half of the argument:

* `chartOpCoeff` / `exists_chartOpSol` / **`fundSol`** — the fundamental solution `Φ` of the chart
  parallel equation, obtained **as an operator**: the solution of `Φ' = A(t) ∘ Φ`, `Φ a = 1` in the
  Banach space `E →L[ℝ] E`, where `A t = -Γ̂(t)`.  Solving in the operator algebra makes the
  linearity of `Φ t` free and gives the ODE directly;
* `fundSol_datum`, `fundSol_hasDerivAt`, `fundSol_vector_hasDerivAt`, `fundSol_eqOn` — `Φ t v` is the
  unique solution of the vector equation `y' = -Γ̂(t) y` with `y a = v`;
* **`fundSol_injective`** — `Φ t` is injective on `[a,b]` (a solution of a linear ODE that vanishes
  somewhere vanishes identically, by `Commons.Analysis.ODE.eqOn_of_hasDerivAt_linearODE`);
* `fundSol_det_ne_zero`, `continuous_linearMap_det`, `fundSol_continuousOn_det`,
  **`fundSol_det_pos`** — **the chart-level parallel transport has strictly positive determinant**:
  `0 < (Φ t).det` for `t ∈ [a,b]`.  Equivalently: `Φ t` acts on the line `ΛⁿE` by a *positive*
  scalar, i.e. it is orientation preserving.  The proof is the IVT on the connected interval
  `[a,b]`: `t ↦ (Φ t).det` is continuous, never vanishes and equals `1` at `t = a`.

Why this is the right first stage: in any chart-based trivialisation of `TM`, the parallel transport
contributes a *positive* factor to the determinant, so the *only* obstruction to `det P = 1` for a
closed curve is the product of the **signs of the chart-transition Jacobians** at the junctions of a
cover (Roadmap §115.2).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.JacobiTensor
open Submission.Jacobi

namespace Submission.FundSol

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## §1 The operator-valued parallel ODE -/

/-- The coefficient of the **operator-valued** parallel equation: `Φ ↦ A t ∘ Φ` with
`A t = -Γ̂(t)`. -/
def chartOpCoeff (x₀ : M) (u w : ℝ → E) (t : ℝ) : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.compL ℝ E E E (-(gammaOp (cov := cov) x₀ u w t))

theorem chartOpCoeff_apply (x₀ : M) (u w : ℝ → E) (t : ℝ) (Φ : E →L[ℝ] E) :
    chartOpCoeff (cov := cov) x₀ u w t Φ = (-(gammaOp (cov := cov) x₀ u w t)).comp Φ := rfl

theorem continuousOn_chartOpCoeff (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (chartOpCoeff (cov := cov) x₀ u w) (Icc a b) :=
  (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn
    ((Submission.IndexCorner2.continuousOn_gammaOp_of_cont (cov := cov) htor hu hw htgt).neg)

/-- **Existence and uniqueness of the operator-valued solution of the parallel equation**:
`Φ' = A(t) ∘ Φ` on `[a,b]` with `Φ a = 1`. -/
theorem exists_chartOpSol (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) :
    ∃ Φ : ℝ → (E →L[ℝ] E), Φ a = 1 ∧
      (∀ t ∈ Icc a b, HasDerivAt Φ (chartOpCoeff (cov := cov) x₀ u w t (Φ t)) t) ∧
      ∀ Ψ : ℝ → (E →L[ℝ] E), Ψ a = 1 →
        (∀ t ∈ Icc a b, HasDerivAt Ψ (chartOpCoeff (cov := cov) x₀ u w t (Ψ t)) t) →
        EqOn Ψ Φ (Icc a b) :=
  Commons.Analysis.ODE.exists_linearODE_solution_Icc (E := E →L[ℝ] E) hab
    (continuousOn_chartOpCoeff (cov := cov) htor hu hw htgt) ⟨le_rfl, hab.le⟩ 1

/-- **The fundamental solution of the chart parallel equation** on `[a,b]`, with datum the identity
at `a`. -/
noncomputable def fundSol (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) : ℝ → (E →L[ℝ] E) :=
  Classical.choose (exists_chartOpSol (cov := cov) htor hab hu hw htgt)

theorem fundSol_datum (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) :
    fundSol (cov := cov) htor hab hu hw htgt a = 1 :=
  (Classical.choose_spec (exists_chartOpSol (cov := cov) htor hab hu hw htgt)).1

theorem fundSol_hasDerivAt (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) :
    ∀ t ∈ Icc a b, HasDerivAt (fundSol (cov := cov) htor hab hu hw htgt)
      (chartOpCoeff (cov := cov) x₀ u w t (fundSol (cov := cov) htor hab hu hw htgt t)) t :=
  (Classical.choose_spec (exists_chartOpSol (cov := cov) htor hab hu hw htgt)).2.1

/-- The fundamental solution applied to a fixed vector solves the **vector** parallel equation. -/
theorem fundSol_vector_hasDerivAt (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) (v : E) :
    ∀ t ∈ Icc a b, HasDerivAt (fun s => fundSol (cov := cov) htor hab hu hw htgt s v)
      (-(gammaOp (cov := cov) x₀ u w t
        (fundSol (cov := cov) htor hab hu hw htgt t v))) t := by
  intro t ht
  have h := (fundSol_hasDerivAt (cov := cov) htor hab hu hw htgt t ht).clm_apply
    (hasDerivAt_const (x := t) v)
  have hval : chartOpCoeff (cov := cov) x₀ u w t (fundSol (cov := cov) htor hab hu hw htgt t) v
      + (fundSol (cov := cov) htor hab hu hw htgt t) 0
      = -(gammaOp (cov := cov) x₀ u w t (fundSol (cov := cov) htor hab hu hw htgt t v)) := by
    rw [chartOpCoeff_apply]
    simp
  rw [hval] at h
  exact h

/-- **Uniqueness for the vector parallel equation**: any solution with datum `v` at `a` agrees with
the fundamental solution. -/
theorem fundSol_eqOn (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) {y : ℝ → E} {v : E} (hy0 : y a = v)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (-(gammaOp (cov := cov) x₀ u w t (y t))) t) :
    EqOn y (fun s => fundSol (cov := cov) htor hab hu hw htgt s v) (Icc a b) := by
  have hAcont : ContinuousOn (fun t : ℝ => -(gammaOp (cov := cov) x₀ u w t)) (Icc a b) :=
    (Submission.IndexCorner2.continuousOn_gammaOp_of_cont (cov := cov) htor hu hw htgt).neg
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hAcont
  refine Commons.Analysis.ODE.eqOn_of_hasDerivAt_linearODE
    (A := fun t : ℝ => -(gammaOp (cov := cov) x₀ u w t))
    (M := ⟨max C 0, le_max_right _ _⟩) (fun t ht => ?_) ⟨le_rfl, hab.le⟩ hy
    (fundSol_vector_hasDerivAt (cov := cov) htor hab hu hw htgt v) ?_
  · exact le_trans (hC t ht) (le_max_left _ _)
  · have h := congrArg (fun L : E →L[ℝ] E => L v)
      (fundSol_datum (cov := cov) htor hab hu hw htgt)
    simpa using h ▸ hy0

/-! ## §2 Injectivity and positivity of the determinant -/

/-- **The fundamental solution is injective** at every time: a solution of a linear ODE that vanishes
somewhere vanishes identically. -/
theorem fundSol_injective (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Injective (fundSol (cov := cov) htor hab hu hw htgt t) := by
  intro v v' hvv'
  have h0 : fundSol (cov := cov) htor hab hu hw htgt t (v - v') = 0 := by
    rw [map_sub, hvv', sub_self]
  have hAcont : ContinuousOn (fun t : ℝ => -(gammaOp (cov := cov) x₀ u w t)) (Icc a b) :=
    (Submission.IndexCorner2.continuousOn_gammaOp_of_cont (cov := cov) htor hu hw htgt).neg
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hAcont
  have hM : ∀ s ∈ Icc a b, ‖-(gammaOp (cov := cov) x₀ u w s)‖ ≤ max C 0 :=
    fun s hs => le_trans (hC s hs) (le_max_left _ _)
  have hzero : ∀ s ∈ Icc a b, HasDerivAt (fun _ : ℝ => (0 : E))
      (-(gammaOp (cov := cov) x₀ u w s) ((fun _ : ℝ => (0 : E)) s)) s := by
    intro s hs
    simpa using hasDerivAt_const (x := s) (0 : E)
  have heq := Commons.Analysis.ODE.eqOn_of_hasDerivAt_linearODE
    (A := fun s : ℝ => -(gammaOp (cov := cov) x₀ u w s)) (M := ⟨max C 0, le_max_right _ _⟩)
    hM ht (fundSol_vector_hasDerivAt (cov := cov) htor hab hu hw htgt (v - v')) hzero h0
  have ha := heq (left_mem_Icc.mpr hab.le)
  have ha' : fundSol (cov := cov) htor hab hu hw htgt a (v - v') = 0 := by
    simpa using ha
  have h1 : v - v' = 0 := by
    have h := congrArg (fun (L : E →L[ℝ] E) => L (v - v'))
      (fundSol_datum (cov := cov) htor hab hu hw htgt)
    rw [ha'] at h
    simpa using h.symm
  exact sub_eq_zero.mp h1

/-- **The determinant of the fundamental solution is nonzero** (it is an invertible operator). -/
theorem fundSol_det_ne_zero (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) {t : ℝ} (ht : t ∈ Icc a b) :
    LinearMap.det (fundSol (cov := cov) htor hab hu hw htgt t).toLinearMap ≠ 0 := by
  intro hz
  have hker : (fundSol (cov := cov) htor hab hu hw htgt t).toLinearMap.ker ≠ ⊥ :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz
  obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff _).mp hker
  have hv0 : (fundSol (cov := cov) htor hab hu hw htgt t) v = 0 :=
    LinearMap.mem_ker.mp hv
  exact hvne (fundSol_injective (cov := cov) htor hab hu hw htgt ht (by rw [hv0, map_zero]))

/-- **The determinant is a continuous function of a continuous linear map.** -/
theorem continuous_linearMap_det :
    Continuous fun f : E →L[ℝ] E => LinearMap.det f.toLinearMap := by
  have hkey : (fun f : E →L[ℝ] E => LinearMap.det f.toLinearMap)
      = fun f => (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E)
          f.toLinearMap).det := by
    funext f
    exact (LinearMap.det_toMatrix (Module.finBasis ℝ E) f.toLinearMap).symm
  rw [hkey]
  refine Continuous.matrix_det (continuous_matrix (fun i j => ?_))
  have hmat : ∀ i j, (fun f : E →L[ℝ] E =>
        (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E) f.toLinearMap) i j)
      = fun f => (Module.finBasis ℝ E).coord i (f ((Module.finBasis ℝ E) j)) := by
    intro i j
    funext f
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [hmat i j]
  exact ((Module.finBasis ℝ E).coord i).continuous_of_finiteDimensional.comp
    ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) j)).continuous)

/-- Continuity of the determinant of the fundamental solution along `[a,b]`. -/
theorem fundSol_continuousOn_det (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) :
    ContinuousOn (fun t : ℝ => LinearMap.det (fundSol (cov := cov) htor hab hu hw htgt t).toLinearMap)
      (Icc a b) :=
  continuous_linearMap_det.comp_continuousOn
    (HasDerivAt.continuousOn (fundSol_hasDerivAt (cov := cov) htor hab hu hw htgt))

/-- **THE CHART-LEVEL PARALLEL TRANSPORT HAS POSITIVE DETERMINANT.**  The fundamental solution of
the chart parallel equation on `[a,b]` — i.e. the chart-level parallel transport from time `a` to
time `t` — has strictly positive determinant for every `t ∈ [a,b]`.  Equivalently: it acts on the
line `Λ^n E` by a strictly positive scalar, so it is **orientation preserving**.

This is the analytic content of "on a trivialised manifold the holonomy is orientation preserving":
the determinant is a continuous never-vanishing function of `t`, equal to `1` at `t = a`. -/
theorem fundSol_det_pos (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) {t : ℝ} (ht : t ∈ Icc a b) :
    0 < LinearMap.det (fundSol (cov := cov) htor hab hu hw htgt t).toLinearMap := by
  have hcont := fundSol_continuousOn_det (cov := cov) htor hab hu hw htgt
  have hga : LinearMap.det (fundSol (cov := cov) htor hab hu hw htgt a).toLinearMap = 1 := by
    rw [fundSol_datum (cov := cov) htor hab hu hw htgt]
    exact LinearMap.det_id
  have hne : ∀ s ∈ Icc a b,
      LinearMap.det (fundSol (cov := cov) htor hab hu hw htgt s).toLinearMap ≠ 0 :=
    fun s hs => fundSol_det_ne_zero (cov := cov) htor hab hu hw htgt hs
  rcases lt_trichotomy (LinearMap.det (fundSol (cov := cov) htor hab hu hw htgt t).toLinearMap) 0 with
    hneg | hzero | hpos
  · exfalso
    have him := intermediate_value_Icc' (a := a) (b := t) ht.1
      (hcont.mono (fun s hs => ⟨hs.1, le_trans hs.2 ht.2⟩))
    have hmem : (0 : ℝ) ∈ Icc (LinearMap.det (fundSol (cov := cov) htor hab hu hw htgt t).toLinearMap)
        (LinearMap.det (fundSol (cov := cov) htor hab hu hw htgt a).toLinearMap) :=
      ⟨hneg.le, by rw [hga]; norm_num⟩
    obtain ⟨s, hs, hgs⟩ := him hmem
    exact hne s ⟨hs.1, le_trans hs.2 ht.2⟩ hgs
  · exact absurd hzero (hne t ht)
  · exact hpos

end

end Submission.FundSol
