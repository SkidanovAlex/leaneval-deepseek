import Submission.OrientSign

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The determinant of the composite holonomy along a chart cover

The sign of the determinant of the parallel transport around a closed curve is the sign of the
chart-covered loop (`Submission.OrientSign`).  This module proves the analytic half:

* `coordC z γ k` — the chart coordinate curve of `γ` in the chart `z k`;
* **`pieceTrans`** — the chart-level parallel transport along the piece `[P.t k, P.t (k+1)]`, i.e.
  `FundSol.fundSol` evaluated at the right endpoint; `pieceTrans_det_pos` — its determinant is
  **positive** (from `FundSol.fundSol_det_pos`);
* **`holAux`** — the composite holonomy `τ_{N-1} ∘ Φ_{N-1} ∘ ⋯ ∘ τ_0 ∘ Φ_0` in the chart `z 0` at
  the base point, as a recursive product in the monoid `E →L[ℝ] E`;
* **`det_holAux`** — its determinant is the product of the `factor`s
  (`factor k = det (τ k) · det (Φ k)`, `1` outside the range), proved by induction with
  `LinearMap.det_comp`;
* **`sign_det_holAux`** — **the sign of the determinant of the composite holonomy is the sign of the
  chart-covered loop** — the determinant identity of the determinant theorem `det P = 1`
  (Roadmap §115.2), in the form needed for the application.

Together with `Submission.OrientSign.exists_chartLoop_of_simplyConnected` this gives: the composite
holonomy of a null-homotopic loop is orientation preserving.  The remaining step (Roadmap §118) is to
identify `holAux` with the intrinsic parallel transport along the curve (isometry, velocity).
-/


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.JacobiTensor
open Submission.OrientSign
open Submission.ChartConnection
open Submission.BonnetMyers
open Submission.Jacobi

namespace Submission.HolDet

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

/-! ## §1 The determinant of a product of continuous linear maps -/

theorem det_toLinearMap_mul (f g : E →L[ℝ] E) :
    LinearMap.det ((f * g).toLinearMap)
      = LinearMap.det (f.toLinearMap) * LinearMap.det (g.toLinearMap) := by
  have h : (f * g).toLinearMap = f.toLinearMap.comp g.toLinearMap := by
    ext v; rfl
  rw [h, LinearMap.det_comp]

theorem det_toLinearMap_mul_left (f g : E →L[ℝ] E) :
    LinearMap.det ((g * f).toLinearMap)
      = LinearMap.det (g.toLinearMap) * LinearMap.det (f.toLinearMap) :=
  det_toLinearMap_mul g f

/-! ## §2 The chart-level parallel transport along the pieces of a chart cover -/

variable {P : Partition 0 1} {z : ℕ → M} {γ : ℝ → M}

/-- The chart coordinate curve of `γ` in the chart `z k`. -/
def coordC (k : ℕ) : ℝ → E := fun t => extChartAt I (z k) (γ t)

/-- **The chart-level parallel transport along the piece `k`** of a chart cover: the fundamental
solution of `y' = -Γ̂ y` in the chart `z k`, over `[P.t k, P.t (k+1)]`, evaluated at the right
endpoint. -/
noncomputable def pieceTrans (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k)) (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (k : ℕ) (hk : k < P.N) : E →L[ℝ] E :=
  FundSol.fundSol (cov := cov) (x₀ := z k) htor (P.mono k hk) (hu k hk) (hw k hk) (htgt k hk)
    (P.t (k+1))

/-- The determinant of the chart-level parallel transport along a piece is **positive**. -/
theorem pieceTrans_det_pos (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k)) (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (k : ℕ) (hk : k < P.N) :
    0 < LinearMap.det ((pieceTrans (cov := cov) htor hu hw htgt k hk).toLinearMap) :=
  FundSol.fundSol_det_pos (cov := cov) (x₀ := z k) htor (P.mono k hk) (hu k hk) (hw k hk) (htgt k hk)
    ⟨(P.mono k hk).le, le_rfl⟩

/-- The **composite holonomy** along the chart cover, in the chart `z 0` at the base point: the
product `τ_{N-1} ∘ Φ_{N-1} ∘ ⋯ ∘ τ_0 ∘ Φ_0` of the piece transports and the chart transitions. -/
noncomputable def holAux (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k)) (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target) : ℕ → E →L[ℝ] E
  | 0 => 1
  | (k+1) => (if h : k < P.N then
        (chartTransition (I := I) (z k) (z (k+1)) (γ (P.t (k+1)))
          * pieceTrans (cov := cov) htor hu hw htgt k h) * holAux htor hu hw htgt k
      else holAux htor hu hw htgt k)

/-- The determinant factor contributed by the piece `k`: the determinant of the chart transition at
the far junction times the determinant of the piece transport (`1` outside the range `[0, P.N)`). -/
noncomputable def factor (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (k : ℕ) : ℝ :=
  if h : k < P.N then
    chartDet (I := I) (z k) (z (k+1)) (γ (P.t (k+1)))
      * LinearMap.det ((pieceTrans (cov := cov) htor hu hw htgt k h).toLinearMap)
  else 1

theorem factor_eq (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    {k : ℕ} (hk : k < P.N) :
    factor (cov := cov) htor hu hw htgt k
      = chartDet (I := I) (z k) (z (k+1)) (γ (P.t (k+1)))
        * LinearMap.det ((pieceTrans (cov := cov) htor hu hw htgt k hk).toLinearMap) :=
  dif_pos hk

theorem det_holAux (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target) :
    ∀ n : ℕ, LinearMap.det ((holAux (cov := cov) htor hu hw htgt n).toLinearMap)
      = ∏ k ∈ Finset.range n, factor (cov := cov) htor hu hw htgt k := by
  intro n
  induction n with
  | zero => simp [holAux]
  | succ m ih =>
    rw [show holAux (cov := cov) htor hu hw htgt (m+1)
        = (if h : m < P.N then
            (chartTransition (I := I) (z m) (z (m+1)) (γ (P.t (m+1)))
              * pieceTrans (cov := cov) htor hu hw htgt m h) * holAux htor hu hw htgt m
          else holAux htor hu hw htgt m) from rfl]
    rw [Finset.prod_range_succ]
    by_cases hm : m < P.N
    · rw [dif_pos hm, factor_eq (cov := cov) htor hu hw htgt hm, det_toLinearMap_mul,
        det_toLinearMap_mul, ih]
      simp only [chartDet]
      ring
    · rw [dif_neg hm, show factor (cov := cov) htor hu hw htgt m = 1 from dif_neg hm, mul_one, ih]

/-! ## §3 The sign of the determinant of the composite holonomy -/

theorem sign_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, f i ≠ 0) :
    (if 0 < ∏ i ∈ s, f i then (1 : ℝ) else -1)
      = ∏ i ∈ s, (if 0 < f i then (1 : ℝ) else -1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Submission.OrientSign.ite_pos_mul_ite (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr (fun b hb => hf b (Finset.mem_insert_of_mem hb))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- **The sign of the determinant of the composite holonomy is the sign of the chart-covered
loop.** -/
theorem sign_det_holAux (hP : IsChartLoop (H := H) P γ z) (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target) :
    (if 0 < LinearMap.det ((holAux (cov := cov) htor hu hw htgt P.N).toLinearMap)
        then (1 : ℝ) else -1)
      = loopSignOf (I := I) P γ z := by
  classical
  have hne : ∀ k ∈ Finset.range P.N, factor (cov := cov) htor hu hw htgt k ≠ 0 := by
    intro k hk
    have hk' : k < P.N := Finset.mem_range.mp hk
    rw [factor_eq (cov := cov) htor hu hw htgt hk']
    exact mul_ne_zero (chartDet_ne_zero (I := I) (isChartLoop_junction hP hk'))
      (ne_of_gt (pieceTrans_det_pos (cov := cov) htor hu hw htgt k hk'))
  rw [det_holAux (cov := cov) htor hu hw htgt P.N, sign_prod _ _ hne, loopSignOf]
  refine Finset.prod_congr rfl (fun k hk => ?_)
  have hk' : k < P.N := Finset.mem_range.mp hk
  rw [factor_eq (cov := cov) htor hu hw htgt hk',
    Submission.OrientSign.ite_pos_mul_ite (chartDet_ne_zero (I := I) (isChartLoop_junction hP hk'))
      (ne_of_gt (pieceTrans_det_pos (cov := cov) htor hu hw htgt k hk')),
    if_pos (pieceTrans_det_pos (cov := cov) htor hu hw htgt k hk'), mul_one]
  exact Submission.OrientSign.chartSign_eq_ite (I := I) (z k) (z (k+1)) (γ (P.t (k+1)))


/-- **The composite holonomy of a chart-covered loop whose sign is `1` is orientation preserving.**
Combined with `Submission.OrientSign.exists_chartLoop_of_simplyConnected` (which produces such a
family for every loop in a simply connected manifold), this is the determinant theorem `det P = 1`
in the form "the parallel transport around a null-homotopic loop preserves the orientation". -/
theorem sign_det_holAux_eq_one_of_loopSignOf_eq_one (hP : IsChartLoop (H := H) P γ z)
    (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (hloop : loopSignOf (I := I) P γ z = 1) :
    (if 0 < LinearMap.det ((holAux (cov := cov) htor hu hw htgt P.N).toLinearMap)
        then (1 : ℝ) else -1) = 1 := by
  rw [sign_det_holAux (cov := cov) hP htor hu hw htgt, hloop]



/-! ## §4 The chart velocity is parallel along a piece -/

/-- **The chart velocity is parallel along a piece**: the chart velocity of a geodesic solves the
parallel equation `y' = -Γ̂ y`, so the chart-level transport along the piece fixes it. -/
theorem fundSol_velocity
    (hgeo : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      HasDerivAt (deriv (coordC (I := I) (z := z) (γ := γ) k))
        (chartGeodesicVectorField cov (z k)
          (coordC (I := I) (z := z) (γ := γ) k t,
            deriv (coordC (I := I) (z := z) (γ := γ) k) t)) t)
    (hsrc : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)), γ t ∈ (chartAt H (z k)).source)
    (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (k : ℕ) (hk : k < P.N) :
    (pieceTrans (cov := cov) htor hu hw htgt k hk)
        (deriv (coordC (I := I) (z := z) (γ := γ) k) (P.t k))
      = deriv (coordC (I := I) (z := z) (γ := γ) k) (P.t (k+1)) := by
  have hy : ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      HasDerivAt (deriv (coordC (I := I) (z := z) (γ := γ) k))
        (-(gammaOp (cov := cov) (z k) (coordC (I := I) (z := z) (γ := γ) k)
          (deriv (coordC (I := I) (z := z) (γ := γ) k)) t
          (deriv (coordC (I := I) (z := z) (γ := γ) k) t))) t := by
    intro t ht
    have h1 := hgeo k hk t ht
    have hmem : γ t ∈ (extChartAt I (z k)).source := by
      rw [extChartAt_source]
      exact hsrc k hk t ht
    have hsymm : (extChartAt I (z k)).symm (coordC (I := I) (z := z) (γ := γ) k t) = γ t :=
      PartialEquiv.left_inv _ hmem
    have hsrc' : (extChartAt I (z k)).symm
        (coordC (I := I) (z := z) (γ := γ) k t) ∈ (chartAt H (z k)).source := by
      rw [hsymm]
      exact hsrc k hk t ht
    rw [Submission.ParallelGlobal.chartGeodesicVectorField_eq_neg_gammaOp (cov := cov)
      (x₀ := z k) (u := coordC (I := I) (z := z) (γ := γ) k)
      (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) (t := t) hsrc'] at h1
    exact h1
  have heq := FundSol.fundSol_eqOn (cov := cov) (x₀ := z k) htor (P.mono k hk) (hu k hk)
    (hw k hk) (htgt k hk) (y := deriv (coordC (I := I) (z := z) (γ := γ) k))
    (v := deriv (coordC (I := I) (z := z) (γ := γ) k) (P.t k)) rfl hy
    ⟨(P.mono k hk).le, le_rfl⟩
  exact heq.symm


/-! ## §5 The chart transition and the chart velocity / the chart Gram -/

variable {z z' : M} {x : M}

theorem coordChangeL_continuousLinearMapAt
    (e e' : Bundle.Trivialization E (Bundle.TotalSpace.proj : Bundle.TotalSpace E
      (TangentSpace I (M := M)) → M))
    [e.IsLinear ℝ] [e'.IsLinear ℝ] {b : M}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (v : TangentSpace I b) :
    Bundle.Trivialization.coordChangeL ℝ e e' b (e.continuousLinearMapAt ℝ b v)
      = e'.continuousLinearMapAt ℝ b v := by
  have h1 : e.continuousLinearMapAt ℝ b v = (e.linearEquivAt ℝ b hb.1) v := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hb.1 v,
      Bundle.Trivialization.linearEquivAt_apply]
  have h2 : e'.continuousLinearMapAt ℝ b v = (e'.linearEquivAt ℝ b hb.2) v := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e' hb.2 v,
      Bundle.Trivialization.linearEquivAt_apply]
  rw [h1, h2, Bundle.Trivialization.coe_coordChangeL _ _ hb, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

/-- **A chart transition is the change of frame**: the frame vector with the *target* chart's
coordinates agrees with the frame vector with the *source* chart's coordinates. -/
theorem chartTransition_frameVector
    (hx : x ∈ (chartAt H z).source ∩ (chartAt H z').source) (a : E) :
    frameVector (I := I) z' x (chartTransition (I := I) z z' x a)
      = frameVector (I := I) z x a := by
  have hxz : x ∈ (extChartAt I z).source := by rw [extChartAt_source]; exact hx.1
  have hxz' : x ∈ (extChartAt I z').source := by rw [extChartAt_source]; exact hx.2
  have hb : x ∈ (trivializationAt E (TangentSpace I) z).baseSet ∩
      (trivializationAt E (TangentSpace I) z').baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  have hkey : chartTransition (I := I) z z' x a
      = (trivializationAt E (TangentSpace I) z').continuousLinearMapAt ℝ x
          (frameVector (I := I) z x a) := by
    calc chartTransition (I := I) z z' x a
        = Bundle.Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) z)
            (trivializationAt E (TangentSpace I) z') x a := rfl
      _ = Bundle.Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) z)
            (trivializationAt E (TangentSpace I) z') x
            ((trivializationAt E (TangentSpace I) z).continuousLinearMapAt ℝ x
              (frameVector (I := I) z x a)) := by
          rw [Submission.GExpFlow.clm_frameVector (I := I) hxz a]
      _ = (trivializationAt E (TangentSpace I) z').continuousLinearMapAt ℝ x
            (frameVector (I := I) z x a) := coordChangeL_continuousLinearMapAt _ _ hb _
  rw [hkey, Submission.GExpFlow.frameVector_clm (I := I) hxz']

/-- **The chart Gram matrix changes by the chart transition.** -/
theorem chartGram_chartTransition
    (hx : x ∈ (chartAt H z).source ∩ (chartAt H z').source) (a b : E) :
    chartGram (I := I) z' x (chartTransition (I := I) z z' x a) (chartTransition (I := I) z z' x b)
      = chartGram (I := I) z x a b := by
  rw [chartGram_apply, chartGram_apply, chartTransition_frameVector hx a,
    chartTransition_frameVector hx b]

/-- **The chart transition commutes with the chart velocity**: the coordinates of the velocity of a
curve in two charts containing the curve are related by the chart transition. -/
theorem chartTransition_velocity {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hx : γ t ∈ (chartAt H z).source ∩ (chartAt H z').source) :
    chartTransition (I := I) z z' (γ t) (deriv (fun s : ℝ => (extChartAt I z) (γ s)) t)
      = deriv (fun s : ℝ => (extChartAt I z') (γ s)) t := by
  have hb : γ t ∈ (trivializationAt E (TangentSpace I) z).baseSet ∩
      (trivializationAt E (TangentSpace I) z').baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  rw [Submission.GlobalBM.deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity (I := I) z hγ hx.1,
    Submission.GlobalBM.deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity (I := I) z' hγ hx.2]
  exact coordChangeL_continuousLinearMapAt _ _ hb _

/-! ## §5 The composite holonomy fixes the velocity -/

variable {P : Partition 0 1} {z : ℕ → M} {γ : ℝ → M}

/-- **The composite holonomy fixes the velocity coordinate**: the chart-`z 0` coordinate of the
velocity is preserved by `holAux`.  The induction over the pieces: the piece transport fixes the
velocity by `fundSol_velocity`, and the chart transitions commute with the chart velocity by
`chartTransition_velocity`. -/
theorem holAux_velocity_aux
    (hP : IsChartLoop (H := H) P γ z)
    (hgeo : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      HasDerivAt (deriv (coordC (I := I) (z := z) (γ := γ) k))
        (chartGeodesicVectorField cov (z k)
          (coordC (I := I) (z := z) (γ := γ) k t,
            deriv (coordC (I := I) (z := z) (γ := γ) k) t)) t)
    (hsrc : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)), γ t ∈ (chartAt H (z k)).source)
    (hγmd : ∀ t ∈ Icc (P.t 0) (P.t P.N), MDifferentiableAt 𝓘(ℝ) I γ t)
    (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target) :
    ∀ k, k ≤ P.N → holAux (cov := cov) htor hu hw htgt k
        ((trivializationAt E (TangentSpace I) (z 0)).continuousLinearMapAt ℝ (γ (P.t 0))
          (curveVelocity (I := I) γ (P.t 0)))
      = (trivializationAt E (TangentSpace I) (z k)).continuousLinearMapAt ℝ (γ (P.t k))
          (curveVelocity (I := I) γ (P.t k)) := by
  intro k
  refine Nat.le_induction ?_ ?_ k (Nat.zero_le k)
  · intro _
    have h0 : holAux (cov := cov) htor hu hw htgt 0 = 1 := rfl
    rw [h0, one_apply_eq_self]
  · intro m _ ih hm
    have hlt : m < P.N := by omega
    have hmem : P.t (m+1) ∈ Icc (P.t 0) (P.t P.N) :=
      ⟨P.mono_le (Nat.zero_le _) (by omega), P.mono_le (by omega) le_rfl⟩
    have hm0 : P.t m ∈ Icc (P.t 0) (P.t P.N) :=
      ⟨P.mono_le (Nat.zero_le _) (by omega), P.mono_le (by omega) le_rfl⟩
    have hbr : ∀ (y : M) (t : ℝ) (hy : γ t ∈ (chartAt H y).source)
        (ht : t ∈ Icc (P.t 0) (P.t P.N)),
        (trivializationAt E (TangentSpace I) y).continuousLinearMapAt ℝ (γ t)
            (curveVelocity (I := I) γ t)
          = deriv (fun s : ℝ => (extChartAt I y) (γ s)) t :=
      fun y t hy ht => (Submission.GlobalBM.deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity
        (I := I) y (hγmd t ht) hy).symm
    rw [show holAux (cov := cov) htor hu hw htgt (m+1)
        = (chartTransition (I := I) (z m) (z (m+1)) (γ (P.t (m+1)))
            * pieceTrans (cov := cov) htor hu hw htgt m hlt) * holAux (cov := cov) htor hu hw htgt m
        from by rw [holAux]; exact dif_pos hlt,
      mul_apply_eq_comp, mul_apply_eq_comp, ih (by omega),
      hbr (z m) (P.t m) (hsrc m hlt (P.t m) ⟨le_rfl, (P.mono m hlt).le⟩) hm0,
      show deriv (fun s : ℝ => (extChartAt I (z m)) (γ s)) (P.t m)
        = deriv (coordC (I := I) (z := z) (γ := γ) m) (P.t m) from rfl,
      Submission.HolDet.fundSol_velocity (cov := cov) hgeo hsrc htor hu hw htgt m hlt,
      show deriv (coordC (I := I) (z := z) (γ := γ) m) (P.t (m+1))
        = deriv (fun s : ℝ => (extChartAt I (z m)) (γ s)) (P.t (m+1)) from rfl,
      chartTransition_velocity (I := I) (hγmd (P.t (m+1)) hmem) (isChartLoop_junction hP hlt),
      ← hbr (z (m+1)) (P.t (m+1)) (hP.2.1 m hlt) hmem]

/-- The fundamental solution is differentiable with derivative its `deriv` on the closed interval. -/
theorem fundSol_hasDerivAt_deriv {x₀ : M} {u w : ℝ → E} {a b : ℝ} (htor : cov.torsion = 0)
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) (v : E) :
    ∀ t ∈ Icc a b, HasDerivAt
      (fun s : ℝ => FundSol.fundSol (cov := cov) (x₀ := x₀) (u := u) (w := w) htor hab hu hw htgt s v)
      (deriv (fun s : ℝ => FundSol.fundSol (cov := cov) (x₀ := x₀) (u := u) (w := w) htor hab hu hw htgt s v) t) t := by
  intro t ht
  exact (FundSol.fundSol_vector_hasDerivAt (cov := cov) (x₀ := x₀) (u := u) (w := w) htor hab hu hw htgt v t ht).congr_deriv
    (FundSol.fundSol_vector_hasDerivAt (cov := cov) (x₀ := x₀) (u := u) (w := w) htor hab hu hw htgt v t ht).deriv.symm

/-- The fundamental solution solves the parallel equation (chart covariant derivative zero). -/
theorem fundSol_chartCovDeriv_eq_zero {x₀ : M} {u w : ℝ → E} {a b : ℝ} (htor : cov.torsion = 0)
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I x₀).target) (v : E) :
    ∀ t ∈ Icc a b, chartCovDeriv cov x₀ u w
      (fun s : ℝ => FundSol.fundSol (cov := cov) (x₀ := x₀) (u := u) (w := w) htor hab hu hw htgt s v) t = 0 :=
  fun t ht => Submission.ParallelField.chartCovDeriv_eq_zero_iff (cov := cov) (htgt t ht)
    (FundSol.fundSol_vector_hasDerivAt (cov := cov) (x₀ := x₀) (u := u) (w := w) htor hab hu hw htgt v t ht)

/-- **The chart-level transport along one piece preserves the chart Gram matrix.** -/
theorem chartGram_fundSol (k : ℕ) (hmet : IsMetricCompatible cov)
    (hdiff : ∀ t ∈ Ioo (P.t k) (P.t (k+1)), HasDerivAt (coordC (I := I) (z := z) (γ := γ) k)
      (deriv (coordC (I := I) (z := z) (γ := γ) k) t) t)
    (hγcont : ContinuousOn γ (Icc (P.t k) (P.t (k+1))))
    (hsrc : ∀ t ∈ Icc (P.t k) (P.t (k+1)), γ t ∈ (chartAt H (z k)).source)
    (htor : cov.torsion = 0)
    (hu : ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k)) (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target)
    (hab : P.t k < P.t (k+1)) (v w : E) :
    ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      chartGram (I := I) (z k) (γ t)
          (FundSol.fundSol (cov := cov) (x₀ := z k)
            (u := coordC (I := I) (z := z) (γ := γ) k)
            (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt t v)
          (FundSol.fundSol (cov := cov) (x₀ := z k)
            (u := coordC (I := I) (z := z) (γ := γ) k)
            (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt t w)
        = chartGram (I := I) (z k) (γ (P.t k)) v w := by
  have hmemIoo : ∀ t ∈ Ioo (P.t k) (P.t (k+1)), t ∈ Icc (P.t k) (P.t (k+1)) :=
    fun t ht => ⟨ht.1.le, ht.2.le⟩
  set s : ℝ := (P.t k + P.t (k+1)) / 2 with hs
  have hsIoo : s ∈ Ioo (P.t k) (P.t (k+1)) := by
    rw [hs]; exact ⟨by linarith, by linarith⟩
  have hconst : ∀ t ∈ Ioo (P.t k) (P.t (k+1)),
      chartGram (I := I) (z k) (γ t)
          (FundSol.fundSol (cov := cov) (x₀ := z k)
            (u := coordC (I := I) (z := z) (γ := γ) k)
            (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt t v)
          (FundSol.fundSol (cov := cov) (x₀ := z k)
            (u := coordC (I := I) (z := z) (γ := γ) k)
            (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt t w)
        = chartGram (I := I) (z k) (γ s)
          (FundSol.fundSol (cov := cov) (x₀ := z k)
            (u := coordC (I := I) (z := z) (γ := γ) k)
            (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt s v)
          (FundSol.fundSol (cov := cov) (x₀ := z k)
            (u := coordC (I := I) (z := z) (γ := γ) k)
            (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt s w) := by
    intro t ht
    have key := Submission.ParallelField.chartGram_parallelField_eq (cov := cov) hmet
      (x₀ := z k) (u := coordC (I := I) (z := z) (γ := γ) k)
      (w := deriv (coordC (I := I) (z := z) (γ := γ) k))
      (X := fun r : ℝ => FundSol.fundSol (cov := cov) (x₀ := z k)
        (u := coordC (I := I) (z := z) (γ := γ) k)
        (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt r v)
      (Y := fun r : ℝ => FundSol.fundSol (cov := cov) (x₀ := z k)
        (u := coordC (I := I) (z := z) (γ := γ) k)
        (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt r w)
      hdiff (fun r hr => htgt r (hmemIoo r hr))
      (fun r hr => fundSol_hasDerivAt_deriv (cov := cov) (x₀ := z k) htor hab hu hw htgt v r (hmemIoo r hr))
      (fun r hr => fundSol_hasDerivAt_deriv (cov := cov) (x₀ := z k) htor hab hu hw htgt w r (hmemIoo r hr))
      (fun r hr => fundSol_chartCovDeriv_eq_zero (cov := cov) (x₀ := z k) htor hab hu hw htgt v r (hmemIoo r hr))
      (fun r hr => fundSol_chartCovDeriv_eq_zero (cov := cov) (x₀ := z k) htor hab hu hw htgt w r (hmemIoo r hr))
      t ht s hsIoo
    rwa [show (extChartAt I (z k)).symm (coordC (I := I) (z := z) (γ := γ) k t) = γ t from
          PartialEquiv.left_inv _ (by rw [extChartAt_source]; exact hsrc t (hmemIoo t ht)),
        show (extChartAt I (z k)).symm (coordC (I := I) (z := z) (γ := γ) k s) = γ s from
          PartialEquiv.left_inv _ (by rw [extChartAt_source]; exact hsrc s (hmemIoo s hsIoo))] at key

  have hcont : ContinuousOn (fun t : ℝ => chartGram (I := I) (z k) (γ t)
      (FundSol.fundSol (cov := cov) (x₀ := z k)
        (u := coordC (I := I) (z := z) (γ := γ) k)
        (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt t v)
      (FundSol.fundSol (cov := cov) (x₀ := z k)
        (u := coordC (I := I) (z := z) (γ := γ) k)
        (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt t w))
      (Icc (P.t k) (P.t (k+1))) :=
    continuousOn_chartGram_curve (I := I) (x₀ := z k) hγcont
      (HasDerivAt.continuousOn (fundSol_hasDerivAt_deriv (cov := cov) (x₀ := z k) htor hab hu hw htgt v))
      (HasDerivAt.continuousOn (fundSol_hasDerivAt_deriv (cov := cov) (x₀ := z k) htor hab hu hw htgt w))
      hsrc
  have hext := Set.EqOn.of_subset_closure (f := fun t : ℝ => chartGram (I := I) (z k) (γ t)
      (FundSol.fundSol (cov := cov) (x₀ := z k)
        (u := coordC (I := I) (z := z) (γ := γ) k)
        (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt t v)
      (FundSol.fundSol (cov := cov) (x₀ := z k)
        (u := coordC (I := I) (z := z) (γ := γ) k)
        (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt t w))
    (g := fun _ : ℝ => chartGram (I := I) (z k) (γ s)
      (FundSol.fundSol (cov := cov) (x₀ := z k)
        (u := coordC (I := I) (z := z) (γ := γ) k)
        (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt s v)
      (FundSol.fundSol (cov := cov) (x₀ := z k)
        (u := coordC (I := I) (z := z) (γ := γ) k)
        (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt s w))
    (s := Ioo (P.t k) (P.t (k+1))) (t := Icc (P.t k) (P.t (k+1)))
    hconst hcont continuousOn_const (fun t ht => ⟨ht.1.le, ht.2.le⟩)
    (by rw [closure_Ioo (ne_of_lt hab)])
  have hbase : chartGram (I := I) (z k) (γ (P.t k))
      (FundSol.fundSol (cov := cov) (x₀ := z k)
        (u := coordC (I := I) (z := z) (γ := γ) k)
        (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt (P.t k) v)
      (FundSol.fundSol (cov := cov) (x₀ := z k)
        (u := coordC (I := I) (z := z) (γ := γ) k)
        (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt (P.t k) w)
      = chartGram (I := I) (z k) (γ (P.t k)) v w := by
    rw [FundSol.fundSol_datum (cov := cov) (x₀ := z k) (u := coordC (I := I) (z := z) (γ := γ) k)
        (w := deriv (coordC (I := I) (z := z) (γ := γ) k)) htor hab hu hw htgt]
    simp
  intro t ht
  exact (hext ht).trans ((hext ⟨le_rfl, hab.le⟩).symm.trans hbase)

/-- **The composite holonomy is an isometry** with respect to the chart Gram matrix at the base
point.  The induction over the pieces: the piece transport preserves the chart Gram by
`chartGram_fundSol`, and the chart transitions change it by `chartGram_chartTransition`. -/
theorem chartGram_holAux_aux (hP : IsChartLoop (H := H) P γ z) (hmet : IsMetricCompatible cov)
    (hdiff : ∀ k < P.N, ∀ t ∈ Ioo (P.t k) (P.t (k+1)), HasDerivAt (coordC (I := I) (z := z) (γ := γ) k)
      (deriv (coordC (I := I) (z := z) (γ := γ) k) t) t)
    (hγcont : ContinuousOn γ (Icc (P.t 0) (P.t P.N)))
    (hsrc : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)), γ t ∈ (chartAt H (z k)).source)
    (htor : cov.torsion = 0)
    (hu : ∀ k < P.N, ContinuousOn (coordC (I := I) (z := z) (γ := γ) k) (Icc (P.t k) (P.t (k+1))))
    (hw : ∀ k < P.N, ContinuousOn (deriv (coordC (I := I) (z := z) (γ := γ) k))
      (Icc (P.t k) (P.t (k+1))))
    (htgt : ∀ k < P.N, ∀ t ∈ Icc (P.t k) (P.t (k+1)),
      coordC (I := I) (z := z) (γ := γ) k t ∈ (extChartAt I (z k)).target) :
    ∀ k, k ≤ P.N → ∀ v w : E,
      chartGram (I := I) (z k) (γ (P.t k)) (holAux (cov := cov) htor hu hw htgt k v)
          (holAux (cov := cov) htor hu hw htgt k w)
        = chartGram (I := I) (z 0) (γ (P.t 0)) v w := by
  intro k
  refine Nat.le_induction ?_ ?_ k (Nat.zero_le k)
  · intro _ v w
    have h0 : holAux (cov := cov) htor hu hw htgt 0 = 1 := rfl
    rw [h0]
    simp
  · intro m _ ih hm v w
    have hlt : m < P.N := by omega
    have hsub : ∀ t ∈ Icc (P.t k) (P.t (k+1)), True := fun _ _ => trivial
    -- piece isometry
    have hpiece := chartGram_fundSol (cov := cov) (P := P) (z := z) (γ := γ) m hmet
      (hdiff m hlt) (hγcont.mono (fun t ht => ⟨le_trans (P.mono_le (Nat.zero_le m) hlt.le) ht.1,
        le_trans ht.2 (P.mono_le (by omega) le_rfl)⟩)) (hsrc m hlt) htor (hu m hlt) (hw m hlt) (htgt m hlt)
      (P.mono m hlt)
      (holAux (cov := cov) htor hu hw htgt m v) (holAux (cov := cov) htor hu hw htgt m w)
      (P.t (m+1)) ⟨(P.mono m hlt).le, le_rfl⟩
    -- unfold the composite
    have hunf : holAux (cov := cov) htor hu hw htgt (m+1) v
        = chartTransition (I := I) (z m) (z (m+1)) (γ (P.t (m+1)))
            ((pieceTrans (cov := cov) htor hu hw htgt m hlt)
              (holAux (cov := cov) htor hu hw htgt m v)) := by
      rw [show holAux (cov := cov) htor hu hw htgt (m+1)
          = (chartTransition (I := I) (z m) (z (m+1)) (γ (P.t (m+1)))
              * pieceTrans (cov := cov) htor hu hw htgt m hlt) * holAux (cov := cov) htor hu hw htgt m
          from by rw [holAux]; exact dif_pos hlt,
        mul_apply_eq_comp, mul_apply_eq_comp]
    have hunf' : holAux (cov := cov) htor hu hw htgt (m+1) w
        = chartTransition (I := I) (z m) (z (m+1)) (γ (P.t (m+1)))
            ((pieceTrans (cov := cov) htor hu hw htgt m hlt)
              (holAux (cov := cov) htor hu hw htgt m w)) := by
      rw [show holAux (cov := cov) htor hu hw htgt (m+1)
          = (chartTransition (I := I) (z m) (z (m+1)) (γ (P.t (m+1)))
              * pieceTrans (cov := cov) htor hu hw htgt m hlt) * holAux (cov := cov) htor hu hw htgt m
          from by rw [holAux]; exact dif_pos hlt,
        mul_apply_eq_comp, mul_apply_eq_comp]
    rw [hunf, hunf', chartGram_chartTransition (isChartLoop_junction hP hlt)]
    rw [show pieceTrans (cov := cov) htor hu hw htgt m hlt
        = FundSol.fundSol (cov := cov) (x₀ := z m)
            (u := coordC (I := I) (z := z) (γ := γ) m)
            (w := deriv (coordC (I := I) (z := z) (γ := γ) m)) htor (P.mono m hlt)
            (hu m hlt) (hw m hlt) (htgt m hlt) (P.t (m+1)) from rfl]
    exact hpiece.trans (ih (by omega) v w)


end
end Submission.HolDet
