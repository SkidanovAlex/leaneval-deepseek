import Mathlib
import Submission.Work.RiemLib.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_cov_apply
import Submission.Work.RiemLib.Commons.Geometry.Manifold.Tangent.contMDiffOn_trivializationAt_symmL_apply
import Submission.Work.RiemLib.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq_pointwise

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold.VectorBundle.CovariantDerivative

open scoped _root_.Manifold _root_.ContDiff Topology
open _root_.VectorField Set _root_.CovariantDerivative Bundle Filter

/-! ## Helper lemmas -/

section helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The section `q ↦ T.symmL ℝ q v` of the tangent bundle, in curried form. -/
theorem contMDiffOn_trivializationAt_symmL_section (x₀ : M) (v : E) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v⟩ :
        TangentBundle I M)) ((chartAt H x₀).source) := by
  have h := Commons.Geometry.Manifold.Tangent.contMDiffOn_trivializationAt_symmL_apply
    (I := I) (M := M) x₀
  have hpair : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun q : M => (q, v)) ((chartAt H x₀).source) :=
    contMDiffOn_id.prodMk contMDiffOn_const
  have h2 := h.comp hpair (fun q hq => ⟨hq, mem_univ v⟩)
  simpa only [Function.comp_def] using h2

/-- **Smoothness of a section read in the tangent-bundle trivialisation.**  If a section `W` of
the tangent bundle is `C^∞` on a set `u`, then its coordinate expression
`q ↦ T.clmAt q (W q)` in the tangent-bundle trivialisation `T` at `x₀` is `C^∞` on
`u ∩ (chartAt H x₀).source`. -/
theorem contMDiffOn_continuousLinearMapAt_section (x₀ : M) {W : Π q : M, TangentSpace I q}
    {u : Set M} (hW : CMDiff[u] ∞ (T% W)) :
    ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun q => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ q (W q))
      (u ∩ (chartAt H x₀).source) := by
  intro q hq
  obtain ⟨hqu, hqs⟩ := hq
  have hbase : q ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have h1 : ContMDiffWithinAt I 𝓘(ℝ, E) ∞
      (fun q => ((trivializationAt E (TangentSpace I) x₀) ⟨q, W q⟩).2) u q :=
    ((Trivialization.contMDiffWithinAt_section (s := W) u hbase).1 (hW q hqu))
  refine (h1.mono (inter_subset_left : u ∩ (chartAt H x₀).source ⊆ u)).congr ?_ ?_
  · intro y hy
    exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) x₀)
      (by rw [TangentBundle.trivializationAt_baseSet]; exact hy.2) (W y)
  · exact Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) x₀) hbase (W q)

/-- **Reading a smooth section in the chart.**  If `W` is a `C^∞` section of the tangent bundle on
the chart at `x₀`, then the coordinate expression of `W` in the tangent-bundle trivialisation at
`x₀`, pulled back by the inverse chart, is `C^∞` on `(extChartAt I x₀).target ×ˢ univ`. -/
theorem contDiffOn_continuousLinearMapAt_section_comp_extChartAt_symm (x₀ : M)
    {W : Π q : M, TangentSpace I q} (hW : CMDiff[(chartAt H x₀).source] ∞ (T% W)) :
    ContDiffOn ℝ ∞
      (fun z : E × E => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
        ((extChartAt I x₀).symm z.1) (W ((extChartAt I x₀).symm z.1)))
      ((extChartAt I x₀).target ×ˢ (univ : Set E)) := by
  set s : Set (E × E) := (extChartAt I x₀).target ×ˢ (univ : Set E) with hs
  -- smoothness of the inverse chart, composed with the first projection
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm (extChartAt I x₀).target :=
    contMDiffOn_extChartAt_symm x₀
  have hfst : ContMDiffOn 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞ (Prod.fst : E × E → E) s :=
    contDiffOn_fst.contMDiffOn
  have hp : ContMDiffOn 𝓘(ℝ, E × E) I ∞
      (fun z : E × E => (extChartAt I x₀).symm z.1) s :=
    hsymm.comp hfst (fun z hz => hz.1)
  -- the section read in the trivialisation
  have hsec : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun q => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ q (W q))
      ((chartAt H x₀).source) := by
    have h := contMDiffOn_continuousLinearMapAt_section x₀ (u := (chartAt H x₀).source) hW
    simpa only [inter_self] using h
  have hcomp := hsec.comp hp (fun z hz => by
    have h1 : (extChartAt I x₀).symm z.1 ∈ (extChartAt I x₀).source :=
      PartialEquiv.map_target (extChartAt I x₀) hz.1
    rwa [extChartAt_source] at h1)
  exact hcomp.contDiffOn

/-- **The Christoffel computation.**  For `z = (y, v)` with `y` in the target of the chart at `x₀`,
the second-order term of the geodesic spray, `∇_w σ_v` evaluated at `y` (where `σ_v(q) = T.symmL q v`
and `w = T.symmL y v`), expands in a basis `b` of `E` as
`∑ i j, v^i v^j • ∇_{σ_{b_i}} σ_{b_j}`, with `σ_{b_i}(q) = T.symmL q (b i)`. -/
theorem cov_symmL_chart_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (x₀ : M) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) {z : E × E}
    (hz : z.1 ∈ (extChartAt I x₀).target) :
    cov (fun q => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q z.2)
        ((extChartAt I x₀).symm z.1)
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm z.1) z.2)
      = ∑ i, ∑ j, ((b.coord i) z.2 * (b.coord j) z.2) •
          cov (fun q => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (b i))
            ((extChartAt I x₀).symm z.1)
            ((trivializationAt E (TangentSpace I) x₀).symmL ℝ
              ((extChartAt I x₀).symm z.1) (b j)) := by
  classical
  set x : M := (extChartAt I x₀).symm z.1 with hx
  have hxsrc : x ∈ (chartAt H x₀).source := by
    rw [hx]
    have h1 : (extChartAt I x₀).symm z.1 ∈ (extChartAt I x₀).source :=
      PartialEquiv.map_target (extChartAt I x₀) hz
    rwa [extChartAt_source] at h1
  have hsrc_nhds : (chartAt H x₀).source ∈ 𝓝 x :=
    (chartAt H x₀).open_source.mem_nhds hxsrc
  -- the relevant sections are smooth at `x`
  have hsec : ∀ i, CMDiffAt ∞
      (T% (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (b i))) x := fun i =>
    ((contMDiffOn_trivializationAt_symmL_section (I := I) (M := M) x₀ (b i)) x hxsrc).contMDiffAt
      hsrc_nhds
  have hZ : CMDiffAt ∞
      (T% (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q z.2)) x :=
    ((contMDiffOn_trivializationAt_symmL_section (I := I) (M := M) x₀ z.2) x hxsrc).contMDiffAt
      hsrc_nhds
  -- the pointwise expansion of the section `σ_v` in the frame `σ_{b_i}`
  have hexp : ∀ (y : M) (v : E),
      (trivializationAt E (TangentSpace I) x₀).symmL ℝ y v
        = ∑ i, (b.coord i) v • (trivializationAt E (TangentSpace I) x₀).symmL ℝ y (b i) := by
    intro y v
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, Module.Basis.coord_apply]
  have heq : (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q z.2)
      =ᶠ[𝓝 x] fun y => ∑ i ∈ Finset.univ,
        (fun _ : M => (b.coord i) z.2) y •
          (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (b i)) y := by
    filter_upwards with y
    exact hexp y z.2
  have hkey := cov_eq_sum_of_eventuallyEq_pointwise (cov := cov) Finset.univ
    (fun i (_ : M) => (b.coord i) z.2)
    (fun i q => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (b i))
    (Z := fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q z.2)
    (x := x) (v := (trivializationAt E (TangentSpace I) x₀).symmL ℝ x z.2) hZ hsec
    (fun i => contMDiffAt_const) heq
  rw [hkey]
  have hzero : ∀ i, mvfderiv I (fun _ : M => (b.coord i) z.2) x
      ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x z.2)
      • (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b i) = 0 := by
    intro i
    rw [mvfderiv_const, zero_apply, zero_smul]
  rw [Finset.sum_eq_zero (fun i _ => hzero i), add_zero]
  rw [hexp x z.2]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_sum, map_smul]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]

end helpers

/-- **The geodesic spray is smooth in a chart.**  For a `C^∞` covariant derivative `cov` on the
tangent bundle of a `C^∞` manifold, the chart-level second-order ODE of geodesics
`z = (y, v) ↦ -Γ(y)(v, v)` is `C^∞` on the set of pairs `(y, v)` with `y` in the target of the
chart at `x₀`.

Here `Γ(y)(v, v)` is the coordinate expression of `∇_w σ_v` where `σ_v (q) = T.symmL ℝ q v` is the
section of the tangent bundle with constant coordinates `v` in the tangent-bundle trivialisation
`T` at `x₀`, and `w = T.symmL ℝ y v` is the tangent vector at `y` whose coordinates are `v`.
(Note the *second* Christoffel slot is the tangent vector `T.symmL ℝ y v`, not the element `v` of
`E` viewed as a tangent vector via the defeq `TangentSpace I y = E`.) -/
theorem contDiffOn_chartSpray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ContDiffOn ℝ ∞ (fun z : E × E =>
      - (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
          ((extChartAt I x₀).symm z.1)
          (cov (fun q => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q z.2)
            ((extChartAt I x₀).symm z.1)
            ((trivializationAt E (TangentSpace I) x₀).symmL ℝ
              ((extChartAt I x₀).symm z.1) z.2)))
      ((extChartAt I x₀).target ×ˢ (univ : Set E)) := by
  classical
  -- a basis of `E` to expand the section and the vector
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  -- the frame sections `σ_{b i}`
  have hσ : ∀ i, CMDiff[(chartAt H x₀).source] ∞
      (T% (fun q : M => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (b i))) := fun i =>
    contMDiffOn_trivializationAt_symmL_section (I := I) (M := M) x₀ (b i)
  -- the coefficient functions `z ↦ b.coord i z.2`
  have hc : ∀ i : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (fun z : E × E => (b.coord i) z.2)
        ((extChartAt I x₀).target ×ˢ (univ : Set E)) := fun i =>
    ContDiffOn.continuousLinearMap_comp (LinearMap.toContinuousLinearMap (b.coord i))
      contDiffOn_snd
  -- the Christoffel symbols, read in the trivialisation
  have hA : ∀ i j : Fin (Module.finrank ℝ E), ContDiffOn ℝ ∞
      (fun z : E × E =>
        (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
          ((extChartAt I x₀).symm z.1)
          (cov (fun q => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (b i))
            ((extChartAt I x₀).symm z.1)
            ((trivializationAt E (TangentSpace I) x₀).symmL ℝ
              ((extChartAt I x₀).symm z.1) (b j))))
      ((extChartAt I x₀).target ×ˢ (univ : Set E)) := fun i j =>
    contDiffOn_continuousLinearMapAt_section_comp_extChartAt_symm (I := I) (M := M) x₀
      (W := fun q : M => cov (fun q => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (b i))
        q ((trivializationAt E (TangentSpace I) x₀).symmL ℝ q (b j)))
      (contMDiffOn_cov_apply cov (inferInstance)
        (chartAt H x₀).open_source (hσ i) (hσ j))
  -- the whole spray expression as a finite sum of smooth functions
  have hsum : ContDiffOn ℝ ∞ (fun z : E × E => - ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        ((b.coord i) z.2 * (b.coord j) z.2) •
          (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
            ((extChartAt I x₀).symm z.1)
            (cov (fun q => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q (b i))
              ((extChartAt I x₀).symm z.1)
              ((trivializationAt E (TangentSpace I) x₀).symmL ℝ
                ((extChartAt I x₀).symm z.1) (b j))))
      ((extChartAt I x₀).target ×ˢ (univ : Set E)) := by
    refine ContDiffOn.neg ?_
    refine ContDiffOn.sum (fun i _ => ?_)
    refine ContDiffOn.sum (fun j _ => ?_)
    exact ContDiffOn.smul (ContDiffOn.mul (hc i) (hc j)) (hA i j)
  -- pointwise, the spray expression equals that finite sum
  refine ContDiffOn.congr hsum (fun z hz => ?_)
  rw [cov_symmL_chart_expansion (cov := cov) x₀ b (z := z) hz.1]
  simp only [map_sum, map_smul]

end Commons.Geometry.Manifold.VectorBundle.CovariantDerivative