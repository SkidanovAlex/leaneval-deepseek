import Mathlib
import Submission.Work.Diff.Evol.Vocab

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

/-!
# A skew-symmetric `1`-jet on a manifold is realised by a smooth map

`Work.Diff.Evol.smooth_skew_jet1`: given a point `x` of a boundaryless `C^∞` manifold `M` and a
linear map `L : T_xM → (Fin n → Fin n → ℝ)` whose values are skew-symmetric matrices, there is a
**globally** `C^∞` map `B : M → (Fin n → Fin n → ℝ)` with `B x = 0`, skew-symmetric values
everywhere and `mvfderiv I B x = L`.

The construction is the standard one: with the chart `χ = extChartAt I x` and `G y = χ y - χ x`,
the manifold derivative of `G` at `x` is the identity (Mathlib's `mfderiv_extChartAt_self`:
`T_xM` is *defined* as `E` through the chart at `x`), so the linear map `L` itself, viewed as a
continuous linear map `E →L (Fin n → Fin n → ℝ)` via `LinearMap.toContinuousLinearMap`, realises
the jet along `G`; multiplying by a `SmoothBumpFunction` which is `1` at `x` and is supported in the
chart source globalises the construction while keeping `B x = 0` and the derivative at `x`.

Nothing here is a `sorry`.
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The derivative of the chart displacement.**  For a continuous linear map `Φ : E →L[ℝ] W` the
manifold derivative at `x` of `y ↦ Φ (χ y - χ x)` (with `χ = extChartAt I x`) is `Φ` itself: the
manifold derivative of the chart at its own centre is the identity.  This is the vector-valued
form of `Work.Diff.C.mvfderiv_affine_chart`. -/
theorem mvfderiv_clm_comp_chart (x : M) {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Φ : E →L[ℝ] W) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => Φ ((extChartAt I x) y - (extChartAt I x) x)) x v = Φ v := by
  have hχ : MDifferentiableAt I 𝓘(ℝ,E) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  set c : E := (extChartAt I x) x with hc
  have hsplit : (fun y : M => Φ ((extChartAt I x) y - c))
      = (fun w : E => Φ (w - c)) ∘ (extChartAt I x) := rfl
  have hdphi : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ W)
      (fun w : E => Φ (w - c)) c := by
    have h1 : (fun w : E => Φ (w - c)) = ((fun w : E => Φ w) - fun _ : E => Φ c) := by
      ext w; rw [Pi.sub_apply, map_sub]
    rw [h1]
    exact ((ContinuousLinearMap.contMDiff (n := ∞) Φ).sub contMDiff_const).mdifferentiableAt
      (by simp)
  have hclm : mvfderiv (modelWithCornersSelf ℝ E) (fun w : E => Φ (w - c)) c = Φ := by
    have h1 : (fun w : E => Φ (w - c)) = ((fun w : E => Φ w) - fun _ : E => Φ c) := by
      ext w; rw [Pi.sub_apply, map_sub]
    rw [h1]
    have hd1 : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ W)
        (fun w : E => Φ w) c :=
      (ContinuousLinearMap.contMDiff (n := ∞) Φ).mdifferentiableAt (by simp)
    have hd2 : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ W)
        (fun _ : E => Φ c) c := mdifferentiableAt_const (c := Φ c)
    rw [mvfderiv_sub hd1 hd2, mvfderiv_const, sub_zero, mvfderiv_eq_fderiv]
    exact (ContinuousLinearMap.hasFDerivAt Φ).fderiv
  rw [hsplit, mvfderiv_comp x hdphi hχ, hclm]
  rw [mfderiv_extChartAt_self]
  rfl

end Helpers

theorem smooth_skew_jet1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    {n : ℕ} (x : M) (L : TangentSpace I x → (Fin n → Fin n → ℝ))
    (hLlin : ∀ (r s : ℝ) (v w : TangentSpace I x),
      L (r • v + s • w) = r • L v + s • L w)
    (hLsk : ∀ (v : TangentSpace I x) (p i : Fin n), L v i p = -(L v p i)) :
    ∃ B : M → (Fin n → Fin n → ℝ),
      Work.Diff.Evol.SmoothMap I M B ∧ B x = 0 ∧
      (∀ (y : M) (p i : Fin n), B y i p = -(B y p i)) ∧
      (∀ v : TangentSpace I x, mvfderiv I B x v = L v) := by
  classical
  -- `L` is additive and homogeneous, hence a continuous linear map.
  have hL0 : L 0 = 0 := by
    have h := hLlin 0 0 (0 : TangentSpace I x) (0 : TangentSpace I x)
    simpa using h
  have hLadd : ∀ v w : TangentSpace I x, L (v + w) = L v + L w := by
    intro v w
    have h := hLlin 1 1 v w
    simpa using h
  have hLsmul : ∀ (r : ℝ) (v : TangentSpace I x), L (r • v) = r • L v := by
    intro r v
    have h := hLlin r 0 v (0 : TangentSpace I x)
    simpa [hL0] using h
  let Lin : TangentSpace I x →ₗ[ℝ] (Fin n → Fin n → ℝ) :=
    { toFun := L, map_add' := hLadd, map_smul' := hLsmul }
  let Φ : E →L[ℝ] (Fin n → Fin n → ℝ) := LinearMap.toContinuousLinearMap Lin
  have hΦ : ∀ v : TangentSpace I x, Φ v = L v := by
    intro v
    exact congrFun (LinearMap.coe_toContinuousLinearMap' Lin) v
  -- a bump function, `1` at `x` and supported in the chart source
  obtain ⟨ψ, -, hψsupp⟩ : ∃ ψ : SmoothBumpFunction I x,
      True ∧ tsupport (ψ : M → ℝ) ⊆ (chartAt H x).source :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  -- the chart displacement
  set G : M → E := fun y => (extChartAt I x) y - (extChartAt I x) x with hG
  have hGOn : ContMDiffOn I 𝓘(ℝ,E) ∞ G (chartAt H x).source :=
    (contMDiffOn_extChartAt (I := I) (x := x)).sub_const _
  have hΦOn : ContMDiffOn I (modelWithCornersSelf ℝ (Fin n → Fin n → ℝ)) ∞ (fun y : M => Φ (G y))
      (chartAt H x).source :=
    (ContinuousLinearMap.contMDiff (n := ∞) Φ).comp_contMDiffOn (f := G) hGOn
  refine ⟨fun y : M => (ψ : M → ℝ) y • (Φ (G y)), ?_, ?_, ?_, ?_⟩
  · -- global smoothness
    exact ψ.contMDiff_smul hΦOn
  · -- value at `x`
    show (ψ : M → ℝ) x • Φ (G x) = 0
    simp [hG]
  · -- skew-symmetry everywhere
    intro y p i
    show ((fun y : M => (ψ : M → ℝ) y • (Φ (G y))) y) i p
        = -((fun y : M => (ψ : M → ℝ) y • (Φ (G y))) y) p i
    have hsk : ∀ p i : Fin n, Φ (G y) i p = -(Φ (G y) p i) := by
      intro p i
      rw [hΦ (G y)]
      exact hLsk (G y) p i
    simp only [Pi.smul_apply, smul_eq_mul, hsk i p, mul_neg, neg_neg]
  · -- the derivative at `x`
    intro v
    have hψd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M => (ψ : M → ℝ) y) x :=
      ψ.contMDiff.mdifferentiableAt (by simp)
    have hΦd : MDifferentiableAt I (modelWithCornersSelf ℝ (Fin n → Fin n → ℝ))
        (fun y : M => Φ (G y)) x :=
      ((hΦOn x (mem_chart_source H x)).contMDiffAt
        ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))).mdifferentiableAt (by simp)
    have hmul : mvfderiv I (fun y : M => (ψ : M → ℝ) y • Φ (G y)) x
        = (ψ : M → ℝ) x • mvfderiv I (fun y : M => Φ (G y)) x
          + (mvfderiv I (fun y : M => (ψ : M → ℝ) y) x).smulRight (Φ (G x)) :=
      mvfderiv_smul hψd hΦd
    have hchart : mvfderiv I (fun y : M => Φ (G y)) x v = Φ v := by
      have h := mvfderiv_clm_comp_chart (I := I) x Φ v
      simpa [hG] using h
    have hψx : (ψ : M → ℝ) x = 1 := SmoothBumpFunction.eq_one ψ
    have hGx : G x = 0 := by simp [hG]
    rw [hmul]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply, hchart, hψx, hGx, map_zero,
      smul_zero, add_zero, one_smul]
    exact hΦ v

end Work.Diff.Evol
