import Mathlib
import Submission.Work.Diff.STE.DeTurckField
import Submission.Work.Diff.STE.deTurck.traceVec_eq_sum_invGram
import Submission.Work.Diff.GE.covRmChartExpr_eq
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.EXT.ricAt_invGram_chart
import Submission.Work.Diff.EXT.eq_sum_frameVector_of_pairing
import Submission.ChartConnection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart components of the DeTurck field

`Work.Diff.STE.DeTurck.deTurckVec g gbar` is the DeTurck field `W(g) = tr_g (∇^g - ∇^{gbar})`,
defined frame-freely as the metric trace of the tensor `connDiff g gbar`
(`Submission.Work.Diff.STE.DeTurckField`).  `Work.Diff.STE.DeTurck.deTurckChartComp` is the
coordinate expression for its components in the chart frame of the chart at `x₀`,
`∑_{a,b} γ^{ab}(Γ^k_{ab} - Γ̃^k_{ab})`.  This file proves that the two agree, i.e. that the
frame-free trace really computes the classical DeTurck vector field.

The ingredients are
* `traceVec_eq_sum_invGram` (linear algebra): the metric trace in an arbitrary frame is the
  contraction of the tensor with the inverse Gram matrix;
* `Work.Diff.EXT.eq_sum_frameVector_of_pairing` (linear algebra): a tangent vector is recovered
  from its pairings with the chart frame by the inverse Gram matrix, so
  `∑_j γ^{kj} ⟪W, σ_j⟫` is the `k`-th coefficient of `W` in that frame;
* `Work.Diff.GE.CovRmChartAux.lcOf_field_eq_sum_chrCoord` (chart formula): the connection applied
  to a coordinate-frame field is `∑_n Γ^n_{ma} σ_n`;
* the symmetry `chrCoord n a b = chrCoord n b a` of the Christoffel symbols in their lower
  indices, which is the symmetry of the Koszul expression in `a, b`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic

namespace Work.Diff.STE.deTurck

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

noncomputable section

/-- **Symmetry of the Koszul expression in its two lower indices.**  This is the symmetry of the
metric (not of the connection): `koszulPair` is `½(∂_a G_{bc} + ∂_b G_{ca} - ∂_c G_{ab})` and the
swap `a ↔ b` merely permutes the three terms. -/
theorem koszulPair_symm (G : ℝ → SMet I M) (x₀ : M) (a b c : Fin (Module.finrank ℝ E))
    (t : ℝ) (y : M) :
    Work.Diff.GE.koszulPair (I := I) G x₀ a b c t y
      = Work.Diff.GE.koszulPair (I := I) G x₀ b a c t y := by
  have hbc : (fun y' : M => (G t).inner y' (Work.Diff.GE.cFrame (I := I) x₀ b y')
        (Work.Diff.GE.cFrame (I := I) x₀ c y'))
      = (fun y' : M => (G t).inner y' (Work.Diff.GE.cFrame (I := I) x₀ c y')
        (Work.Diff.GE.cFrame (I := I) x₀ b y')) :=
    funext fun y' => (G t).symm y' _ _
  have hac : (fun y' : M => (G t).inner y' (Work.Diff.GE.cFrame (I := I) x₀ a y')
        (Work.Diff.GE.cFrame (I := I) x₀ c y'))
      = (fun y' : M => (G t).inner y' (Work.Diff.GE.cFrame (I := I) x₀ c y')
        (Work.Diff.GE.cFrame (I := I) x₀ a y')) :=
    funext fun y' => (G t).symm y' _ _
  have hab : (fun y' : M => (G t).inner y' (Work.Diff.GE.cFrame (I := I) x₀ b y')
        (Work.Diff.GE.cFrame (I := I) x₀ a y'))
      = (fun y' : M => (G t).inner y' (Work.Diff.GE.cFrame (I := I) x₀ a y')
        (Work.Diff.GE.cFrame (I := I) x₀ b y')) :=
    funext fun y' => (G t).symm y' _ _
  simp only [Work.Diff.GE.koszulPair]
  rw [hac, hbc, hab]
  ring

/-- **The Christoffel symbols are symmetric in their two frame indices**: `Γ^n_{ab} = Γ^n_{ba}`. -/
theorem chrCoord_symm (G : ℝ → SMet I M) (x₀ : M) (n a b : Fin (Module.finrank ℝ E))
    (t : ℝ) (y : M) :
    Work.Diff.GE.chrCoord (I := I) G x₀ n a b t y
      = Work.Diff.GE.chrCoord (I := I) G x₀ n b a t y := by
  simp only [Work.Diff.GE.chrCoord]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [koszulPair_symm]

/-- **The coordinate of a finite linear combination in a basis.**  If `c : ι → ℝ` is a family of
coefficients, the `k`-th coordinate of `∑ i, c i • e i` in the basis `e` is `c k`. -/
lemma basis_coord_sum_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module ℝ V] (e : Module.Basis ι ℝ V) (c : ι → ℝ) (k : ι) :
    e.coord k (∑ i, c i • e i) = c k := by
  rw [map_sum]
  rw [Finset.sum_eq_single k]
  · rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
    simp
  · intro i _ hi
    rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne (Ne.symm hi)]
    simp
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **The difference of the two Levi-Civita connections in the chart frame.**  With
`σ_i = cFrame x₀ i` the coordinate frame of the chart at `x₀`, the tensor `∇^g - ∇^{gbar}` applied
to `(σ_a, σ_b)` is `∑_n (Γ^n_{ba} - Γ̃^n_{ba}) σ_n`: the connection is applied to the field `σ_a`
in the direction `σ_b`, which is why the indices of `chrCoord` appear as `b a`. -/
theorem connDiff_frame_eq_chart
    (hLC : LCSmooth I M) (g gbar : SMet I M) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.DeTurck.connDiff g gbar p
        (Work.Diff.GE.cFrame (I := I) x₀ a p) (Work.Diff.GE.cFrame (I := I) x₀ b p)
      = ∑ n, (Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => g) x₀ n b a 0 p
              - Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => gbar) x₀ n b a 0 p)
          • Work.Diff.GE.cFrame (I := I) x₀ n p := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨X, hXsm, hXeq⟩ :=
    Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀
      (Work.Diff.GE.cBasis (E := E) a) hp
  have hXp : X p = Work.Diff.GE.cFrame (I := I) x₀ a p := by
    rw [hXeq.self_of_nhds]
    rfl
  have hg : (lcOf g) X p (Work.Diff.GE.cFrame (I := I) x₀ b p)
      = ∑ n, Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => g) x₀ n b a 0 p
          • Work.Diff.GE.cFrame (I := I) x₀ n p :=
    Work.Diff.GE.CovRmChartAux.lcOf_field_eq_sum_chrCoord (I := I) hLC (fun _ : ℝ => g) x₀ hp 0 b a
      hXsm hXeq
  have hgb : (lcOf gbar) X p (Work.Diff.GE.cFrame (I := I) x₀ b p)
      = ∑ n, Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => gbar) x₀ n b a 0 p
          • Work.Diff.GE.cFrame (I := I) x₀ n p :=
    Work.Diff.GE.CovRmChartAux.lcOf_field_eq_sum_chrCoord (I := I) hLC (fun _ : ℝ => gbar) x₀ hp
      0 b a hXsm hXeq
  have happ := Work.Diff.STE.DeTurck.connDiff_apply (I := I) (g := g) (gbar := gbar) (x := p)
    (σ := X) (hXsm.mdifferentiableAt (by simp)) (Work.Diff.GE.cFrame (I := I) x₀ b p)
  rw [← hXp, happ, hg, hgb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [sub_smul]

end

end Helpers

theorem deTurckVec_chartComp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g gbar : Submission.Diff.SMet I M) (x₀ : M) (k : Fin (Module.finrank ℝ E))
    {p : M} (hp : p ∈ (chartAt H x₀).source) :
    ∑ j, Work.Diff.GE.GramInv (fun _ : ℝ => g) (I := I) x₀ 0 p k j
        * g.inner p (Work.Diff.STE.DeTurck.deTurckVec g gbar p)
            (Work.Diff.GE.cFrame (I := I) x₀ j p)
      = Work.Diff.STE.DeTurck.deTurckChartComp (I := I) g gbar x₀ p k := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hLC : LCSmooth I M := Work.Diff.T.lc_smooth (I := I) (M := M)
  -- the coordinate frame of the chart at `x₀` is a basis of `T_pM`
  set e : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    Work.Diff.EXT.frameBasis (I := I) x₀ p hp with he
  have hcv : ∀ i : Fin (Module.finrank ℝ E),
      e i = Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E i) := by
    intro i
    rw [he, Work.Diff.EXT.frameBasis_apply]
  have hcf : ∀ i : Fin (Module.finrank ℝ E), e i = Work.Diff.GE.cFrame (I := I) x₀ i p :=
    fun i => by rw [hcv i]; rfl
  -- its Gram matrix is `GramM`, so its inverse is `GramInv`
  have hGram : (Matrix.of fun i j => g.inner p (e i) (e j))
      = Work.Diff.GE.GramM (I := I) (fun _ : ℝ => g) x₀ 0 p := by
    ext i j
    show g.inner p (e i) (e j) = g.inner p (Work.Diff.GE.cFrame (I := I) x₀ i p)
      (Work.Diff.GE.cFrame (I := I) x₀ j p)
    rw [hcf i, hcf j]
  have hγg : (Matrix.of fun i j => g.inner p (e i) (e j))⁻¹
      = Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 p := by
    rw [Work.Diff.GE.GramInv, hGram]
  have hγI : (Matrix.of fun i j => inner ℝ (e i) (e j))⁻¹
      = Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 p := hγg
  -- the trace expansion of the DeTurck field in the chart frame
  have hW : Work.Diff.STE.DeTurck.traceVec (Work.Diff.STE.DeTurck.connDiff g gbar p)
      = ∑ a, ∑ b, Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 p a b
          • (Work.Diff.STE.DeTurck.connDiff g gbar p (e a) (e b)) := by
    rw [Work.Diff.STE.deTurck.traceVec_eq_sum_invGram
      (Work.Diff.STE.DeTurck.connDiff g gbar p) e, hγI]
  -- the coordinate of `connDiff (e a) (e b)` in the chart frame
  have hS : ∀ a b, e.coord k (Work.Diff.STE.DeTurck.connDiff g gbar p (e a) (e b))
      = Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => g) x₀ k b a 0 p
        - Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => gbar) x₀ k b a 0 p := by
    intro a b
    rw [hcf a, hcf b, connDiff_frame_eq_chart (I := I) hLC g gbar x₀ hp a b]
    simp_rw [← hcf]
    exact basis_coord_sum_smul e
      (fun n => Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => g) x₀ n b a 0 p
        - Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => gbar) x₀ n b a 0 p) k
  -- the left-hand side is the `k`-th coordinate of the DeTurck field
  have hcoeff : (∑ j, Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 p k j
        * g.inner p (Work.Diff.STE.DeTurck.deTurckVec g gbar p)
            (Work.Diff.GE.cFrame (I := I) x₀ j p))
      = e.coord k (Work.Diff.STE.DeTurck.deTurckVec g gbar p) := by
    have hFU := Work.Diff.EXT.eq_sum_frameVector_of_pairing (I := I) (g := g) hp
      (Work.Diff.STE.DeTurck.deTurckVec g gbar p)
    symm
    conv_lhs => rw [hFU]
    simp_rw [← hcv]
    rw [basis_coord_sum_smul, hγg, Matrix.mulVec_apply, dotProduct]
    simp only [Matrix.row_apply, hcf]
  -- that coordinate, computed
  have hcoord : e.coord k (Work.Diff.STE.DeTurck.deTurckVec g gbar p)
      = ∑ a, ∑ b, Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 p a b
          * (Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => g) x₀ k b a 0 p
            - Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => gbar) x₀ k b a 0 p) := by
    show e.coord k (Work.Diff.STE.DeTurck.traceVec (Work.Diff.STE.DeTurck.connDiff g gbar p))
      = ∑ a, ∑ b, Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 p a b
          * (Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => g) x₀ k b a 0 p
            - Work.Diff.GE.chrCoord (I := I) (fun _ : ℝ => gbar) x₀ k b a 0 p)
    rw [hW]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hS a b]
  -- the Christoffel symbols are symmetric in their lower indices
  rw [hcoeff, hcoord, Work.Diff.STE.DeTurck.deTurckChartComp]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [chrCoord_symm (I := I) (fun _ : ℝ => g) x₀ k b a 0 p,
    chrCoord_symm (I := I) (fun _ : ℝ => gbar) x₀ k b a 0 p]

end Work.Diff.STE.deTurck
