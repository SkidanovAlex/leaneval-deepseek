import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.cos_sq_gt_half
import Submission.Work.Diff.C.at_most_one_neq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The algebra of the ray data.**  `p : M`, `e : Fin n → T_pM` orthonormal, `u ∈ T_pM` a unit
vector, `β i = ⟪e i, u⟫`.  Then `∑ β i ^ 2 = 1` (Parseval), **at most one** index has
`β i ≤ -cos α` (as `2 cos²α > 1` for `α ≤ 1/4`), and for such an index every `j ≠ i` satisfies
`|β j| ≤ sin α` (because `‖u - β i • e i‖² = 1 - β i² ≤ sin²α`).  Finally, if `β i > -cos α` then
`-cos α ≤ β i * sin σ` for every `σ ∈ [0,π]` (for `β i ≥ 0` the product is `≥ 0 ≥ -cos α`, and for
`β i < 0` it is `≥ β i > -cos α` since `sin σ ≤ 1`). -/
theorem ray_cap_algebra
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {u : TangentSpace I p} (hu : Inner.inner ℝ u u = 1) :
    (∑ i, (Inner.inner ℝ (e i) u) ^ 2 = 1) ∧
    (∀ i j, i ≠ j → Inner.inner ℝ (e i) u ≤ -Real.cos α →
      Inner.inner ℝ (e j) u ≤ -Real.cos α → False) ∧
    (∀ i j, i ≠ j → Inner.inner ℝ (e i) u ≤ -Real.cos α →
      |Inner.inner ℝ (e j) u| ≤ Real.sin α) ∧
    (∀ i, -Real.cos α < Inner.inner ℝ (e i) u → ∀ σ ∈ Set.Icc (0 : ℝ) Real.pi,
      -Real.cos α ≤ Inner.inner ℝ (e i) u * Real.sin σ) := by
  -- The tangent space at `p` is `E` itself (`TangentSpace I p` is definitionally `E`), so the
  -- fibre carries a genuine inner product space structure (that of the Riemannian bundle), of
  -- real dimension `finrank ℝ E`, and `e` is an orthonormal family of the right cardinality:
  -- hence a basis, and Parseval holds.
  letI : InnerProductSpace ℝ (TangentSpace I p) := inferInstance
  have hfr : Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ E := rfl
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I p) := by
    rw [Fintype.card_fin, hfr]
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  have hv : Orthonormal ℝ e := orthonormal_iff_ite.mpr hON
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    basisOfOrthonormalOfCardEqFinrank hv hcard
  have hcoe : (b : Fin (Module.finrank ℝ E) → TangentSpace I p) = e :=
    coe_basisOfOrthonormalOfCardEqFinrank hv hcard
  have hsum : u = ∑ i, b.repr u i • e i := by
    rw [← hcoe]
    exact (b.sum_repr u).symm
  -- `β i` is the `i`-th coordinate of `u` in the basis `e`.
  have hbeta : ∀ i, b.repr u i = Inner.inner ℝ (e i) u := by
    intro i
    have h1 : Inner.inner ℝ (e i) u = Inner.inner ℝ (e i) (∑ j, b.repr u j • e j) :=
      congrArg (fun w => Inner.inner ℝ (e i) w) hsum
    rw [h1, hv.inner_right_fintype]
  -- Parseval.
  have hParseval : (∑ i, (Inner.inner ℝ (e i) u) ^ 2) = 1 := by
    have hpp : (∑ i, (Inner.inner ℝ (e i) u) ^ 2) = Inner.inner ℝ u u := by
      calc (∑ i, (Inner.inner ℝ (e i) u) ^ 2)
          = ∑ i, (b.repr u i) ^ 2 := by
            apply Finset.sum_congr rfl; intro i _; rw [hbeta i]
        _ = Inner.inner ℝ (∑ i, b.repr u i • e i) (∑ i, b.repr u i • e i) := by
            rw [hv.inner_sum]; simp [sq]
        _ = Inner.inner ℝ u u := by rw [show (∑ i, b.repr u i • e i) = u from hsum.symm]
    rw [hpp, hu]
  -- The trigonometric facts about `α ∈ (0, 1/4]`.
  have hcos_pos : 0 < Real.cos α := by
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hα],
      by linarith [Real.pi_gt_three, hα1]⟩
  have hsin_nn : 0 ≤ Real.sin α :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hα) (by linarith [Real.pi_gt_three, hα1])
  have hcos_sq : 1 / 2 < Real.cos α ^ 2 := cos_sq_gt_half hα hα1
  -- At most one negative index, and the bound on the remaining coordinates.
  obtain ⟨h2, h3⟩ :=
    at_most_one_neq (β := fun i => Inner.inner ℝ (e i) u) hParseval hcos_sq
      (le_of_lt hcos_pos) hsin_nn
  refine ⟨hParseval, h2, h3, ?_⟩
  intro i hi σ hσ
  have hsin_le : Real.sin σ ≤ 1 := Real.sin_le_one σ
  have hsin_nn' : 0 ≤ Real.sin σ := Real.sin_nonneg_of_nonneg_of_le_pi hσ.1 hσ.2
  by_cases hb : 0 ≤ Inner.inner ℝ (e i) u
  · have : 0 ≤ Inner.inner ℝ (e i) u * Real.sin σ := mul_nonneg hb hsin_nn'
    linarith
  · push_neg at hb
    have hstep := mul_le_mul_of_nonpos_left hsin_le (le_of_lt hb)
    linarith

end Work.Diff.C
