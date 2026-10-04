import Mathlib
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Frame change of the curvature components

`Submission.Diff.rmFrame g x e i j k l = g.inner x (R(eᵢ,eⱼ)e_l) e_k` is the array of curvature
components of the metric `g` at `x` in the frame `e`.  Its definition uses only the *pointwise*
curvature `rmVec (lcOf g) x u v w`, which is tensorial (`Work.Diff.GE.rmVec_antisymm`,
`Work.Diff.GE.rmVec_add_*`, `Work.Diff.GE.rmVec_smul_*`), so `rmFrame g x ·` is a 4-multilinear
function of the frame vectors: expanding a new frame `e'` in an old one, `e' i = ∑ j, A i j • e j`,
multiplies the component array by `A` in each of its four indices.

This file proves that identity:

* `rmFrame_eq_rot`: `rmFrame g x e' = Submission.Diff.Alg.rot A (rmFrame g x e)`.

No orthonormality of the frames is needed (nor used): the statement is purely the multilinearity of
the curvature tensor together with the bilinearity of the metric.  Consequently the lemma applies to
*any* two frames related by a matrix `A`, which is what the frame-independence arguments of the
gradient-estimate area need (they obtain `A ∈ O(n)` from the orthonormality, but only the expansion
`e' i = ∑ j, A i j • e j` is consumed).

The proof decomposes into the three elementary steps below:
`rmVec_sum3` (multilinearity of the curvature in three slots as a nested sum),
`inner_nested3` (bilinearity of `g.inner x` on nested sums), and
`sum_reorder` (the bookkeeping permutation of the four sums matching `rot`'s index order).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Multilinearity of `rmVec` in sum form -/

private lemma rmVec_sum3 [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (x : M) (n : ℕ) (c₁ c₂ c₃ : Fin n → ℝ) (u v w : Fin n → TangentSpace I x) :
    rmVec cov x (∑ a, c₁ a • u a) (∑ b, c₂ b • v b) (∑ d, c₃ d • w d)
      = ∑ a, ∑ b, ∑ d, (c₁ a * c₂ b * c₃ d) • rmVec cov x (u a) (v b) (w d) := by
  rw [rmVec_sum_left cov hcov (s := Finset.univ)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [rmVec_sum_middle cov hcov (s := Finset.univ)]
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [rmVec_sum_right cov hcov (s := Finset.univ)]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring_nf

/-! ## Bilinearity of the metric on nested sums -/

private lemma inner_smul_sum (g : SMet I M) (n : ℕ) (x : M) (u : TangentSpace I x)
    (c : Fin n → ℝ) (v : Fin n → TangentSpace I x) :
    g.inner x u (∑ i, c i • v i) = ∑ i, c i * g.inner x u (v i) := by
  simp only [map_sum, map_smul, smul_eq_mul]

private lemma inner_nested3_left (g : SMet I M) (x : M) (n : ℕ)
    (c : Fin n → Fin n → Fin n → ℝ) (u : Fin n → Fin n → Fin n → TangentSpace I x)
    (z : TangentSpace I x) :
    g.inner x (∑ a, ∑ b, ∑ d, c a b d • u a b d) z
      = ∑ a, ∑ b, ∑ d, c a b d * g.inner x (u a b d) z := by
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]

/-- Bilinearity of the metric on a triple sum in the first slot and a single sum in the second. -/
private lemma inner_nested3 (g : SMet I M) (x : M) (n : ℕ)
    (c : Fin n → Fin n → Fin n → ℝ) (u : Fin n → Fin n → Fin n → TangentSpace I x)
    (c' : Fin n → ℝ) (z : Fin n → TangentSpace I x) :
    g.inner x (∑ a, ∑ b, ∑ d, c a b d • u a b d) (∑ k, c' k • z k)
      = ∑ a, ∑ b, ∑ d, ∑ k, c a b d * c' k * g.inner x (u a b d) (z k) := by
  rw [inner_nested3_left g x n c u (∑ k, c' k • z k)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun d _ => ?_)))
  rw [inner_smul_sum g n x _ _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-! ## The index bookkeeping of `rot` -/

/-- The fourfold sum of the component change, in the index order produced by the multilinearity
steps (`a b d c`), is the one in `rot`'s order (`a b c d`). -/
private lemma sum_reorder (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i j k l : Fin n)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ d, ∑ c, (A i a * A j b * A l d) * A k c * R a b c d
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R a b c d := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [show (∑ d : Fin n, ∑ c : Fin n, (A i a * A j b * A l d) * A k c * R a b c d)
      = ∑ d : Fin n, ∑ c : Fin n, (A i a * A j b * A k c * A l d) * R a b c d from
        Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ => by ring))]
  exact Finset.sum_comm

/-! ## The frame change -/

theorem rmFrame_eq_rot
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hA : ∀ i, e' i = ∑ j, A i j • e j) :
    Submission.Diff.rmFrame g x e'
      = Submission.Diff.Alg.rot A (Submission.Diff.rmFrame g x e) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  obtain ⟨hcov, -, -⟩ := hLC g
  obtain ⟨hcov⟩ := hcov
  ext i j k l
  simp only [Submission.Diff.rmFrame, Submission.Diff.Alg.rot]
  rw [hA i, hA j, hA l, hA k]
  rw [rmVec_sum3 (lcOf g) hcov x (Module.finrank ℝ E) (A i) (A j) (A l) e e e]
  rw [inner_nested3 g x (Module.finrank ℝ E)
        (fun a b d => A i a * A j b * A l d)
        (fun a b d => rmVec (lcOf g) x (e a) (e b) (e d)) (A k) e]
  exact sum_reorder (Module.finrank ℝ E) A i j k l _

end Work.Diff.GE
