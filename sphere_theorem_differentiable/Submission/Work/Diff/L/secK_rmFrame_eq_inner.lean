import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.rmFrame_eq_rot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]

/-! ## Elementary expansion lemmas

The two ingredients of the main identity are the multilinearity of the pointwise curvature
`rmVec` (which is `Work.Diff.GE.rmVec_sum_left/middle/right`) and the bilinearity of the metric
`g.inner x`.  Everything is stated over an arbitrary `Fin n → ℝ` coefficient families, so that the
same expansion is available for any dimension. -/

/-- Multilinearity of `rmVec` in its three vector slots, as a nested sum over `Fin n`. -/
private lemma rmVec_sum3 [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (x : M) (n : ℕ) (c₁ c₂ c₃ : Fin n → ℝ) (u v w : Fin n → TangentSpace I x) :
    rmVec cov x (∑ a, c₁ a • u a) (∑ b, c₂ b • v b) (∑ d, c₃ d • w d)
      = ∑ a, ∑ b, ∑ d, (c₁ a * c₂ b * c₃ d) • rmVec cov x (u a) (v b) (w d) := by
  rw [Work.Diff.GE.rmVec_sum_left (ι := Fin n) cov hcov x Finset.univ c₁ u
    (∑ b, c₂ b • v b) (∑ d, c₃ d • w d)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Work.Diff.GE.rmVec_sum_middle (ι := Fin n) cov hcov x Finset.univ c₂ v (u a)
    (∑ d, c₃ d • w d)]
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Work.Diff.GE.rmVec_sum_right (ι := Fin n) cov hcov x Finset.univ c₃ w (u a) (v b)]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring_nf

/-- Bilinearity of `g.inner x` in the second slot on a sum. -/
private lemma inner_smul_sum (g : SMet I M) (n : ℕ) (x : M) (u : TangentSpace I x)
    (c : Fin n → ℝ) (v : Fin n → TangentSpace I x) :
    g.inner x u (∑ i, c i • v i) = ∑ i, c i * g.inner x u (v i) := by
  simp only [map_sum, map_smul, smul_eq_mul]

/-- Bilinearity of `g.inner x` in the first slot on a triple sum. -/
private lemma inner_nested3_left (g : SMet I M) (x : M) (n : ℕ)
    (c : Fin n → Fin n → Fin n → ℝ) (u : Fin n → Fin n → Fin n → TangentSpace I x)
    (z : TangentSpace I x) :
    g.inner x (∑ a, ∑ b, ∑ d, c a b d • u a b d) z
      = ∑ a, ∑ b, ∑ d, c a b d * g.inner x (u a b d) z := by
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]

/-- Bilinearity of `g.inner x` on a triple sum in the first slot and a single sum in the second. -/
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

/-- The index bookkeeping: the fourfold sum produced by the multilinearity expansion (index order
`a b d k`) equals the one in `secK`'s order (`a b k d`). -/
private lemma sum_reorder (n : ℕ) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (u v : Fin n → ℝ) :
    (∑ a, ∑ b, ∑ d, ∑ k, (u a * v b * v d) * u k * R a b k d)
      = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * u i * v j * u k * v l := by
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))

/-- Frame components of the curvature, evaluated on coordinate vectors, are the curvature paired with
the corresponding vectors.  For a frame `e` at `x` and coefficients `u`, `v`,
`secK (rmFrame g x e) u v = g(R(∑ᵢ uᵢeᵢ, ∑ⱼ vⱼeⱼ)∑ₗ vₗeₗ, ∑ₖ uₖeₖ)`, where
`rmFrame g x e i j k l = g(R(eᵢ,eⱼ)eₗ, eₖ)` and `rmVec (lcOf g) x · · ·` is the pointwise curvature
defined with chosen smooth extensions.  (Orthonormality of `e` is not needed for this identity.) -/
theorem secK_rmFrame_eq_inner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (g : SMet I M) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hcov : ContMDiffCovariantDerivative (lcOf g) ∞) (u v : Fin (Module.finrank ℝ E) → ℝ) :
    Submission.Diff.Alg.secK (rmFrame g x e) u v
      = g.inner x (rmVec (lcOf g) x (∑ i, u i • e i) (∑ j, v j • e j) (∑ l, v l • e l))
          (∑ k, u k • e k) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hvec : rmVec (lcOf g) x (∑ i, u i • e i) (∑ j, v j • e j) (∑ l, v l • e l)
      = ∑ a, ∑ b, ∑ d, (u a * v b * v d) • rmVec (lcOf g) x (e a) (e b) (e d) :=
    rmVec_sum3 (lcOf g) hcov x (Module.finrank ℝ E) u v v e e e
  rw [hvec]
  rw [inner_nested3 g x (Module.finrank ℝ E) (fun a b d => u a * v b * v d)
      (fun a b d => rmVec (lcOf g) x (e a) (e b) (e d)) u e]
  unfold Submission.Diff.Alg.secK Submission.Diff.Alg.R4 Submission.Diff.rmFrame
  exact (sum_reorder (Module.finrank ℝ E)
    (fun i j k l => g.inner x (rmVec (lcOf g) x (e i) (e j) (e l)) (e k)) u v).symm

end Work.Diff.L
