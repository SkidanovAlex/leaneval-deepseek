import Mathlib
import Submission.Work.Diff.GE.rmChartExpr_kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The inverse Gram matrix expansion of the chart metric

This file proves `Work.Diff.GE.cGram_eq_sum_gramInv`: in the chart at `x₀`, the metric pairing of
two coordinate vectors `V W : E` is recovered from the pairings with the coordinate basis
`cBasis` and the *inverse* Gram matrix of the chart frame (the standard "raise both indices with
the inverse metric" identity).

The mathematical heart is the following completely general statement about a nondegenerate
symmetric bilinear form `B` on a vector space with a basis `b`: the matrix inverse of the Gram
matrix `B.toMatrix b` is the matrix of `B` on the `B`-dual basis of `b`, whence

  `B v w = ∑ i, ∑ j, (B.toMatrix b)⁻¹ i j * B v (b i) * B w (b j)`.

The bilinear form attached to the chart metric is `gramBil`, built from `cGram`; it is symmetric
and — because `cGram x₀ y a a > 0` for `a ≠ 0` (the frame is a basis on the chart source and the
metric is positive definite) — nondegenerate. Finally `GramM` is literally the matrix of that
bilinear form, so `GramInv = (GramM)⁻¹ = (gramBil.toMatrix cBasis)⁻¹`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic

namespace Work.Diff.GE

/-! ## The abstract inverse-Gram expansion -/

/-- **The inverse Gram matrix of a nondegenerate symmetric bilinear form.**  For a nondegenerate
symmetric bilinear form `B` on a vector space with basis `b`, the pairings of a vector `v` with
the basis elements, contracted with the inverse of the Gram matrix, reproduce `B v w`:

  `B v w = ∑ i, ∑ j, (B.toMatrix b)⁻¹ i j * B v (b i) * B w (b j)`. -/
theorem bilinForm_eq_sum_inv_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hsym : B.IsSymm)
    (b : Module.Basis ι ℝ V) (v w : V) :
    B v w = ∑ i, ∑ j, (LinearMap.BilinForm.toMatrix b B)⁻¹ i j * B v (b i) * B w (b j) := by
  classical
  let b' : Module.Basis ι ℝ V := B.dualBasis hB b
  have hleft : ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
    fun i j => LinearMap.BilinForm.apply_dualBasis_left hB b i j
  have hright : ∀ i j, B (b i) (b' j) = if i = j then 1 else 0 :=
    fun i j => LinearMap.BilinForm.apply_dualBasis_right hB hsym b i j
  have hrepr : ∀ (x : V) (i : ι), b'.repr x i = B x (b i) :=
    fun x i => LinearMap.BilinForm.dualBasis_repr_apply hB b x i
  -- The `B`-dual basis vector `b' k` is the combination `∑ j, B (b' j) (b' k) • b j`.
  have hz : ∀ k, (∑ j, B (b' j) (b' k) • b j) = b' k := by
    intro k
    have hcheck : ∀ m, B (b' m) (∑ j, B (b' j) (b' k) • b j) = B (b' m) (b' k) := by
      intro m
      rw [map_sum]
      rw [Finset.sum_eq_single m]
      · rw [map_smul, smul_eq_mul, hleft m m]
        simp
      · intro j _ hj
        rw [map_smul, smul_eq_mul, hleft m j]
        simp [hj]
      · intro hm
        exact absurd (Finset.mem_univ m) hm
    have hext : B.flip (∑ j, B (b' j) (b' k) • b j) = B.flip (b' k) :=
      b'.ext (fun m => hcheck m)
    refine sub_eq_zero.mp (hB.2 _ (fun y => ?_))
    rw [map_sub, sub_eq_zero]
    exact DFunLike.congr_fun hext y
  have hv : v = ∑ i, B v (b i) • b' i := by
    conv_lhs => rw [← b'.sum_repr v]
    exact Finset.sum_congr rfl (fun i _ => by rw [hrepr])
  have hw : w = ∑ j, B w (b j) • b' j := by
    conv_lhs => rw [← b'.sum_repr w]
    exact Finset.sum_congr rfl (fun j _ => by rw [hrepr])
  -- The inverse of the Gram matrix is the matrix of `B` on the dual basis.
  have hD : (LinearMap.BilinForm.toMatrix b B)⁻¹ = Matrix.of (fun i j => B (b' i) (b' j)) := by
    refine Matrix.inv_eq_right_inv ?_
    ext i k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    have h2 : (∑ j, (LinearMap.BilinForm.toMatrix b B) i j * B (b' j) (b' k))
        = B (b i) (∑ j, B (b' j) (b' k) • b j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.BilinForm.toMatrix_apply, map_smul, smul_eq_mul, mul_comm]
    rw [h2, hz k, hright i k]
  have h1 : B v w = ∑ i, B v (b i) * B (b' i) w := by
    rw [← LinearMap.flip_apply B v w]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, LinearMap.flip_apply]
  have h2 : ∀ i, B (b' i) w = ∑ j, B w (b j) * B (b' i) (b' j) := by
    intro i
    conv_lhs => rw [hw]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [hD]
  simp only [Matrix.of_apply]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2 i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

namespace CGramInv

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ## Bilinearity of `cGram` -/

lemma cGram_smul_fst (g : Submission.Diff.SMet I M) (x₀ p : M) (c : ℝ) (a b : E) :
    cGram g x₀ p (c • a) b = c * cGram g x₀ p a b := by
  show (g.inner p) (frameVector x₀ p (c • a)) (frameVector x₀ p b) = _
  rw [frameVector_smul, map_smul]
  rfl

lemma cGram_add_snd (g : Submission.Diff.SMet I M) (x₀ p : M) (a b₁ b₂ : E) :
    cGram g x₀ p a (b₁ + b₂) = cGram g x₀ p a b₁ + cGram g x₀ p a b₂ := by
  show (g.inner p) (frameVector x₀ p a) (frameVector x₀ p (b₁ + b₂)) = _
  rw [frameVector_add, map_add]
  rfl

lemma cGram_smul_snd (g : Submission.Diff.SMet I M) (x₀ p : M) (c : ℝ) (a b : E) :
    cGram g x₀ p a (c • b) = c * cGram g x₀ p a b := by
  show (g.inner p) (frameVector x₀ p a) (frameVector x₀ p (c • b)) = _
  rw [frameVector_smul, map_smul]
  rfl

lemma cGram_comm (g : Submission.Diff.SMet I M) (x₀ p : M) (a b : E) :
    cGram g x₀ p a b = cGram g x₀ p b a := by
  show (g.inner p) (frameVector x₀ p a) (frameVector x₀ p b) = _
  exact g.symm p _ _

/-! ## The bilinear form of the chart metric -/

/-- The bilinear form `(a, b) ↦ cGram (G t) x₀ y a b` of the metric `G t` in the chart at `x₀`. -/
noncomputable def gramBil (G : ℝ → Submission.Diff.SMet I M) (x₀ y : M) (t : ℝ) :
    LinearMap.BilinForm ℝ E :=
  LinearMap.mk₂ ℝ (fun a b : E => cGram (G t) x₀ y a b)
    (fun a₁ a₂ b => cGram_add_fst (G t) x₀ y a₁ a₂ b)
    (fun c a b => cGram_smul_fst (G t) x₀ y c a b)
    (fun a b₁ b₂ => cGram_add_snd (G t) x₀ y a b₁ b₂)
    (fun c a b => cGram_smul_snd (G t) x₀ y c a b)

lemma gramBil_apply (G : ℝ → Submission.Diff.SMet I M) (x₀ y : M) (t : ℝ) (a b : E) :
    gramBil G x₀ y t a b = cGram (G t) x₀ y a b := rfl

lemma gramBil_isSymm (G : ℝ → Submission.Diff.SMet I M) (x₀ y : M) (t : ℝ) :
    (gramBil G x₀ y t).IsSymm :=
  ⟨fun a b => by rw [gramBil_apply, gramBil_apply, cGram_comm]⟩

/-- `cGram` is positive definite on the chart: the frame vectors of the coordinate basis are
linearly independent on the source of the chart and the metric is positive definite. -/
lemma cGram_self_pos (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) {a : E} (ha : a ≠ 0) :
    0 < cGram (G t) x₀ y a a := by
  show 0 < (G t).inner y (frameVector x₀ y a) (frameVector x₀ y a)
  refine (G t).pos y (frameVector x₀ y a) ?_
  exact fun h => ha ((Submission.ChartBounds.frameVector_eq_zero_iff hy a).mp h)

lemma gramBil_nondegenerate (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (t : ℝ) :
    (gramBil G x₀ y t).Nondegenerate := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · by_contra hne
    have h1 := cGram_self_pos G x₀ hy t hne
    have h2 : cGram (G t) x₀ y a a = 0 := by
      have h := ha a
      rwa [gramBil_apply] at h
    linarith
  · by_contra hne
    have h1 := cGram_self_pos G x₀ hy t hne
    have h2 : cGram (G t) x₀ y b b = 0 := by
      have h := hb b
      rwa [gramBil_apply] at h
    linarith

/-- The Gram matrix of the chart frame is the matrix of the bilinear form `gramBil`. -/
lemma GramM_eq_toMatrix (G : ℝ → Submission.Diff.SMet I M) (x₀ y : M) (t : ℝ) :
    GramM (I := I) G x₀ t y
      = LinearMap.BilinForm.toMatrix (cBasis (E := E)) (gramBil G x₀ y t) := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, gramBil_apply]
  rfl

end

end CGramInv

/-! ## The main statement -/

theorem cGram_eq_sum_gramInv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) {y : M} (hy : y ∈ (chartAt H x₀).source) (t : ℝ)
    (V W : E) :
    Work.Diff.GE.cGram (G t) x₀ y V W
      = ∑ m, ∑ n, Work.Diff.GE.GramInv (I := I) G x₀ t y m n
          * Work.Diff.GE.cGram (G t) x₀ y V (Work.Diff.GE.cBasis (E := E) m)
          * Work.Diff.GE.cGram (G t) x₀ y W (Work.Diff.GE.cBasis (E := E) n) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hkey := bilinForm_eq_sum_inv_toMatrix (CGramInv.gramBil (I := I) G x₀ y t)
    (CGramInv.gramBil_nondegenerate (I := I) G x₀ hy t)
    (CGramInv.gramBil_isSymm (I := I) G x₀ y t) (cBasis (E := E)) V W
  rw [show cGram (G t) x₀ y V W
        = CGramInv.gramBil (I := I) G x₀ y t V W
      from (CGramInv.gramBil_apply (I := I) G x₀ y t V W).symm]
  rw [hkey]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  rw [← CGramInv.GramM_eq_toMatrix (I := I) G x₀ y t]
  rfl

end Work.Diff.GE
