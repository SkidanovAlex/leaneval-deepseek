import Mathlib
import Submission.Work.Diff.STE.DeTurckField

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The metric trace `traceVec` in an arbitrary basis

`Work.Diff.STE.DeTurck.traceVec S` is the metric trace of a tensor `S : V →L[ℝ] V →L[ℝ] V`
(the linear-algebraic core of the DeTurck field `W(g) = tr_g (∇^g - ∇^{g̃})`).  It is defined
frame-freely, as the Riesz representative of the functional `ξ ↦ tr (rzEnd S ξ)`, i.e. as
`∑_i S (e_i) (e_i)` for an orthonormal basis `e`.  This file identifies it with the *frame formula*

`traceVec S = ∑_i ∑_j γ^{ij} • S (b i) (b j)`,

for an arbitrary basis `b` with inverse Gram matrix `γ = (⟪b i, b j⟫)⁻¹`; this is what makes it
possible to write the DeTurck field down in a coordinate frame.

The mathematical content is the pure linear-algebra identity `trace_eq_sum_inv_gram` (the trace of
an endomorphism contracted with the inverse Gram matrix, proved with the `B`-dual basis) plus the
dictionary between `traceVec` and `LinearMap.trace`.
-/

namespace Work.Diff.STE.deTurck

open scoped InnerProductSpace

set_option linter.unusedSectionVars false

/-! ## The pure linear-algebra identity

(For use below: the trace of an endomorphism against the inverse Gram matrix.  This is
`Work.Diff.EXT.trace_eq_sum_inv_toMatrix`; it is repeated here so that this module depends only on
`Mathlib` and on the definition of `traceVec`.) -/

/-- **The trace of an endomorphism against the inverse Gram matrix.**  For a nondegenerate
symmetric bilinear form `B` on a vector space `V` with a basis `b` and an endomorphism `T` of `V`,
the trace of `T`, read off in the basis `b`, equals the contraction of `B (T ·) ·` with the inverse
of the Gram matrix `B.toMatrix b`. -/
theorem trace_eq_sum_inv_gram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hsym : B.IsSymm)
    (b : Module.Basis ι ℝ V) (T : V →ₗ[ℝ] V) :
    (LinearMap.toMatrix b b T).trace
      = ∑ k, ∑ l, ((LinearMap.BilinForm.toMatrix b B))⁻¹ k l * B (T (b k)) (b l) := by
  classical
  let b' : Module.Basis ι ℝ V := B.dualBasis hB b
  have hleft : ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
    fun i j => LinearMap.BilinForm.apply_dualBasis_left hB b i j
  have hright : ∀ i j, B (b i) (b' j) = if i = j then 1 else 0 :=
    fun i j => LinearMap.BilinForm.apply_dualBasis_right hB hsym b i j
  -- expansion of a vector in the primal basis, using the dual basis
  have hexp : ∀ x : V, x = ∑ j, (B x (b' j)) • b j := by
    intro x
    have hcheck : ∀ m, B (b' m) (∑ j, (B x (b' j)) • b j) = B (b' m) x := by
      intro m
      rw [map_sum]
      rw [Finset.sum_eq_single m]
      · rw [map_smul, smul_eq_mul, hleft m m]
        simp only [ite_true, mul_one]
        exact hsym.eq x (b' m)
      · intro j _ hj
        rw [map_smul, smul_eq_mul, hleft m j]
        simp [hj]
      · intro hm; exact absurd (Finset.mem_univ m) hm
    have hext : B.flip (∑ j, (B x (b' j)) • b j) = B.flip x :=
      b'.ext (fun m => hcheck m)
    refine (sub_eq_zero.mp (hB.2 _ (fun z => ?_))).symm
    rw [map_sub, sub_eq_zero]
    exact DFunLike.congr_fun hext z
  have hexp_symm : ∀ x : V, x = ∑ j, (B (b' j) x) • b j := by
    intro x
    conv_lhs => rw [hexp x]
    exact Finset.sum_congr rfl (fun j _ => by rw [hsym.eq x (b' j)])
  -- the coordinates of a vector against the dual basis
  have hcself : ∀ i, b.coord i (b i) = 1 := fun i => by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  have hcne : ∀ i j, i ≠ j → b.coord i (b j) = 0 := fun i j h => by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne (a := j) (a' := i) h]
  have hcoef : ∀ (x : V) (i : ι), b.coord i x = B x (b' i) := by
    intro x i
    have h := congrArg (b.coord i) (hexp x)
    simp only [map_sum, map_smul, smul_eq_mul] at h
    rw [h, Finset.sum_eq_single i]
    · rw [hcself i, mul_one]
    · intro j _ hj
      rw [hcne i j (Ne.symm hj), mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  -- the inverse of the Gram matrix is the matrix of the pairings of the dual basis
  have hG : (LinearMap.BilinForm.toMatrix b B)⁻¹ = Matrix.of (fun i j => B (b' i) (b' j)) := by
    refine Matrix.inv_eq_right_inv ?_
    ext i k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [LinearMap.BilinForm.toMatrix_apply, Matrix.of_apply]
    have hkey : (∑ j, B (b i) (b j) * B (b' j) (b' k))
        = B (b i) (∑ j, B (b' j) (b' k) • b j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [hkey, ← hexp_symm (b' k)]
    exact hright i k
  have h1 : (LinearMap.toMatrix b b T).trace = ∑ i, B (T (b i)) (b' i) := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply, ← hcoef]
  rw [h1]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hG]
  simp only [Matrix.of_apply]
  conv_lhs => rw [hexp (b' k)]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, smul_eq_mul]

/-! ## The dictionary between `traceVec` and `LinearMap.trace` -/

section Trace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [CompleteSpace V]

/-- The defining property of `traceVec`: pairing it with `ξ` gives the trace of the endomorphism
`rzEnd S ξ`. -/
lemma traceVec_inner (S : V →L[ℝ] V →L[ℝ] V) (ξ : V) :
    inner ℝ (Work.Diff.STE.DeTurck.traceVec S) ξ
      = LinearMap.trace ℝ V (Work.Diff.STE.DeTurck.rzEnd S ξ) := by
  unfold Work.Diff.STE.DeTurck.traceVec Work.Diff.STE.DeTurck.rz
  rw [InnerProductSpace.toDual_symm_apply]
  simp only [LinearMap.coe_toContinuousLinearMap']
  rfl

/-- The value of the endomorphism `rzEnd S ξ` against a vector. -/
lemma rzEnd_inner (S : V →L[ℝ] V →L[ℝ] V) (ξ u w : V) :
    inner ℝ (Work.Diff.STE.DeTurck.rzEnd S ξ u) w = inner ℝ (S u w) ξ := by
  show inner ℝ
      (Work.Diff.STE.DeTurck.rz ((Work.Diff.STE.DeTurck.innerFun ξ).comp (S u))) w
    = inner ℝ (S u w) ξ
  unfold Work.Diff.STE.DeTurck.rz
  rw [InnerProductSpace.toDual_symm_apply]
  simp only [ContinuousLinearMap.comp_apply, Work.Diff.STE.DeTurck.innerFun_apply]

/-- The bilinear form `innerₗ V` evaluated on `rzEnd S ξ`. -/
lemma innerₗ_rzEnd (S : V →L[ℝ] V →L[ℝ] V) (ξ u w : V) :
    innerₗ V (Work.Diff.STE.DeTurck.rzEnd S ξ u) w = inner ℝ (S u w) ξ := by
  rw [innerₗ_apply_apply, rzEnd_inner]

/-- Pairing a doubly indexed sum with a vector. -/
lemma inner_sum_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (T : ι → κ → V) (ξ : V) :
    inner ℝ (∑ i, ∑ j, A i j • T i j) ξ = ∑ i, ∑ j, A i j * inner ℝ (T i j) ξ := by
  simp only [sum_inner, real_inner_smul_left]

end Trace

/-! ## The frame formula -/

theorem traceVec_eq_sum_invGram
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [CompleteSpace V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : V →L[ℝ] V →L[ℝ] V) (b : Module.Basis ι ℝ V) :
    Work.Diff.STE.DeTurck.traceVec S
      = ∑ i, ∑ j, ((Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹) i j • S (b i) (b j) := by
  classical
  -- the inner product as a nondegenerate symmetric bilinear form
  have hnondeg : (innerₗ V).Nondegenerate :=
    ⟨fun x hx => inner_self_eq_zero.mp (hx x),
     fun y hy => inner_self_eq_zero.mp (hy y)⟩
  have hsymm : LinearMap.BilinForm.IsSymm (innerₗ V) :=
    ⟨fun x y => (real_inner_comm x y).symm⟩
  have hGram : LinearMap.BilinForm.toMatrix b (innerₗ V)
      = Matrix.of (fun i j => inner ℝ (b i) (b j)) := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Matrix.of_apply, innerₗ_apply_apply]
  -- pairing `traceVec S` with `ξ`: the trace of `rzEnd S ξ`, contracted with the inverse Gram
  -- matrix
  have key : ∀ ξ : V, inner ℝ (Work.Diff.STE.DeTurck.traceVec S) ξ
      = ∑ i, ∑ j, ((Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹) i j
          * inner ℝ (S (b i) (b j)) ξ := by
    intro ξ
    rw [traceVec_inner S ξ]
    rw [LinearMap.trace_eq_matrix_trace ℝ b (Work.Diff.STE.DeTurck.rzEnd S ξ)]
    rw [trace_eq_sum_inv_gram (innerₗ V) hnondeg hsymm b (Work.Diff.STE.DeTurck.rzEnd S ξ)]
    rw [hGram]
    simp only [innerₗ_rzEnd]
  -- turn the pointwise contraction into the pairing with the trace vector
  have key' : ∀ ξ : V, inner ℝ (Work.Diff.STE.DeTurck.traceVec S) ξ
      = inner ℝ (∑ i, ∑ j, ((Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹) i j
          • S (b i) (b j)) ξ := by
    intro ξ
    exact (key ξ).trans (inner_sum_smul
      (fun i j => ((Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹) i j)
      (fun i j => S (b i) (b j)) ξ).symm
  have h0 : inner ℝ (Work.Diff.STE.DeTurck.traceVec S
        - ∑ i, ∑ j, ((Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹) i j • S (b i) (b j))
      (Work.Diff.STE.DeTurck.traceVec S
        - ∑ i, ∑ j, ((Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹) i j
            • S (b i) (b j)) = 0 := by
    rw [inner_sub_left, key' (Work.Diff.STE.DeTurck.traceVec S
        - ∑ i, ∑ j, ((Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹) i j • S (b i) (b j)),
      sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)

end Work.Diff.STE.deTurck
