import Mathlib
import Submission.Work.Diff.EXT.ricPhiPartialDefs
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ricAt_invGram_chart`: the Ricci tensor in the coordinate frame

The pointwise Ricci tensor `Submission.Diff.ricAt (lcOf g) p u v` is defined as the trace of the
endomorphism `w ↦ R(w,u)v` of `T_pM` computed in the canonical basis `Module.finBasis ℝ E` of the
model space.  This file evaluates the same trace in the *coordinate frame* of the chart at `x₀`,
which is a genuine basis of `T_pM` as soon as `p` lies in the source of the chart, and expresses it
in terms of the inverse of the Gram matrix of that frame:

`Ric(σ_i, σ_j) = ∑_{k,l} γ^{kl} ⟪R(σ_k, σ_i)σ_j, σ_l⟫`.

The mathematical content is a purely linear-algebraic identity: for a nondegenerate symmetric
bilinear form `B` on a vector space `V` with basis `b` and an endomorphism `T` of `V`,

`(matrix of T in b).trace = ∑_{k,l} (B.toMatrix b)⁻¹ k l * B (T (b k)) (b l)`,

proved with the `B`-dual basis of `b` (`LinearMap.BilinForm.dualBasis`).  The identity is then
instantiated with `B = g.inner p`, `T = (w ↦ R(w,σ_i)σ_j)` and `b` the coordinate frame.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

/-! ## The abstract linear-algebra identity -/

/-- **The trace against the inverse Gram matrix.**  For a nondegenerate symmetric bilinear form `B`
on a vector space `V` with a basis `b : Basis ι ℝ V` and an endomorphism `T` of `V`, the trace of
`T` (read off in the basis `b`) equals the contraction of `B (T ·) ·` with the inverse of the Gram
matrix `B.toMatrix b`. -/
theorem trace_eq_sum_inv_toMatrix
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

/-! ## The coordinate frame of a chart as a basis -/

section Chart

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The coordinate frame of the chart at `x₀` at `p`, as a basis of `T_pM`.**  It is the image of
the canonical basis of the model space under the inverse of the tangent-bundle trivialisation at
`x₀`, which is a linear isomorphism as soon as `p` lies in the source of the chart. -/
noncomputable def frameBasis (x₀ p : M) (hp : p ∈ (chartAt H' x₀).source) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
  (bB (E := E)).map
    ((Trivialization.continuousLinearEquivAt ℝ (trivializationAt E (TangentSpace I) x₀) p
      (by rw [TangentBundle.trivializationAt_baseSet]; exact hp)).symm.toLinearEquiv)

lemma frameBasis_apply (x₀ p : M) (hp : p ∈ (chartAt H' x₀).source)
    (k : Fin (Module.finrank ℝ E)) :
    frameBasis (I := I) x₀ p hp k = cvec (I := I) x₀ p (bB (E := E) k) := by
  rw [frameBasis, Module.Basis.map_apply]
  show ((Trivialization.continuousLinearEquivAt ℝ
      (trivializationAt E (TangentSpace I) x₀) p _).symm) (bB (E := E) k)
    = Submission.Geodesic.frameVector (I := I) x₀ p (bB (E := E) k)
  rw [Trivialization.symm_continuousLinearEquivAt_eq]
  rfl

/-- The bilinear form `(v, w) ↦ g.inner p v w` attached to a smooth metric at a point. -/
noncomputable def innerBilin (g : Submission.Diff.SMet I M) (p : M) :
    LinearMap.BilinForm ℝ (TangentSpace I p) :=
  LinearMap.mk₂ ℝ (fun v w => g.inner p v w)
    (fun v₁ v₂ w => by simp)
    (fun c v w => by simp)
    (fun v w₁ w₂ => by simp)
    (fun c v w => by simp)

lemma innerBilin_apply (g : Submission.Diff.SMet I M) (p : M)
    (v w : TangentSpace I p) : innerBilin g p v w = g.inner p v w :=
  LinearMap.mk₂_apply ℝ _ v w

lemma innerBilin_symm (g : Submission.Diff.SMet I M) (p : M) :
    (innerBilin g p).IsSymm :=
  ⟨fun v w => g.symm p v w⟩

lemma innerBilin_nondegenerate (g : Submission.Diff.SMet I M) (p : M) :
    (innerBilin g p).Nondegenerate := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · by_contra hne
    have h0 : g.inner p v v = 0 := hv v
    have hpos : 0 < g.inner p v v := g.pos p v hne
    rw [h0] at hpos
    exact absurd hpos (lt_irrefl (0 : ℝ))
  · by_contra hne
    have h0 : g.inner p v v = 0 := hv v
    have hpos : 0 < g.inner p v v := g.pos p v hne
    rw [h0] at hpos
    exact absurd hpos (lt_irrefl (0 : ℝ))

end Chart

/-! ## The statement -/

theorem ricAt_invGram_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {p : M} (hp : p ∈ (chartAt H' x₀).source)
    (i j : Fin (Module.finrank ℝ E)) :
    Submission.Diff.ricAt (Submission.Diff.lcOf g) p
        (Work.Diff.EXT.cvec (I := I) x₀ p (Work.Diff.EXT.bB (E := E) i))
        (Work.Diff.EXT.cvec (I := I) x₀ p (Work.Diff.EXT.bB (E := E) j))
      = ∑ k, ∑ l, (Work.Diff.EXT.cgramM g x₀ p)⁻¹ k l
          * g.inner p
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) p
                (Work.Diff.EXT.cvec (I := I) x₀ p (Work.Diff.EXT.bB (E := E) k))
                (Work.Diff.EXT.cvec (I := I) x₀ p (Work.Diff.EXT.bB (E := E) i))
                (Work.Diff.EXT.cvec (I := I) x₀ p (Work.Diff.EXT.bB (E := E) j)))
              (Work.Diff.EXT.cvec (I := I) x₀ p (Work.Diff.EXT.bB (E := E) l)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hcov : ContMDiffCovariantDerivative (Submission.Diff.lcOf g) (⊤ : ℕ∞) :=
    ((Work.Diff.T.lc_smooth (I := I) (M := M)) g).1.some
  -- the endomorphism `w ↦ R(w, σ_i)σ_j`
  let T : TangentSpace I p →ₗ[ℝ] TangentSpace I p :=
    { toFun := fun w => Submission.Diff.rmVec (Submission.Diff.lcOf g) p w
        (cvec (I := I) x₀ p (bB (E := E) i)) (cvec (I := I) x₀ p (bB (E := E) j))
      map_add' := fun a b =>
        Work.Diff.GE.rmVec_add_left (Submission.Diff.lcOf g) hcov p a b
          (cvec (I := I) x₀ p (bB (E := E) i)) (cvec (I := I) x₀ p (bB (E := E) j))
      map_smul' := fun c a =>
        Work.Diff.GE.rmVec_smul_left (Submission.Diff.lcOf g) hcov p c a
          (cvec (I := I) x₀ p (bB (E := E) i)) (cvec (I := I) x₀ p (bB (E := E) j)) }
  have hT : ∀ w : TangentSpace I p, T w = Submission.Diff.rmVec (Submission.Diff.lcOf g) p w
      (cvec (I := I) x₀ p (bB (E := E) i)) (cvec (I := I) x₀ p (bB (E := E) j)) :=
    fun _ => rfl
  -- the left-hand side is the trace of `T`
  have hleft : Submission.Diff.ricAt (Submission.Diff.lcOf g) p
      (cvec (I := I) x₀ p (bB (E := E) i)) (cvec (I := I) x₀ p (bB (E := E) j))
      = LinearMap.trace ℝ (TangentSpace I p) T := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (Module.finBasis ℝ (TangentSpace I p)) T]
    simp only [Submission.Diff.ricAt, Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hT]
    rfl
  rw [hleft]
  -- read the trace in the coordinate frame
  rw [LinearMap.trace_eq_matrix_trace ℝ (frameBasis (I := I) x₀ p hp) T]
  rw [trace_eq_sum_inv_toMatrix (innerBilin g p) (innerBilin_nondegenerate g p)
    (innerBilin_symm g p) (frameBasis (I := I) x₀ p hp) T]
  -- the Gram matrix of the coordinate frame is `cgramM`
  have hGram : LinearMap.BilinForm.toMatrix (frameBasis (I := I) x₀ p hp) (innerBilin g p)
      = cgramM g x₀ p := by
    ext k l
    rw [LinearMap.BilinForm.toMatrix_apply, innerBilin_apply, frameBasis_apply, frameBasis_apply]
    rfl
  rw [hGram]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  simp only [innerBilin_apply, hT, frameBasis_apply]

end Work.Diff.EXT
