import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.finrank_symmetric_matrices
import Submission.Commons.GeometryOfNumbers.Ellipsoid.finrank_tensor_span_le_card_half
import Submission.Commons.Analysis.InnerProductSpace.finrank_inf_orthogonal

/-!
# The space of symmetric matrices as an inner product space

Mathlib has no `NormedAddCommGroup`/`InnerProductSpace` instance on `Matrix (Fin d) (Fin d) ℝ`
(and none on `EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)`), so the stochastic
machinery used in `Submission/PLAN_V3.md` (orthogonal projections, `stdGaussian`, martingales
with values in the state space) has no ambient space to run in.

This file provides one: `MatV d := EuclideanSpace ℝ (Fin d × Fin d)` together with the linear
equivalence `matOf d : MatV d ≃ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ` to matrices.  All matrix notions
(`IsSymm`, `PosDef`, `det`, `mulVec`, `vecMulVec`) are transported along `matOf`; the quadratic
form `∑ i j v (i,j) * x i * x j` is a *linear functional* on `MatV d`, equal to the inner
product with the rank-one tensor `x ⊗ x`.  The symmetric matrices form a submodule `symV d`, and
for a finite set `S` of vectors the "tangent space" `tangentSub S` (the intersection of the
kernels of the quadratic functionals of `S` inside `symV d`) is a submodule of `MatV d`, on
which `Submodule.starProjection` is available.
-/

namespace Submission.MatSpace

open Matrix

noncomputable section

/-- `d × d` real matrices, as a Euclidean space (Frobenius inner product). -/
abbrev MatV (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin d)

/-- The linear equivalence from `MatV d` to `d × d` matrices. -/
def matOf (d : ℕ) : MatV d ≃ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ :=
  (WithLp.linearEquiv 2 ℝ ((Fin d × Fin d) → ℝ)).trans
    (LinearEquiv.curry ℝ ℝ (Fin d) (Fin d))

@[simp] lemma matOf_apply (d : ℕ) (v : MatV d) (i j : Fin d) : matOf d v i j = v (i, j) := rfl

/-- The quadratic form of a vector of `MatV d`, read as a matrix. -/
def quadFormV {d : ℕ} (v : MatV d) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ∑ j, v (i, j) * x i * x j

lemma quadFormV_eq_dotProduct {d : ℕ} (v : MatV d) (x : EuclideanSpace ℝ (Fin d)) :
    quadFormV v x = x ⬝ᵥ (matOf d v).mulVec x := by
  simp only [quadFormV, dotProduct, mulVec, matOf_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The quadratic form as a linear functional of the matrix variable. -/
def quadLin {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : MatV d →ₗ[ℝ] ℝ where
  toFun := fun v => quadFormV v x
  map_add' := by
    intro a b
    rw [quadFormV_eq_dotProduct, quadFormV_eq_dotProduct, quadFormV_eq_dotProduct, map_add,
      add_mulVec, dotProduct_add]
  map_smul' := by
    intro c a
    rw [quadFormV_eq_dotProduct, quadFormV_eq_dotProduct, map_smul, smul_mulVec,
      dotProduct_smul]
    rfl

/-- The rank-one tensor `x ⊗ x` as an element of `MatV d`. -/
def tensorV {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : MatV d :=
  WithLp.toLp 2 (fun p : Fin d × Fin d => x p.1 * x p.2)

@[simp] lemma tensorV_apply {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (i j : Fin d) :
    tensorV x (i, j) = x i * x j := rfl

lemma matOf_tensorV {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    matOf d (tensorV x) = Matrix.vecMulVec x x := by
  ext i j; rfl

/-- The symmetric matrices form a submodule of `MatV d`. -/
def symV (d : ℕ) : Submodule ℝ (MatV d) where
  carrier := {v | (matOf d v).IsSymm}
  add_mem' := by
    intro a b ha hb
    show (matOf d (a + b)).IsSymm
    rw [map_add]; exact ha.add hb
  zero_mem' := by
    show (matOf d 0).IsSymm
    rw [map_zero]; simp [Matrix.IsSymm]
  smul_mem' := by
    intro c a ha
    show (matOf d (c • a)).IsSymm
    rw [map_smul]; exact ha.smul c

/-- The tangent space of the constraint cone at a matrix with contact set `S`: the symmetric
matrices whose quadratic form vanishes on all of `S`. -/
def tangentSub {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : Submodule ℝ (MatV d) :=
  symV d ⊓ ⨅ x : (S : Set (EuclideanSpace ℝ (Fin d))), LinearMap.ker (quadLin x)

@[simp] lemma mem_symV {d : ℕ} {v : MatV d} : v ∈ symV d ↔ (matOf d v).IsSymm := Iff.rfl

lemma mem_tangentSub {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) (v : MatV d) :
    v ∈ tangentSub S ↔ (matOf d v).IsSymm ∧ ∀ x ∈ S, quadFormV v x = 0 := by
  rw [tangentSub, Submodule.mem_inf, mem_symV, Submodule.mem_iInf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x hx => by
      have := h2 ⟨x, by simpa using hx⟩
      simpa [quadLin, quadFormV] using this⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => by
      have := h2 i.1 (by simpa using i.2)
      simpa [quadLin, quadFormV] using this⟩

/-- The quadratic functional is the inner product with the rank-one tensor `x ⊗ x`. -/
lemma quadLin_eq_inner {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (v : MatV d) :
    quadLin x v = inner ℝ v (tensorV x) := by
  simp only [quadLin, LinearMap.coe_mk, AddHom.coe_mk, quadFormV]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [tensorV, WithLp.ofLp_toLp]
  ring


/-! ## The dimension of the tangent space

For a finite set `S` of vectors closed under negation and not containing `0`, the space
`tangentSub S` cut out by the quadratic forms `⟨x ⊗ x, ·⟩`, `x ∈ S`, has dimension at least
`d(d+1)/2 - |S|/2`.  This is the dimension bookkeeping of `Submission/PLAN_V3.md` (Klartag's
`N_t ≥ dim Sym_d - #{contacts}/2`): each contact costs at most one half dimension, because
`x` and `-x` give the same rank-one tensor.
-/

/-- The kernel of the quadratic functional of `x` is the orthogonal complement of the line
spanned by the rank-one tensor `x ⊗ x`. -/
lemma ker_quadLin {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    LinearMap.ker (quadLin x) = (Submodule.span ℝ {tensorV x})ᗮ := by
  ext v
  rw [LinearMap.mem_ker, quadLin_eq_inner, Submodule.mem_orthogonal_singleton_iff_inner_left]

/-- `tangentSub S` is the symmetric part of the orthogonal complement of the span of the
rank-one tensors of the elements of `S`. -/
lemma tangentSub_eq {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) :
    tangentSub S = symV d ⊓
      (Submodule.span ℝ (tensorV '' (S : Set (EuclideanSpace ℝ (Fin d)))))ᗮ := by
  rw [tangentSub]
  congr 1
  have h1 : (⨅ x : ↥(S : Set (EuclideanSpace ℝ (Fin d))), LinearMap.ker (quadLin x.1))
      = ⨅ x : ↥(S : Set (EuclideanSpace ℝ (Fin d))), (Submodule.span ℝ {tensorV x.1})ᗮ := by
    refine le_antisymm (le_iInf fun x => ?_) (le_iInf fun x => ?_)
    · exact (iInf_le _ x).trans_eq (ker_quadLin x.1)
    · exact (iInf_le _ x).trans_eq (ker_quadLin x.1).symm
  have h2 : (⨆ x : ↥(S : Set (EuclideanSpace ℝ (Fin d))), Submodule.span ℝ {tensorV x.1})
      = Submodule.span ℝ (tensorV '' (S : Set (EuclideanSpace ℝ (Fin d)))) := by
    apply le_antisymm
    · rw [iSup_le_iff]
      intro x
      refine Submodule.span_le.mpr ?_
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Submodule.subset_span ⟨x.1, x.2, rfl⟩
    · rw [Submodule.span_le]
      rintro y ⟨x, hx, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨x, hx⟩ (Submodule.mem_span_singleton_self _)
  rw [h1, ← h2, Submodule.iInf_orthogonal]

/-- `matOf` carries `symV d` onto the submodule of symmetric matrices. -/
lemma map_symV {d : ℕ} :
    (symV d).map (matOf d : MatV d →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
      = Commons.LinearAlgebra.Matrix.symmSubmodule d := by
  ext A
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hA
    exact ⟨(matOf d).symm A, hA, by simp⟩

/-- The dimension of the space of symmetric `d × d` matrices, in `MatV` form. -/
lemma finrank_symV (d : ℕ) : Module.finrank ℝ ↥(symV d) = d * (d + 1) / 2 := by
  rw [← LinearEquiv.finrank_map_eq (matOf d) (symV d), map_symV,
    ← Commons.LinearAlgebra.Matrix.span_eq_symmSubmodule d]
  exact Commons.LinearAlgebra.Matrix.finrank_symmetric_matrices d

/-- `matOf` carries the span of the rank-one tensors of `S` to the span of the `vecMulVec`s. -/
lemma map_span_tensorV {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) :
    (Submodule.span ℝ (tensorV '' (S : Set (EuclideanSpace ℝ (Fin d))))).map
        (matOf d : MatV d →ₗ[ℝ] Matrix (Fin d) (Fin d) ℝ)
      = Submodule.span ℝ ((fun x : EuclideanSpace ℝ (Fin d) => Matrix.vecMulVec x x) ''
          (S : Set (EuclideanSpace ℝ (Fin d)))) := by
  rw [Submodule.map_span]
  congr 1
  ext A
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, matOf_tensorV x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨tensorV x, ⟨x, hx, rfl⟩, matOf_tensorV x⟩

/-- The dimension of the span of the rank-one tensors of `S`, computed on matrices. -/
lemma finrank_span_tensorV_eq {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) :
    Module.finrank ℝ ↥(Submodule.span ℝ (tensorV '' (S : Set (EuclideanSpace ℝ (Fin d)))))
      = Module.finrank ℝ ↥(Submodule.span ℝ
          ((fun x : EuclideanSpace ℝ (Fin d) => Matrix.vecMulVec x x) ''
            (S : Set (EuclideanSpace ℝ (Fin d))))) := by
  rw [← LinearEquiv.finrank_map_eq (matOf d)
    (Submodule.span ℝ (tensorV '' (S : Set (EuclideanSpace ℝ (Fin d))))), map_span_tensorV]

/-- Each pair `±x` of nonzero vectors contributes at most one half dimension to the span of
the rank-one tensors. -/
lemma two_mul_finrank_span_tensorV_le_card {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d)))
    (hne : ∀ x ∈ S, x ≠ 0) (hneg : ∀ x ∈ S, -x ∈ S) :
    2 * Module.finrank ℝ ↥(Submodule.span ℝ (tensorV '' (S : Set (EuclideanSpace ℝ (Fin d)))))
      ≤ S.card := by
  rw [finrank_span_tensorV_eq S]
  exact Commons.GeometryOfNumbers.Ellipsoid.finrank_tensor_span_le_card_half S hne hneg

/-- **Dimension of the tangent space.** For a finite set `S` of nonzero vectors closed under
negation, the tangent space `tangentSub S` of the constraint cone has dimension at least
`d(d+1)/2 - |S|/2`; equivalently `d(d+1) ≤ 2 dim (tangentSub S) + |S|`. -/
theorem finrank_tangentSub_ge {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d)))
    (hne : ∀ x ∈ S, x ≠ 0) (hneg : ∀ x ∈ S, -x ∈ S) :
    d * (d + 1) ≤ 2 * Module.finrank ℝ ↥(tangentSub S) + S.card := by
  set W := Submodule.span ℝ (tensorV '' (S : Set (EuclideanSpace ℝ (Fin d)))) with hW
  have hWle : W ≤ symV d := by
    rw [hW, Submodule.span_le]
    rintro v ⟨x, -, rfl⟩
    show (matOf d (tensorV x)).IsSymm
    rw [matOf_tensorV, Matrix.IsSymm.ext_iff]
    intro i j
    simp [Matrix.vecMulVec, mul_comm]
  have hfr : Module.finrank ℝ ↥(tangentSub S)
      = Module.finrank ℝ ↥(symV d) - Module.finrank ℝ ↥W := by
    rw [tangentSub_eq, ← hW]
    exact Commons.Analysis.InnerProductSpace.finrank_inf_orthogonal (symV d) W hWle
  have hsym : Module.finrank ℝ ↥(symV d) = d * (d + 1) / 2 := finrank_symV d
  have hdvd : 2 ∣ d * (d + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self d)
  have hWcard : 2 * Module.finrank ℝ ↥W ≤ S.card :=
    two_mul_finrank_span_tensorV_le_card S hne hneg
  have hmono : Module.finrank ℝ ↥W ≤ Module.finrank ℝ ↥(symV d) := Submodule.finrank_mono hWle
  have h2 : 2 * Module.finrank ℝ ↥(tangentSub S)
      = d * (d + 1) - 2 * Module.finrank ℝ ↥W := by
    rw [hfr, Nat.mul_sub, hsym, Nat.mul_div_cancel' hdvd]
  have hb : 2 * Module.finrank ℝ ↥W ≤ d * (d + 1) := by
    calc 2 * Module.finrank ℝ ↥W ≤ 2 * Module.finrank ℝ ↥(symV d) := by omega
      _ = d * (d + 1) := by rw [hsym, Nat.mul_div_cancel' hdvd]
  omega

end

end Submission.MatSpace
