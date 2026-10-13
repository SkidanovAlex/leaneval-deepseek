import Mathlib
import Submission.Work.WilkiesH.Norm.JointDefs
import Submission.Work.WilkiesH.Omega.omega_poly_le
import Submission.Work.WilkiesH.Omega.omega_poly_lt
import Submission.Work.WilG5.Reindex3

/-!
# `normJointGraph σ` is `Ω`-definable

`normJointGraph σ` is the intersection, over the coordinates `i : Fin n`, of the relation
`shapeRelSet i (σ i)` — the pair consisting of the `i`-th coordinate of the image block and
the `i`-th coordinate of the source block satisfies the shape relation of `σ i`
(`shapeRelPoly (σ i) = 0`, a polynomial of total degree at most `2`).

Each relation is a coordinate preimage (`Work.WilG5.coordPre_mem`) of the zero set of that
polynomial, so it lies in `S.Ω (2 + 64 * ((n+n) + 2) + 64) (2 + 32 * ((n+n) + 2) + 32) (n+n)`
uniformly in `i`, and one application of `SOMin.inter` (which costs one format and sums the
degrees over the `n` coordinates) gives the claim.
-/

set_option autoImplicit false
noncomputable section

namespace Work.WilkiesH.Norm

open WilkiesDesign

/-- The shape relation polynomial has total degree at most two, for each of the four shapes
(`w 0 - w 1`, `w 0 + w 1`, `w 0 * w 1 - 1`, `w 0 * w 1 + 1`). -/
private theorem totalDegree_shapeRelPoly_le_two (s : NormShape) : (shapeRelPoly s).totalDegree ≤ 2 := by
  cases s with
  | pos =>
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    simp [MvPolynomial.totalDegree_X]
  | neg =>
    refine (MvPolynomial.totalDegree_add _ _).trans ?_
    simp [MvPolynomial.totalDegree_X]
  | big =>
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [max_le_iff]
    refine ⟨(MvPolynomial.totalDegree_mul _ _).trans ?_, ?_⟩
    · rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    · rw [MvPolynomial.totalDegree_C]; norm_num
  | bigNeg =>
    refine (MvPolynomial.totalDegree_add _ _).trans ?_
    rw [max_le_iff]
    refine ⟨(MvPolynomial.totalDegree_mul _ _).trans ?_, ?_⟩
    · rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    · rw [MvPolynomial.totalDegree_C]; norm_num

/-- The two-variable shape graph set of a shape is `Ω`-definable with format `2` and
degree `2` (the zero set of a polynomial of total degree at most two). -/
private theorem shapeGraphSet_mem (S : SOMin) (s : NormShape) : shapeGraphSet s ∈ S.Ω 2 2 2 :=
  Work.WilkiesH.Omega.omega_mono_D S (S.hyp 2 (shapeRelPoly s)) (totalDegree_shapeRelPoly_le_two s)

/-- Each relation set is `Ω`-definable, with format and degree independent of the shape `s`
and of the coordinate `i`: it is the coordinate preimage, along `shapeCoordMap i : Fin 2 →
Fin (n + n)`, of the zero set of `shapeRelPoly s`. -/
private theorem shapeRelSet_mem (S : SOMin) {n : ℕ} (i : Fin n) (s : NormShape) :
    shapeRelSet i s ∈ S.Ω (2 + 64 * ((n + n) + 2) + 64) (2 + 32 * ((n + n) + 2) + 32)
      (n + n) :=
  Work.WilG5.coordPre_mem (S := S) (m := 2) (N := n + n) (ι := shapeCoordMap i)
    (A := shapeGraphSet s) (shapeGraphSet_mem S s)

/-- The joint graph relation `normJointGraph σ = ⋂ i, shapeRelSet i (σ i)` is `Ω`-definable:
intersecting the `n` relation sets costs one format and adds up their (uniform) degrees. -/
theorem normJointGraph_mem_alt {n : ℕ} (σ : Fin n → Work.WilkiesH.Norm.NormShape) :
    ∃ a b : ℕ, ∀ S : WilkiesDesign.SOMin, Work.WilkiesH.Norm.normJointGraph σ ∈ S.Ω a b (n + n) := by
  refine ⟨2 + 64 * ((n + n) + 2) + 64 + 1, ∑ _ : Fin n, (2 + 32 * ((n + n) + 2) + 32), ?_⟩
  intro S
  exact S.inter (F := 2 + 64 * ((n + n) + 2) + 64) (n := n + n) (k := n)
    (fun _ : Fin n => 2 + 32 * ((n + n) + 2) + 32)
    (fun i : Fin n => shapeRelSet i (σ i))
    (fun i => shapeRelSet_mem S i (σ i))

end Work.WilkiesH.Norm
