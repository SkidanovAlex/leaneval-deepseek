import Mathlib

/-!
# The commuting family of symmetric operators attached to an abelian subgroup of `O(V)`

For a subgroup `B ≤ O(V)` of the orthogonal group of a real inner product space `V` we consider the
family of self-adjoint (symmetric) operators

* `oSym b = b + b⁻¹`                (indexed by `(b, none)`),
* `blkT (b, some b') = (b - b⁻¹) * (b' - b'⁻¹)` (composition, indexed by `(b, some b')`),

on the index set `↥B × Option ↥B`.  When `B` is abelian these operators pairwise commute, they
commute with every `b ∈ B`, and each of them is symmetric; hence their joint eigenspaces give an
orthogonal decomposition of `V` into `B`-invariant pieces
(`Work.Mostow.blkT_isSymmetric_and_commute`, `Work.Mostow.jointEigenspacesCover`).
-/

namespace Work.Mostow

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The antisymmetric part `b - b⁻¹` of an orthogonal map `b`. -/
def oSk (b : V ≃ₗᵢ[ℝ] V) : V →ₗ[ℝ] V :=
  (b : V →ₗ[ℝ] V) - (((b⁻¹ : V ≃ₗᵢ[ℝ] V)) : V →ₗ[ℝ] V)

/-- The symmetric part `b + b⁻¹` of an orthogonal map `b`. -/
def oSym (b : V ≃ₗᵢ[ℝ] V) : V →ₗ[ℝ] V :=
  (b : V →ₗ[ℝ] V) + (((b⁻¹ : V ≃ₗᵢ[ℝ] V)) : V →ₗ[ℝ] V)

@[simp] lemma oSk_apply (b : V ≃ₗᵢ[ℝ] V) (x : V) :
    oSk b x = b x - ((b⁻¹ : V ≃ₗᵢ[ℝ] V)) x := rfl

@[simp] lemma oSym_apply (b : V ≃ₗᵢ[ℝ] V) (x : V) :
    oSym b x = b x + ((b⁻¹ : V ≃ₗᵢ[ℝ] V)) x := rfl

/-- The commuting family of symmetric operators attached to a subgroup `B ≤ O(V)`. -/
def blkT {B : Subgroup (V ≃ₗᵢ[ℝ] V)} (i : ↥B × Option ↥B) : V →ₗ[ℝ] V :=
  match i with
  | (b, none) => oSym (b : V ≃ₗᵢ[ℝ] V)
  | (b, some b') => oSk (b : V ≃ₗᵢ[ℝ] V) * oSk (b' : V ≃ₗᵢ[ℝ] V)

@[simp] lemma blkT_fst_none {B : Subgroup (V ≃ₗᵢ[ℝ] V)} (b : ↥B) :
    blkT ((b, none) : ↥B × Option ↥B) = oSym (b : V ≃ₗᵢ[ℝ] V) := rfl

@[simp] lemma blkT_fst_some {B : Subgroup (V ≃ₗᵢ[ℝ] V)} (b b' : ↥B) :
    blkT ((b, some b') : ↥B × Option ↥B) = oSk (b : V ≃ₗᵢ[ℝ] V) * oSk (b' : V ≃ₗᵢ[ℝ] V) := rfl

end Work.Mostow
