import Mathlib
import Submission.Work.Mostow.abelianBlockDefs

namespace Work.Mostow

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {B : Subgroup (V ≃ₗᵢ[ℝ] V)}

/-- The underlying linear map of an element of `B`, for bookkeeping only. -/
private def blkG (b : ↥B) : V →ₗ[ℝ] V := (b : V ≃ₗᵢ[ℝ] V)

/-- Elements of an abelian `B ≤ O(V)` have commuting underlying linear maps. -/
private lemma blkG_commute (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (x y : ↥B) :
    Commute (blkG x) (blkG y) := by
  have h : ((x : ↥B) : V ≃ₗᵢ[ℝ] V) * ((y : ↥B) : V ≃ₗᵢ[ℝ] V)
        = ((y : ↥B) : V ≃ₗᵢ[ℝ] V) * ((x : ↥B) : V ≃ₗᵢ[ℝ] V) :=
    hcomm (x : V ≃ₗᵢ[ℝ] V) x.2 (y : V ≃ₗᵢ[ℝ] V) y.2
  show blkG x * blkG y = blkG y * blkG x
  ext z
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have hz := congrFun (congrArg (fun e : V ≃ₗᵢ[ℝ] V => (e : V → V)) h) z
  simpa [blkG, LinearIsometryEquiv.coe_mul] using hz

/-- `oSym b = b + b⁻¹` written with the inverse taken inside `↥B`. -/
private lemma blkG_oSym (b : ↥B) : oSym (b : V ≃ₗᵢ[ℝ] V) = blkG b + blkG b⁻¹ := by
  unfold oSym blkG
  rw [Subgroup.coe_inv]

/-- `oSk b = b - b⁻¹` written with the inverse taken inside `↥B`. -/
private lemma blkG_oSk (b : ↥B) : oSk (b : V ≃ₗᵢ[ℝ] V) = blkG b - blkG b⁻¹ := by
  unfold oSk blkG
  rw [Subgroup.coe_inv]

/-- The symmetric part `b + b⁻¹` is self-adjoint. -/
private lemma blkG_oSym_isSymmetric (b : V ≃ₗᵢ[ℝ] V) : (oSym b).IsSymmetric := by
  intro x y
  simp only [oSym_apply, inner_add_left, inner_add_right]
  have h1 : ⟪b x, y⟫ = ⟪x, b⁻¹ y⟫ := by
    simpa using LinearIsometryEquiv.inner_map_map b x (b⁻¹ y)
  have h2 : ⟪b⁻¹ x, y⟫ = ⟪x, b y⟫ := by
    simpa using LinearIsometryEquiv.inner_map_map b⁻¹ x (b y)
  rw [h1, h2]
  ring

/-- The antisymmetric part `b - b⁻¹` is skew-adjoint. -/
private lemma blkG_oSk_skew (b : V ≃ₗᵢ[ℝ] V) (x y : V) :
    ⟪oSk b x, y⟫ = -⟪x, oSk b y⟫ := by
  simp only [oSk_apply, inner_sub_left, inner_sub_right]
  have h1 : ⟪b x, y⟫ = ⟪x, b⁻¹ y⟫ := by
    simpa using LinearIsometryEquiv.inner_map_map b x (b⁻¹ y)
  have h2 : ⟪b⁻¹ x, y⟫ = ⟪x, b y⟫ := by
    simpa using LinearIsometryEquiv.inner_map_map b⁻¹ x (b y)
  rw [h1, h2]; ring

/-- The product of two commuting skew-adjoint maps is self-adjoint. -/
private lemma blkG_isSymmetric_mul_of_skew {A B : V →ₗ[ℝ] V}
    (hA : ∀ x y, ⟪A x, y⟫ = -⟪x, A y⟫) (hB : ∀ x y, ⟪B x, y⟫ = -⟪x, B y⟫)
    (hAB : Commute A B) : (A * B).IsSymmetric := by
  intro x y
  rw [Module.End.mul_apply, Module.End.mul_apply, hA, hB, neg_neg]
  congr 1
  have h : A * B = B * A := hAB
  have hy := congrArg (fun f : V →ₗ[ℝ] V => f y) h
  simpa [Module.End.mul_apply] using hy.symm

private lemma blkG_commute_oSym_blkG (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (b c : ↥B) : Commute (oSym (b : V ≃ₗᵢ[ℝ] V)) (blkG c) := by
  rw [blkG_oSym]
  exact (blkG_commute hcomm b c).add_left (blkG_commute hcomm b⁻¹ c)

private lemma blkG_commute_oSk_blkG (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (b c : ↥B) : Commute (oSk (b : V ≃ₗᵢ[ℝ] V)) (blkG c) := by
  rw [blkG_oSk]
  exact (blkG_commute hcomm b c).sub_left (blkG_commute hcomm b⁻¹ c)

private lemma blkG_commute_oSym_oSym (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (b c : ↥B) : Commute (oSym (b : V ≃ₗᵢ[ℝ] V)) (oSym (c : V ≃ₗᵢ[ℝ] V)) := by
  rw [blkG_oSym, blkG_oSym]
  exact (blkG_commute_oSym_blkG hcomm b c).add_right (blkG_commute_oSym_blkG hcomm b c⁻¹)

private lemma blkG_commute_oSym_oSk (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (b c : ↥B) : Commute (oSym (b : V ≃ₗᵢ[ℝ] V)) (oSk (c : V ≃ₗᵢ[ℝ] V)) := by
  rw [blkG_oSk]
  exact (blkG_commute_oSym_blkG hcomm b c).sub_right (blkG_commute_oSym_blkG hcomm b c⁻¹)

private lemma blkG_commute_oSym_oSk_mul (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (b c d : ↥B) :
    Commute (oSym (b : V ≃ₗᵢ[ℝ] V)) (oSk (c : V ≃ₗᵢ[ℝ] V) * oSk (d : V ≃ₗᵢ[ℝ] V)) :=
  (blkG_commute_oSym_oSk hcomm b c).mul_right (blkG_commute_oSym_oSk hcomm b d)

private lemma blkG_commute_oSk_oSk (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (b c : ↥B) : Commute (oSk (b : V ≃ₗᵢ[ℝ] V)) (oSk (c : V ≃ₗᵢ[ℝ] V)) := by
  rw [blkG_oSk, blkG_oSk]
  exact ((blkG_commute hcomm b c).sub_left (blkG_commute hcomm b⁻¹ c)).sub_right
        ((blkG_commute hcomm b c⁻¹).sub_left (blkG_commute hcomm b⁻¹ c⁻¹))

private lemma blkG_commute_oSk_oSk_mul (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (b c d e : ↥B) :
    Commute (oSk (b : V ≃ₗᵢ[ℝ] V) * oSk (c : V ≃ₗᵢ[ℝ] V))
            (oSk (d : V ≃ₗᵢ[ℝ] V) * oSk (e : V ≃ₗᵢ[ℝ] V)) :=
  ((blkG_commute_oSk_oSk hcomm b d).mul_left (blkG_commute_oSk_oSk hcomm c d)).mul_right
    ((blkG_commute_oSk_oSk hcomm b e).mul_left (blkG_commute_oSk_oSk hcomm c e))

private lemma blkG_commute_oSk_oSk_blkG (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (b c d : ↥B) :
    Commute (oSk (b : V ≃ₗᵢ[ℝ] V) * oSk (c : V ≃ₗᵢ[ℝ] V)) (blkG d) :=
  (blkG_commute_oSk_blkG hcomm b d).mul_left (blkG_commute_oSk_blkG hcomm c d)

/-- **The family of symmetric operators attached to an abelian `B ≤ O(V)` is symmetric, pairwise
commuting, and commutes with every element of `B`.**

Recall from `Submission.Work.Mostow.abelianBlockDefs`: `oSym b = b + b⁻¹`, `oSk b = b - b⁻¹`, and
`blkT (b, none) = oSym b`, `blkT (b, some b') = oSk b * oSk b'` (composition), on the index type
`↥B × Option ↥B`.

* For the first conjunct: the adjoint of an orthogonal `b` is `b⁻¹`, so `b + b⁻¹` is self-adjoint
  (i.e. `LinearMap.IsSymmetric`); `oSk b` is antisymmetric, and the product of two *commuting*
  antisymmetric maps is symmetric, so `blkT (b, some b')` is symmetric (this uses `hcomm`).
* For the second: every `blkT i` is a sum/product of `b`, `b⁻¹` (`b ∈ B`), and these pairwise
  commute by `hcomm`, so the `blkT i` pairwise commute.
* For the third: same reason, `blkT i` commutes with `(b : V →ₗ[ℝ] V)` for every `b : ↥B`.

Useful facts: `LinearIsometryEquiv.inner_map_map` (⟪b x, b y⟫ = ⟪x, y⟫),
`LinearIsometryEquiv.coe_inv` (`⇑b⁻¹ = ⇑b.symm`), `LinearMap.mul_apply`, `LinearMap.IsSymmetric`,
and `real_inner_comm`.  Expansions of `LinearMap` sums/products are handled by
`LinearMap.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub` followed by `abel`.

This is the input needed for `Work.Mostow.jointEigenspacesCover` (already proved:
`Submission.Work.Mostow.jointEigenspacesCover`). -/
theorem blkT_isSymmetric_and_commute {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {B : Subgroup (V ≃ₗᵢ[ℝ] V)} (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    (∀ i : ↥B × Option ↥B, (blkT i).IsSymmetric) ∧
    (Pairwise (Function.onFun Commute (blkT (V := V) (B := B)))) ∧
    (∀ (i : ↥B × Option ↥B) (b : ↥B), Commute (blkT i) ((b : ↥B) : V →ₗ[ℝ] V)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, _ | b'⟩
    · exact blkG_oSym_isSymmetric (b : V ≃ₗᵢ[ℝ] V)
    · exact blkG_isSymmetric_mul_of_skew (blkG_oSk_skew (b : V ≃ₗᵢ[ℝ] V))
        (blkG_oSk_skew (b' : V ≃ₗᵢ[ℝ] V)) (blkG_commute_oSk_oSk hcomm b b')
  · intro i j _
    rcases i with ⟨b, _ | b'⟩ <;> rcases j with ⟨c, _ | c'⟩
    · exact blkG_commute_oSym_oSym hcomm b c
    · exact blkG_commute_oSym_oSk_mul hcomm b c c'
    · exact (blkG_commute_oSym_oSk_mul hcomm c b b').symm
    · exact blkG_commute_oSk_oSk_mul hcomm b b' c c'
  · rintro ⟨b, _ | b'⟩ c
    · exact blkG_commute_oSym_blkG hcomm b c
    · exact blkG_commute_oSk_oSk_blkG hcomm b b' c

end Work.Mostow
