import Mathlib
import Submission.Work.KT.Defs

/-!
# The rank of a block sum

`Work.KT.Mat.sum p q` is the block sum of two square matrices over `ℂ`, in the sense of `K₀`:
it is `p ⊕ q` (`Matrix.fromBlocks p 0 0 q`, reindexed along `Fin n ⊕ Fin m ≃ Fin (n + m)`).

This file computes its rank: `rank (p ⊕ q) = rank p + rank q`.  No idempotency is needed.

The proof is the standard one: the underlying linear map `mulVecLin` of a block diagonal matrix
decomposes, under the canonical identification `(Fin n ⊕ Fin m → 𝕜) ≃ (Fin n → 𝕜) × (Fin m → 𝕜)`,
as the product of the two `mulVecLin`s; hence the range is the product of the two ranges, and the
dimension of a product of submodules is the sum of the dimensions.

* `submoduleProdEquiv` — the (missing in Mathlib) linear equivalence `↥(p.prod q) ≃ₗ ↥p × ↥q`.
* `finrank_prod_submodule` — `finrank (p.prod q) = finrank p + finrank q`.
* `Matrix.mulVecLin_fromBlocks` — the decomposition of `mulVecLin` of a block diagonal matrix.
* `Matrix.rank_fromBlocks` — `rank (fromBlocks A 0 0 B) = rank A + rank B`.
-/

namespace Work.KT.Rank

open Matrix Module

/-! ## `finrank` of a product of submodules -/

section SubmoduleProd

variable {R M₂ M₃ : Type*} [Semiring R] [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid M₃] [Module R M₃]

/-- The canonical linear equivalence `↥(p.prod q) ≃ₗ ↥p × ↥q` between the product of two
submodules (as a submodule of the product) and the product of the two submodules. -/
def submoduleProdEquiv (p : Submodule R M₂) (q : Submodule R M₃) :
    ↥(p.prod q) ≃ₗ[R] ↥p × ↥q where
  toFun x := (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
  invFun y := ⟨(y.1.1, y.2.1), Submodule.mem_prod.mpr ⟨y.1.2, y.2.2⟩⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_smul' c x := by ext <;> rfl

variable {𝕜 : Type*} [Field 𝕜]
variable {A₁ B₁ : Type*} [AddCommGroup A₁] [Module 𝕜 A₁] [AddCommGroup B₁] [Module 𝕜 B₁]

/-- The dimension of a product of submodules is the sum of the dimensions. -/
lemma finrank_prod_submodule [FiniteDimensional 𝕜 A₁] [FiniteDimensional 𝕜 B₁]
    (p : Submodule 𝕜 A₁) (q : Submodule 𝕜 B₁) :
    Module.finrank 𝕜 ↥(p.prod q) = Module.finrank 𝕜 ↥p + Module.finrank 𝕜 ↥q := by
  have hfree : Module.Free 𝕜 ↥p := Module.Free.of_divisionRing 𝕜 ↥p
  have hfree' : Module.Free 𝕜 ↥q := Module.Free.of_divisionRing 𝕜 ↥q
  rw [LinearEquiv.finrank_eq (submoduleProdEquiv p q), Module.finrank_prod]

end SubmoduleProd

/-! ## Rank of a block diagonal matrix -/

section BlockRank

variable {𝕜 : Type*} [Field 𝕜] {n m : ℕ}

/-- `mulVecLin` of a block diagonal matrix is the product of the two `mulVecLin`s, transported
across the canonical identification `(Fin n ⊕ Fin m → 𝕜) ≃ (Fin n → 𝕜) × (Fin m → 𝕜)`. -/
lemma mulVecLin_fromBlocks (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin m) (Fin m) 𝕜) :
    (Matrix.fromBlocks A 0 0 B).mulVecLin =
      (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) 𝕜 𝕜).symm.toLinearMap ∘ₗ
      ((A.mulVecLin.prodMap B.mulVecLin) ∘ₗ
        (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) 𝕜 𝕜).toLinearMap) := by
  apply LinearMap.ext
  intro v
  have h1 : (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) 𝕜 𝕜 v).1 = v ∘ Sum.inl :=
    funext fun a => LinearEquiv.sumArrowLequivProdArrow_apply_fst v a
  have h2 : (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) 𝕜 𝕜 v).2 = v ∘ Sum.inr :=
    funext fun a => LinearEquiv.sumArrowLequivProdArrow_apply_snd v a
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec,
    LinearMap.prodMap_apply, LinearEquiv.coe_toLinearMap, zero_mulVec, add_zero, h1, h2]
  funext i
  rcases i with i | i <;>
    simp [LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

/-- **The rank of a block diagonal matrix is the sum of the ranks.** -/
theorem rank_fromBlocks (A : Matrix (Fin n) (Fin n) 𝕜) (B : Matrix (Fin m) (Fin m) 𝕜) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  have hrange : ((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) 𝕜 𝕜).symm.toLinearMap ∘ₗ
      ((A.mulVecLin.prodMap B.mulVecLin) ∘ₗ
        (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) 𝕜 𝕜).toLinearMap)).range
      = (A.mulVecLin.range.prod B.mulVecLin.range).map
        (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) 𝕜 𝕜).symm.toLinearMap := by
    rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      LinearMap.range_prodMap]
  calc (Matrix.fromBlocks A 0 0 B).rank
      = Module.finrank 𝕜 ↥((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) 𝕜 𝕜).symm.toLinearMap ∘ₗ
          ((A.mulVecLin.prodMap B.mulVecLin) ∘ₗ
            (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) 𝕜 𝕜).toLinearMap)).range := by
        rw [Matrix.rank, mulVecLin_fromBlocks]
    _ = Module.finrank 𝕜 ↥((A.mulVecLin.range.prod B.mulVecLin.range).map
          (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) 𝕜 𝕜).symm.toLinearMap) := by
        rw [hrange]
    _ = Module.finrank 𝕜 ↥(A.mulVecLin.range.prod B.mulVecLin.range) :=
        LinearEquiv.finrank_map_eq (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) 𝕜 𝕜).symm _
    _ = A.rank + B.rank := by
        rw [finrank_prod_submodule, Matrix.rank, Matrix.rank]

end BlockRank

/-- The rank of a block sum `p ⊕ q` (`Work.KT.Mat.sum` in `Submission/Work/KT/Defs.lean`) is the
sum of the ranks.  No idempotency is needed. -/
theorem rank_sum (n m : ℕ) (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin m) (Fin m) ℂ) :
    ((Work.KT.Mat.sum (⟨n, P⟩ : Work.KT.Mat ℂ) (⟨m, Q⟩ : Work.KT.Mat ℂ)).2).rank
      = P.rank + Q.rank := by
  show (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P 0 0 Q)).rank
      = P.rank + Q.rank
  rw [Matrix.rank_reindex, rank_fromBlocks]

end Work.KT.Rank
