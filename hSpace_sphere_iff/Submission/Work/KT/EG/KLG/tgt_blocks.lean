import Mathlib
import Submission.Work.KT.EG.KLG.kappa_bott_defs

namespace Work.KT.EG.KLG

/-!
# `Work.KT.EG.KLG.tgt_blocks` — the block form of the disc targets

The disc targets `upTgt X A B = upFrame X A B * upRet X A B` and
`dnTgt X A B = dnFrame X A B * dnRet X A B` are the products of the explicit frame
`![A; B ⊗ (1+s, ζ)]` (resp. `![A; B ⊗ (ζ̄, 1+s)]`) with the explicit retraction
`[A, B(1+s)⁻¹, 0]` (resp. `[A, ζB, s²(1+s)⁻¹B]`).  For `A`, `B` an orthogonal pair of
idempotents (`A² = A`, `B² = B`, `A B = B A = 0`) the products therefore take the block
diagonal form

* `upTgt A B = A ⊕ (B ⊗ R₁)`,  `R₁ = !![1, 0; ζ(1+s)⁻¹, 0]`,
* `dnTgt A B = A ⊕ (B ⊗ R₂)`,  `R₂ = !![ζζ̄, ζ̄ s²(1+s)⁻¹; (1+s)ζ, s²]`,

which is the statement proved here.  The proof is a direct `4 × 4` block computation;
the scalar identities `1·(1+s)⁻¹ = 1` and `(1+s)·(1+s)⁻¹ = 1` on the disc are
`Work.KT.Fund.KL.one_add_zs_mul_zsinv` (and its consequences).

The block `(inr (a,α), inr (b,β))` of, say, `upTgt` is
`∑ k (B a k · c_α) · (B k b · d_β) = (B·B) a b · (c_α d_β) = B a b · R₁ α β`,
where `c_α = if α = 0 then 1+s else ζ` is the `α`-th entry of the frame column `(1+s, ζ)`
and `d_β = if β = 0 then (1+s)⁻¹ else 0` is the `β`-th entry of the retraction row.
The four scalar identities `c_α d_β = R₁ α β` (resp. `= R₂ α β`) are checked by `fin_cases`.
-/

theorem tgt_blocks (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) C(X × Work.KT.Ball ℂ, ℂ))
    (hA : A * A = A) (hB : B * B = B) (hAB : A * B = 0) (hBA : B * A = 0) :
    (Work.KT.EG.KLG.upTgt X A B =
        Matrix.fromBlocks A 0 0 (Matrix.kroneckerMap (· * ·) B (Work.KT.EG.KLG.R1 X))) ∧
      (Work.KT.EG.KLG.dnTgt X A B =
        Matrix.fromBlocks A 0 0 (Matrix.kroneckerMap (· * ·) B (Work.KT.EG.KLG.R2 X))) := by
  constructor
  · -- upper disc
    rw [upTgt]
    ext i j
    rcases i with a | ⟨a, α⟩ <;> rcases j with b | ⟨b, β⟩
    · -- `(A, A)`-block: `∑ k A a k · A k b = (A·A) a b = A a b`
      simp only [Matrix.mul_apply, upFrame, upRet, Matrix.fromBlocks_apply₁₁]
      rw [← Matrix.mul_apply, hA]
    · -- `(A, B ⊗ ·)`-block: `∑ k A a k · (B k b · d_β) = (A·B) a b · d_β = 0`
      simp only [Matrix.mul_apply, upFrame, upRet, Matrix.fromBlocks_apply₁₂]
      have h1 : ∀ j, A a j * (B j b * (if β = 0 then Work.KT.Fund.KL.zsinv X else 0))
          = (A a j * B j b) * (if β = 0 then Work.KT.Fund.KL.zsinv X else 0) :=
        fun j => (mul_assoc _ _ _).symm
      simp only [h1]
      rw [← Finset.sum_mul, ← Matrix.mul_apply, hAB]
      simp [Matrix.zero_apply]
    · -- `(B ⊗ ·, A)`-block: `∑ k (B a k · c_α) · A k b = c_α · (B·A) a b = 0`
      simp only [Matrix.mul_apply, upFrame, upRet, Matrix.fromBlocks_apply₂₁]
      have h1 : ∀ j,
          (B a j * (if α = 0 then 1 + Work.KT.Fund.KL.zs X else Work.KT.Fund.KL.zc X))
            * A j b
          = (if α = 0 then 1 + Work.KT.Fund.KL.zs X else Work.KT.Fund.KL.zc X)
            * (B a j * A j b) := fun j => by ring
      simp only [h1]
      rw [← Finset.mul_sum, ← Matrix.mul_apply, hBA]
      simp [Matrix.zero_apply]
    · -- `(B ⊗ ·, B ⊗ ·)`-block: `∑ k (B a k · c_α)(B k b · d_β) = B a b · (c_α d_β) = B a b · R₁ α β`
      simp only [Matrix.mul_apply, upFrame, upRet, Matrix.fromBlocks_apply₂₂,
        Matrix.kroneckerMap_apply]
      have h1 : ∀ j,
          (B a j * (if α = 0 then 1 + Work.KT.Fund.KL.zs X else Work.KT.Fund.KL.zc X))
            * (B j b * (if β = 0 then Work.KT.Fund.KL.zsinv X else 0))
          = (B a j * B j b)
            * ((if α = 0 then 1 + Work.KT.Fund.KL.zs X else Work.KT.Fund.KL.zc X)
              * (if β = 0 then Work.KT.Fund.KL.zsinv X else 0)) := fun j => by ring
      simp only [h1]
      rw [← Finset.sum_mul, ← Matrix.mul_apply, hB]
      congr 1
      fin_cases α <;> fin_cases β <;>
        simp [R1, Work.KT.Fund.KL.one_add_zs_mul_zsinv]
  · -- lower disc
    rw [dnTgt]
    ext i j
    rcases i with a | ⟨a, α⟩ <;> rcases j with b | ⟨b, β⟩
    · simp only [Matrix.mul_apply, dnFrame, dnRet, Matrix.fromBlocks_apply₁₁]
      rw [← Matrix.mul_apply, hA]
    · simp only [Matrix.mul_apply, dnFrame, dnRet, Matrix.fromBlocks_apply₁₂]
      have h1 : ∀ j, A a j * (B j b * (if β = 0 then Work.KT.Fund.KL.zc X
          else Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zsinv X))
          = (A a j * B j b) * (if β = 0 then Work.KT.Fund.KL.zc X
            else Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zsinv X) :=
        fun j => (mul_assoc _ _ _).symm
      simp only [h1]
      rw [← Finset.sum_mul, ← Matrix.mul_apply, hAB]
      simp [Matrix.zero_apply]
    · simp only [Matrix.mul_apply, dnFrame, dnRet, Matrix.fromBlocks_apply₂₁]
      have h1 : ∀ j,
          (B a j * (if α = 0 then Work.KT.Fund.KL.zcb X else 1 + Work.KT.Fund.KL.zs X))
            * A j b
          = (if α = 0 then Work.KT.Fund.KL.zcb X else 1 + Work.KT.Fund.KL.zs X)
            * (B a j * A j b) := fun j => by ring
      simp only [h1]
      rw [← Finset.mul_sum, ← Matrix.mul_apply, hBA]
      simp [Matrix.zero_apply]
    · simp only [Matrix.mul_apply, dnFrame, dnRet, Matrix.fromBlocks_apply₂₂,
        Matrix.kroneckerMap_apply]
      have h1 : ∀ j,
          (B a j * (if α = 0 then Work.KT.Fund.KL.zcb X else 1 + Work.KT.Fund.KL.zs X))
            * (B j b * (if β = 0 then Work.KT.Fund.KL.zc X
                else Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zsinv X))
          = (B a j * B j b)
            * ((if α = 0 then Work.KT.Fund.KL.zcb X else 1 + Work.KT.Fund.KL.zs X)
              * (if β = 0 then Work.KT.Fund.KL.zc X
                else Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zsinv X)) :=
        fun j => by ring
      simp only [h1]
      rw [← Finset.sum_mul, ← Matrix.mul_apply, hB]
      rw [show (if α = 0 then Work.KT.Fund.KL.zcb X else 1 + Work.KT.Fund.KL.zs X)
            * (if β = 0 then Work.KT.Fund.KL.zc X
              else Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zsinv X)
          = R2 X α β from by
        fin_cases α <;> fin_cases β <;> simp [R2]
        · ring
        · ring
        · rw [show (1 + Work.KT.Fund.KL.zs X)
              * (Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zsinv X)
            = ((1 + Work.KT.Fund.KL.zs X) * Work.KT.Fund.KL.zsinv X)
              * (Work.KT.Fund.KL.zs X * Work.KT.Fund.KL.zs X) by ring,
            Work.KT.Fund.KL.one_add_zs_mul_zsinv, one_mul]]

end Work.KT.EG.KLG
