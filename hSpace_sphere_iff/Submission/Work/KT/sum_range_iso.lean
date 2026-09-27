import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.mvLin

/-!
# `Work.KT.sum_range_iso`

The image of the block sum `p ⊕ 1_k` is the product of the image of `p` with `k` free coordinates.

All of this is elementary matrix algebra over a ring `R` whose commutativity is an explicit
hypothesis `hcomm` (the project's convention: subrings such as `Work.KT.FiberProd` carry only a
`Ring` instance, and `Work.KT.mvLin` is the replacement for Mathlib's `Matrix.mulVecLin`).  With
`B = fromBlocks p 0 0 1` acting on `Fin N ⊕ Fin k → R` and
`A = reindex e e B` acting on `Fin (N+k) → R` (`e = finSumFinEquiv`), the two steps are

* the image of `B *ᵥ ·` is `(image of p *ᵥ ·) × (Fin k → R)`, i.e. a vector `w` is `B *ᵥ u` exactly
  when its first block is in the image of `p` and its second block is arbitrary;
* reindexing does not change the image: `A *ᵥ v = (B *ᵥ (v ∘ e)) ∘ e.symm`.

The equivalence is exhibited explicitly as the inverse of the obvious map
`(a, b) ↦ (i ↦ Sum.elim a b (e.symm i))`.
-/

namespace Work.KT

open Matrix

noncomputable section

variable {R : Type} [Ring R]

namespace SumRangeIso

/-! ## Pointwise `mulVec` lemmas -/

/-- Pointwise `mulVec` of a reindexed matrix. -/
lemma mulVec_reindex_apply {α γ : Type} [Fintype α] [Fintype γ] (e : α ≃ γ)
    (B : Matrix α α R) (v : γ → R) (i : γ) :
    ((Matrix.reindex e e B) *ᵥ v) i = (B *ᵥ (v ∘ ⇑e)) (e.symm i) := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv B v (⇑e.symm) e.symm]
  rfl

/-- `mulVec` of a block matrix on `Sum.elim a b`. -/
lemma mulVec_fromBlocks_elim {n k : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (D : Matrix (Fin k) (Fin k) R) (a : Fin n → R) (b : Fin k → R) :
    (Matrix.fromBlocks A 0 0 D) *ᵥ (Sum.elim a b) = Sum.elim (A *ᵥ a) (D *ᵥ b) := by
  rw [Matrix.fromBlocks_mulVec]
  funext s
  rcases s with i | j <;> simp

/-- `mulVec` of a reindexed block-diagonal matrix, as a function. -/
lemma mulVec_reindex_eq {n k : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (e : Fin n ⊕ Fin k ≃ Fin (n + k)) (v : Fin (n + k) → R) :
    (Matrix.reindex e e (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin k) (Fin k) R))) *ᵥ v
      = fun i => (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin k) (Fin k) R) *ᵥ (v ∘ ⇑e))
          (e.symm i) := by
  funext i
  rw [mulVec_reindex_apply]

/-- `mulVec` of a reindexed block-diagonal matrix on `Sum.elim v b ∘ e.symm`. -/
lemma mulVec_reindex_elim {n k : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (e : Fin n ⊕ Fin k ≃ Fin (n + k)) (v : Fin n → R) (b : Fin k → R) :
    (Matrix.reindex e e (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin k) (Fin k) R))) *ᵥ
        (fun i => Sum.elim v b (e.symm i))
      = fun i => Sum.elim (A *ᵥ v) b (e.symm i) := by
  funext i
  rw [mulVec_reindex_apply]
  have hfun : (fun i => Sum.elim v b (e.symm i)) ∘ ⇑e = Sum.elim v b := by
    funext j
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [hfun, mulVec_fromBlocks_elim, Matrix.one_mulVec]

/-! ## The product-to-sum assembly map -/

/-- The inverse of the block-sum decomposition: a pair `(a, b)`, with `a` in the image of `p`, is
sent to the vector `i ↦ Sum.elim a b (e.symm i)`. -/
def prodToSum (hcomm : ∀ x y : R, x * y = y * x) {N k : ℕ}
    (p : Matrix (Fin N) (Fin N) R) (e : Fin N ⊕ Fin k ≃ Fin (N + k)) :
    ((mvLin hcomm p).range × (Fin k → R)) →ₗ[R] (Fin (N + k) → R) where
  toFun := fun x i => Sum.elim x.1.1 x.2 (e.symm i)
  map_add' := by
    intro x y
    funext i
    show Sum.elim (x + y).1.1 (x + y).2 (e.symm i)
      = Sum.elim x.1.1 x.2 (e.symm i) + Sum.elim y.1.1 y.2 (e.symm i)
    rcases e.symm i with a | b <;> simp
  map_smul' := by
    intro c x
    funext i
    show Sum.elim (c • x).1.1 (c • x).2 (e.symm i)
      = c * Sum.elim x.1.1 x.2 (e.symm i)
    rcases e.symm i with a | b <;> simp

lemma prodToSum_apply (hcomm : ∀ x y : R, x * y = y * x) {N k : ℕ}
    (p : Matrix (Fin N) (Fin N) R) (e : Fin N ⊕ Fin k ≃ Fin (N + k))
    (x : (mvLin hcomm p).range × (Fin k → R)) :
    prodToSum hcomm p e x = fun i => Sum.elim x.1.1 x.2 (e.symm i) := rfl

end SumRangeIso

/-! ## The theorem -/

/-- The image of the block sum `p ⊕ 1_k` is the product of the image of `p` with `k` free
coordinates. -/
theorem sum_range_iso {R : Type} [Ring R] (hcomm : ∀ x y : R, x * y = y * x)
    {N k : ℕ} (p : Matrix (Fin N) (Fin N) R) :
    Nonempty ((mvLin hcomm ((Mat.sum ⟨N, p⟩ (Mat.one R k)).2)).range ≃ₗ[R]
      ((mvLin hcomm p).range × (Fin k → R))) := by
  let e : Fin N ⊕ Fin k ≃ Fin (N + k) := finSumFinEquiv
  change Nonempty ((mvLin hcomm (Matrix.reindex e e
      (Matrix.fromBlocks p 0 0 (1 : Matrix (Fin k) (Fin k) R)))).range ≃ₗ[R]
    ((mvLin hcomm p).range × (Fin k → R)))
  have hmem : ∀ x : (mvLin hcomm p).range × (Fin k → R),
      SumRangeIso.prodToSum hcomm p e x ∈
        (mvLin hcomm (Matrix.reindex e e
          (Matrix.fromBlocks p 0 0 (1 : Matrix (Fin k) (Fin k) R)))).range := by
    rintro ⟨a, b⟩
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp a.2
    refine LinearMap.mem_range.mpr ⟨fun i => Sum.elim v b (e.symm i), ?_⟩
    show (mvLin hcomm (Matrix.reindex e e
        (Matrix.fromBlocks p 0 0 (1 : Matrix (Fin k) (Fin k) R))))
        (fun i => Sum.elim v b (e.symm i)) = SumRangeIso.prodToSum hcomm p e (a, b)
    rw [mvLin_apply, SumRangeIso.prodToSum_apply, SumRangeIso.mulVec_reindex_elim]
    have hv' : p *ᵥ v = a.1 := hv
    show (fun i => Sum.elim (p *ᵥ v) b (e.symm i)) = fun i => Sum.elim a.1 b (e.symm i)
    rw [hv']
  have hinj : Function.Injective (SumRangeIso.prodToSum hcomm p e) := by
    intro x y hxy
    have h2 : Sum.elim x.1.1 x.2 = Sum.elim y.1.1 y.2 := by
      funext s
      rcases s with i | j
      · have h := congrFun hxy (e (Sum.inl i))
        simpa [SumRangeIso.prodToSum_apply] using h
      · have h := congrFun hxy (e (Sum.inr j))
        simpa [SumRangeIso.prodToSum_apply] using h
    refine Prod.ext (Subtype.ext ?_) ?_
    · funext i
      simpa using congrFun h2 (Sum.inl i)
    · funext j
      simpa using congrFun h2 (Sum.inr j)
  have hsurj : Function.Surjective ((SumRangeIso.prodToSum hcomm p e).codRestrict
      (mvLin hcomm (Matrix.reindex e e
        (Matrix.fromBlocks p 0 0 (1 : Matrix (Fin k) (Fin k) R)))).range hmem) := by
    intro y
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp y.2
    have hsplit : (u ∘ ⇑e) = Sum.elim (u ∘ ⇑e ∘ Sum.inl) (u ∘ ⇑e ∘ Sum.inr) := by
      funext s
      rcases s with i | j <;> rfl
    refine ⟨((⟨p *ᵥ (u ∘ ⇑e ∘ Sum.inl), ⟨u ∘ ⇑e ∘ Sum.inl, rfl⟩⟩ :
        (mvLin hcomm p).range), u ∘ ⇑e ∘ Sum.inr), ?_⟩
    apply Subtype.ext
    show SumRangeIso.prodToSum hcomm p e
      ((⟨p *ᵥ (u ∘ ⇑e ∘ Sum.inl), ⟨u ∘ ⇑e ∘ Sum.inl, rfl⟩⟩ :
        (mvLin hcomm p).range), u ∘ ⇑e ∘ Sum.inr) = y.1
    rw [SumRangeIso.prodToSum_apply]
    show (fun i => Sum.elim (p *ᵥ (u ∘ ⇑e ∘ Sum.inl)) (u ∘ ⇑e ∘ Sum.inr) (e.symm i)) = y.1
    rw [← hu, mvLin_apply, SumRangeIso.mulVec_reindex_eq, hsplit,
      SumRangeIso.mulVec_fromBlocks_elim, Matrix.one_mulVec]
  have hinj' : Function.Injective
      ((SumRangeIso.prodToSum hcomm p e).codRestrict
        (mvLin hcomm (Matrix.reindex e e
          (Matrix.fromBlocks p 0 0 (1 : Matrix (Fin k) (Fin k) R)))).range hmem) := by
    intro x y hxy
    have hxy' : SumRangeIso.prodToSum hcomm p e x = SumRangeIso.prodToSum hcomm p e y :=
      congrArg (fun z : (mvLin hcomm (Matrix.reindex e e
          (Matrix.fromBlocks p 0 0 (1 : Matrix (Fin k) (Fin k) R)))).range =>
        (z : Fin (N + k) → R)) hxy
    exact hinj hxy'
  exact ⟨(LinearEquiv.ofBijective
    ((SumRangeIso.prodToSum hcomm p e).codRestrict _ hmem) ⟨hinj', hsurj⟩).symm⟩

end

end Work.KT
