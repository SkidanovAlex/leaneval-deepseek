import Mathlib

namespace Work.WilE7.PadAux

/-- The rank of a block-diagonal matrix `fromBlocks A 0 0 D` is the sum of the ranks of the
diagonal blocks. -/
lemma rank_fromBlocks_zero {R : Type*} [Field R]
    {a b c e : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
    (A : Matrix a b R) (D : Matrix c e R) :
    (Matrix.fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  set f : (b ⊕ e → R) →ₗ[R] (a ⊕ c → R) := (Matrix.fromBlocks A 0 0 D).mulVecLin with hf
  set g : ((b → R) × (e → R)) →ₗ[R] ((a → R) × (c → R)) :=
    A.mulVecLin.prodMap D.mulVecLin with hg
  set e₁ : (b ⊕ e → R) ≃ₗ[R] ((b → R) × (e → R)) :=
    LinearEquiv.sumArrowLequivProdArrow b e R R with he₁
  set e₂ : (a ⊕ c → R) ≃ₗ[R] ((a → R) × (c → R)) :=
    LinearEquiv.sumArrowLequivProdArrow a c R R with he₂
  have hpoint : ∀ x : b ⊕ e → R,
      (e₂ : (a ⊕ c → R) →ₗ[R] ((a → R) × (c → R))) (f x)
        = g ((e₁ : (b ⊕ e → R) →ₗ[R] ((b → R) × (e → R))) x) := by
    intro x
    rw [hf, hg, Matrix.mulVecLin_apply, LinearMap.prodMap_apply,
      Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    have h1 : ((e₁ : (b ⊕ e → R) →ₗ[R] ((b → R) × (e → R))) x).1 = x ∘ Sum.inl := by
      funext i; simp [he₁, LinearEquiv.sumArrowLequivProdArrow_apply_fst]
    have h2 : ((e₁ : (b ⊕ e → R) →ₗ[R] ((b → R) × (e → R))) x).2 = x ∘ Sum.inr := by
      funext i; simp [he₁, LinearEquiv.sumArrowLequivProdArrow_apply_snd]
    rw [h1, h2, Matrix.fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, add_zero, zero_add]
    apply Prod.ext
    · funext i; simp [he₂, LinearEquiv.sumArrowLequivProdArrow_apply_fst]
    · funext i; simp [he₂, LinearEquiv.sumArrowLequivProdArrow_apply_snd]
  have hcomm : (e₂ : (a ⊕ c → R) →ₗ[R] ((a → R) × (c → R))) ∘ₗ f
      = g ∘ₗ (e₁ : (b ⊕ e → R) →ₗ[R] ((b → R) × (e → R))) :=
    LinearMap.ext hpoint
  have hrange_g : LinearMap.range (g ∘ₗ (e₁ : (b ⊕ e → R) →ₗ[R] ((b → R) × (e → R))))
      = LinearMap.range g := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  have hrange_e : LinearMap.range ((e₂ : (a ⊕ c → R) →ₗ[R] ((a → R) × (c → R))) ∘ₗ f)
      = Submodule.map (e₂ : (a ⊕ c → R) →ₗ[R] ((a → R) × (c → R))) (LinearMap.range f) := by
    rw [LinearMap.range_comp]
  have key : Module.finrank R (LinearMap.range g)
      = Module.finrank R (LinearMap.range A.mulVecLin)
        + Module.finrank R (LinearMap.range D.mulVecLin) := by
    rw [hg, LinearMap.range_prodMap]
    rw [(Submodule.prodEquiv (LinearMap.range A.mulVecLin) (LinearMap.range D.mulVecLin)).finrank_eq,
      Module.finrank_prod]
  calc (Matrix.fromBlocks A 0 0 D).rank
      = Module.finrank R (LinearMap.range f) := rfl
    _ = Module.finrank R
          (LinearMap.range ((e₂ : (a ⊕ c → R) →ₗ[R] ((a → R) × (c → R))) ∘ₗ f)) := by
          rw [hrange_e, LinearEquiv.finrank_map_eq]
    _ = Module.finrank R
          (LinearMap.range (g ∘ₗ (e₁ : (b ⊕ e → R) →ₗ[R] ((b → R) × (e → R))))) := by
          rw [hcomm]
    _ = Module.finrank R (LinearMap.range g) := by rw [hrange_g]
    _ = Module.finrank R (LinearMap.range A.mulVecLin)
        + Module.finrank R (LinearMap.range D.mulVecLin) := key
    _ = A.rank + D.rank := by rw [Matrix.rank, Matrix.rank]

theorem rank_block (d q : ℕ) (J : Matrix (Fin q) (Fin q) ℝ) (hJ : J.rank = q)
    (M : Matrix (Fin (d + q)) (Fin (d + q)) ℝ)
    (hM : M.submatrix (finSumFinEquiv (m := d) (n := q)) (finSumFinEquiv (m := d) (n := q))
      = Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) ℝ) 0 0 J) :
    M.rank = d + q := by
  have h := Matrix.rank_submatrix M (finSumFinEquiv (m := d) (n := q))
    (finSumFinEquiv (m := d) (n := q))
  rw [hM, rank_fromBlocks_zero, Matrix.rank_one, Fintype.card_fin, hJ] at h
  exact h.symm

end Work.WilE7.PadAux
