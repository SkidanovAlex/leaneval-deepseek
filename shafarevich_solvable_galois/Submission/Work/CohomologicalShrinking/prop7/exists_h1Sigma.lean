import Mathlib
import Submission.Work.CohomologicalShrinking.Prop7
import Submission.Work.CohomologicalShrinking.Prop5
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.prop7

open scoped TensorProduct

/-!
# The surjection `σ` of Proposition 7

This file constructs, for every pair `τ = (i,j)` and every finitely generated `𝔽_p[G]`-module
`T`, the `𝔽_p`-linear *surjection*

`σ(m) : (F(m)/F(m)²)^{⊗(j+1)} ⊗ T ↠ F(m)/F(m)² ⊗ (E(m,τ) ⊗ T)`

of Schmidt–Wingberg's Proposition 7 — the combination of the universal coefficient formula
`H₁(F(m)/ν, E⊗T) ≅ F(m)/F(m)² ⊗ E ⊗ T` with the surjection `θ_τ` of Proposition 5 and the
associativity of the tensor power — together with its naturality in the rank `m` along the maps
induced by surjective `G`-operator homomorphisms `Φ : F(m) → F(n)`.

Concretely `σ(m)` sends a pure tensor
`x₀ ⊗ x₁ ⊗ ⋯ ⊗ x_j ⊗ t` to `x₀ ⊗ (θ_τ(x₁ ⊗ ⋯ ⊗ x_j) ⊗ t)`; the only content is the
re-association of the tensor power `(⨂^{(j+1)} Q)` with `Q ⊗ (⨂^j Q)`, which is provided by
`splitFirst` and is natural in `Q` by `splitFirst_natural`.

This supplies the hypotheses `σ`, `hσ`, `hσnat` of `exists_shrinking_H1` of `Prop7.lean`.
-/

/-! ## Splitting off the first tensor factor -/

/-- The type equivalence `Fin (j+1) ≃ Fin 1 ⊕ Fin j` splitting off the first index. -/
def finSplit (j : ℕ) : Fin (j+1) ≃ Fin 1 ⊕ Fin j :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

lemma finSplit_symm_inl_zero (j : ℕ) : (finSplit j).symm (Sum.inl 0) = 0 := by
  simp [finSplit, finCongr, Fin.castAdd]

lemma finSplit_symm_inr_succ (j : ℕ) (i : Fin j) : (finSplit j).symm (Sum.inr i) = i.succ := by
  ext; simp [finSplit, finCongr, Fin.natAdd, Fin.succ]; omega

/-- The `R`-linear equivalence `(⨂^{(j+1)} Q) ⊗ T ≃ Q ⊗ ((⨂^j Q) ⊗ T)` isolating the first
tensor factor.  It is the composite of the reindexing `Fin (j+1) ≃ Fin 1 ⊕ Fin j`, the
splitting `⨂^{1+j} ≃ ⨂^1 ⊗ ⨂^j` of `PiTensorProduct.tmulEquiv`, the associativity of the
binary tensor product and the identification `⨂^1 Q ≃ Q`. -/
noncomputable def splitFirst (R : Type*) [CommRing R] (j : ℕ) (Q T : Type*)
    [AddCommGroup Q] [Module R Q] [AddCommGroup T] [Module R T] :
    (PiTensorProduct R (fun _ : Fin (j+1) => Q)) ⊗[R] T ≃ₗ[R]
      Q ⊗[R] (PiTensorProduct R (fun _ : Fin j => Q) ⊗[R] T) :=
  (LinearEquiv.rTensor T (PiTensorProduct.reindex R (fun _ : Fin (j+1) => Q) (finSplit j))).trans
  ((LinearEquiv.rTensor T (PiTensorProduct.tmulEquiv R Q).symm).trans
  ((TensorProduct.assoc R (PiTensorProduct R (fun _ : Fin 1 => Q))
      (PiTensorProduct R (fun _ : Fin j => Q)) T).trans
  (LinearEquiv.rTensor (PiTensorProduct R (fun _ : Fin j => Q) ⊗[R] T)
      (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 => Q) 0))))

/-- The value of `splitFirst` on a pure tensor: the first factor is isolated. -/
lemma splitFirst_tprod (R : Type*) [CommRing R] (j : ℕ) (Q T : Type*)
    [AddCommGroup Q] [Module R Q] [AddCommGroup T] [Module R T]
    (x : Fin (j+1) → Q) (t : T) :
    splitFirst R j Q T (PiTensorProduct.tprod R x ⊗ₜ[R] t)
      = x 0 ⊗ₜ[R] (PiTensorProduct.tprod R (fun i : Fin j => x i.succ) ⊗ₜ[R] t) := by
  simp only [splitFirst, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
    PiTensorProduct.reindex_tprod, PiTensorProduct.tmulEquiv_symm_apply,
    TensorProduct.assoc_tmul, PiTensorProduct.subsingletonEquiv_apply_tprod,
    finSplit_symm_inl_zero, finSplit_symm_inr_succ]

/-- `splitFirst` is natural in the first module: the two ways of splitting off the first factor
after applying a linear map `q` agree. -/
lemma splitFirst_natural (R : Type*) [CommRing R] (j : ℕ) (Q Q' T : Type*)
    [AddCommGroup Q] [Module R Q] [AddCommGroup Q'] [Module R Q']
    [AddCommGroup T] [Module R T] (q : Q →ₗ[R] Q') :
    (TensorProduct.map q ((PiTensorProduct.map (fun _ : Fin j => q)).rTensor T)) ∘ₗ
        (splitFirst R j Q T : _ →ₗ[R] _)
      = (splitFirst R j Q' T : _ →ₗ[R] _) ∘ₗ
        ((PiTensorProduct.map (fun _ : Fin (j+1) => q)).rTensor T) := by
  apply TensorProduct.curry_injective
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  ext t
  simp only [LinearMap.compMultilinearMap_apply, TensorProduct.curry_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [splitFirst_tprod]
  simp only [LinearMap.rTensor_tmul, PiTensorProduct.map_tprod, TensorProduct.map_tmul]
  rw [splitFirst_tprod]

/-- Splitting `TensorProduct.map q (X ∘ Y)` in the second factor, the first factor carrying
`q`. -/
lemma tmap_id_comp (R : Type*) [CommRing R] {Q Q' A A' B : Type*}
    [AddCommGroup Q] [Module R Q] [AddCommGroup Q'] [Module R Q']
    [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    [AddCommGroup B] [Module R B]
    (q : Q →ₗ[R] Q') (X : A →ₗ[R] B) (Y : A' →ₗ[R] A) :
    TensorProduct.map q (X ∘ₗ Y)
      = TensorProduct.map (LinearMap.id : Q' →ₗ[R] Q') X ∘ₗ TensorProduct.map q Y := by
  conv_lhs => rw [← LinearMap.id_comp q]
  rw [← TensorProduct.map_comp]

/-! ## The family `σ` -/

/-- The map `σ(m) : (F(m)/F(m)²)^{⊗(j+1)} ⊗ T → F(m)/F(m)² ⊗ (E(m,τ) ⊗ T)` sending
`x₀ ⊗ ⋯ ⊗ x_j ⊗ t` to `x₀ ⊗ (θ_τ(x₁ ⊗ ⋯ ⊗ x_j) ⊗ t)`. -/
noncomputable def h1SigmaFamily (p : ℕ) [NeZero p] (G : Type*) [Group G] {i j : ℕ}
    (D : Work.CohomologicalShrinking.Prop5Data p G i j) (T : Type*) [AddCommGroup T]
    [Module (ZMod p) T] (m : ℕ) :
    (PiTensorProduct (ZMod p)
        (fun _ : Fin (j+1) => Work.CohomologicalShrinking.squareQuotient p G m)) ⊗[ZMod p] T
        →ₗ[ZMod p]
      Work.CohomologicalShrinking.squareQuotient p G m ⊗[ZMod p]
        (Work.CohomologicalShrinking.E p G m i j ⊗[ZMod p] T) :=
  (TensorProduct.map (LinearMap.id) ((D.θ m).rTensor T)) ∘ₗ
    (splitFirst (ZMod p) j (Work.CohomologicalShrinking.squareQuotient p G m) T : _ →ₗ[ZMod p] _)

/-! ## The main theorem -/

theorem exists_h1Sigma (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (D : Work.CohomologicalShrinking.Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T] :
    ∃ σ : ∀ m : ℕ, TensorProduct (ZMod p)
          (PiTensorProduct (ZMod p) (fun _ : Fin (j + 1) => Work.CohomologicalShrinking.squareQuotient p G m)) T →ₗ[ZMod p]
        TensorProduct (ZMod p) (Work.CohomologicalShrinking.squareQuotient p G m)
          (TensorProduct (ZMod p) (Work.CohomologicalShrinking.E p G m i j) T),
      (∀ m : ℕ, Function.Surjective (σ m)) ∧
      (∀ ⦃m n : ℕ⦄ (Φ : Work.CohomologicalShrinking.OperatorMap G m n),
        (Work.CohomologicalShrinking.OperatorMap.h1Map p G T Φ).comp (σ m)
          = (σ n).comp ((PiTensorProduct.map
              (fun _ : Fin (j + 1) => Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)).rTensor T)) := by
  classical
  refine ⟨fun m => h1SigmaFamily p G D T m, ?_, ?_⟩
  · -- Surjectivity: `σ m` is the composite of a bijection with `id ⊗ (θ ⊗ id)`.
    intro m
    simp only [h1SigmaFamily, LinearMap.coe_comp]
    exact (TensorProduct.map_surjective (fun x => ⟨x, rfl⟩)
      (LinearMap.rTensor_surjective T (D.θ_surjective m))).comp
      (splitFirst (ZMod p) j (Work.CohomologicalShrinking.squareQuotient p G m) T).surjective
  · -- Naturality in the rank, from the naturality of `θ` (Proposition 5) and of `splitFirst`.
    intro m n Φ
    have key := splitFirst_natural (ZMod p) j
      (Work.CohomologicalShrinking.squareQuotient p G m)
      (Work.CohomologicalShrinking.squareQuotient p G n) T
      (Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)
    have hfm : (TensorProduct.map (Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)
        ((Work.CohomologicalShrinking.gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)) ∘ₗ
      (TensorProduct.map (LinearMap.id) ((D.θ m).rTensor T))
      = (TensorProduct.map (LinearMap.id) ((D.θ n).rTensor T)) ∘ₗ
        (TensorProduct.map (Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)
          ((PiTensorProduct.map (fun _ : Fin j =>
            Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)).rTensor T)) := by
      calc (TensorProduct.map (Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)
            ((Work.CohomologicalShrinking.gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)) ∘ₗ
          (TensorProduct.map (LinearMap.id) ((D.θ m).rTensor T))
          = TensorProduct.map (Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)
              (((Work.CohomologicalShrinking.gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) ∘ₗ
                ((D.θ m).rTensor T)) := by
            rw [← TensorProduct.map_comp, LinearMap.comp_id]
        _ = TensorProduct.map (Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)
              (((Work.CohomologicalShrinking.gradedMapLin p Φ.toHom Φ.surjective i j) ∘ₗ
                (D.θ m)).rTensor T) := by
            rw [LinearMap.rTensor_comp]
        _ = TensorProduct.map (Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)
              (((D.θ n) ∘ₗ (PiTensorProduct.map fun _ : Fin j =>
                Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)).rTensor T) := by
            rw [← D.θ_natural Φ.toHom Φ.surjective Φ.equivariant]
        _ = TensorProduct.map (Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)
              (((D.θ n).rTensor T) ∘ₗ ((PiTensorProduct.map fun _ : Fin j =>
                Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective).rTensor T)) := by
            rw [LinearMap.rTensor_comp]
        _ = TensorProduct.map (LinearMap.id) ((D.θ n).rTensor T) ∘ₗ
            (TensorProduct.map (Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective)
              ((PiTensorProduct.map fun _ : Fin j =>
                Work.CohomologicalShrinking.quotMapLin p G Φ.toHom Φ.surjective).rTensor T)) := by
            rw [tmap_id_comp]
    simp only [h1SigmaFamily, Work.CohomologicalShrinking.OperatorMap.h1Map]
    rw [← LinearMap.comp_assoc, hfm]
    simp only [LinearMap.comp_assoc]
    rw [key]

end Work.CohomologicalShrinking.prop7
