import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.StemsB.RelChainsR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

/-!
# Splitting the long exact sequence of a pair into `coker × ker` (with `ℚ`-coefficients)

For a pair `(X,A)` and any coefficient ring `R`, the relative singular chains
`C_*(X,A;R) = C_*(X;R)/C_*(A;R)` fit into the short exact sequence of chain complexes

`0 → C_*(A;R) → C_*(X;R) → C_*(X,A;R) → 0`,

whose long exact sequence in homology (`Work.StemsB.relChainsR_exact₁/₂/₃`) reads

`⋯ → H_m(A) --f--> H_m(X) --g--> H_m(X,A) --δ--> H_{m-1}(A) --f'--> H_{m-1}(X) → ⋯`.

Over a *field* (here `ℚ`) every short exact sequence of vector spaces splits, so the middle
term of the exact fragment `coker f → H_m(X,A) → ker f'` decomposes as
`H_m(X,A) ≅ coker f × ker f'`.  That is `lesSplitPair`.  The linear-algebra input is
`linearEquiv_prod_of_exact` below; it only uses exactness at the three spots.
-/

noncomputable section

/-- **Linear algebra splitting lemma.**  Given an exact fragment of `ℚ`-vector spaces
`A --f--> B --g--> C --δ--> A' --f'--> B'` (exactness at `B`, `C` and `A'`), the vector space `C`
is the direct product of the cokernel of `f` and the kernel of `f'`.  The only thing used about
`ℚ` is that every subspace has a complement (`quotient_prod_linearEquiv`). -/
theorem linearEquiv_prod_of_exact {A B C A' B' : Type}
    [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    [AddCommGroup C] [Module ℚ C] [AddCommGroup A'] [Module ℚ A'] [AddCommGroup B'] [Module ℚ B']
    (f : A →ₗ[ℚ] B) (g : B →ₗ[ℚ] C) (δ : C →ₗ[ℚ] A') (f' : A' →ₗ[ℚ] B')
    (h₁ : LinearMap.range f = LinearMap.ker g)
    (h₂ : LinearMap.range g = LinearMap.ker δ)
    (h₃ : LinearMap.range δ = LinearMap.ker f') :
    Nonempty (C ≃ₗ[ℚ] (B ⧸ LinearMap.range f) × (LinearMap.ker f')) := by
  -- `C ≅ (C ⧸ ker δ) × ker δ`
  obtain ⟨e₂⟩ := quotient_prod_linearEquiv (K := ℚ) (LinearMap.ker δ)
  -- `B ⧸ range f ≅ range g = ker δ`
  have eC : (B ⧸ LinearMap.range f) ≃ₗ[ℚ] LinearMap.ker δ :=
    (Submodule.quotEquivOfEq _ _ h₁) ≪≫ₗ (LinearMap.quotKerEquivRange g) ≪≫ₗ
      (LinearEquiv.ofEq _ _ h₂)
  -- `C ⧸ ker δ ≅ range δ = ker f'`
  have e₃ : (C ⧸ LinearMap.ker δ) ≃ₗ[ℚ] LinearMap.ker f' :=
    (LinearMap.quotKerEquivRange δ) ≪≫ₗ (LinearEquiv.ofEq _ _ h₃)
  exact ⟨e₂.symm ≪≫ₗ (e₃.prodCongr eC.symm) ≪≫ₗ LinearEquiv.prodComm ℚ _ _⟩

set_option maxHeartbeats 1000000 in
theorem lesSplitPair (X : TopCat) (A : Set X) (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (((Work.StemsB.relChainsR ℚ X A).homology m) ≅
      ModuleCat.of ℚ (↥(CategoryTheory.Limits.cokernel
          (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ X A) m))
        × ↥(CategoryTheory.Limits.kernel
          (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ X A) (m-1))))) := by
  -- write `m = k + 1`, so that the index `m - 1` is `k` definitionally
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  -- the three exactness spots of the pair sequence
  have h₁ := (Work.StemsB.relChainsR_exact₂ ℚ X A (k+1)).moduleCat_range_eq_ker
  have h₂ := (Work.StemsB.relChainsR_exact₃ ℚ X A k).moduleCat_range_eq_ker
  have h₃ := (Work.StemsB.relChainsR_exact₁ ℚ X A k).moduleCat_range_eq_ker
  obtain ⟨e₀⟩ := linearEquiv_prod_of_exact
      (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ X A) (k+1)).hom
      (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.StemsB.relChainsRIncl ℚ X A)) (k+1)).hom
      (Work.StemsB.relChainsRδ ℚ X A k).hom
      (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ X A) k).hom h₁ h₂ h₃
  -- identify the abstract `cokernel`/`kernel` with the quotients appearing above
  have eC := (ModuleCat.cokernelIsoRangeQuotient
    (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ X A) (k+1))).toLinearEquiv
  have eK := (ModuleCat.kernelIsoKer
    (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ X A) k)).toLinearEquiv
  exact ⟨(e₀.trans (eC.prodCongr eK).symm).toModuleIso⟩

end

end Work.Serre.DiscPair
