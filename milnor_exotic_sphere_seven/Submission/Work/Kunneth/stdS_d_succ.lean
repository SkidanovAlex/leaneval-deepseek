import Mathlib
import Submission.Work.Kunneth.ModelContr

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The contraction identity for the chains of the standard simplex

`stdS p n` is the degree-`+1` map on the singular chains `C_*(Δ[p])` of the standard
`n`-simplex induced by the extra degeneracy `stdCone p n` of the augmented standard simplex.
The present file proves the contraction identity in positive degrees,

`d (stdS p (m+1) x) + stdS p m (d x) = x`,

i.e. that `stdS` together with the augmentation (the deficiency operator `stdPl`, see
`stdS_d_zero`) makes `C_*(Δ[p])` a contractible chain complex.

The proof reduces to the generators `genCh (SdS p) σ` using the universal property of the
coproduct presentation `SSet.chainComplexXCofan` of the simplicial chains, and then uses the
two simplicial identities `δ₀ (stdCone p (m+1) σ) = σ` and
`δ_{i+1} (stdCone p (m+1) σ) = stdCone p m (δ_i σ)` of the extra degeneracy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

universe u

/-- The 0-th face of the cone on a simplex is the simplex itself: `δ₀ ∘ s = 𝟙`. -/
lemma stdCone_δ_zero (p m : ℕ) (σ : (SdS.{u} p) _⦋m+1⦌) :
    (SdS.{u} p).δ (0 : Fin (m+1+2)) (stdCone.{u} p (m+1) σ) = σ := by
  have h : ((stdED.{u} p).s (m+1) ≫ (SdS.{u} p).δ (0 : Fin (m+1+2))) = 𝟙 _ :=
    (stdED.{u} p).s_comp_δ₀ (m+1)
  have h2 := ConcreteCategory.congr_hom h σ
  simp only [stdCone] at h2 ⊢
  rw [CategoryTheory.comp_apply] at h2
  change ConcreteCategory.hom (SimplicialObject.δ (SdS.{u} p) (0 : Fin (m+1+2)))
    (ConcreteCategory.hom ((stdED.{u} p).s (m+1)) σ) = σ at h2
  exact h2

/-- The `(i+1)`-st face of the cone on a simplex is the cone on the `i`-th face:
`δ_{i+1} ∘ s = s ∘ δ_i`. -/
lemma stdCone_δ_succ (p m : ℕ) (σ : (SdS.{u} p) _⦋m+1⦌) (i : Fin (m+2)) :
    (SdS.{u} p).δ i.succ (stdCone.{u} p (m+1) σ)
      = stdCone.{u} p m ((SdS.{u} p).δ i σ) := by
  have h : ((stdED.{u} p).s (m+1) ≫ (SdS.{u} p).δ i.succ)
      = ((SdS.{u} p).δ i ≫ (stdED.{u} p).s m) :=
    (stdED.{u} p).s_comp_δ m i
  have h2 := ConcreteCategory.congr_hom h σ
  simp only [stdCone] at h2 ⊢
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h2
  change ConcreteCategory.hom (SimplicialObject.δ (SdS.{u} p) i.succ)
    (ConcreteCategory.hom ((stdED.{u} p).s (m+1)) σ)
    = ConcreteCategory.hom ((stdED.{u} p).s m)
        (ConcreteCategory.hom (SimplicialObject.δ (SdS.{u} p) i) σ) at h2
  exact h2

/-- The contraction identity on the generator of a simplex of `Δ[p]`. -/
lemma stdS_d_gen (p m : ℕ) (σ : (SdS p) _⦋m+1⦌) :
    ((sChain (SdS p)).d (m+2) (m+1)).hom (stdS p (m+1) (genCh (SdS p) σ))
      + (stdS p m) (((sChain (SdS p)).d (m+1) m).hom (genCh (SdS p) σ))
      = genCh (SdS p) σ := by
  rw [stdS_gen p (m+1) σ]
  rw [d_genCh (SdS p) (m+1) (stdCone p (m+1) σ)]
  rw [d_genCh (SdS p) m σ]
  rw [map_sum]
  simp only [map_zsmul, stdS_gen]
  change (∑ x : Fin (m+1+2), (-1:ℤ)^(x:ℕ) •
          genCh (SdS p) ((SdS p).δ x (stdCone p (m+1) σ)))
      + (∑ x : Fin (m+2), (-1:ℤ)^(x:ℕ) • genCh (SdS p) (stdCone p m ((SdS p).δ x σ)))
      = genCh (SdS p) σ
  have hzero : (-1:ℤ)^((0 : Fin (m+1+2)):ℕ) •
      genCh (SdS p) ((SdS p).δ (0 : Fin (m+1+2)) (stdCone p (m+1) σ))
      = genCh (SdS p) σ := by
    rw [stdCone_δ_zero]; simp
  have hsucc : (∑ i : Fin (m+2), (-1:ℤ)^((i.succ : Fin (m+1+2)):ℕ) •
        genCh (SdS p) ((SdS p).δ i.succ (stdCone p (m+1) σ)))
      = - (∑ i : Fin (m+2), (-1:ℤ)^(i:ℕ) •
          genCh (SdS p) (stdCone p m ((SdS p).δ i σ))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [stdCone_δ_succ p m σ i]
    have hc : (-1:ℤ)^((i.succ : Fin (m+1+2)):ℕ) = -((-1:ℤ)^(i:ℕ)) := by
      rw [Fin.val_succ, pow_succ, mul_neg_one]
    rw [hc, neg_zsmul]
  rw [Fin.sum_univ_succ, hzero, hsucc]
  abel

theorem stdS_d_succ (p m : ℕ) (x : ↥((sChain (SdS p)).X (m+1))) :
    ((sChain (SdS p)).d (m+2) (m+1)).hom (stdS p (m+1) x)
      + (stdS p m) (((sChain (SdS p)).d (m+1) m).hom x) = x := by
  let Φ : (sChain (SdS p)).X (m+1) ⟶ (sChain (SdS p)).X (m+1) :=
    ModuleCat.ofHom (stdS p (m+1)) ≫ (sChain (SdS p)).d (m+2) (m+1)
      + (sChain (SdS p)).d (m+1) m ≫ ModuleCat.ofHom (stdS p m)
  have hΦ : Φ = 𝟙 _ := by
    apply SSet.chainComplex_hom_ext (X := SdS p) (R := zz) (n := m+1)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    change Φ.hom (genCh (SdS p) σ) = genCh (SdS p) σ
    have hstep : Φ.hom (genCh (SdS p) σ)
        = ((sChain (SdS p)).d (m+2) (m+1)).hom (stdS p (m+1) (genCh (SdS p) σ))
          + (stdS p m) (((sChain (SdS p)).d (m+1) m).hom (genCh (SdS p) σ)) := by
      simp only [Φ, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
        LinearMap.comp_apply, ModuleCat.hom_ofHom]
    rw [hstep, stdS_d_gen]
  have h := congrArg (fun (ψ : (sChain (SdS p)).X (m+1) ⟶ (sChain (SdS p)).X (m+1))
    => ψ.hom x) hΦ
  simp only [ModuleCat.hom_id, LinearMap.id_apply] at h
  have hstep : Φ.hom x = ((sChain (SdS p)).d (m+2) (m+1)).hom (stdS p (m+1) x)
      + (stdS p m) (((sChain (SdS p)).d (m+1) m).hom x) := by
    simp only [Φ, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
      LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rw [← hstep]
  exact h

end

end Work.Kunneth
