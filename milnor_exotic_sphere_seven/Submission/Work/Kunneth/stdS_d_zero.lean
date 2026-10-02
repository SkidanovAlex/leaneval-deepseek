import Mathlib
import Submission.Work.Kunneth.ModelContr

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The differential in degree `1` of the singular chain complex of a simplicial set, evaluated on
the generator attached to a `1`-simplex `y`. -/
lemma chainComplex_d_one_gen (X : SSet) (y : X _⦋1⦌) :
    ((X.chainComplex zz).d 1 0).hom ((X.ιChainComplex (R := zz) y).hom 1)
      = (X.ιChainComplex (R := zz) (X.δ 0 y)).hom 1
        - (X.ιChainComplex (R := zz) (X.δ 1 y)).hom 1 := by
  have h := SSet.ιChainComplex_d (X := X) (R := zz) (n := 0) y
  rw [Fin.sum_univ_two] at h
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.mod_succ, Int.reduceNeg, pow_zero,
    pow_one, one_smul, Nat.reduceAdd] at h
  have h' := congrArg (fun (φ : zz ⟶ (X.chainComplex zz).X 0) => φ.hom 1) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  simp at h'
  rw [sub_eq_add_neg]
  exact h'

theorem stdS_d_zero (p : ℕ) (x : ↥((sChain (SdS p)).X 0)) :
    ((sChain (SdS p)).d 1 0).hom (stdS p 0 x) = x - stdPl p 0 x := by
  -- any two elements of the terminal object `X.right` are equal
  have hall : ∀ a b : (SSet.Augmented.stdSimplex.obj ⦋p⦌).right, a = b := fun a b => by
    have hfg : (↾(fun _ : PUnit => a)) = (↾(fun _ : PUnit => b)) :=
      Limits.terminal.hom_ext _ _
    have := congrArg
      (fun (f : PUnit ⟶ (SSet.Augmented.stdSimplex.obj ⦋p⦌).right) => f PUnit.unit) hfg
    simpa using this
  -- the two faces of the cone on a `0`-simplex
  have hface0 : ∀ σ : (SdS p) _⦋0⦌, (SdS p).δ 0 (stdCone p 0 σ) = σ := fun σ =>
    congrArg (fun f => f σ) (SimplicialObject.Augmented.ExtraDegeneracy.s_comp_δ₀ (stdED p) 0)
  have hface1 : ∀ σ : (SdS p) _⦋0⦌, (SdS p).δ 1 (stdCone p 0 σ) = stdPt p := fun σ => by
    have h := SimplicialObject.Augmented.ExtraDegeneracy.s₀_comp_δ₁ (stdED p)
    have hσ : ((stdED p).s 0 ≫ (SSet.Augmented.stdSimplex.obj ⦋p⦌).left.δ 1) σ =
        ((SSet.Augmented.stdSimplex.obj ⦋p⦌).hom.app (Opposite.op ⦋0⦌) ≫ (stdED p).s') σ :=
      congrArg (fun f => f σ) h
    change ((stdED p).s 0 ≫ (SSet.Augmented.stdSimplex.obj ⦋p⦌).left.δ 1) σ = stdPt p
    rw [hσ]
    show (stdED p).s' (((SSet.Augmented.stdSimplex.obj ⦋p⦌).hom.app (Opposite.op ⦋0⦌)) σ) = stdPt p
    unfold stdPt
    exact congrArg (fun z => (stdED p).s' z) (hall _ _)
  -- the identity `d (stdS x) + stdPl x = x` on the generators of degree `0`
  have key : ∀ σ : (SdS p) _⦋0⦌,
      (((sChain (SdS p)).d 1 0).hom.comp (stdS p 0) + stdPl p 0)
          (((SdS p).ιChainComplex (R := zz) σ).hom 1)
        = ((SdS p).ιChainComplex (R := zz) σ).hom 1 := by
    intro σ
    rw [LinearMap.add_apply, LinearMap.comp_apply, stdS_gen p 0 σ]
    rw [chainComplex_d_one_gen (SdS p) (stdCone p 0 σ), hface0 σ, hface1 σ]
    have hpl : stdPl p 0 (((SdS p).ιChainComplex (R := zz) σ).hom 1)
        = ((SdS p).ιChainComplex (R := zz) (stdPt p)).hom 1 := by
      show (LinearMap.toSpanSingleton ℤ ↥((sChain (SdS p)).X 0) (stdBP p))
        ((stdAug p) _) = _
      rw [stdAug_gen p σ, LinearMap.toSpanSingleton_apply_one]
      rfl
    rw [hpl, sub_add_cancel]
  -- hence the corresponding endomorphism is the identity
  have hG : ModuleCat.ofHom
        (((sChain (SdS p)).d 1 0).hom.comp (stdS p 0) + stdPl p 0)
      = 𝟙 ((sChain (SdS p)).X 0) := by
    apply SSet.chainComplex_hom_ext (X := SdS p) (R := zz) (n := 0)
      (T := (sChain (SdS p)).X 0)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    exact key σ
  have h := congrArg (fun (φ : (sChain (SdS p)).X 0 ⟶ (sChain (SdS p)).X 0) => φ.hom x) hG
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at h
  rw [eq_sub_iff_add_eq]
  exact h

end

end Work.Kunneth
