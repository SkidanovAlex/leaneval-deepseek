/-
The statement of this lemma mentions only `classesK`/`classIncl` (`SSGRoute.PTExt`, from
`Submission.Work.SSGRoute.PTDefs`) and `NK.GlobalCFT.IdeleClassGroup.normClassHom`, so the original
`import Submission.Work.SSGRoute.Sha2Lib.Sha2Shim` (whose closure is a large part of the
`SSGRoute` development) is not needed.  The two ingredients used are

* `Work.SSGRoute.classIncl_isCanonical` — the canonical inclusion `C_k → C_F` is induced by an idèle
  inclusion `φ : 𝕀_k →* 𝕀_F` whose `w`-components are the local embeddings;
* `NK.GlobalCFT.globalCFT_normClassHom_eq_prod_smul` (`Submission.NK.GlobalCFT.H0Computation`) — the
  `H⁰`-computation: the global norm followed by the inclusion is the product of the Galois
  conjugates.

The mathematical content is the identity `∏_{σ ∈ Gal(F/k)} σ·q = incl(N_{F/k} q)` in `C_F`.  The
left-hand side is the norm endomorphism `Rep.norm` of the representation `C_F`, which is the sum
`∑_σ ρ(σ)` of the Galois action; by `NK.GlobalCFT.globalCFT_normClassHom_eq_prod_smul` the product
of the conjugates is `ψ(N_{F/k} q)` for the group homomorphism `ψ : C_k →* C_F` induced by the idèle
inclusion `φ`, and `ψ` agrees with `classIncl k k F` on the image of `𝕀_k` (which is all of `C_k`),
giving the right-hand side of the statement.
-/
import Mathlib
import Submission.Work.SSGRoute.classIncl_isCanonical
import Submission.NK.GlobalCFT.H0Computation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory Work.SSGRoute SSGRoute.PTExt

/- The defeq checks below have to see through `classesK = classGroupRep = Rep.ofDistribMulAction`
(i.e. through `↑(classesK k F) = Additive (C_F)`), which fails at the implicit/reducible
transparency level used by `rw` and by type class search; this is the standard workaround in this
development (see e.g. `Submission.Work.SSGRoute.zz_dev`). -/
set_option backward.isDefEq.respectTransparency false

/-- **The norm on the class group is the inclusion of the global norm.**  For a finite Galois
extension `F/k` of number fields, the norm endomorphism of the Galois module `C_F` (the sum of the
conjugates `q ↦ ∏_{σ} σ·q`) is the inclusion `C_k → C_F` of the global idèle-class norm
`N_{F/k} q`. -/
theorem classGroupRep_norm_eq_classIncl (k F : Type) [Field k] [NumberField k] [Field F]
    [NumberField F] [Algebra k F] [FiniteDimensional k F] [IsGalois k F]
    (q : NK.GlobalCFT.IdeleClassGroup F) :
    (Rep.Hom.hom (classesK k F).norm) (Additive.ofMul q)
      = (Rep.Hom.hom (classIncl k k F))
          (Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.normClassHom k F q)) := by
  classical
  -- write the class `q` as the class of an idèle `x`
  obtain ⟨x, rfl⟩ := NK.GlobalCFT.IdeleClassGroup.mk_surjective F q
  -- `classIncl` is the canonical inclusion, induced by an idèle map `φ`
  obtain ⟨u, hu, φ, hφ, hι⟩ := classIncl_isCanonical k k F
  -- the group homomorphism `ψ : C_k →* C_F` induced by `φ`
  obtain ⟨ψ, hψ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists u hu φ hφ
  -- the `H⁰`-computation: the norm is the product of the conjugates
  have hnorm : ψ (NK.GlobalCFT.IdeleClassGroup.normClassHom k F
        (NK.GlobalCFT.IdeleClassGroup.mk F x))
      = ∏ σ : F ≃ₐ[k] F, σ • (NK.GlobalCFT.IdeleClassGroup.mk F x) :=
    NK.GlobalCFT.globalCFT_normClassHom_eq_prod_smul u hu φ hφ ψ hψ _
  -- the norm endomorphism `Rep.norm` of `C_F` is the sum of the Galois action
  have hnormRep : (Rep.Hom.hom (classesK k F).norm)
        (Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk F x))
      = Additive.ofMul (∏ σ : F ≃ₐ[k] F, σ • (NK.GlobalCFT.IdeleClassGroup.mk F x)) := by
    rw [Rep.norm_apply, Representation.norm]
    rw [LinearMap.sum_apply Finset.univ (fun σ : F ≃ₐ[k] F => (classesK k F).ρ σ)
      (Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk F x))]
    rw [show (∑ σ : F ≃ₐ[k] F, (classesK k F).ρ σ
          (Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.mk F x)))
        = ∑ σ : F ≃ₐ[k] F, Additive.ofMul (σ • NK.GlobalCFT.IdeleClassGroup.mk F x) from
      Finset.sum_congr rfl (fun σ _ =>
        NK.HassePrinciple.classGroupRep_ρ_apply k F σ (NK.GlobalCFT.IdeleClassGroup.mk F x))]
    exact (ofMul_prod Finset.univ
      (fun σ : F ≃ₐ[k] F => σ • NK.GlobalCFT.IdeleClassGroup.mk F x)).symm
  -- on the image of `𝕀_k` the inclusion `classIncl` is `ψ`
  have hRHS : (Rep.Hom.hom (classIncl k k F))
        (Additive.ofMul (NK.GlobalCFT.IdeleClassGroup.normClassHom k F
          (NK.GlobalCFT.IdeleClassGroup.mk F x)))
      = Additive.ofMul (∏ σ : F ≃ₐ[k] F, σ • (NK.GlobalCFT.IdeleClassGroup.mk F x)) := by
    rw [NK.GlobalCFT.IdeleClassGroup.normClassHom_mk]
    rw [hι (NK.GlobalCFT.Idele.normIdeleHom k F x),
      ← hψ (NK.GlobalCFT.Idele.normIdeleHom k F x)]
    rw [← hnorm, NK.GlobalCFT.IdeleClassGroup.normClassHom_mk]
  exact hnormRep.trans hRHS.symm

end Work.SSGRoute.Sha2Lib
