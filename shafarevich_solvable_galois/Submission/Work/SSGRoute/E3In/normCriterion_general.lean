import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.phi1_defs
import Submission.Work.SSGRoute.CFTSide.cyclicNormCriterion_classesK
import Submission.Work.SSGRoute.classIncl_isCanonical
import Submission.Work.SSGRoute.groupCohomology_levelInf_nat
import Submission.Work.SSGRoute.classIncl_inflation_injective
import Submission.Work.SSGRoute.Sha2Lib.character_factors
import Submission.Work.SSGRoute.Sha2Lib.exists_classIncl_preimage_fixed
import Submission.Work.SSGRoute.Sha2Lib.H1pi_character_ne_zero
import Submission.Work.SSGRoute.Sha2Lib.galF_cyclic_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The general-level cyclic norm criterion (reduction to the prime-degree subfield)

This file proves `Work.SSGRoute.E3In.normCriterion_general`: `E3`'s CFT input.  For `L/k` finite
Galois, `F` an intermediate field with `[F : k] = p` (so `Gal(F/k) ≅ ℤ/p`), `a ∈ C_L` fixed by
`Gal(L/k)` and a nonzero character `g : Gal(L/k) → ℤ/p` whose kernel is exactly the fixing subgroup
of `F`: if the cup-product class `a ∪ δg` vanishes, then `a` is the inclusion of a norm from `F`,
i.e. `a ∈ classIncl_{F→L}(N_{F/k} C_F)`.

The proof reduces to the proved prime-degree cyclic criterion `cyclicNormCriterion_classesK` at the
smaller level `F/k`:

* `g` descends to `Gal(F/k)` (`Sha2Lib.character_factors`);
* `a` is in the image of `classIncl k F L`, with a `Gal(F/k)`-fixed preimage
  (`Sha2Lib.exists_classIncl_preimage_fixed`);
* the pairing `a ∪ δ g` at the level `L` equals the inflation (along `Gal(L/k) → Gal(F/k)` and
  `classIncl`) of the pairing at the level `F` (`groupCohomology_levelInf_nat`), using the cocycle
  identity `H1pi_inflation_eq` and the compatibility `powHomCls_classIncl_compat`;
* the inflation `H²(Gal(F/k), C_F) → H²(Gal(L/k), C_L)` is injective
  (`classIncl_inflation_injective`), so the level-`L` vanishing is equivalent to the level-`F`
  vanishing, to which the prime-degree cyclic criterion applies.
-/

namespace Work.SSGRoute.E3In

open CategoryTheory
open SSGRoute.PTExt

noncomputable section

/-- **Inflation of a character class**: the `H¹`-class of the character `g = gF ∘ galRes` is the
inflation (along `galRes` with the trivial-module coefficient identity) of the `H¹`-class of
`gF`. -/
theorem H1pi_inflation_eq (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime] (F : IntermediateField k L) [FiniteDimensional k F] [NumberField F]
    [IsGalois k F]
    (g : Additive (L ≃ₐ[k] L) →+ ZMod p)
    (gF : Additive (F ≃ₐ[k] F) →+ ZMod p)
    (hgF : ∀ σ : L ≃ₐ[k] L, g (Additive.ofMul σ) = gF (Additive.ofMul (galRes k F L σ))) :
    groupCohomology.H1π (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p))
        ⟨g ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom
          (A := Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) g⟩
      = (groupCohomology.map (galRes k F L) (trivResInv (galRes k F L) (ZMod p)) 1).hom
          (groupCohomology.H1π (Rep.trivial Coeff (F ≃ₐ[k] F) (ZMod p))
            ⟨gF ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom
              (A := Rep.trivial Coeff (F ≃ₐ[k] F) (ZMod p)) gF⟩) := by
  let zG : groupCohomology.cocycles₁ (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) :=
    ⟨g ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom
      (A := Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) g⟩
  let zF : groupCohomology.cocycles₁ (Rep.trivial Coeff (F ≃ₐ[k] F) (ZMod p)) :=
    ⟨gF ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom
      (A := Rep.trivial Coeff (F ≃ₐ[k] F) (ZMod p)) gF⟩
  have hcoc : groupCohomology.mapCocycles₁ (galRes k F L)
      (trivResInv (galRes k F L) (ZMod p)) zF = zG := by
    apply Subtype.ext
    refine (Work.SSGRoute.coe_mapCocycles₁_trivResInv_aux (galRes k F L) p zF).trans ?_
    funext h
    show gF (Additive.ofMul (galRes k F L h)) = g (Additive.ofMul h)
    exact (hgF h).symm
  have hmap := groupCohomology.H1π_comp_map_apply (galRes k F L)
    (trivResInv (galRes k F L) (ZMod p)) zF
  rw [hcoc] at hmap
  exact hmap.symm

/-- The trivial-module identification `trivRes f V` is the identity on carriers. -/
lemma trivRes_hom_apply {G H : Type} [Group G] [Group H] (f : H →* G) (V : Type)
    [AddCommGroup V] [Module Coeff V] (x : V) :
    (Rep.Hom.hom (trivRes f V)) x = x := rfl

/-- **Compatibility of the coefficient class `powHomCls` with the inclusion `C_F → C_L`**: if
`a = classIncl k F L aF` and `aF` is `Gal(F/k)`-fixed, then the `Gal(L/k)`-module map `1 ↦ a` is
the trivial-module identification `trivRes` followed by (the restriction of `1 ↦ aF`) followed by
`classIncl k F L`. -/
theorem powHomCls_classIncl_compat (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime] (F : IntermediateField k L) [FiniteDimensional k F] [NumberField F]
    [IsGalois k F] (a : classesK k L) (hafix : ∀ σ : L ≃ₐ[k] L, (classesK k L).ρ σ a = a)
    (aF : classesK k F) (haFfix : ∀ τ : F ≃ₐ[k] F, (classesK k F).ρ τ aF = aF)
    (haFeq : (classIncl k F L).hom aF = a) :
    Phi1.powHomCls k L a hafix
      = CategoryTheory.CategoryStruct.comp (trivRes (galRes k F L) Coeff)
          (CategoryTheory.CategoryStruct.comp
            ((Rep.resFunctor (galRes k F L)).map (Phi1.powHomCls k F aF haFfix))
            (classIncl k F L)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro n
  change (Rep.Hom.hom (Phi1.powHomCls k L a hafix)) n = (Rep.Hom.hom
    (CategoryTheory.CategoryStruct.comp (trivRes (galRes k F L) Coeff)
      (CategoryTheory.CategoryStruct.comp
        ((Rep.resFunctor (galRes k F L)).map (Phi1.powHomCls k F aF haFfix))
        (classIncl k F L)))) n
  rw [Rep.hom_comp, Rep.hom_comp]
  simp only [Representation.IntertwiningMap.comp_apply]
  rw [trivRes_hom_apply, Rep.resMap_hom_apply, Phi1.powHomCls_apply, Phi1.powHomCls_apply,
    map_smul, haFeq]

/-- **The general-level cyclic norm criterion** (`C_L` coefficients, `E3`'s CFT input). -/
theorem normCriterion_general (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) [Fact p.Prime] (F : IntermediateField k L) [FiniteDimensional k F] [IsGalois k F] [NumberField F] (hF : Module.finrank k F = p) (a : SSGRoute.PTExt.classesK k L) (hafix : ∀ σ : L ≃ₐ[k] L, (SSGRoute.PTExt.classesK k L).ρ σ a = a) (g : Additive (L ≃ₐ[k] L) →+ ZMod p) (hne : g ≠ 0) (hker : ∀ σ : L ≃ₐ[k] L, g (Additive.ofMul σ) = 0 ↔ σ ∈ F.fixingSubgroup) (hvan : groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L)) (SSGRoute.Phi1.powHomCls k L a hafix) 2 ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom (groupCohomology.H1π (Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p)) ⟨g ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom (A := Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p)) g⟩)) = 0) : ∃ b : SSGRoute.PTExt.classesK k F, SSGRoute.PTExt.classIncl k F L ((SSGRoute.PTExt.classesK k F).norm.hom b) = a := by
  -- (1) `g` descends to `Gal(F/k)`
  obtain ⟨gF, hgFne, hgF⟩ := Work.SSGRoute.Sha2Lib.character_factors k L p F g hne hker
  -- (2) `a` has a `Gal(F/k)`-fixed preimage under `classIncl`
  obtain ⟨aF, haFfix, haFeq⟩ :=
    Work.SSGRoute.Sha2Lib.exists_classIncl_preimage_fixed k F L a hafix
  -- (3) the coefficient class `1 ↦ a` is `trivRes ≫ (res (1 ↦ aF) ≫ classIncl)`
  have hpow := powHomCls_classIncl_compat k L p F a hafix aF haFfix haFeq
  -- (4) the `H¹`-classes
  let zG : groupCohomology.cocycles₁ (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) :=
    ⟨g ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom
      (A := Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) g⟩
  let zF : groupCohomology.cocycles₁ (Rep.trivial Coeff (F ≃ₐ[k] F) (ZMod p)) :=
    ⟨gF ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom
      (A := Rep.trivial Coeff (F ≃ₐ[k] F) (ZMod p)) gF⟩
  let hG : groupCohomology (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 1 :=
    groupCohomology.H1π (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) zG
  let hFi : groupCohomology (Rep.trivial Coeff (F ≃ₐ[k] F) (ZMod p)) 1 :=
    groupCohomology.H1π (Rep.trivial Coeff (F ≃ₐ[k] F) (ZMod p)) zF
  have hvan' : (groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L)) (Phi1.powHomCls k L a hafix) 2).hom
      ((groupCohomology.δ (Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom hG) = 0 := hvan
  have hhG : hG
      = (groupCohomology.map (galRes k F L) (trivResInv (galRes k F L) (ZMod p)) 1).hom hFi :=
    H1pi_inflation_eq k L p F g gF hgF
  -- (5) level naturality of the pairing
  have hlevel := Work.SSGRoute.groupCohomology_levelInf_nat k F L p
    (Phi1.powHomCls k F aF haFfix) hFi
  -- the inner `trivRes`-twist is the identity on cohomology
  have htriv : trivRes (galRes k F L) Coeff = 𝟙 (unitRep (L ≃ₐ[k] L)) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro n
    rfl
  have hmapE : groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
      (CategoryTheory.CategoryStruct.comp (trivRes (galRes k F L) Coeff)
        (CategoryTheory.CategoryStruct.comp
          ((Rep.resFunctor (galRes k F L)).map (Phi1.powHomCls k F aF haFfix))
          (classIncl k F L))) 2
      = groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
          (A := Rep.res (galRes k F L) (unitRep (F ≃ₐ[k] F)))
          (CategoryTheory.CategoryStruct.comp
            ((Rep.resFunctor (galRes k F L)).map (Phi1.powHomCls k F aF haFfix))
            (classIncl k F L)) 2 := by
    rw [htriv]
    exact congrArg (fun φ => groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L)) φ 2)
      (CategoryTheory.Category.id_comp
        (CategoryTheory.CategoryStruct.comp
          ((Rep.resFunctor (galRes k F L)).map (Phi1.powHomCls k F aF haFfix))
          (classIncl k F L)))
  rw [hpow] at hvan'
  have hvan2 : (groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
        (CategoryTheory.CategoryStruct.comp
          ((Rep.resFunctor (galRes k F L)).map (Phi1.powHomCls k F aF haFfix))
          (classIncl k F L)) 2).hom
      ((groupCohomology.δ (Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom hG) = 0 := by
    have hc := congrArg (fun (m : groupCohomology (unitRep (L ≃ₐ[k] L)) 2
          ⟶ groupCohomology (classesK k L) 2) =>
        (ModuleCat.Hom.hom m)
          ((groupCohomology.δ (Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom hG)) hmapE
    exact hc.symm.trans hvan'
  rw [hhG] at hvan2
  have hmain : (groupCohomology.map (galRes k F L) (classIncl k F L) 2).hom
      ((groupCohomology.map (MonoidHom.id (F ≃ₐ[k] F)) (Phi1.powHomCls k F aF haFfix) 2).hom
        ((groupCohomology.δ (Phi1.coeffSES_shortExact (F ≃ₐ[k] F) p) 1 2 rfl).hom hFi)) = 0 :=
    hlevel.symm.trans hvan2
  -- (6) injectivity of the level inflation
  have hzero : (groupCohomology.map (MonoidHom.id (F ≃ₐ[k] F))
        (Phi1.powHomCls k F aF haFfix) 2).hom
      ((groupCohomology.δ (Phi1.coeffSES_shortExact (F ≃ₐ[k] F) p) 1 2 rfl).hom hFi) = 0 :=
    (Work.SSGRoute.classIncl_inflation_injective k F L) (by
      change (ModuleCat.Hom.hom (groupCohomology.map (galRes k F L) (classIncl k F L) 2))
          ((ModuleCat.Hom.hom
              (groupCohomology.map (MonoidHom.id (F ≃ₐ[k] F)) (Phi1.powHomCls k F aF haFfix) 2))
            ((ModuleCat.Hom.hom
              (groupCohomology.δ (Phi1.coeffSES_shortExact (F ≃ₐ[k] F) p) 1 2 rfl)) hFi))
        = (ModuleCat.Hom.hom (groupCohomology.map (galRes k F L) (classIncl k F L) 2)) 0
      rw [hmain]
      simp)
  -- (7) the prime-degree cyclic criterion at the level `F`
  have hcyc : IsCyclic (F ≃ₐ[k] F) := (Work.SSGRoute.Sha2Lib.galF_cyclic_card k L p F hF).1
  have hcard : Nat.card (F ≃ₐ[k] F) = p := (Work.SSGRoute.Sha2Lib.galF_cyclic_card k L p F hF).2
  have hFne : hFi ≠ 0 :=
    Work.SSGRoute.Sha2Lib.H1pi_character_ne_zero (F ≃ₐ[k] F) p gF hgFne
  obtain ⟨b, hb⟩ :=
    ((Work.SSGRoute.CFTSide.cyclicNormCriterion_classesK k F p hcyc hcard aF haFfix
        hFi hFne).mp hzero)
  exact ⟨b, by rw [hb]; exact haFeq⟩

end

end Work.SSGRoute.E3In
