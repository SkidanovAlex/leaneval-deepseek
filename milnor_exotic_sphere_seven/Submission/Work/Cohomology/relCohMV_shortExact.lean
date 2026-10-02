import Mathlib
import Submission.Work.Cohomology.RelMVDefs
import Submission.Work.Cohomology.relMV_shortExact
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Cohomology.relSmallCochains_iso
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.mvCochainShortExact
import Submission.Work.Cohomology.relCohMVDefs
import Submission.Work.Cohomology.existsLeftInverseOfKerEqRange
import Submission.Work.Cohomology.relCohMVF_injective
import Submission.Work.Cohomology.relCohMVG_ker_le_range

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative Mayer–Vietoris short exact sequence of cochain complexes

Dualising the chain level relative Mayer–Vietoris sequence
(`Work.Cohomology.relMV_shortExact`) gives the sequence of cochain complexes

`0 ⟶ C^*(X,A) --relCohMVF--> C^*(U, U ∩ A) ⊞ C^*(V, V ∩ A) --relCohMVG--> C^*(U ∩ V, U ∩ V ∩ A) ⟶ 0`

whose short exactness is `Work.Cohomology.relCohMV_shortExact`.  The two maps and their component
identities are in `Submission/Work/Cohomology/relCohMVDefs.lean`; the degreewise injectivity of
`relCohMVF` is `Work.Cohomology.relCohMVF_injective` and the degreewise exactness in the middle is
`Work.Cohomology.relCohMVG_ker_le_range`.  The remaining degreewise input, the surjectivity of
`relCohMVG`, is `relCohMVG_surjective` below: it is the statement that every `ℤ`-valued functional
on `C^{U,V}_n(U ∩ V, U ∩ V ∩ A)` extends along the chain level injection
`relMVChainBeta₁ ⊞ relMVChainBeta₂`, which holds because that injection is split (it is the first
map of a degreewise short exact sequence whose third term is projective,
`Work.Cohomology.existsLeftInverseOfKerEqRange`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

open DualBiprod

variable (X : TopCat) (A U V : Set X)

/-! ## Surjectivity of the second cohomological relative Mayer–Vietoris map -/

/-- **The second map of the relative cohomological Mayer–Vietoris sequence is degreewise
surjective.** -/
theorem relCohMVG_surjective (n : ℕ) :
    Function.Surjective (ModuleCat.Hom.hom ((relCohMVG X A U V).f n)) := by
  haveI hproj : Module.Projective ℤ ↥((relMVTopC X A U V).X n) := relSmallTopProjective X U V A n
  obtain ⟨r, hr⟩ := existsLeftInverseOfKerEqRange
    (ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n))
    (ModuleCat.Hom.hom ((relMVChainRight X A U V).f n))
    (relMVChainDegreewise_injective X A U V n)
    (relMVChainDegreewise_surjective X A U V n)
    (relMVChainDegreewise_ker X A U V n)
  have hr_apply : ∀ a, r ((ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n)) a) = a := fun a =>
    LinearMap.congr_fun hr a
  -- the two components of the retraction
  let ρ₁ : (relMVUU X A U V).X n →ₗ[ℤ] (relMVUV X A U V).X n :=
    r.comp (ModuleCat.Hom.hom
      ((biprod.inl : relMVUU X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V).f n))
  let ρ₂ : (relMVVV X A U V).X n →ₗ[ℤ] (relMVUV X A U V).X n :=
    r.comp (ModuleCat.Hom.hom
      ((biprod.inr : relMVVV X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V).f n))
  -- they retract the two components of the first chain map
  have hkey : ∀ a, ρ₁ ((ModuleCat.Hom.hom ((relMVChainBeta₁ X A U V).f n)) a)
      + ρ₂ ((ModuleCat.Hom.hom ((relMVChainBeta₂ X A U V).f n)) a) = a := by
    intro a
    have hβ₁ : (ModuleCat.Hom.hom ((relMVChainBeta₁ X A U V).f n)) a
        = (ModuleCat.Hom.hom ((biprod.fst : relMVUU X A U V ⊞ relMVVV X A U V ⟶
            relMVUU X A U V).f n)) ((ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n)) a) := by
      rw [relMVChainBeta₁_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    have hβ₂ : (ModuleCat.Hom.hom ((relMVChainBeta₂ X A U V).f n)) a
        = (ModuleCat.Hom.hom ((biprod.snd : relMVUU X A U V ⊞ relMVVV X A U V ⟶
            relMVVV X A U V).f n)) ((ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n)) a) := by
      rw [relMVChainBeta₂_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [hβ₁, hβ₂]
    show r ((ModuleCat.Hom.hom ((biprod.inl : relMVUU X A U V ⟶
            relMVUU X A U V ⊞ relMVVV X A U V).f n))
          ((ModuleCat.Hom.hom ((biprod.fst : relMVUU X A U V ⊞ relMVVV X A U V ⟶
            relMVUU X A U V).f n)) ((ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n)) a)))
        + r ((ModuleCat.Hom.hom ((biprod.inr : relMVVV X A U V ⟶
            relMVUU X A U V ⊞ relMVVV X A U V).f n))
          ((ModuleCat.Hom.hom ((biprod.snd : relMVUU X A U V ⊞ relMVVV X A U V ⟶
            relMVVV X A U V).f n)) ((ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n)) a))) = a
    rw [← map_add, show
      (ModuleCat.Hom.hom ((biprod.inl : relMVUU X A U V ⟶
            relMVUU X A U V ⊞ relMVVV X A U V).f n))
          ((ModuleCat.Hom.hom ((biprod.fst : relMVUU X A U V ⊞ relMVVV X A U V ⟶
            relMVUU X A U V).f n)) ((ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n)) a))
        + (ModuleCat.Hom.hom ((biprod.inr : relMVVV X A U V ⟶
            relMVUU X A U V ⊞ relMVVV X A U V).f n))
          ((ModuleCat.Hom.hom ((biprod.snd : relMVUU X A U V ⊞ relMVVV X A U V ⟶
            relMVVV X A U V).f n)) ((ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n)) a))
        = (ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n)) a from
      biprodTotal_apply_chain (relMVUU X A U V) (relMVVV X A U V) n
        ((relMVChainLeft X A U V).f n a)]
    exact hr_apply a
  -- the transpose of `(β₁, β₂)` is surjective
  intro φ
  refine ⟨(biprod.inl : dualComplex ℤ (relMVUU X A U V) ⟶
        dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n
          (dualMapHom (ModuleCat.ofHom ρ₁) φ)
      + (biprod.inr : dualComplex ℤ (relMVVV X A U V) ⟶
        dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n
          (dualMapHom (ModuleCat.ofHom ρ₂) φ), ?_⟩
  have hG1 : (ModuleCat.Hom.hom ((relCohMVG X A U V).f n))
      ((biprod.inl : dualComplex ℤ (relMVUU X A U V) ⟶
        dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n
          (dualMapHom (ModuleCat.ofHom ρ₁) φ))
      = (dualMapHom ((relMVChainBeta₁ X A U V).f n)).hom
          (dualMapHom (ModuleCat.ofHom ρ₁) φ) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, relCohMVG_inl]
    rfl
  have hG2 : (ModuleCat.Hom.hom ((relCohMVG X A U V).f n))
      ((biprod.inr : dualComplex ℤ (relMVVV X A U V) ⟶
        dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n
          (dualMapHom (ModuleCat.ofHom ρ₂) φ))
      = (dualMapHom ((relMVChainBeta₂ X A U V).f n)).hom
          (dualMapHom (ModuleCat.ofHom ρ₂) φ) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, relCohMVG_inr]
    rfl
  have hc1 := dualMapHom_comp_apply ((relMVChainBeta₁ X A U V).f n) (ModuleCat.ofHom ρ₁) φ
  have hc2 := dualMapHom_comp_apply ((relMVChainBeta₂ X A U V).f n) (ModuleCat.ofHom ρ₂) φ
  have hsum := dualMapHom_add_apply (((relMVChainBeta₁ X A U V).f n) ≫ (ModuleCat.ofHom ρ₁))
      (((relMVChainBeta₂ X A U V).f n) ≫ (ModuleCat.ofHom ρ₂)) φ
  have hkeymap : (((relMVChainBeta₁ X A U V).f n) ≫ (ModuleCat.ofHom ρ₁))
      + (((relMVChainBeta₂ X A U V).f n) ≫ (ModuleCat.ofHom ρ₂))
      = 𝟙 ((relMVUV X A U V).X n) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rw [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply, LinearMap.comp_apply, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom,
      ModuleCat.hom_id, LinearMap.id_apply]
    exact hkey a
  rw [map_add, hG1, hG2, hc1, hc2, ← hsum, hkeymap, dualMapHom_id_apply]

/-! ## The degreewise short complex -/

/-- The degreewise part of the relative cohomological Mayer–Vietoris sequence. -/
theorem relCohMV_degreewise_shortExact (n : ℕ) :
    ((relCohMVShortComplex X A U V).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).ShortExact := by
  have hf : ((relCohMVShortComplex X A U V).map
        (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).f
      = (relCohMVF X A U V).f n :=
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.up ℕ) n (relCohMVF X A U V)
  have hg : ((relCohMVShortComplex X A U V).map
        (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).g
      = (relCohMVG X A U V).f n :=
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.up ℕ) n (relCohMVG X A U V)
  haveI hmono : Mono (((relCohMVShortComplex X A U V).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).f) := by
    rw [hf]
    exact (ModuleCat.mono_iff_injective _).2 (relCohMVF_injective X A U V n)
  haveI hepi : Epi (((relCohMVShortComplex X A U V).map
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)).g) := by
    rw [hg]
    exact (ModuleCat.epi_iff_surjective _).2 (relCohMVG_surjective X A U V n)
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range, hf, hg]
  exact relCohMVG_ker_le_range X A U V n

/-! ## The main result -/

theorem relCohMV_shortExact (X : TopCat) (A U V : Set X) :
    ∃ (f : Work.Cohomology.dualComplex ℤ (Work.Cohomology.relSmallTop U V A) ⟶
          CategoryTheory.Limits.biprod
            (Work.Cohomology.dualComplex ℤ
              (Work.Cohomology.relSmallChains U V U (U ∩ A) Set.inter_subset_left))
            (Work.Cohomology.dualComplex ℤ
              (Work.Cohomology.relSmallChains U V V (V ∩ A) Set.inter_subset_left)))
      (g : CategoryTheory.Limits.biprod
            (Work.Cohomology.dualComplex ℤ
              (Work.Cohomology.relSmallChains U V U (U ∩ A) Set.inter_subset_left))
            (Work.Cohomology.dualComplex ℤ
              (Work.Cohomology.relSmallChains U V V (V ∩ A) Set.inter_subset_left)) ⟶
          Work.Cohomology.dualComplex ℤ
            (Work.Cohomology.relSmallChains U V (U ∩ V) (U ∩ V ∩ A) Set.inter_subset_left))
      (h : CategoryTheory.CategoryStruct.comp f g = 0),
      (CategoryTheory.ShortComplex.mk f g h).ShortExact := by
  refine ⟨relCohMVF X A U V, relCohMVG X A U V, relCohMV_comp X A U V, ?_⟩
  exact HomologicalComplex.shortExact_of_degreewise_shortExact (relCohMVShortComplex X A U V)
    (fun n => relCohMV_degreewise_shortExact X A U V n)

end

end Work.Cohomology
