import Submission.Work.Kunneth.Bridge
import Submission.Work.Kunneth.GenPowGenerates

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The powers of `ζ` generate the cohomology of `P(ε^m)`

This module proves the key input of `Work.Kunneth.lerayHirschFull_point`: for the trivial bundle
`ε^{n+1}` over the point, `ζ^j` generates `H^{2j}(P(ε^{n+1});ℤ)` for `j ≤ n`
(`Work.Kunneth.keyLH`).

The route is: `Work.Kunneth.GenPowGenerates` proves the statement for `c₁(O(-1))` on `ℂP^n` (the
Gen presentation), the bundle isomorphism `Work.Kunneth.bridgeIso` identifies `O(-1)` with the
tautological bundle of `P(ε^{n+1})`, and `Work.LerayHirsch.zeta_trivCore_comap_projUniv` transports
along `projUniv`.
-/

open scoped LinearAlgebra.Projectivization

namespace Work.Kunneth

noncomputable section

/-- A version of `Work.Kunneth.span_singleton_image_eq_top` with the generator explicit. -/
theorem span_image_eq_top' {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) (x : M)
    (hx : Submodule.span ℤ {x} = ⊤) : Submodule.span ℤ {f x} = ⊤ :=
  span_singleton_image_eq_top f hf hx

/-- **`CohMap` of `wkCM n` is surjective** (it is the `CohMap` of a homeomorphism). -/
theorem surjective_CohMap_wkCM (n k : ℕ) :
    Function.Surjective (Work.Thom.CohMap (wkCM n) ℤ k).hom := by
  have hcomp : ((wkHomeo n).symm : C(Work.Projective.CP n,
      ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))))).comp (wkCM n) = ContinuousMap.id _ := by
    ext x
    exact (wkHomeo n).symm_apply_apply x
  intro y
  refine ⟨(Work.Thom.CohMap ((wkHomeo n).symm : C(Work.Projective.CP n,
      ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))))) ℤ k).hom y, ?_⟩
  have h1 : (Work.Thom.CohMap (wkCM n) ℤ k).hom.comp
      (Work.Thom.CohMap ((wkHomeo n).symm : C(Work.Projective.CP n,
        ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))))) ℤ k).hom = LinearMap.id := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.id_apply,
      Work.Thom.CohMap_comp_apply (wkCM n) ((wkHomeo n).symm : C(Work.Projective.CP n,
        ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1))))) ℤ k x, hcomp, Work.Thom.CohMap_id]
    simp only [ModuleCat.hom_id, LinearMap.id_apply]
  have hy := LinearMap.congr_fun h1 y
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hy

/-- `projClass` as a continuous map. -/
def pcCM (n : ℕ) : C(Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (n + 1)),
    ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :=
  ⟨Work.LerayHirsch.projClass (Work.LerayHirsch.trivCore (n + 1)),
    Work.LerayHirsch.continuous_projClass_trivCore (n + 1)⟩

/-- **`CohMap` of `projUniv` is surjective** (its inverse is `projClass`). -/
theorem surjective_CohMap_projUniv (n k : ℕ) :
    Function.Surjective (Work.Thom.CohMap (Work.LerayHirsch.projUniv (n + 1)) ℤ k).hom := by
  have hcomp : (pcCM n).comp (Work.LerayHirsch.projUniv (n + 1)) = ContinuousMap.id _ := by
    ext x
    exact (Work.LerayHirsch.projUnivHomeo (n + 1)).left_inv x
  intro y
  refine ⟨(Work.Thom.CohMap (pcCM n) ℤ k).hom y, ?_⟩
  have h1 : (Work.Thom.CohMap (Work.LerayHirsch.projUniv (n + 1)) ℤ k).hom.comp
      (Work.Thom.CohMap (pcCM n) ℤ k).hom = LinearMap.id := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.id_apply,
      Work.Thom.CohMap_comp_apply (Work.LerayHirsch.projUniv (n + 1)) (pcCM n) ℤ k x,
      hcomp, Work.Thom.CohMap_id]
    simp only [ModuleCat.hom_id, LinearMap.id_apply]
  have hy := LinearMap.congr_fun h1 y
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hy

/-- **Generation transfers back along an injective map.** -/
theorem span_eq_top_of_injective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Injective f) (x : M)
    (h : Submodule.span ℤ {f x} = ⊤) : Submodule.span ℤ {x} = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro y
  have hmem : f y ∈ Submodule.map f (Submodule.span ℤ {x}) := by
    rw [Submodule.map_span, Set.image_singleton, h]
    trivial
  obtain ⟨u, hu, hfu⟩ := hmem
  simpa [hf hfu] using hu

/-- **`CohMap` of `projUniv` is injective** (its inverse is `projClass`). -/
theorem injective_CohMap_projUniv (n k : ℕ) :
    Function.Injective (Work.Thom.CohMap (Work.LerayHirsch.projUniv (n + 1)) ℤ k).hom := by
  have hcomp : (Work.LerayHirsch.projUniv (n + 1)).comp (pcCM n) = ContinuousMap.id _ := by
    ext x
    exact (Work.LerayHirsch.projUnivHomeo (n + 1)).right_inv x
  have h1 : (Work.Thom.CohMap (pcCM n) ℤ k).hom.comp
      (Work.Thom.CohMap (Work.LerayHirsch.projUniv (n + 1)) ℤ k).hom = LinearMap.id := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.id_apply,
      Work.Thom.CohMap_comp_apply (pcCM n) (Work.LerayHirsch.projUniv (n + 1)) ℤ k x,
      hcomp, Work.Thom.CohMap_id]
    simp only [ModuleCat.hom_id, LinearMap.id_apply]
  intro x y hxy
  have hx := LinearMap.congr_fun h1 x
  have hy := LinearMap.congr_fun h1 y
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
  rw [← hx, hxy, hy]

/-- **The key statement, in the normalisation of `pow2`.** -/
theorem keyLH_aux (n j : ℕ) (hj : j ≤ n) :
    Submodule.span ℤ {(Work.Kunneth.pow2
      (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore (n + 1))) j)} = ⊤ := by
  -- (1) the `O(-1)`-class over `ℂP^n`, pulled back along `wkHomeo`
  have hgen : Submodule.span ℤ {(Work.Kunneth.pow2
      ((Work.Thom.CohMap (wkCM n) ℤ 2).hom
        (Work.Thom.chernClass 1 1 (Work.Gen.tautLine n))) j)} = ⊤ := by
    have h := span_image_eq_top' ((Work.Thom.CohMap (wkCM n) ℤ (2 * j)).hom)
      (surjective_CohMap_wkCM n (2 * j))
      (Work.Kunneth.pow2 (Work.Thom.chernClass 1 1 (Work.Gen.tautLine n)) j)
      (GenPowGenerates n j hj)
    rwa [pow2_CohMap] at h
  -- (2) identify the pulled-back class with `c₁(ℓ)` of `P(ε^{n+1})`
  have hc₁ : (Work.Thom.CohMap (wkCM n) ℤ 2).hom
        (Work.Thom.chernClass 1 1 (Work.Gen.tautLine n))
      = Work.Thom.chernClass 1 1 (Work.LerayHirsch.tautLineP (n + 1)) :=
    (zetaP_eq_chernClass n).symm
  have h₂ : Submodule.span ℤ {(Work.Kunneth.pow2
      (Work.Thom.chernClass 1 1 (Work.LerayHirsch.tautLineP (n + 1))) j)} = ⊤ :=
    hc₁ ▸ hgen
  -- (3) transport along `projUniv`
  have hc₂ : (Work.Thom.CohMap (Work.LerayHirsch.projUniv (n + 1)) ℤ 2).hom
        (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore (n + 1)))
      = Work.Thom.chernClass 1 1 (Work.LerayHirsch.tautLineP (n + 1)) := by
    rw [Work.LerayHirsch.zeta_trivCore_comap_projUniv, Work.LerayHirsch.zetaP,
      Work.Thom.cohTransport_rfl]
  exact span_eq_top_of_injective
    ((Work.Thom.CohMap (Work.LerayHirsch.projUniv (n + 1)) ℤ (2 * j)).hom)
    (injective_CohMap_projUniv n (2 * j))
    (Work.Kunneth.pow2 (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore (n + 1))) j)
    (by rw [pow2_CohMap, hc₂]; exact h₂)

/-- **The key statement**: `ζ^j` generates `H^{2j}(P(ε^{n+1});ℤ)` for `j ≤ n`. -/
theorem keyLH (n j : ℕ) (hj : j ≤ n) :
    Submodule.span ℤ {Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) j} = ⊤ := by
  rw [← pow2_zeta (Work.LerayHirsch.trivCore (n + 1)) j]
  exact keyLH_aux n j hj

end

end Work.Kunneth
