import Mathlib
import Submission.Work.ThomBordism.tautologicalClassSensitivity
import Submission.Work.ThomBordism.gtdUWith_eq_of_normalData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The class `gtdUWith` does not depend on the normal datum — *branched* Gauss data

`Work.ThomBordism.gtdUWith E ND G hgm U` is the pull-back of a Thom class `U` of the tautological
bundle over the Grassmannian along a bundle map `G : ν(ND) → γ` over the (padded) Gauss map of the
normal data `ND`, transported along the Euclidean normal homeomorphism
`eucNormalHomeomorph E ND : ν(ND).TotalSpace ≃ₜ NormalTotal E` to a relative class on the pair
`(NormalTotal E, normalNonzero E)`.

`Work.ThomBordism.gtdUWith_eq_of_normalData` proves the datum-independence of this class when both
bundle maps `G`, `G'` follow the *positive* branch of the Gauss data
(`proj (G p) = padGaussFun E ND p.1`).  The present file removes that restriction: the maps may
follow either branch, `proj (G p) = padGaussFun E ND p.1` or
`proj (G p) = ogFlip (padGaussFun E ND p.1)`, the branch being the *same* for `G` and `G'` and
recorded by the integer `σ ∈ {±1}`.

The proof is the same as the unbranched one — the transfer map
`T = eucNormalHomeomorph E ND' ∘ normalToBundle E ND` carries the two models of the normal bundle
onto one another fibrewise over `V`, so `G = G' ∘ T` *as functions*, which is the input of the
functoriality of `relCohMap` — with one change: the *plane* comparison now goes through the datum
independence of the padded Gauss map (`Work.ThomBordism.padGaussFun_eq_of_normalData`) **under the
branch function** `(if σ = 1 then id else ogFlip k 10)`, and the *vector* comparison is unchanged
(`bundleToNormal_normalToBundle`).

Note that the branch is *not* reconstructed from the data: the hypotheses of this file are the exact
input of `Work.ThomBordism.gaussBranch_uniform`, whose conclusion pins a branch `s`; the content of
the present lemma is that for a fixed branch the class does not depend on the normal datum. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.Tubular

noncomputable section

/-- **`gtdUWith` does not depend on the normal datum, in either branch.**  See the module
docstring. -/
theorem gtdUWith_eq_of_normalData_branch
    {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND ND' : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (hodd : Odd k)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = (if σ = 1 then id else Work.ThomBordism.Grassmann.ogFlip k 10)
          (Work.ThomBordism.Grassmann.padGaussFun E ND p.1))
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (G' : C((Work.Tubular.normalBundle E ND').TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm' : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND'),
      G' p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp' : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G' p)
      = (if σ = 1 then id else Work.ThomBordism.Grassmann.ogFlip k 10)
          (Work.ThomBordism.Grassmann.padGaussFun E ND' p.1))
    (hvec' : ∀ p, Work.ThomBordism.Grassmann.evalVec (G' p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND' p)))
    (u₀ : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k) :
    Work.ThomBordism.gtdUWith E ND G hgm u₀
      = Work.ThomBordism.gtdUWith E ND' G' hgm' u₀ := by
  -- the two Euclidean normal homeomorphisms (as continuous maps) and the transfer map
  let h : C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace) :=
    ((Work.Tubular.eucNormalHomeomorph E ND).symm :
      C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace))
  let h' : C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND').TotalSpace) :=
    ((Work.Tubular.eucNormalHomeomorph E ND').symm :
      C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND').TotalSpace))
  let T_map : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.Tubular.normalBundle E ND').TotalSpace) :=
    h'.comp ((Work.Tubular.eucNormalHomeomorph E ND) :
      C((Work.Tubular.normalBundle E ND).TotalSpace, Work.Tubular.NormalTotal E))
  let A : Set (Work.Tubular.normalBundle E ND).TotalSpace :=
    Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND)
  let A' : Set (Work.Tubular.normalBundle E ND').TotalSpace :=
    Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND')
  let B : Set (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace :=
    Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
  let Nz : Set (Work.Tubular.NormalTotal E) := Work.Tubular.normalNonzero E
  have h'_apply : ∀ z : Work.Tubular.NormalTotal E, h' z = Work.Tubular.normalToBundle E ND' z :=
    fun z => gtdEucNormalHomeomorph_symm_apply E ND' z
  have h_apply : ∀ z : Work.Tubular.NormalTotal E, h z = Work.Tubular.normalToBundle E ND z :=
    fun z => gtdEucNormalHomeomorph_symm_apply E ND z
  have T_map_apply : ∀ p, T_map p = Work.Tubular.normalToBundle E ND'
      (Work.Tubular.bundleToNormal E ND p) := by
    intro p
    show h' ((Work.Tubular.eucNormalHomeomorph E ND) p) = _
    rw [h'_apply, Work.Tubular.eucNormalHomeomorph_apply]
  have T_proj : ∀ p, (T_map p).1 = p.1 := fun p => by rw [T_map_apply p]; rfl
  have T_bundle : ∀ p, Work.Tubular.bundleToNormal E ND' (T_map p)
      = Work.Tubular.bundleToNormal E ND p := by
    intro p
    rw [T_map_apply p]
    exact Work.Tubular.bundleToNormal_normalToBundle E ND' (Work.Tubular.bundleToNormal E ND p)
  -- the transfer map carries the nonzero complement to the nonzero complement
  have hT : ∀ p ∈ A, T_map p ∈ A' := by
    have hfn : ∀ p, Work.Thom.fibreNorm (Work.Tubular.normalBundle E ND') (T_map p)
        = Work.Thom.fibreNorm (Work.Tubular.normalBundle E ND) p := by
      intro p
      rw [Work.Tubular.fibreNorm_eq_normalNorm, T_bundle p,
        ← Work.Tubular.fibreNorm_eq_normalNorm]
    intro p hp
    rw [Work.Thom.mem_zeroComplement] at hp ⊢
    intro h0
    have hp' : Work.Thom.fibreNorm (Work.Tubular.normalBundle E ND) p ≠ 0 := by
      rw [Work.Thom.fibreNorm]
      exact fun hh => hp (norm_eq_zero.mp hh)
    refine hp' ?_
    rw [← hfn p, Work.Thom.fibreNorm, h0, norm_zero]
  -- the branch function, and the datum independence of the padded Gauss map under it
  have hbranch : ∀ x, (if σ = 1 then id else Work.ThomBordism.Grassmann.ogFlip k 10)
      (Work.ThomBordism.Grassmann.padGaussFun E ND x)
      = (if σ = 1 then id else Work.ThomBordism.Grassmann.ogFlip k 10)
          (Work.ThomBordism.Grassmann.padGaussFun E ND' x) :=
    fun x => congrArg (fun y => (if σ = 1 then id else Work.ThomBordism.Grassmann.ogFlip k 10) y)
      (padGaussFun_eq_of_normalData E ND ND' x)
  -- the bundle map is pinned by the Gauss data, so `G = G' ∘ T`
  have hG : G = G'.comp T_map := by
    apply ContinuousMap.ext
    intro p
    exact Work.ThomBordism.Grassmann.evalVec_injective_of_proj_eq
      (p := G p) (q := G' (T_map p)) (by
        change VectorBundleCore.proj (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (G p)
          = VectorBundleCore.proj (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (G' (T_map p))
        rw [hbp p, hbp' (T_map p), T_proj p]
        exact hbranch p.1) (by
        show Work.ThomBordism.Grassmann.evalVec (G p)
          = Work.ThomBordism.Grassmann.evalVec (G' (T_map p))
        rw [hvec p, hvec' (T_map p), T_bundle p])
  -- and the transfer map intertwines the two Euclidean normal homeomorphisms
  have hcomp : T_map.comp h = h' := by
    apply ContinuousMap.ext
    intro y
    show h' ((Work.Tubular.eucNormalHomeomorph E ND) (h y)) = h' y
    rw [h_apply y, Work.Tubular.eucNormalHomeomorph_apply,
      Work.Tubular.bundleToNormal_normalToBundle]
  have hgf : ∀ p ∈ A, G' (T_map p) ∈ B := fun p hp => hgm' (T_map p) (hT p hp)
  -- functoriality of the pull-back, in the two forms needed
  have hmap1 : Work.Thom.relCohMap G A B hgm ℤ k
      = CategoryTheory.CategoryStruct.comp (Work.Thom.relCohMap G' A' B hgm' ℤ k)
          (Work.Thom.relCohMap T_map A A' hT ℤ k) :=
    (Work.Thom.relCohMap_congr' A B hG hgm hgf ℤ k).trans
      (Work.Thom.relCohMap_comp A A' B T_map G' hT hgm' hgf ℤ k).symm
  have hrel1 : (Work.Thom.relCohMap G A B hgm ℤ k).hom u₀.τ
      = (Work.Thom.relCohMap T_map A A' hT ℤ k).hom
          ((Work.Thom.relCohMap G' A' B hgm' ℤ k).hom u₀.τ) := by
    have := congrArg (fun φ => φ.hom u₀.τ) hmap1
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  have hmap2 : CategoryTheory.CategoryStruct.comp (Work.Thom.relCohMap T_map A A' hT ℤ k)
        (Work.Thom.relCohMap h Nz A (gtd_mem E ND) ℤ k)
      = Work.Thom.relCohMap h' Nz A' (gtd_mem E ND') ℤ k :=
    (Work.Thom.relCohMap_comp Nz A A' h T_map (gtd_mem E ND) hT
      (fun y hy => hT (h y) (gtd_mem E ND y hy)) ℤ k).trans
      (Work.Thom.relCohMap_congr' Nz A' hcomp _ (gtd_mem E ND') ℤ k)
  have hrel2 : (Work.Thom.relCohMap h Nz A (gtd_mem E ND) ℤ k).hom
        ((Work.Thom.relCohMap T_map A A' hT ℤ k).hom
          ((Work.Thom.relCohMap G' A' B hgm' ℤ k).hom u₀.τ))
      = (Work.Thom.relCohMap h' Nz A' (gtd_mem E ND') ℤ k).hom
          ((Work.Thom.relCohMap G' A' B hgm' ℤ k).hom u₀.τ) := by
    have := congrArg (fun φ => φ.hom ((Work.Thom.relCohMap G' A' B hgm' ℤ k).hom u₀.τ)) hmap2
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  -- unfold the two sides and rewrite
  show (Work.Thom.relCohMap h Nz A (gtd_mem E ND) ℤ k).hom
      ((Work.Thom.relCohMap G A B hgm ℤ k).hom u₀.τ)
    = (Work.Thom.relCohMap h' Nz A' (gtd_mem E ND') ℤ k).hom
      ((Work.Thom.relCohMap G' A' B hgm' ℤ k).hom u₀.τ)
  rw [hrel1, hrel2]

end

end Work.ThomBordism
