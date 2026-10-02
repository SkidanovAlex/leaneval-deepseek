import Mathlib
import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.Iso
import Submission.Work.Thom.IsoPunct
import Submission.Work.Thom.mixedCupC_pairNatural
import Submission.Work.Thom.step_natural
import Submission.Work.TangentClasses.Bundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Isomorphism-invariance of the Euler class of a Thom class

Two isomorphic real bundles over a common base have the *same* Euler classes: more precisely, for
any Thom class `T` of `Z` there is a Thom class `T'` of `Z'` (namely the pullback of `T` along the
inverse of the bundle isomorphism) with `T'.eulerClass = T.eulerClass`.

This is the transport statement that lets one move an oriented-bundle structure across a bundle
isomorphism.  The proof:

* `e.symm.toHomeomorph : Z'.TotalSpace ≃ₜ Z.TotalSpace` is a homeomorphism of pairs
  `(Z',Z'∖0) ≃ₜ (Z,Z∖0)`, so it induces a **bijection** on relative cohomology
  (`Work.Thom.bijective_relCohMap_of_homeomorphA`); define `τ' = f^*(T.τ)`.
* The Thom map is natural: `f^*(π_Z^*x ⌣ T.τ) = π_{Z'}^*x ⌣ f^*(T.τ)`
  (`Work.Thom.mixedCupC_pairNatural`, together with `π_Z ∘ f = π_{Z'}`), so `T'` is a Thom class
  because `T` is.
* `relToAbs` is natural (`Work.Thom.relCohMap_relToAbs_apply`) and `f ∘ z_{Z'} = z_Z`, so the
  Euler class — the pullback of the Thom class along the zero section — is preserved.
-/

namespace Work.Agree

open Work.TangentClasses
open Work.Thom

/-- A bundle isomorphism carries the zero section of the source bundle to the zero section of the
target bundle: the inverse of `e` sends the zero section of `Z'` to the zero section of `Z`. -/
private lemma comp_zeroSection_symm {B : Type} [TopologicalSpace B]
    {F F' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {ι ι' : Type}
    (Z : RealBundle B F ι) (Z' : RealBundle B F' ι') (e : BundleIso Z Z') :
    ((↑e.symm.toHomeomorph : C(Z'.TotalSpace, Z.TotalSpace)).comp (Work.Thom.zeroSection Z') =
      Work.Thom.zeroSection Z) := by
  apply ContinuousMap.ext; intro b
  simp only [ContinuousMap.comp_apply, Work.Thom.zeroSection_apply]
  simp

theorem eulerClassIso {B : Type} [TopologicalSpace B]
    {F F' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {ι ι' : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (Z' : Work.TangentClasses.RealBundle B F' ι')
    (e : Work.Thom.BundleIso Z Z') (T : Work.Thom.ThomClass Z n) :
    ∃ T' : Work.Thom.ThomClass Z' n, T'.eulerClass = T.eulerClass := by
  classical
  -- the bundle isomorphism, read as a map of the punctured total spaces
  have hiff : ∀ x : Z'.TotalSpace,
      x ∈ Work.Thom.zeroComplement Z' ↔
        e.symm.toHomeomorph x ∈ Work.Thom.zeroComplement Z := by
    intro x
    simp only [Work.Thom.mem_zeroComplement]
    constructor
    · intro h
      show e.inv x.1 x.2 ≠ 0
      exact e.symm.hom_ne_zero h
    · intro h hx0
      refine h ?_
      have hz : e.inv x.1 x.2 = 0 := by
        rw [hx0]
        exact map_zero (e.inv x.1)
      exact hz
  set f : C(Z'.TotalSpace, Z.TotalSpace) :=
    (↑e.symm.toHomeomorph : C(Z'.TotalSpace, Z.TotalSpace)) with hf_def
  set hf : ∀ x ∈ Work.Thom.zeroComplement Z', f x ∈ Work.Thom.zeroComplement Z :=
    fun x hx => (hiff x).mp hx with hf_mem
  -- the transported Thom class
  set τ' : Work.Thom.OpenThom Z' n :=
    (Work.Thom.relCohMap f (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z)
      hf ℤ n).hom T.τ with hτ'
  -- the induced map on the relative cohomology of the Thom pairs is bijective
  have hbijrel : ∀ m, Function.Bijective
      (Work.Thom.relCohMap f (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z)
        hf ℤ m).hom :=
    fun m => Work.Thom.bijective_relCohMap_of_homeomorphA
      (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) e.symm.toHomeomorph hiff ℤ m
  -- `τ'` is a Thom class: the Thom map is natural under the isomorphism of Thom pairs
  have hisThom : ∀ k, Function.Bijective (Work.Thom.thomMap Z' n τ' k) := by
    intro k
    have hpoint : ∀ x : Coh ℤ k B,
        Work.Thom.thomMap Z' n τ' k x
          = (Work.Thom.relCohMap f (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z)
              hf ℤ (k + n)).hom (Work.Thom.thomMap Z n T.τ k x) := by
      intro x
      rw [Work.Thom.thomMap_apply, Work.Thom.thomMap_apply]
      rw [Work.Thom.mixedCupC_pairNatural f (Work.Thom.zeroComplement Z')
            (Work.Thom.zeroComplement Z) hf k n
            ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x) T.τ]
      rw [Work.Thom.CohMap_comp_apply f (Work.Thom.bundleProj Z) ℤ k x]
      have hbp : (Work.Thom.bundleProj Z).comp f = Work.Thom.bundleProj Z' := by ext p; rfl
      rw [hbp, hτ']
    constructor
    · intro x y hxy
      have h2 : (Work.Thom.relCohMap f (Work.Thom.zeroComplement Z')
            (Work.Thom.zeroComplement Z) hf ℤ (k + n)).hom
            (Work.Thom.thomMap Z n T.τ k x)
          = (Work.Thom.relCohMap f (Work.Thom.zeroComplement Z')
              (Work.Thom.zeroComplement Z) hf ℤ (k + n)).hom
            (Work.Thom.thomMap Z n T.τ k y) := by
        rw [← hpoint x, ← hpoint y]; exact hxy
      exact (T.isThom k).1 ((hbijrel (k + n)).1 h2)
    · intro y
      obtain ⟨z, hz⟩ := (hbijrel (k + n)).2 y
      obtain ⟨x, hx⟩ := (T.isThom k).2 z
      exact ⟨x, by rw [hpoint x, hx, hz]⟩
  -- the Euler classes agree
  have heuler : Work.Thom.eulerClass Z' n τ' = Work.Thom.eulerClass Z n T.τ := by
    rw [Work.Thom.eulerClass, Work.Thom.eulerClass]
    rw [hτ']
    rw [Work.Thom.relCohMap_relToAbs_apply f (Work.Thom.zeroComplement Z')
      (Work.Thom.zeroComplement Z) hf ℤ n T.τ]
    rw [Work.Thom.CohMap_comp_apply (Work.Thom.zeroSection Z') f ℤ n
      ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) n).hom T.τ)]
    have hzs : f.comp (Work.Thom.zeroSection Z') = Work.Thom.zeroSection Z := by
      rw [hf_def]
      exact comp_zeroSection_symm Z Z' e
    rw [hzs]
  exact ⟨⟨τ', hisThom⟩, heuler⟩

end Work.Agree
