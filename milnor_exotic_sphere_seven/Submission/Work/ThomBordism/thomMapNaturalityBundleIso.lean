import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.Thom.comapAux
import Submission.Work.Thom.IsoPunct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- **Naturality of the Thom map under a map of pairs covering a base map.**
For a continuous map `h : Z'.TotalSpace → Z.TotalSpace` lying over `f : B' → B`
(`π_Z ∘ h = f ∘ π_{Z'}`) and carrying the complement of the zero section of `Z'` into that of `Z`,
pulling back the Thom map of `Z` along `h` is the Thom map of `Z'` for the pulled-back class
`h^* τ`, applied to `f^* x`:
`h^*(x ⌣ π_Z^*τ) = (f^*x) ⌣ π_{Z'}^*(h^*τ)`. -/
theorem thomMap_naturality_relCohMap
    {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {ι ι' : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (Z' : Work.TangentClasses.RealBundle B' F' ι')
    (f : C(B', B)) (h : C(Z'.TotalSpace, Z.TotalSpace))
    (hproj : (Work.Thom.bundleProj Z).comp h = f.comp (Work.Thom.bundleProj Z'))
    (n k : ℕ) (τ : Work.Thom.OpenThom Z n) (x : Work.Thom.Coh ℤ k B)
    (hh : ∀ p ∈ Work.Thom.zeroComplement Z', h p ∈ Work.Thom.zeroComplement Z) :
    (Work.Thom.relCohMap h (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hh ℤ (k+n)).hom
        (Work.Thom.thomMap Z n τ k x)
      = Work.Thom.thomMap Z' n
          ((Work.Thom.relCohMap h (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hh ℤ n).hom τ)
          k ((Work.Thom.CohMap f ℤ k).hom x) := by
  rw [Work.Thom.thomMap_apply Z n τ k x,
    Work.Thom.thomMap_apply Z' n
      ((Work.Thom.relCohMap h (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hh ℤ n).hom τ)
      k ((Work.Thom.CohMap f ℤ k).hom x)]
  rw [Work.Thom.mixedCupC_pairNatural h (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hh k n
        ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x) τ]
  have habs : (Work.Thom.CohMap h ℤ k).hom ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x)
      = (Work.Thom.CohMap (Work.Thom.bundleProj Z') ℤ k).hom ((Work.Thom.CohMap f ℤ k).hom x) := by
    rw [Work.Thom.CohMap_comp_apply h (Work.Thom.bundleProj Z) ℤ k x,
        Work.Thom.CohMap_comp_apply (Work.Thom.bundleProj Z') f ℤ k x, hproj]
  rw [habs]

theorem thomMapNaturalityBundleIso
    {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {ι ι' : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (Z' : Work.TangentClasses.RealBundle B' F' ι')
    (f : C(B', B)) (e : Work.Thom.BundleIso (Work.Thom.bundleComap Z f) Z')
    (n k : ℕ) (τ : Work.Thom.OpenThom Z n) (x : Work.Thom.Coh ℤ k B)
    (h₁ : ∀ p : Z'.TotalSpace, p ∈ Work.Thom.zeroComplement Z' →
      e.invTotalSpace p ∈ Work.Thom.zeroComplement (Work.Thom.bundleComap Z f)) :
    (Work.Thom.relCohMap (e.toHomeomorph.symm : C(Z'.TotalSpace, (Work.Thom.bundleComap Z f).TotalSpace))
        (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
        h₁ ℤ (k + n)).hom
      ((Work.Thom.relCohMap (Work.Thom.totalMap Z f) (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
        (Work.Thom.zeroComplement Z)
        (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ (k + n)).hom
        (Work.Thom.thomMap Z n τ k x))
    = Work.Thom.thomMap Z' n
        ((Work.Thom.relCohMap (((Work.Thom.totalMap Z f).comp
            (e.toHomeomorph.symm : C(Z'.TotalSpace, (Work.Thom.bundleComap Z f).TotalSpace))) :
              C(Z'.TotalSpace, Z.TotalSpace))
          (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z)
          (fun p hp => Work.Thom.totalMap_mem_zeroComplement Z f (e.invTotalSpace p) (h₁ p hp)) ℤ n).hom τ)
        k ((Work.Thom.CohMap f ℤ k).hom x) := by
  have hproj : (Work.Thom.bundleProj Z).comp
      ((Work.Thom.totalMap Z f).comp (e.toHomeomorph.symm : C(Z'.TotalSpace, (Work.Thom.bundleComap Z f).TotalSpace)))
      = f.comp (Work.Thom.bundleProj Z') := by
    ext p
    simp only [ContinuousMap.comp_apply, Work.Thom.totalMap_apply, Work.Thom.bundleProj_apply]
    rfl
  rw [Work.Thom.relCohMap_compA_apply (Work.Thom.zeroComplement Z')
        (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f)) (Work.Thom.zeroComplement Z)
        (e.toHomeomorph.symm : C(Z'.TotalSpace, (Work.Thom.bundleComap Z f).TotalSpace))
        (Work.Thom.totalMap Z f) h₁ (Work.Thom.totalMap_mem_zeroComplement Z f)
        (fun p hp => Work.Thom.totalMap_mem_zeroComplement Z f (e.invTotalSpace p) (h₁ p hp))
        ℤ (k+n) (Work.Thom.thomMap Z n τ k x)]
  exact thomMap_naturality_relCohMap Z Z' f _ hproj n k τ x
    (fun p hp => Work.Thom.totalMap_mem_zeroComplement Z f (e.invTotalSpace p) (h₁ p hp))

end Work.ThomBordism
