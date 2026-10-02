import Submission.Work.ThomBordism.absThomCompare
import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.mixedCupC_pairNatural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The pullback of the Thom map along a map of pairs

The Thom map `thomMap Z n τ k x = π_Z^*(x) ⌣ τ` (`Work.Thom.thomMap_apply`) is natural under a map
of pairs `g : (Z', Z'∖0) → (Z, Z∖0)` lying over a base map `f`: the pullback of
`thomMap Z n τ k x` is `π_{Z'}^*(f^*x) ⌣ g^*(τ)`.

This is the arithmetic of the "description of the universal classes" (`NOTES_round15_H4.md`): with
`Z = γ_{k,10}`, `τ = U_γ` the universal Thom class and `g` the total-space map of the Gauss bundle
map `ν → γ`, it computes the pullback of the *universal* class `π^*(p₁(γ)²) ⌣ U_γ` as
`π_ν^*(g^*p₁(γ)²) ⌣ g^*(U_γ)` — the geometric class of the normal bundle.
-/

open CategoryTheory
open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
variable {F F' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] {ι ι' : Type}

/-- **Naturality of the Thom map under a map of Thom pairs.**  For bundles `Z`, `Z'`, a base map
`f : B' → B` and a map of total spaces `g : Z' → Z` over `f` carrying `Z'∖0` into `Z∖0`, the
pullback of `thomMap Z n τ k x = π_Z^*(x) ⌣ τ` along `g` is `π_{Z'}^*(f^*x) ⌣ g^*(τ)`. -/
theorem thomMapPullbackPair
    (Z : RealBundle B F ι) (Z' : RealBundle B' F' ι')
    (f : C(B', B)) (g : C(Z'.TotalSpace, Z.TotalSpace))
    (hg : ∀ p : Z'.TotalSpace, p ∈ Work.Thom.zeroComplement Z' →
      g p ∈ Work.Thom.zeroComplement Z)
    (hbproj : ∀ p : Z'.TotalSpace, Work.Thom.bundleProj Z (g p) = f (Work.Thom.bundleProj Z' p))
    (n k : ℕ) (τ : Work.Thom.OpenThom Z n) (x : Work.Thom.Coh ℤ k B) :
    (Work.Thom.relCohMap g (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hg
        ℤ (k + n)).hom (Work.Thom.thomMap Z n τ k x)
      = Work.Thom.mixedCupC ℤ (Work.Thom.zeroComplement Z') k n
          ((Work.Thom.CohMap (Work.Thom.bundleProj Z') ℤ k).hom ((Work.Thom.CohMap f ℤ k).hom x))
          ((Work.Thom.relCohMap g (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hg
            ℤ n).hom τ) := by
  rw [Work.Thom.thomMap_apply,
    Work.Thom.mixedCupC_pairNatural g (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z)
      hg k n ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x) τ]
  have hcomp : (Work.Thom.bundleProj Z).comp g = f.comp (Work.Thom.bundleProj Z') := by
    ext p
    exact hbproj p
  have hmap : Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k ≫ Work.Thom.CohMap g ℤ k
      = Work.Thom.CohMap f ℤ k ≫ Work.Thom.CohMap (Work.Thom.bundleProj Z') ℤ k := by
    rw [← Work.Thom.CohMap_comp g (Work.Thom.bundleProj Z) ℤ k,
      ← Work.Thom.CohMap_comp (Work.Thom.bundleProj Z') f ℤ k, hcomp]
  have h2 : (Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k ≫ Work.Thom.CohMap g ℤ k).hom x
      = (Work.Thom.CohMap f ℤ k ≫ Work.Thom.CohMap (Work.Thom.bundleProj Z') ℤ k).hom x := by
    rw [hmap]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [h2]

end

end Work.ThomBordism
