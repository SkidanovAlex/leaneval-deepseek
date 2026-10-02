import Mathlib
import Submission.Work.Thom.IsoPunct
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Tubular.nonempty_thomClass_of_bundleIso
import Submission.Work.Thom.complexPullback
import Submission.Work.ThomBordism.thomClassPullbackBundleComap
import Submission.Work.ThomBordism.thomClassFibreDefs
import Submission.Work.ThomBordism.thomClass_fibreGenerator
import Submission.Work.ThomBordism.thomClass_of_fibreGenerator
import Submission.Work.ThomBordism.fibreGenerator_bundleComap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The pullback of a Thom class is a Thom class (the rank degree)

The target `Work.ThomBordism.thomClassPullbackBundleComapRank` is reduced here (via the tree's
`Work.ThomBordism.thomClassPullbackBundleComap_of_isThom`) to the bijectivity of the pulled-back
Thom map, and that is assembled from

* `Work.ThomBordism.thomClass_fibreGenerator` *(delegated)* — a Thom class at the rank degree
  restricts to a generator on every fibre (the "exercise" direction of Hatcher 4D.10);
* `Work.ThomBordism.thomClass_of_fibreGenerator` *(delegated)* — a class at the rank degree that
  restricts to a generator on every fibre is a Thom class (the Leray–Hirsch direction, Hatcher
  Corollary 4D.9);
* `Work.ThomBordism.fibreGenerator_bundleComap` — the fibre of the pullback of `Z` along `f` over
  `b'` is (canonically) the fibre of `Z` over `f b'`, so the fibre-generator property is preserved
  by the pullback.
-/

namespace Work.ThomBordism

open Work.TangentClasses

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}

/-- The total-space map of the pullback (`Work.Thom.totalMap`) is the chapter's `thomComapMap`:
the pullback of a class of the Thom pair of `Z` along it is `thomComapClass`. -/
theorem thomComapClass_eq (Z : RealBundle B F ι) (f : C(B', B)) {n : ℕ}
    (σ : Work.Thom.OpenThom Z n) :
    (Work.Thom.relCohMap (thomComapMap Z f)
      (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
      (Work.Thom.zeroComplement Z) (thomComapMap_mem Z f) ℤ n).hom σ
      = (Work.Thom.relCohMap (Work.Thom.totalMap Z f)
          (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
          (Work.Thom.zeroComplement Z) (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n).hom σ :=
  rfl

/-- The target of this file is assembled from the two halves of the equivalence of the definitions
of a Thom class at the rank degree together with the preservation of the fibre-generator property
by the pullback. -/
theorem thomComapClass_isThom_of (Z : RealBundle B F ι) (f : C(B', B)) {n : ℕ}
    (T : Work.Thom.ThomClass Z n) (hn : n = Z.rank)
    (hgen : Work.ThomBordism.IsFibreGenerator Z n T.τ)
    (hgen' : Work.ThomBordism.IsFibreGenerator (Work.Thom.bundleComap Z f) n
      ((Work.Thom.relCohMap (Work.Thom.totalMap Z f)
        (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
        (Work.Thom.zeroComplement Z) (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n).hom T.τ))
    (hfib : ∀ σ : Work.Thom.OpenThom (Work.Thom.bundleComap Z f) n,
      Work.ThomBordism.IsFibreGenerator (Work.Thom.bundleComap Z f) n σ →
        n = Module.finrank ℝ F →
      ∀ k : ℕ, Function.Bijective (Work.Thom.thomMap (Work.Thom.bundleComap Z f) n σ k)) :
    ∀ k, Function.Bijective
      (Work.Thom.thomMap (Work.Thom.bundleComap Z f) n (thomComapClass Z f T) k) := by
  have h := hfib ((Work.Thom.relCohMap (Work.Thom.totalMap Z f)
        (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
        (Work.Thom.zeroComplement Z) (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n).hom T.τ)
    hgen' (by rw [hn]; rfl)
  rwa [← thomComapClass_eq Z f T.τ] at h

/-- **The target.** -/
theorem thomClassPullbackBundleComapRank {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (f : C(B', B)) (T : Work.Thom.ThomClass Z n)
    (hn : n = Z.rank) :
    ∃ ψ : C((Work.Thom.bundleComap Z f).TotalSpace, Z.TotalSpace),
      (∀ p, (ψ p).1 = f p.1) ∧ (∀ p, (ψ p).2 = p.2) ∧
      ∃ (hf : ∀ x ∈ Work.Thom.zeroComplement (Work.Thom.bundleComap Z f),
            ψ x ∈ Work.Thom.zeroComplement Z)
        (T' : Work.Thom.ThomClass (Work.Thom.bundleComap Z f) n),
        T'.τ = (Work.Thom.relCohMap ψ (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
          (Work.Thom.zeroComplement Z) hf ℤ n).hom T.τ := by
  refine thomClassPullbackBundleComap_of_isThom Z f T fun k => ?_
  have hn' : n = Module.finrank ℝ F := by rw [hn]; rfl
  -- the fibre-generator property of `T.τ`
  have hgen : Work.ThomBordism.IsFibreGenerator Z n T.τ :=
    thomClass_fibreGenerator Z T hn'
  -- it is preserved by the pullback
  have hgen' : Work.ThomBordism.IsFibreGenerator (Work.Thom.bundleComap Z f) n
      ((Work.Thom.relCohMap (Work.Thom.totalMap Z f)
        (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
        (Work.Thom.zeroComplement Z) (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n).hom T.τ) :=
    fibreGenerator_bundleComap Z f T.τ hgen
  -- and the fibre-generator condition gives the Thom isomorphism at the rank degree
  have hiso := thomClass_of_fibreGenerator (Work.Thom.bundleComap Z f)
    ((Work.Thom.relCohMap (Work.Thom.totalMap Z f)
      (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
      (Work.Thom.zeroComplement Z) (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n).hom T.τ) hn' hgen'
  have hcls : thomComapClass Z f T
      = (Work.Thom.relCohMap (Work.Thom.totalMap Z f)
        (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
        (Work.Thom.zeroComplement Z) (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n).hom T.τ :=
    thomComapClass_eq Z f T.τ
  rw [hcls]
  exact hiso k

end

end Work.ThomBordism
