import Submission.Work.Thom.Iso
import Submission.Work.Thom.exists_coreMapFibre
import Submission.Work.ThomBordism.PontryaginThom.BundleEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The bundle isomorphism induced by a change of the model fibre

`Work.ThomBordism.PontryaginThom.bundleMapEquiv Z e` transports the gluing data `Z` (fibre `F`)
to the fibre `F'` along a continuous linear equivalence `e : F ≃L[ℝ] F'` — the same cover, the same
base sets, and transition functions conjugated by `e`.  This module records that the two
presentations of the same bundle are *isomorphic*:

`Work.Tubular.nonempty_bundleIso_bundleMapEquiv : Nonempty (BundleIso (bundleMapEquiv Z e) Z)`.

The proof reduces to `Work.Thom.exists_coreMapFibre`, which constructs *some* transported core `Z'`
with the same data, together with an isomorphism `Z ≅ Z'`; the remaining step is that a
`VectorBundleCore` is determined by `baseSet`, `indexAt` and `coordChange` (all other fields being
proofs).

This is the bridge that lets a Thom class of a `Fin k → ℝ`-fibred bundle (`bundleMapEquiv`-transport
of the Grassmann chapter's tautological bundle, which lives in the euclidean fibre
`Euc k = EuclideanSpace ℝ (Fin k)`) be moved, via
`Work.Tubular.nonempty_thomClass_of_bundleIso`, to the coordinate fibre used by
`Work.ThomBordism.PontryaginThom.NormalGaussData`, and conversely.
-/

namespace Work.Tubular

open Work.TangentClasses

noncomputable section

/-- **The transported bundle is isomorphic to the original one.**  For a real bundle `Z` over `B`
with model fibre `F` and a continuous linear equivalence `e : F ≃L[ℝ] F'`, the
`bundleMapEquiv`-transport of `Z` along `e` is isomorphic to `Z`. -/
theorem nonempty_bundleIso_bundleMapEquiv {B : Type} [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {ι : Type} (Z : RealBundle B F ι) (e : F ≃L[ℝ] F') :
    Nonempty (Work.Thom.BundleIso (Work.ThomBordism.PontryaginThom.bundleMapEquiv Z e) Z) := by
  -- A `VectorBundleCore` is determined by its base sets, its index maps and its transition
  -- functions: all the remaining fields are proofs.
  have key : ∀ (Z' : RealBundle B F' ι), Z'.baseSet = Z.baseSet →
      Z'.indexAt = Z.indexAt →
      (∀ i j x, Z'.coordChange i j x
        = (e : F →L[ℝ] F').comp ((Z.coordChange i j x).comp (e.symm : F' →L[ℝ] F))) →
      Z' = Work.ThomBordism.PontryaginThom.bundleMapEquiv Z e := by
    intro Z' hb hi hc
    cases Z' with
    | mk bs obs ia mba cc ccs cocc ccc =>
      simp only at hb hi hc
      subst hb
      subst hi
      have hcc : cc = Work.ThomBordism.PontryaginThom.bundleMapEquivCoordChange Z e := by
        funext i j x
        rw [hc i j x]
        rfl
      subst hcc
      rfl
  obtain ⟨Z', hb, hi, hc, hφ⟩ := Work.Thom.exists_coreMapFibre e Z
  rw [← key Z' hb hi hc]
  exact hφ.map Work.Thom.BundleIso.symm

end

end Work.Tubular
