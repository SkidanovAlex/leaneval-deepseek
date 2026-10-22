import Mathlib
import Submission.Work.DISC.sections_disc

/-!
# The section identification `sdPhi` is `ℤ`-linear

For a discrete abelian group `M` and light profinite sets `S`, `T`, the section-wise
identification

`(ℤ[T] ⟶ (ℤ[S] ⟹ ΔM)) ≃ LocallyConstant (S × T) M`

of `Submission/Work/DISC/sections_disc.lean` (there called `Work.DISC.sdPhi`) is additive,
hence a `ℤ`-linear equivalence. This file records that linear structure explicitly, keeping the
underlying function *definitionally* equal to `Work.DISC.sdPhi`.

The additivity input is `Work.DISC.sdPhi_sub`, which is proved by reducing `sdPhi` to a composite
of the closed-structure adjunction, a precomposition with an isomorphism, and `homFreeEquiv`,
each of which is additive. Since the scalar action on both sides is the canonical `ℤ`-action
determined by the additive structure, additivity upgrades to `ℤ`-linearity via
`AddMonoidHom.map_zsmul`.
-/

namespace Work.ANALYTIC.CechPt

theorem exists_sdPhiLinear (M : ModuleCat.{0} ℤ) (S T : LightProfinite.{0}) : ∃ e : (Work.DISC.zfree T ⟶ (CategoryTheory.ihom (Work.DISC.zfree S)).obj (Work.DISC.lcDisc M)) ≃ₗ[ℤ] LocallyConstant (↥S.toTop × ↥T.toTop) ↥M, ⇑e = ⇑(Work.DISC.sdPhi M S T) := by
  -- The additive structure underlying `sdPhi`: additivity of `sdPhi` packaged as a hom.
  let A : (Work.DISC.zfree T ⟶ (CategoryTheory.ihom (Work.DISC.zfree S)).obj
      (Work.DISC.lcDisc M)) →+ LocallyConstant (↥S.toTop × ↥T.toTop) ↥M :=
    { toFun := ⇑(Work.DISC.sdPhi M S T)
      map_zero' := Work.DISC.sdPhi_zero M S T
      map_add' := fun x y => by
        have h := Work.DISC.sdPhi_sub M S T (x + y) x
        have h' : (x + y) - x = y := by abel
        rw [h'] at h
        rw [h]; abel }
  -- Promote the additive equivalence `sdPhi` to a `ℤ`-linear equivalence, keeping the same
  -- underlying function.
  refine ⟨{ toFun := A
            invFun := ⇑((Work.DISC.sdPhi M S T).symm)
            map_add' := fun x y => A.map_add x y
            map_smul' := fun m x => by
              show A (m • x) = (RingHom.id ℤ) m • A x
              exact A.map_zsmul m x
            left_inv := fun x => (Work.DISC.sdPhi M S T).left_inv x
            right_inv := fun y => (Work.DISC.sdPhi M S T).right_inv y }, rfl⟩

end Work.ANALYTIC.CechPt
