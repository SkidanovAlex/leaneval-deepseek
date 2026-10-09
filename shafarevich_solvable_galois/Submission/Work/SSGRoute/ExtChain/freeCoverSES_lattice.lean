import Mathlib
import Submission.Work.SSGRoute.ExtChain.FreeCover
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ExtChain

open CategoryTheory

/-- The syzygy `R` of the canonical presentation `0 → R → F → X → 0` of a finite representation
`X` (with `F` the free representation on the underlying set of `X`) is free over `ℤ`: it is the
kernel of a surjection from the free `ℤ`-module `Rep.free Coeff G X.V` onto `X`, hence a submodule
of a free module over the PID `ℤ`. -/
theorem freeCoverSES_lattice {G : Type} [Group G] [Fintype G]
    (X : Rep.{0} SSGRoute.PTExt.Coeff G) [Finite X.V] :
    Module.Free ℤ (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)).V := by
  -- Pin the honest `Coeff`-module structures carried by the representations, so that the
  -- intertwining map of the canonical cover can be read as a linear map (`ULift.module` would
  -- otherwise compete with the structures stored in the two `Rep`s).
  letI : Module SSGRoute.PTExt.Coeff
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)).V :=
    (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)).hV2
  letI : Module SSGRoute.PTExt.Coeff (Rep.free SSGRoute.PTExt.Coeff G X.V).V :=
    (Rep.free SSGRoute.PTExt.Coeff G X.V).hV2
  -- The syzygy is a finitely generated `ℤ`-module: it is the kernel of a map from the finitely
  -- generated free `ℤ`-module `Rep.free Coeff G X.V`, and `ℤ` is Noetherian.
  haveI hfin : Module.Finite ℤ (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)).V :=
    Work.SSGRoute.freeCoverSES_finite X
  -- The canonical cover is a monomorphism, so its underlying map is injective.
  have hmono : Function.Injective
      (⇑(Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover X)))) :=
    (Rep.mono_iff_injective _).mp inferInstance
  -- The same map, as a `ℤ`-linear map.
  let iota : (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)).V →ₗ[ℤ]
      (Rep.free SSGRoute.PTExt.Coeff G X.V).V :=
    (Rep.Hom.hom (CategoryTheory.Limits.kernel.ι (Work.SSGRoute.freeCover X))).toLinearMap
      |>.toAddMonoidHom.toIntLinearMap
  have hcoe : ⇑iota = ⇑(Rep.Hom.hom (CategoryTheory.Limits.kernel.ι
      (Work.SSGRoute.freeCover X))) := rfl
  -- The syzygy is torsion-free: it embeds `ℤ`-linearly into the free `ℤ`-module
  -- `Rep.free Coeff G X.V`, which is torsion-free over `ℤ`.
  haveI htf : Module.IsTorsionFree ℤ
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover X)).V :=
    Function.Injective.moduleIsTorsionFree (R := ℤ) (f := iota)
      (by rw [hcoe]; exact hmono) (fun r m => iota.map_smul r m)
  -- A finitely generated torsion-free module over the PID `ℤ` is free.
  exact Module.free_of_finite_type_torsion_free'

end Work.SSGRoute.ExtChain
