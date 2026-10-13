import Mathlib
import Submission.Work.DSCOH.Basic

namespace Work.DSCOH

theorem resAt_id {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (S : Finset (Fin n)) :
    resAt (M := M) (le_refl S) =
      (LinearMap.id : locAt (M := M) S →ₗ[Poly A n] locAt (M := M) S) := by
  -- `resAt h` is `IsLocalizedModule.liftOfLE` for the inclusion of submonoids; with `h = le_refl`
  -- both the source and target localizations are `M[1/X_S]` and the map is obtained by lifting the
  -- localization map `M → M[1/X_S]` itself.  So it suffices to compare the two maps after
  -- precomposition with that localization map, where `lift_comp` and `id_comp` agree; this
  -- comparison is exactly the uniqueness statement `IsLocalizedModule.lift_unique`.
  unfold resAt LocalizedModule.liftOfLE IsLocalizedModule.liftOfLE
  exact IsLocalizedModule.lift_unique _ _ _ _ _ (LinearMap.id_comp _)

end Work.DSCOH
