import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.pt_pairing_ext
import Submission.Work.SSGRoute.extIdele_localisation_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **Injectivity of the place-by-place localisation of `Extʳ_G(M, 𝕀_K)` for finite `M`.**

If a class `x ∈ Extʳ_{Gal(K/k)}(M, 𝕀_K)` localises to `0` at *every* place `w` of `K`
(`extLoc w x = 0`), then `x = 0`.  This is the injectivity half of the idèle Shapiro theorem
(`Work.SSGRoute.ext_idele_shapiro_aux`, node E2 of `DESIGN_EXT.md`), applied to a transversal `R`
of the `Gal(K/k)`-orbits of `Place K`: the hypothesis `∀ w, extLoc w x = 0` restricted to the
places of `R` is exactly the hypothesis of E2. -/
theorem extIdele_localisation_injective_of_finite (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ M.V] (r : ℕ)
    (x : Abelian.Ext.{0} M (idelesK (k := k) K) r)
    (h : ∀ w : NK.GlobalCFT.Place K, extLoc (k := k) w x = 0) : x = 0 := by
  obtain ⟨R, hR⟩ := exists_transversal_of_mulAction (K ≃ₐ[k] K) (NK.GlobalCFT.Place K)
  exact (ext_idele_shapiro_aux k K M (by infer_instance) r R hR).1 x (fun w _ => h w)

theorem extToIdeles_eq_zero_iff_extLoc (k : Type) [Field k] [NumberField k]
    (K : Type) [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ M.V]
    (y : CategoryTheory.Abelian.Ext.{0} M (SSGRoute.PTExt.unitsK k K) 2) :
    SSGRoute.PTExt.extToIdeles (k := k) y = 0 ↔
      ∀ w : NK.GlobalCFT.Place K,
        SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by
  constructor
  · intro h w
    rw [h, extLoc_zero k K w]
  · intro h
    exact extIdele_localisation_injective_of_finite k K M 2
      (SSGRoute.PTExt.extToIdeles (k := k) y) (fun w => h w)

end Work.SSGRoute
