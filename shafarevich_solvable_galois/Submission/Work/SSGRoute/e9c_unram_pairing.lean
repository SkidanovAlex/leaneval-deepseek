import Mathlib
import Submission.Work.SSGRoute.E9c.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-- **E9c, an unramified local class pairs to an unramified `H²`-value.**

For a place `w` of `K`, a class `ζ ∈ Ext¹_{D_w}(res M, K_wˣ)` which is unramified (comes from
`𝒪_wˣ`, `SSGRoute.PTExt.IsUnramifiedExt`) and any `h ∈ H¹(Gal(K/k), M)`, the Yoneda product
`ζ ∘ h ∈ H²_{D_w}(ℤ, K_wˣ)` is unramified.  This is a purely formal consequence of
`ζ = ζ' ≫ mk₀ (localUnitsIncl w)`: associativity of `Abelian.Ext.comp`
(`Abelian.Ext.comp_assoc_of_third_deg_zero`, `Abelian.Ext.mk₀_comp_mk₀`) gives
`h.comp (ζ' ≫ mk₀ incl) rfl = (h.comp ζ' rfl) ≫ mk₀ incl` (one line:
`obtain ⟨ζ', hζ'⟩ := hζ; refine ⟨(extHRestrict (decompK w) h).comp ζ' rfl, ?_⟩; rw [hζ', yonedaPair];
exact (Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ rfl).symm`).

Consumer: with `Work.SSGRoute.eq_zero_of_isUnramifiedExt_of_unramified` this kills the local
pairings at all places `w` at which the extension `K/k` is unramified. -/
theorem e9c_unram_pairing {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} (w : Place K)
    (ζ : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)
    (h : extH M 1) (hζ : IsUnramifiedExt (k := k) (K := K) w ζ) :
    IsUnramifiedExt (k := k) (K := K) w
      (yonedaPair ζ (extHRestrict (decompK (k := k) w) h)) := by
  obtain ⟨ζ', hζ'⟩ := hζ
  refine ⟨(extHRestrict (decompK (k := k) w) h).comp ζ' rfl, ?_⟩
  rw [hζ', yonedaPair]
  exact (Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ rfl).symm

end Work.SSGRoute
