import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.NK.HassePrinciple.localUnits_h2_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node `C1` of the E7cΩ route: the valuation criterion for unramified `Ext¹`-classes

For a finite place `w = Place.ofFinite q` of `K` (with `k ⊆ K` finite Galois), an `Ext¹`-class
`y : Ext¹_{D_w}(res M, K_wˣ)` is *unramified* (`SSGRoute.PTExt.IsUnramifiedExt w y`, i.e. it lies in
the image of `Ext¹_{D_w}(res M, 𝒪_wˣ) → Ext¹_{D_w}(res M, K_wˣ)`) **iff** it is killed by the
valuation `K_wˣ → ℤ`:
`y.comp (mk₀ (localUnitsValHom q)) = 0`.

This is the exactness at `Ext¹` of the long exact `Ext`-sequence of the short exact sequence of
`D_w`-representations
`0 → 𝒪_wˣ → K_wˣ → ℤ → 0`.

The short complex and its short exactness are already in the NK library
(`NK.HassePrinciple.localUnitsShortComplex`, `…_shortExact`, inside
`Submission/NK/HassePrinciple/localUnits_h2_injective.lean`), so `C1` is the single Ext-exactness
step below.  (This corrects the note `E7cOmega/NOTE_from_sha2_image_of_Hm2_on_lead_route.md` §3,
which assumed the short exact sequence still had to be built.)
-/

open CategoryTheory

set_option autoImplicit false

noncomputable section

namespace Work.SSGRoute.ValuationSES

open SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- **C1.** For a finite place `w = Place.ofFinite q`, an `Ext¹`-class `y` is unramified iff the
valuation `K_wˣ → ℤ` kills it. -/
theorem isUnramifiedExt_iff_comp_valHom
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (y : Abelian.Ext.{0}
      (Rep.res (decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite q)) 1) :
    IsUnramifiedExt (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite q) y ↔
      y.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q))
        (add_zero 1) = 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    have hfg : (Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsIncl (K := k) (L := K)
          (NK.GlobalCFT.Place.ofFinite q))).comp
          (Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q))
          (zero_add 0) = 0 := by
      rw [Abelian.Ext.mk₀_comp_mk₀, NK.HassePrinciple.localUnitsIncl_comp_valHom,
        Abelian.Ext.mk₀_zero]
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero, hfg]
    simp
  · intro hy
    obtain ⟨z, hz⟩ := Abelian.Ext.covariant_sequence_exact₂
      (Rep.res (decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (S := NK.HassePrinciple.localUnitsShortComplex (K := k) (L := K) q)
      (NK.HassePrinciple.localUnitsShortComplex_shortExact (K := k) (L := K) q) y hy
    exact ⟨z, hz.symm⟩

end Work.SSGRoute.ValuationSES
