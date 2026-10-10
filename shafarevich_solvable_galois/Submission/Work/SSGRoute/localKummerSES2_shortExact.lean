import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.Work.SSGRoute.LocalKummerAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

/-- **The `p`-th-power inclusion sequence at a local place.**  For a place `w` of a number field `K`
over `k`, the sequence `0 → (K_wˣ)^p → K_wˣ → K_wˣ ⧸ (K_wˣ)^p → 0` — the inclusion of the `p`-th
powers `localPthSub` and the quotient map — is short exact.  The proofs are elementary:
`Submodule.subtype` is injective, `Submodule.mkQ` is surjective, and vanishing in the quotient means
being a `p`-th power (`Submodule.Quotient.mk_eq_zero`).

Definitions live in `Submission.Work.SSGRoute.LocalKummerAux`.  Hint: elements of
`↥(localPthRep k K w p)` are elements of the subtype `↥(localPthSub k K w p)`, best handled with the
`show ↥(localPthSub k K w p) from x` idiom (see `kummer_level_defs.pthMapX_surjective`), and
`Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise` is the criterion
(import it from
`Submission.Commons.RepresentationTheory.GroupCohomology.groupCohomology_two_int_iso_one_qmodz`). -/
theorem localKummerSES2_shortExact (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (p : ℕ) :
    ∃ (h0 : localPthIncl k K w p ≫ localKummerQuotMap k K w p = 0),
      (ShortComplex.mk (localPthIncl k K w p) (localKummerQuotMap k K w p) h0).ShortExact := by
  -- The composite of the inclusion of the `p`-th powers with the quotient map is zero, because
  -- an element of the subtype `↥(localPthSub k K w p)` maps into `localPthSub` by definition.
  have h0 : localPthIncl k K w p ≫ localKummerQuotMap k K w p = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    simp only [Rep.hom_comp, Rep.zero_hom, Representation.IntertwiningMap.comp_toLinearMap,
      Representation.IntertwiningMap.zero_toLinearMap, LinearMap.comp_apply, LinearMap.zero_apply]
    have key : (Rep.Hom.hom (localKummerQuotMap k K w p)).toLinearMap
        ((Rep.Hom.hom (localPthIncl k K w p)).toLinearMap x)
        = (Submodule.mkQ (localPthSub k K w p))
            ((show ↥(localPthSub k K w p) from x) : ↥(localUnitsK (k := k) w)) := rfl
    rw [key, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero (localPthSub k K w p)).mpr
      (show ↥(localPthSub k K w p) from x).2
  refine ⟨h0, ?_⟩
  -- The elementwise mono/epi/kernel criterion: the inclusion is injective (it is a subtype
  -- inclusion), the quotient map is surjective, and an element killed by the quotient map lies in
  -- the `p`-th powers.
  refine Commons.RepresentationTheory.GroupCohomology.shortExact_of_mono_epi_elementwise
    (k := Coeff) (G := decompK (k := k) w)
    (ShortComplex.mk (localPthIncl k K w p) (localKummerQuotMap k K w p) h0) ?_ ?_ ?_
  · rw [Rep.mono_iff_injective]
    intro a b hab
    exact Subtype.ext hab
  · rw [Rep.epi_iff_surjective]
    intro y
    obtain ⟨v, hv⟩ := Submodule.mkQ_surjective (localPthSub k K w p) y
    exact ⟨v, by rw [localKummerQuotMap_apply]; exact hv⟩
  · intro x hx
    have hx'' : (Rep.Hom.hom (localKummerQuotMap k K w p)) x = 0 := hx
    have hxmem : x ∈ localPthSub k K w p := by
      have h : Submodule.Quotient.mk x
          = (0 : ↥(localUnitsK (k := k) w) ⧸ localPthSub k K w p) := by
        rw [← Submodule.mkQ_apply]
        exact hx''
      exact (Submodule.Quotient.mk_eq_zero _).mp h
    refine ⟨⟨x, hxmem⟩, ?_⟩
    exact localPthIncl_apply k K w p ⟨x, hxmem⟩

end Work.SSGRoute
