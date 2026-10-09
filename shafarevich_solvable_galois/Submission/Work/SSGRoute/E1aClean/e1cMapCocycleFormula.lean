import Mathlib
import Submission.Work.SSGRoute.E1cGeneric.Canonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `E1c` dictionary is computed by the cocycle attached to a lift

The canonical dictionary `E1cGeneric.e1cMap R : Ext¹_G(R, Kˣ) ≅ H¹(Γ, Hom_ℤ(R,Ωˣ))` is defined
through the cokernel description of the canonical free cover of `R`.  This file records the form in
which it is *used* in every comparison statement of the E1a lane: given a continuous cocycle
`c ∈ Z¹(Γ, Hom_ℤ(R,Ωˣ))` together with a lift `ñ ∈ Hom_ℤ(F,Ωˣ)` of its values to the middle term of
the cover (i.e. `iotaH (c g) = g·ñ − ñ` for all `g`), the class of `c` *is* the dictionary value:

  `e1cMap (PhiE y) = H1π c`,  where `y` is the `Ext⁰`-class whose `π`-image is `π ñ`.

This is the precise form of the slogan "the cocycle attached to `ψ ∈ Hom(R,U)` is
`g ↦ g·ψ̃ − ψ̃` for any extension `ψ̃` to `F`" used by the route of
`E1aClean.localDictionary_natural_family` (and by the base-change comparison (BC): both sides of
the square are `H1π` of one and the same cocycle).

The proof is cokernel bookkeeping: `betaH` is injective, `betaH ∘ e1cMap ∘ PhiE` is `mk' ∘ PsiEMap`
(by `e1cMap_Phi`), and `betaH (H1π c) = mk' (betaRaw c)`, where `betaRaw c = π (liftOf c)`; the
difference `liftOf c - ñ` is `Γ`-invariant because both its `d0`-images agree, so its `π`-image
lies in `range piH0`.
-/

namespace Work.SSGRoute.ExtChain.E1cGeneric

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- **The dictionary is the class of the cocycle attached to a lift `ñ`.**

`c` is a continuous `1`-cocycle with values in `M = Hom_ℤ(R,Ωˣ)` and `ñ ∈ Hom_ℤ(F,Ωˣ)` a lift of
`c` to the middle term of the canonical cover (`iotaH (c g) = d0 ñ g`, i.e. `c g = g·ñ − ñ`); `y`
is the `Ext⁰`-class whose `π`-image in `H⁰(Γ, Hom_ℤ(R₁,Ωˣ))` is `π ñ`.  Then the `E1c`-dictionary
value of `PhiE y` is the class of `c`. -/
theorem e1cMap_eq_H1π_of_cocycle_lift (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R)))
    (ñ : E1cN (k := k) (Ω := Ω) (K := K) R)
    (hñ : ∀ g : Ω ≃ₐ[k] Ω,
      iotaH (k := k) (Ω := Ω) (K := K) R (c.1 g) =
        Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R) ñ g)
    (y : CategoryTheory.Abelian.Ext.{0}
      (E1cR1 (k := k) (Ω := Ω) (K := K) R) (unitsK k K) 0)
    (hy : (piH (k := k) (Ω := Ω) (K := K) R ñ : Work.SSGRoute.homCoind k Ω K
          (E1cR1 (k := k) (Ω := Ω) (K := K) R))
        = ↑(PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y)) :
    e1cMap (k := k) (Ω := Ω) (K := K) R (PhiE (k := k) (Ω := Ω) (K := K) R y)
      = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) c := by
  -- `π ñ` is `Γ`-invariant
  have hmem : piH (k := k) (Ω := Ω) (K := K) R ñ
      ∈ Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.homCoind k Ω K (E1cR1 (k := k) (Ω := Ω) (K := K) R)) := by
    rw [← d0_eq_zero_iff]
    funext g
    rw [d0_piH]
    show piH (k := k) (Ω := Ω) (K := K) R
        (Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R) ñ g) = 0
    rw [← hñ g, piH_iotaH]
  -- the two cokernel classes agree
  have hmk : QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
        (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y)
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (betaRaw (k := k) (Ω := Ω) (K := K) R c) := by
    have hyS : PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) y
        = (⟨piH (k := k) (Ω := Ω) (K := K) R ñ, hmem⟩ :
            ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
              (Work.SSGRoute.homCoind k Ω K (E1cR1 (k := k) (Ω := Ω) (K := K) R)))) :=
      Subtype.ext hy.symm
    rw [hyS]
    refine (QuotientAddGroup.eq_iff_sub_mem).mpr ?_
    -- `liftOf c - ñ` is `Γ`-invariant
    have hw : liftOf (k := k) (Ω := Ω) (K := K) R c - ñ
        ∈ Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
            (E1cN (k := k) (Ω := Ω) (K := K) R) := by
      rw [← d0_eq_zero_iff, map_sub]
      apply sub_eq_zero.mpr
      funext g
      rw [liftOf_spec, Work.AbsoluteKummer.mapZ1_apply]
      exact hñ g
    refine AddMonoidHom.mem_range.mpr
      ⟨-⟨liftOf (k := k) (Ω := Ω) (K := K) R c - ñ, hw⟩, ?_⟩
    apply Subtype.ext
    show piH (k := k) (Ω := Ω) (K := K) R
        (-(liftOf (k := k) (Ω := Ω) (K := K) R c - ñ))
      = piH (k := k) (Ω := Ω) (K := K) R ñ
        - piH (k := k) (Ω := Ω) (K := K) R (liftOf (k := k) (Ω := Ω) (K := K) R c)
    rw [map_neg, map_sub]
    abel
  -- conclude by injectivity of `betaH`
  apply betaH_injective (k := k) (Ω := Ω) (K := K) R
  rw [e1cMap_Phi (k := k) (Ω := Ω) (K := K) R y,
    ← betaEquiv_apply (k := k) (Ω := Ω) (K := K) R, AddEquiv.apply_symm_apply]
  rw [show betaH (k := k) (Ω := Ω) (K := K) R
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R) c)
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (betaRaw (k := k) (Ω := Ω) (K := K) R c) from
        betaH_mk (k := k) (Ω := Ω) (K := K) R c, ← hmk]

end

end Work.SSGRoute.ExtChain.E1cGeneric
