import Mathlib
import Submission.Work.MotC2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `letI`/`haveI` are needed below to register the instance arguments that `IsRatPlace` and
-- `IsDiscreteValuationRing` carry implicitly; the style linter would prefer `let`/`have`, which
-- drops them from the instance search, so it is silenced here.
set_option linter.style.haveILetI false

namespace Work.MotC2

variable {L : Type*} [Field L]

/-! ## Transporting discrete valuation ring structures along algebra isomorphisms -/

/-- A discrete valuation ring structure is transported along an `L`-algebra isomorphism of
subalgebras of a field: the image of a DVR under `Θ` is again a DVR.

`IsPrincipalIdealRing` is transported along the surjective ring hom `↥S → ↥S'`,
`IsLocalRing` along the ring equivalence, and `not_a_field'` because
`𝔪_{S'} = 𝔪_S.map Θ` (`IsLocalRing.map_ringEquiv_maximalIdeal`) is the image of a non-zero
ideal under an injective map. -/
lemma isDiscreteValuationRing_map_algEquiv {F : Type*} [Field F] [Algebra L F]
    (S : Subalgebra L F) (Θ : F ≃ₐ[L] F) (hS : IsDiscreteValuationRing S) :
    IsDiscreteValuationRing (S.map Θ.toAlgHom) := by
  letI : IsDiscreteValuationRing S := hS
  let e := Subalgebra.equivMapOfInjective S Θ.toAlgHom Θ.injective
  have hpid : IsPrincipalIdealRing ↥(S.map Θ.toAlgHom) :=
    IsPrincipalIdealRing.of_surjective (e : ↥S →+* ↥(S.map Θ.toAlgHom)) e.surjective
  haveI hloc : IsLocalRing ↥(S.map Θ.toAlgHom) := RingEquiv.isLocalRing e.toRingEquiv
  refine { __ := hpid, __ := hloc, not_a_field' := ?_ }
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal (e : ↥S ≃+* ↥(S.map Θ.toAlgHom))]
  intro h
  exact IsDiscreteValuationRing.not_a_field S
    ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h)

/-- The residue field of the image subalgebra `S.map Θ.toAlgHom` is the image of the residue field
of `S` under the ring isomorphism induced by `Θ`: the residue class of `algebraMap L ↥S c` is
mapped to the residue class of `algebraMap L ↥S' c`.

This is the commutation of the canonical map `L → S' ⧸ 𝔪_{S'}` with the quotient isomorphism
`IsLocalRing.ResidueField.mapEquiv Θ`. -/
lemma residueField_mapEquiv_algebraMap {F : Type*} [Field F] [Algebra L F]
    (S : Subalgebra L F) (Θ : F ≃ₐ[L] F) (hS : IsDiscreteValuationRing S)
    (hS' : IsDiscreteValuationRing (S.map Θ.toAlgHom)) (c : L) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (S.map Θ.toAlgHom))
        (algebraMap L (S.map Θ.toAlgHom) c)
      = IsLocalRing.ResidueField.mapEquiv
          (Subalgebra.equivMapOfInjective S Θ.toAlgHom Θ.injective).toRingEquiv
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (algebraMap L S c)) := by
  letI : IsDiscreteValuationRing S := hS
  letI : IsDiscreteValuationRing (S.map Θ.toAlgHom) := hS'
  let e := Subalgebra.equivMapOfInjective S Θ.toAlgHom Θ.injective
  show IsLocalRing.residue (S.map Θ.toAlgHom) (algebraMap L (S.map Θ.toAlgHom) c)
      = IsLocalRing.ResidueField.mapEquiv (e.toRingEquiv)
          (IsLocalRing.residue S (algebraMap L S c))
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rw [← e.commutes c]
  rfl

/-! ## Rational places are preserved by automorphisms -/

/-- Rational places are preserved by `L`-algebra automorphisms of the function field: if `S` is a
rational place of `L(E)/L` then so is its image under `Θ`.

Route.  Let `S' := Subalgebra.map Θ.toAlgHom S`.  `Θ` restricts to an `L`-algebra isomorphism
`↥S ≃ₐ[L] ↥S'` (`Subalgebra.map` is the image, `Θ` is injective), so `S'` is a discrete valuation
ring (transport `IsDiscreteValuationRing` along this algebra equivalence), the maximal ideals
correspond (`Ideal.map` of `𝔪_S` under the surjective hom `↥S → ↥S'` is a maximal ideal of `↥S'`,
hence equals `IsLocalRing.maximalIdeal ↥S'`), and the residue fields are `L`-isomorphic, giving the
bijectivity of `c ↦ Ideal.Quotient.mk 𝔪_{S'} (algebraMap L ↥S' c)` from the same statement for `S`.
For the second conjunct: write `f = Θ (Θ.symm f)` and use that `Θ.symm f * b = a` with `a, b ∈ S`
gives `f * Θ b = Θ a` with `Θ a, Θ b ∈ S'` and `Θ b ≠ 0`. -/
theorem IsRatPlaceMap (L : Type*) [Field L] (E : WeierstrassCurve L)
    (Θ : Work.MotC2.Func E ≃ₐ[L] Work.MotC2.Func E) (S : Subalgebra L (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) :
    Work.MotC2.IsRatPlace E (Subalgebra.map Θ.toAlgHom S) := by
  obtain ⟨⟨hDVR, hres⟩, hfrac⟩ := hS
  letI : IsDiscreteValuationRing ↥S := hDVR
  have hDVR' : IsDiscreteValuationRing ↥(S.map Θ.toAlgHom) :=
    isDiscreteValuationRing_map_algEquiv S Θ hDVR
  -- The residue field of `S'` is the residue field of `S`, so `L → S' ⧸ 𝔪_{S'}` is the composite
  -- of the bijection `L → S ⧸ 𝔪_S` with the quotient isomorphism, hence bijective.
  have hbij : Function.Bijective fun c : L =>
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(S.map Θ.toAlgHom))
        (algebraMap L ↥(S.map Θ.toAlgHom) c) := by
    have hfuneq :
        (fun c : L => Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(S.map Θ.toAlgHom))
            (algebraMap L ↥(S.map Θ.toAlgHom) c))
          = (IsLocalRing.ResidueField.mapEquiv
                (Subalgebra.equivMapOfInjective S Θ.toAlgHom Θ.injective).toRingEquiv) ∘
            (fun c : L =>
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥S) (algebraMap L ↥S c)) :=
      funext fun c => residueField_mapEquiv_algebraMap S Θ hDVR hDVR' c
    rw [hfuneq]
    exact (IsLocalRing.ResidueField.mapEquiv
      (Subalgebra.equivMapOfInjective S Θ.toAlgHom Θ.injective).toRingEquiv).bijective.comp hres
  refine ⟨⟨hDVR', hbij⟩, ?_⟩
  -- `S'` also generates `L(E)` as a fraction field: transport a witness through `Θ`.
  intro f
  obtain ⟨s₁, s₂, hs₂, hprod⟩ := hfrac (Θ.symm f)
  refine ⟨⟨Θ (s₁ : Func E), Subalgebra.mem_map.mpr ⟨(s₁ : Func E), s₁.2, rfl⟩⟩,
          ⟨Θ (s₂ : Func E), Subalgebra.mem_map.mpr ⟨(s₂ : Func E), s₂.2, rfl⟩⟩, ?_, ?_⟩
  · exact fun h => hs₂ (Θ.injective (by simpa using h))
  · have := congrArg Θ hprod
    simpa using this

end Work.MotC2
