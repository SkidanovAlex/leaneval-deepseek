import Mathlib
import Submission.Work.MotC2.IsRatPlaceMap
import Submission.Work.MotC2.Places

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

namespace Work.MotK.TwRuling

variable {L : Type*} [Field L]

/-! ## Transporting the place structure along an isomorphism of function fields

The predicate `Work.MotC2.IsRatPlace E S` only refers to the ambient field `L(E)` (the curve `E`
occurs only through that type).  Accordingly we prove the transport statement for two abstract
`L`-fields `F`, `F'` and an `L`-algebra isomorphism `Θ : F ≃ₐ[L] F'`, and specialise it to
`F = L(E)`, `F' = L(E')` afterwards. -/

/-- A discrete valuation ring structure is transported along an `L`-algebra isomorphism of ambient
fields: the image of a DVR `S ⊆ F` under `Θ : F ≃ₐ[L] F'` is again a DVR.

`IsPrincipalIdealRing` is transported along the surjective ring hom `↥S → ↥(S.map Θ.toAlgHom)`,
`IsLocalRing` along the ring equivalence, and `not_a_field'` because
`𝔪_{S'} = 𝔪_S.map Θ` (`IsLocalRing.map_ringEquiv_maximalIdeal`) is the image of a non-zero
ideal under an injective map. -/
lemma isDVR_map_algEquiv {F F' : Type*} [Field F] [Field F'] [Algebra L F] [Algebra L F']
    (S : Subalgebra L F) (Θ : F ≃ₐ[L] F') (hS : IsDiscreteValuationRing S) :
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
mapped to the residue class of `algebraMap L ↥(S.map Θ.toAlgHom) c`.

This is the commutation of the canonical map `L → S' ⧸ 𝔪_{S'}` with the quotient isomorphism
`IsLocalRing.ResidueField.mapEquiv Θ`. -/
lemma residue_map_algEquiv {F F' : Type*} [Field F] [Field F'] [Algebra L F] [Algebra L F']
    (S : Subalgebra L F) (Θ : F ≃ₐ[L] F') (hS : IsDiscreteValuationRing S)
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

/-- Rational places are preserved by `L`-algebra isomorphisms of function fields: if the
`L`-subalgebra `S ⊆ F` is a DVR with residue field `L` which generates `F` as a fraction field,
then its image under `Θ : F ≃ₐ[L] F'` has the same properties inside `F'`.

Route.  Let `S' := S.map Θ.toAlgHom`.  `Θ` restricts to an `L`-algebra isomorphism
`↥S ≃ₐ[L] ↥S'`, so `S'` is a discrete valuation ring (transport `IsDiscreteValuationRing` along
this algebra equivalence), the maximal ideals correspond, and the residue fields are
`L`-isomorphic, giving the bijectivity of `c ↦ Ideal.Quotient.mk 𝔪_{S'} (algebraMap L ↥S' c)` from
the same statement for `S`.  For the second conjunct: write `f = Θ (Θ.symm f)` and use that
`Θ.symm f * b = a` with `a, b ∈ S` gives `f * Θ b = Θ a` with `Θ a, Θ b ∈ S'` and `Θ b ≠ 0`. -/
lemma isRatPlace_map_algEquiv {F F' : Type*} [Field F] [Field F'] [Algebra L F] [Algebra L F']
    (S : Subalgebra L F) (Θ : F ≃ₐ[L] F')
    (hS : (∃ _ : IsDiscreteValuationRing S,
        Function.Bijective fun c : L =>
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (algebraMap L S c)) ∧
      (∀ f : F, ∃ s₁ : S, ∃ s₂ : S, (s₂ : F) ≠ 0 ∧ f * (s₂ : F) = (s₁ : F))) :
    (∃ _ : IsDiscreteValuationRing (S.map Θ.toAlgHom),
        Function.Bijective fun c : L =>
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (S.map Θ.toAlgHom))
            (algebraMap L (S.map Θ.toAlgHom) c)) ∧
      (∀ f : F', ∃ s₁ : S.map Θ.toAlgHom, ∃ s₂ : S.map Θ.toAlgHom,
        (s₂ : F') ≠ 0 ∧ f * (s₂ : F') = (s₁ : F')) := by
  obtain ⟨⟨hDVR, hres⟩, hfrac⟩ := hS
  haveI : IsDiscreteValuationRing ↥S := hDVR
  have hDVR' : IsDiscreteValuationRing ↥(S.map Θ.toAlgHom) := isDVR_map_algEquiv S Θ hDVR
  haveI : IsDiscreteValuationRing ↥(S.map Θ.toAlgHom) := hDVR'
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
      funext fun c => residue_map_algEquiv S Θ hDVR hDVR' c
    rw [hfuneq]
    exact (IsLocalRing.ResidueField.mapEquiv
      (Subalgebra.equivMapOfInjective S Θ.toAlgHom Θ.injective).toRingEquiv).bijective.comp hres
  refine ⟨⟨hDVR', hbij⟩, ?_⟩
  -- `S'` also generates `F'` as a fraction field: transport a witness through `Θ`.
  intro f
  obtain ⟨s₁, s₂, hs₂, hprod⟩ := hfrac (Θ.symm f)
  refine ⟨⟨Θ (s₁ : F), Subalgebra.mem_map.mpr ⟨(s₁ : F), s₁.2, rfl⟩⟩,
          ⟨Θ (s₂ : F), Subalgebra.mem_map.mpr ⟨(s₂ : F), s₂.2, rfl⟩⟩, ?_, ?_⟩
  · exact fun h => hs₂ (Θ.injective (by simpa using h))
  · have := congrArg Θ hprod
    simpa using this

theorem IsRatPlaceMap_v2 (L : Type*) [Field L] (E E' : WeierstrassCurve L)
    (Θ : Work.MotC2.Func E ≃ₐ[L] Work.MotC2.Func E') (S : Subalgebra L (Work.MotC2.Func E))
    (hS : Work.MotC2.IsRatPlace E S) :
    Work.MotC2.IsRatPlace E' (Subalgebra.map Θ.toAlgHom S) := by
  exact isRatPlace_map_algEquiv S Θ hS

end Work.MotK.TwRuling
