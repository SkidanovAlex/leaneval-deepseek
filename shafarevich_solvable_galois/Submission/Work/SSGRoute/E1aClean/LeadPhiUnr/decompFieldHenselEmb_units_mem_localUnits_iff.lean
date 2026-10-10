import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E1aClean.phiUnrU1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aClean.LeadPhiUnr

open scoped Valued

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-- **(U3), integrality form.**  The canonical embedding `K^h → K_q`
(`decompFieldHenselEmb`) is compatible with the two integral structures: an element of the
henselisation `K^h = Ω^{D_A ⊓ G_K}` is integral for the valuation ring `𝒪_q` of the completion
`K_q` exactly when it is `A`-integral in `Ω`.

The proof is the chain

`𝒪_q ∋ φ u  ↔  𝒪_q = (𝒪_v).comap (adicCompletionToPlaceCompletion)  ↔  𝒪_v ∋ f (φ u)`

(`comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers`), then `f (φ u)` is the
coercion of `algebraMap (φ u) = coInAdjoin u` — the specification `decompFieldHenselEmb_spec` of
the canonical embedding — and finally the contraction
`(𝒪_v).comap (placeCompletionCoe A) = A` (`comap_placeCompletionIntegers`). -/
theorem decompFieldHenselEmb_mem_adicCompletionIntegers_iff
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z)
    (u : ↥(henselOverDecomp k Ω K A)) :
    decompFieldHenselEmb k Ω K A hA q hAq halg u ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K q
      ↔ A.valuation ((u : ↥(henselOverDecomp k Ω K A)) : Ω) ≤ 1 := by
  have hAqK : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q :=
    Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  -- the key compatibility: the two images of `u` in the completion of `Ω` at `A` agree
  have hcoe : NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK
      (decompFieldHenselEmb k Ω K A hA q hAq halg u)
      = NK.NeukirchUchida.placeCompletionCoe A
          ((u : ↥(henselOverDecomp k Ω K A)) : Ω) := by
    have hspec := decompFieldHenselEmb_spec k Ω K A hA q hAq halg u
    have h := congrArg
      (fun y : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := ↥K) (K' := Ω) q A) =>
        (y : NK.NeukirchUchida.placeCompletion A)) hspec
    simp only [IntermediateField.coe_algebraMap_apply, NK.NeukirchUchida.coe_coInAdjoin] at h
    rwa [halg] at h
  -- integrality in the adic completion is integrality in the place completion
  have hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K q :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers q A hAqK
  have hm : decompFieldHenselEmb k Ω K A hA q hAq halg u ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K q
      ↔ NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK
          (decompFieldHenselEmb k Ω K A hA q hAq halg u)
          ∈ NK.NeukirchUchida.placeCompletionIntegers A := by
    rw [← hW]
    exact ValuationSubring.mem_comap
  -- integrality in the place completion is `A`-integrality of the element of `Ω`
  have hPgen : ∀ y : Ω, y ∈ A ↔ NK.NeukirchUchida.placeCompletionCoe A y ∈
      NK.NeukirchUchida.placeCompletionIntegers A := by
    intro y
    have hmem := ValuationSubring.mem_comap (A := NK.NeukirchUchida.placeCompletionIntegers A)
      (f := NK.NeukirchUchida.placeCompletionCoe A) (x := y)
    rw [NK.NeukirchUchida.comap_placeCompletionIntegers A] at hmem
    exact hmem
  rw [hm, hcoe, ← hPgen ((u : ↥(henselOverDecomp k Ω K A)) : Ω)]
  exact (ValuationSubring.valuation_le_one_iff A _).symm

/-- **(U3)** The canonical embedding `K^h → K_q` respects integrality of units: a unit of `K^h`
maps into the local units of `q` iff its `A`-valuation is `1`.  Lead design
`_lead_design/ssg_phiunr_1120.md`.  Proof inputs: `decompFieldHenselEmb_spec` and
`comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers`, together with
`mem_localUnits_ofFinite_iff_valued_eq_one` and `comap_placeCompletionIntegers` (applied to `x` and
to `x⁻¹`). -/
theorem decompFieldHenselEmb_units_mem_localUnits_iff
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    [inst : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)]
    (halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A
          (Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq) z)
    (x : (↥(henselOverDecomp k Ω K A))ˣ) :
    Units.map (decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom x ∈
        NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite q)
      ↔ A.valuation (((x : ↥(henselOverDecomp k Ω K A)) : Ω)) = 1 := by
  -- the inverse of the image of `x` is the image of the inverse of `x`
  have h_inv : ((Units.map (decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom x)⁻¹ :
        q.adicCompletion ↥K)
      = decompFieldHenselEmb k Ω K A hA q hAq halg
          ((x⁻¹ : (↥(henselOverDecomp k Ω K A))ˣ) : ↥(henselOverDecomp k Ω K A)) := by
    rw [Units.coe_map (decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom x,
      Units.val_inv_eq_inv_val x]
    exact (map_inv₀ (decompFieldHenselEmb k Ω K A hA q hAq halg)
      ((x : (↥(henselOverDecomp k Ω K A))ˣ) : ↥(henselOverDecomp k Ω K A))).symm
  -- the inverse of an element of the henselisation, inside `Ω`
  have h_Omega : (((x⁻¹ : (↥(henselOverDecomp k Ω K A))ˣ) :
        ↥(henselOverDecomp k Ω K A)) : Ω)
      = (((x : (↥(henselOverDecomp k Ω K A))ˣ) :
        ↥(henselOverDecomp k Ω K A)) : Ω)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
  rw [NK.GlobalCFT.Place.localUnits_ofFinite]
  constructor
  · -- a local unit is integral, together with its inverse
    intro hx
    rw [Submonoid.mem_units_iff] at hx
    obtain ⟨h1, h2⟩ := hx
    have h1' : decompFieldHenselEmb k Ω K A hA q hAq halg
        ((x : (↥(henselOverDecomp k Ω K A))ˣ) : ↥(henselOverDecomp k Ω K A)) ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K q := by
      rwa [Units.coe_map] at h1
    have h2' : decompFieldHenselEmb k Ω K A hA q hAq halg
        ((x⁻¹ : (↥(henselOverDecomp k Ω K A))ˣ) : ↥(henselOverDecomp k Ω K A)) ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ↥K q := by
      rw [Units.val_inv_eq_inv_val
        (Units.map (decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom x)] at h2
      rwa [h_inv] at h2
    have hle : A.valuation (((x : (↥(henselOverDecomp k Ω K A))ˣ) :
        ↥(henselOverDecomp k Ω K A)) : Ω) ≤ 1 :=
      (decompFieldHenselEmb_mem_adicCompletionIntegers_iff k Ω K A hA q hAq halg _).mp h1'
    have h2u : (A.valuation (((x : (↥(henselOverDecomp k Ω K A))ˣ) :
        ↥(henselOverDecomp k Ω K A)) : Ω))⁻¹ ≤ 1 := by
      have h := (decompFieldHenselEmb_mem_adicCompletionIntegers_iff
        k Ω K A hA q hAq halg _).mp h2'
      rw [h_Omega, Valuation.map_inv] at h
      exact h
    have hne : A.valuation (((x : (↥(henselOverDecomp k Ω K A))ˣ) :
        ↥(henselOverDecomp k Ω K A)) : Ω) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      intro hzero
      refine Units.ne_zero x (Subtype.ext ?_)
      rw [hzero]
      simp
    have hge : (1 : A.ValueGroup) ≤ A.valuation (((x : (↥(henselOverDecomp k Ω K A))ˣ) :
        ↥(henselOverDecomp k Ω K A)) : Ω) := by
      have hpos : 0 < (A.valuation (((x : (↥(henselOverDecomp k Ω K A))ˣ) :
          ↥(henselOverDecomp k Ω K A)) : Ω))⁻¹ :=
        zero_lt_iff.mpr (inv_ne_zero hne)
      have hone := (one_le_inv₀ hpos).mpr h2u
      simpa using hone
    exact le_antisymm hle hge
  · -- a unit whose `A`-valuation is `1` is integral together with its inverse
    intro hx
    rw [Submonoid.mem_units_iff]
    constructor
    · rw [Units.coe_map]
      exact (decompFieldHenselEmb_mem_adicCompletionIntegers_iff
        k Ω K A hA q hAq halg _).mpr (le_of_eq hx)
    · rw [Units.val_inv_eq_inv_val
        (Units.map (decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom x), h_inv]
      refine (decompFieldHenselEmb_mem_adicCompletionIntegers_iff
        k Ω K A hA q hAq halg _).mpr ?_
      rw [h_Omega, Valuation.map_inv, hx, inv_one]

end Work.SSGRoute.E1aClean.LeadPhiUnr
