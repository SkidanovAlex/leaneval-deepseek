import Mathlib
import Submission.Work.SSGRoute.E8Defs
import Submission.Work.SSGRoute.E8Helpers
import Submission.Work.SSGRoute.eb_locUnits_resToGal
import Submission.Work.SSGRoute.eb_local_range
import Submission.Work.SSGRoute.eb_loc_card
import Submission.Work.SSGRoute.eb_crux
import Submission.Work.SSGRoute.eb_brauer_single_place_arch
import Submission.Work.SSGRoute.eb_arch_infl_injective
import Submission.Work.SSGRoute.ramificationIdx_mul_inertiaDeg_dvd_finrank
import Submission.Work.SSGRoute.eb_loc_away
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.HR2.locUnits_inflation_eq_zero_iff
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.CFTLib.hilbertReciprocity_cyclic
import Submission.NK.HR2.exists_cycClassOf_of_res_eq_zero
import Submission.NK.HR2.transferStepOnePlace
import Submission.NK.CFTLib.HRdescent.localConditionCyclotomicPrime
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.NK.Chebotarev.Basic
import Submission.NK.GlobalCFT.GaloisAction
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAction
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_EXT.md (the lead's Ext-core design for Poitou-Tate) + DESIGN_PT.md. Definitions: Submission/Work/SSGRoute/PTDefs.lean (namespace SSGRoute.PTExt; do NOT edit). NK.* CFT library available. Siblings run in parallel.

# E8 `brauer_single_place` - generator-free local-global compatibility

**Statement.** Let `a ∈ Br(L/k) = H²(Gal(L/k), Lˣ)` (NK `unitsRep`). If `locUnits k L w a = 0` at
every place `w` outside the orbit of `w₀`, then `a = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open CategoryTheory NumberField

theorem eb_aux_finite (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (N : ℕ) (hN : 0 < N) : EB_AuxFinite k L v₀ N := by
  classical
  obtain ⟨l, hl, hlt, hdvdord⟩ :=
    NK.CFTLib.IdeleHasse.Descent.exists_prime_gt_orderOf_dvd (Ideal.absNorm v₀.asIdeal)
      (NK.CFTLib.HRdescent.two_le_absNorm v₀) N hN
  have hndvd : ¬ l ∣ Ideal.absNorm v₀.asIdeal := by
    intro hd
    have hpos : 0 < Ideal.absNorm v₀.asIdeal :=
      Nat.pos_of_ne_zero fun hc => v₀.ne_bot (Ideal.absNorm_eq_zero_iff.mp hc)
    have h2 : l ≤ Ideal.absNorm v₀.asIdeal := Nat.le_of_dvd hpos hd
    omega
  have hcop : Nat.Coprime (Ideal.absNorm v₀.asIdeal) l :=
    (hl.coprime_iff_not_dvd.mpr hndvd).symm
  have hlQ : (l : NumberField.RingOfIntegers k) ∉ v₀.asIdeal := by
    intro hmem
    have hle : Ideal.span ({(l : NumberField.RingOfIntegers k)} :
        Set (NumberField.RingOfIntegers k)) ≤ v₀.asIdeal := by
      rw [Ideal.span_singleton_le_iff_mem]; exact hmem
    have hdvd : Ideal.absNorm v₀.asIdeal ∣ Ideal.absNorm
        (Ideal.span ({(l : NumberField.RingOfIntegers k)} :
          Set (NumberField.RingOfIntegers k))) :=
      Ideal.absNorm_dvd_absNorm_of_le hle
    rw [Ideal.absNorm_span_natCast] at hdvd
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
      (n := Ideal.absNorm v₀.asIdeal) (by have := NK.CFTLib.HRdescent.two_le_absNorm v₀; omega)
    have hpl : p ∣ l := hp.dvd_of_dvd_pow (hpdvd.trans hdvd)
    have hpq : p = l := (hl.eq_one_or_self_of_dvd p hpl).resolve_left hp.ne_one
    have hlabs : l ∣ Ideal.absNorm v₀.asIdeal := hpq ▸ hpdvd
    exact hl.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hlabs (dvd_refl l))
  obtain ⟨M, E, hMf, hMN, hEf, hEN, hkM, hkE, hLE, hME, hstLE, hstME, hfdM, hfdE, hgalM,
    hgalE, hcycM, hcycExt, hgen, heridiv⟩ :=
    NK.CFTLib.IdeleHasse.Crux.cyclotomicAuxiliary (K := k) (L := L) l hl v₀ hcop
  letI : Field M := hMf
  letI : NumberField M := hMN
  letI : Field E := hEf
  letI : NumberField E := hEN
  letI : Algebra k M := hkM
  letI : Algebra k E := hkE
  letI : Algebra L E := hLE
  letI : Algebra M E := hME
  letI : IsScalarTower k L E := hstLE
  letI : IsScalarTower k M E := hstME
  letI : FiniteDimensional k M := hfdM
  letI : FiniteDimensional k E := hfdE
  letI : IsGalois k M := hgalM
  letI : IsGalois k E := hgalE
  letI : IsCyclic (M ≃ₐ[k] M) := hcycM
  letI : IsCyclotomicExtension {l} k M := hcycExt
  refine ⟨M, E, hMf, hMN, hEf, hEN, hkM, hkE, hLE, hME, hstLE, hstME, hfdM, hfdE,
    hgalM, hgalE, hcycM, hgen, ?_⟩
  intro W hW
  haveI : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := k) (L := M) v₀
  have hunrIn : v₀.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers M) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers k)
      (B := NumberField.RingOfIntegers M) v₀.asIdeal P.asIdeal (Gal(M/k))]
    exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (n := l) v₀ hlQ P hP
  refine ⟨?_, ?_⟩
  · rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers k)
      (B := NumberField.RingOfIntegers M) v₀.asIdeal W.asIdeal (Gal(M/k))]
    exact hunrIn
  · have h1 : N ∣ orderOf (ZMod.unitOfCoprime (Ideal.absNorm v₀.asIdeal) hcop) := by
      rw [NK.CFTLib.HRdescent.orderOf_unitOfCoprime_eq hcop]
      exact hdvdord
    exact dvd_trans h1 (heridiv W hW)

/-! ## The cyclic case: Hilbert reciprocity -/

/-- **The cyclic case of `brauer_single_place`.**  For a cyclic extension `M/k`, a class of
`H²(Gal(M/k), Mˣ)` whose localisation vanishes at every place outside one place `v₀` is zero.

This is Hilbert reciprocity: the class is the cyclic class of some `b ∈ kˣ`
(`NK.HR2.exists_cycClassOf_eq_period`), the hypothesis says that `b` is a local norm at every place
`≠ v₀` (the localisation dictionary `NK.HR2.localNormSubgroup_iff_cycClass_place`), Hilbert
reciprocity `NK.CFTLib.hilbertReciprocity_onePlace_aux` supplies it at `v₀`, and the Hasse principle
for units `NK.GlobalCFTdeep.hbnUnits` finishes. -/
theorem brauer_single_place_cyclic (k M : Type) [Field k] [NumberField k] [Field M] [NumberField M]
    [Algebra k M] [FiniteDimensional k M] [IsGalois k M] [IsCyclic (M ≃ₐ[k] M)]
    (β : groupCohomology (NK.HassePrinciple.unitsRep k M) 2) (v₀ : NK.GlobalCFT.Place k)
    (h : ∀ w : NK.GlobalCFT.Place M, ¬ NK.GlobalCFT.Place.LiesOver w v₀ →
      (NK.HassePrinciple.locUnits k M w).hom β = 0) : β = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M ≃ₐ[k] M)
  obtain ⟨b, hb⟩ := NK.HR2.exists_cycClassOf_eq_period (K := k) (M := M) g hg β
  have hloc : ∀ v : NK.GlobalCFT.Place k, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v b ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := k) (L := M) v := by
    intro v hv
    obtain ⟨w, hw⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := k) (L := M) v
    have hw₀ : ¬ NK.GlobalCFT.Place.LiesOver w v₀ := fun hh =>
      hv (NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique hw hh)
    have h0 : (NK.HassePrinciple.locUnits k M w).hom β = 0 := h w hw₀
    rw [← hb] at h0
    exact (NK.HR2.localNormSubgroup_iff_cycClass_place (K := k) (F := M) g hg w v hw b).mp h0
  have h₀ : NK.CFTLib.IdeleHasse.localImageAt v₀ b ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := k) (L := M) v₀ := by
    refine NK.CFTLib.hilbertReciprocity_onePlace_aux b v₀ (fun v hv => ?_)
    simpa only [NK.CFTLib.IdeleHasse.localImageAt, NK.CFTLib.localImageHom_apply] using hloc v hv
  have hall : ∀ w : NK.GlobalCFT.Place M, (NK.HassePrinciple.locUnits k M w).hom β = 0 := by
    intro w
    by_cases hw : NK.GlobalCFT.Place.LiesOver w v₀
    · rw [← hb]
      exact (NK.HR2.localNormSubgroup_iff_cycClass_place (K := k) (F := M) g hg w v₀ hw b).mpr h₀
    · exact h w hw
  exact (NK.GlobalCFTdeep.hbnUnits (F := k) (E := M)) β hall



/-! ## The finite-place case of the main theorem (assembly)

This is the assembly of the finite-place case from:
* `eb_aux_finite` (the auxiliary cyclic cyclotomic level, PROVED in this file),
* `Work.SSGRoute.eb_crux` (the local degree step at the places above `v₀`),
* `Work.SSGRoute.ramificationIdx_mul_inertiaDeg_dvd_finrank` (hypothesis (B) for `L`),
* `Work.SSGRoute.eb_loc_away` and `Work.SSGRoute.eb_cyc_vanish_away` (the localisations away from
  `v₀`, via `NK.HR2.locUnits_inflation_eq_zero_of_loc_eq_zero`),
* `NK.GlobalCFTdeep.hbnUnits`, `NK.HR2.exists_cycClassOf_of_res_eq_zero`,
* `brauer_single_place_cyclic` (PROVED in this file),
* injectivity of the level inflation (`Work.SSGRoute.eb_arch_infl_injective`).

Plan: `N := Module.finrank k L`; the auxiliary tower `M, E` comes from `eb_aux_finite k L v₀ N`;
`β := res_{E/M}(inf_E a)`; every localisation of `β` vanishes (over `v₀` by `eb_crux`, elsewhere by
the hypothesis through the restriction–locality square), so `β = 0` by `hbnUnits M E`; descent
(`exists_cycClassOf_of_res_eq_zero`) writes `inf_E(a) = inf_M(γ)` with `γ ≤ cycClassOf_{M/k}(b)`;
the localisations of `γ` vanish away from `v₀`, so `γ = 0` by the cyclic case
`brauer_single_place_cyclic` at level `M/k`; hence `inf_E(a) = 0` and `a = 0` by injectivity of the
inflation. -/

/-- **`Place.LiesOver` at finite places is the ideal-theoretic `LiesOver`.** -/
private theorem place_liesOver_ofFinite_iff {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :
    NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q)
      (NK.GlobalCFT.Place.ofFinite Q) ↔ q.asIdeal.LiesOver Q.asIdeal := by
  constructor
  · intro h
    rcases h with ⟨w, v, h1, h2, _⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact absurd h1.symm (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w q)
    · rw [NK.GlobalCFT.Place.ofFinite_inj] at h1 h2
      subst h1; subst h2
      exact h3
  · exact NK.GlobalCFT.Place.liesOver_ofFinite

/-- **Injectivity of the level inflation `H²(Gal(L/k), Lˣ) → H²(Gal(E/k), Eˣ)`** for `k ⊆ L ⊆ E`
Galois: Hilbert 90 for `E/L` (`NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep`)
together with the general inflation–restriction exactness
(`Commons…H2_inflation_injective_of_subsingleton_H1`).  Proved in
`Submission/Work/SSGRoute/eb_arch_infl_injective.lean`. -/
theorem eb_inflation_injective {k L E : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Field E] [NumberField E] [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional k E] [IsGalois k L] [IsGalois k E] :
    Function.Injective ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom) :=
  eb_arch_infl_injective (k := k) (L := L) (E := E)

/-- **The finite-place case of `brauer_single_place`.** -/
theorem brauer_single_place_finite (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (a : groupCohomology (NK.HassePrinciple.unitsRep k L) 2)
    (ŵ₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : ∀ w : NK.GlobalCFT.Place L,
      (∀ σ : L ≃ₐ[k] L, σ • NK.GlobalCFT.Place.ofFinite ŵ₀ ≠ w) →
      (NK.HassePrinciple.locUnits k L w).hom a = 0) : a = 0 := by
  classical
  -- the place of `k` below `ŵ₀`
  let v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    ⟨ŵ₀.asIdeal.under (NumberField.RingOfIntegers k), inferInstance,
      Ideal.under_ne_bot _ ŵ₀.ne_bot⟩
  let N : ℕ := Module.finrank k L
  have hN : 0 < N := Module.finrank_pos
  -- the auxiliary cyclic cyclotomic tower
  obtain ⟨M, E, hMf, hMN, hEf, hEN, hkM, hkE, hLE, hME, hstLE, hstME, hfdM, hfdE, hgalM, hgalE,
    hcycM, hgen, heridiv⟩ := eb_aux_finite k L v₀ N hN
  letI : Field M := hMf
  letI : NumberField M := hMN
  letI : Field E := hEf
  letI : NumberField E := hEN
  letI : Algebra k M := hkM
  letI : Algebra k E := hkE
  letI : Algebra L E := hLE
  letI : Algebra M E := hME
  letI : IsScalarTower k L E := hstLE
  letI : IsScalarTower k M E := hstME
  letI : FiniteDimensional k M := hfdM
  letI : FiniteDimensional k E := hfdE
  letI : IsGalois k M := hgalM
  letI : IsGalois k E := hgalE
  letI : IsCyclic (M ≃ₐ[k] M) := hcycM
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite k M E
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois k M E
  -- (B): the local degrees of `L` at `v₀` divide `N = [L : k]`
  have hLdeg : ∀ (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
      r.asIdeal.LiesOver v₀.asIdeal →
      r.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
        r.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) ∣ N := by
    intro r hr
    exact ramificationIdx_mul_inertiaDeg_dvd_finrank k L v₀ r hr
  -- the hypothesis, in the `LiesOver` form
  have hv₀ : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite ŵ₀)
      (NK.GlobalCFT.Place.ofFinite v₀) :=
    (place_liesOver_ofFinite_iff (k := k) (L := L) ŵ₀ v₀).mpr (Ideal.over_under ŵ₀.asIdeal)
  have haway : ∀ r : NK.GlobalCFT.Place L,
      ¬ NK.GlobalCFT.Place.LiesOver r (NK.GlobalCFT.Place.ofFinite v₀) →
      (NK.HassePrinciple.locUnits k L r).hom a = 0 :=
    fun r hr => h r ((not_liesOver_iff_not_mem_orbit k L (NK.GlobalCFT.Place.ofFinite ŵ₀)
      (NK.GlobalCFT.Place.ofFinite v₀) hv₀ r).mpr hr)
  -- the class `β = res_{E/M}(inf_E a)`
  let β : groupCohomology (NK.HassePrinciple.unitsRep M E) 2 :=
    (NK.NUV2.ChebAux.Transfer.resToGal k M E).hom
      ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a)
  -- every localisation of `β` vanishes
  have hβ : ∀ ŵ : NK.GlobalCFT.Place E, (NK.HassePrinciple.locUnits M E ŵ).hom β = 0 := by
    intro ŵ
    by_cases hŵ : NK.GlobalCFT.Place.LiesOver ŵ (NK.GlobalCFT.Place.ofFinite v₀)
    · -- `ŵ` is a finite place above `v₀`: the local degree step
      obtain ⟨ŵ', rfl⟩ := NK.GlobalCFT.Place.isFinite_iff.mp
        ((NK.GlobalCFT.Place.isFinite_of_liesOver hŵ).mpr
          (NK.GlobalCFT.Place.isFinite_ofFinite v₀))
      have hŵ' : ŵ'.asIdeal.LiesOver v₀.asIdeal :=
        (place_liesOver_ofFinite_iff (k := k) (L := E) ŵ' v₀).mp hŵ
      exact eb_crux k L M E hgen v₀ N heridiv hLdeg ŵ' hŵ' a
    · -- `ŵ` is outside `v₀`: the general away-from-`v₀` step
      obtain ⟨r, hr⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := L) (L := E) ŵ
      have hr₀ : ¬ NK.GlobalCFT.Place.LiesOver r (NK.GlobalCFT.Place.ofFinite v₀) :=
        fun hrr => hŵ (place_liesOver_trans hr hrr)
      exact eb_loc_away (k := k) (L := L) (M := M) (E := E) a ŵ r hr (haway r hr₀)
  have hβ0 : β = 0 := NK.GlobalCFTdeep.hbnUnits (F := M) (E := E) β hβ
  -- descent to the cyclic level `M/k`
  obtain ⟨gM, hgM⟩ := IsCyclic.exists_generator (α := M ≃ₐ[k] M)
  obtain ⟨b, hb⟩ := NK.HR2.exists_cycClassOf_of_res_eq_zero (K := k) (L := L) (M := M) (E := E)
    hgen gM hgM ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a) hβ0
  set γ : groupCohomology (NK.HassePrinciple.unitsRep k M) 2 :=
    NK.CFTLib.IdeleHasse.Descent.cycClassOf gM hgM b with hγ
  have hb' : (NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a
      = (NK.NUV2.ARL.HR.inflation (K := k) (L := M) (E := E)).hom γ := by
    rw [hb]
  -- `γ = 0` by the cyclic case
  have hγ0 : γ = 0 := brauer_single_place_cyclic k M γ (NK.GlobalCFT.Place.ofFinite v₀)
    (fun W hW => by
      -- a place of `E` above `W`, and a place of `L` below it
      obtain ⟨Ŵ, hŴ⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := M) (L := E) W
      obtain ⟨s, hs⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := L) (L := E) Ŵ
      -- `s` is outside the orbit: otherwise `W` would lie over `v₀`
      have hs₀ : ¬ NK.GlobalCFT.Place.LiesOver s (NK.GlobalCFT.Place.ofFinite v₀) := by
        intro hsl
        obtain ⟨t, ht⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := k) (L := M) W
        have h1 : NK.GlobalCFT.Place.LiesOver Ŵ (NK.GlobalCFT.Place.ofFinite v₀) :=
          place_liesOver_trans hs hsl
        have h2 : NK.GlobalCFT.Place.LiesOver Ŵ t := place_liesOver_trans hŴ ht
        have h3 : t = NK.GlobalCFT.Place.ofFinite v₀ :=
          NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique h2 h1
        exact hW (h3 ▸ ht)
      have hE : (NK.HassePrinciple.locUnits k E Ŵ).hom
          ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a) = 0 :=
        NK.HR2.locUnits_inflation_eq_zero_of_loc_eq_zero (K := k) (L := L) (E := E) a s Ŵ hs
          (haway s hs₀)
      rw [← (NK.HR2.locUnits_inflation_eq_zero_iff (K := k) (M := M) (E := E) γ W Ŵ hŴ)]
      rw [← hb']
      exact hE)
  -- conclude
  have hmain : (NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a = 0 := by
    rw [hb', hγ0, map_zero]
  exact eb_inflation_injective (by rw [hmain, map_zero])

/-! ## The main theorem -/

/-- **E8 (generator-free local-global compatibility).** A class of `Br(L/k) = H²(Gal(L/k), Lˣ)`
whose localisation vanishes at every place of `L` outside one `Gal(L/k)`-orbit is zero (the weak
form "no Brauer class is ramified at exactly one place" of `Σ_v inv_v = 0`). -/
theorem brauer_single_place (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (a : groupCohomology (NK.HassePrinciple.unitsRep k L) 2) (w₀ : NK.GlobalCFT.Place L)
    (h : ∀ w : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ w) →
      (NK.HassePrinciple.locUnits k L w).hom a = 0) : a = 0 := by
  rcases w₀ with w₀ | ŵ₀
  · exact eb_brauer_single_place_arch k L a w₀ h
  · exact brauer_single_place_finite k L a ŵ₀ h

end Work.SSGRoute
