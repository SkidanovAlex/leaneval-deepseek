import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.CFTLib.unramifiedAbelianDegreeLe
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.Unramified.normGroup_eq_unramifiedNormGroup
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.CFTLib.Existence.localNormImage_of_forall_ne
import Submission.NK.CFTLib.Existence.ramificationIdx_eq_one_of_localUnits_le_localNorm
import Submission.NK.CFTLib.Existence.localUnits_le_range_localNorm_of_integralIdeles
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean

/-!
# Unramifiedness from `N_{L/K}C_L ⊇ im(𝕀_K⁰)` in the Kummer case

For a number field `K` containing a primitive `p`-th root of unity `ζ` (`p` prime), and a finite
Galois extension `L / K` of degree `p` whose norm class subgroup `N_{L/K}C_L` contains the image
of the idèles which are local units at every finite place, the extension `L / K` is unramified at
every finite place and at every archimedean place.

The mathematical content is the *local–global* ("conductor detection") statement: the local units
at a place `v` map into the global norm subgroup only if the local extension at `v` is trivial.
This is the compatibility of the global Artin map with the local Artin maps — the product formula
for the local norm residue symbols, i.e. Hilbert reciprocity.

The proof consumes three inputs, each of which is *proved* (sorry-free, axiom-clean) in a sibling
file of this directory:

* `NK.CFTLib.Existence.localNormImage_of_forall_ne` — the "no single place of local-norm
  failure" form of Hilbert reciprocity (the crux; proved via
  `NK.CFTLib.hilbertReciprocity_cyclic`, i.e. `∑_v inv_v = 0` for cyclic `L/K`);
* `NK.CFTLib.Existence.localUnits_le_range_localNorm_of_integralIdeles` — the local extraction
  (every local unit is a local norm), which consumes the previous input together with the witness
  decomposition `im(𝕀_K⁰) ≤ N_{L/K}C_L ⟹ (u)_v = c·n`;
* `NK.CFTLib.Existence.ramificationIdx_eq_one_of_localUnits_le_localNorm` — the local norm index
  theorem: if the local norm is onto the units then `e = 1`.

The file itself contributes

* the witness decomposition `exists_principalIdele_mul_mem_normImage_of_mem_integralIdeles`
  (re-exported from the local extraction file),
* the `differentIdeal = ⊤` assembly (`differentIdeal_eq_top_of_ramificationIdx_heightOne`), and
* the archimedean half of the conclusion: a real place cannot complexify, because the norm
  `ℂˣ → ℝˣ` takes only positive values, while the local units are local norms by the extraction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Existence

open NK.GlobalCFT

/-! ## The different ideal -/

/-- **`differentIdeal = ⊤` from the ramification indices being one at the height one primes.** -/
theorem differentIdeal_eq_top_of_ramificationIdx_heightOne
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h : ∀ q : HeightOneSpectrum (𝓞 L), q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  refine Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_forall_not_dvd ?_
  intro Q hQ
  by_cases hbot : Q = ⊥
  · rw [hbot]
    intro hdvd
    have hle : differentIdeal (𝓞 K) (𝓞 L) ≤ ⊥ := (Ideal.dvd_iff_le.mp hdvd).trans bot_le
    exact differentIdeal_ne_bot (le_bot_iff.mp hle)
  · let q : HeightOneSpectrum (𝓞 L) := ⟨Q, hQ, hbot⟩
    rw [Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal Q hQ]
    exact h q

/-! ## The main theorem -/

theorem isUnramified_of_normClassSubgroup_le_integralIdeles_kummer
    {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = p)
    (hray : (NK.GlobalCFT.Idele.integralIdeles K).map (NK.GlobalCFT.IdeleClassGroup.mk K) ≤
      NK.GlobalCFT.Idele.normClassSubgroup K L) :
    differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤ ∧
      IsUnramifiedAtInfinitePlaces K L := by
  classical
  have hcyc : IsCyclic (L ≃ₐ[K] L) := by
    refine isCyclic_of_prime_card (p := p) ?_
    rw [IsGalois.card_aut_eq_finrank K L]
    exact hdeg
  obtain ⟨hfin, hinf⟩ :=
    localUnits_le_range_localNorm_of_integralIdeles (K := K) (L := L) (p := p) (hζ := hζ)
      (hdeg := hdeg) (fun {x v₀} hx => localNormImage_of_forall_ne (K := K) (L := L) hcyc hx) hray
  constructor
  · -- finite places: the ramification index of every height one prime is one
    refine differentIdeal_eq_top_of_ramificationIdx_heightOne ?_
    intro q
    let QK : HeightOneSpectrum (𝓞 K) := q.under (𝓞 K)
    have hlies : q.asIdeal.LiesOver QK.asIdeal :=
      (Ideal.liesOver_iff _ _).mpr (by simp only [QK, HeightOneSpectrum.under_asIdeal])
    exact ramificationIdx_eq_one_of_localUnits_le_localNorm (K := K) (L := L) hcyc hdeg
      QK q hlies (hfin QK q hlies)
  · -- archimedean places: no real place complexifies
    refine ⟨fun w => ?_⟩
    rw [NumberField.InfinitePlace.isUnramified_iff]
    rcases w.isReal_or_isComplex with hR | hC
    · exact Or.inl hR
    · refine Or.inr ?_
      by_contra hv
      have hvR : (w.comap (algebraMap K L)).IsReal :=
        NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hv
      haveI hwv : w.LiesOver (w.comap (algebraMap K L)) :=
        (NK.GlobalCFT.Norm.liesOver_iff_comap_eq w _).mpr rfl
      let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvR
      let u : (w.comap (algebraMap K L)).Completionˣ :=
        Units.map e.symm.toMulEquiv.toMonoidHom (Units.mk0 (-1 : ℝ) (by norm_num))
      obtain ⟨u', hu'⟩ := hinf (w.comap (algebraMap K L)) w u
      have hle : (NK.GlobalCFT.Place.localNormInfinite w (w.comap (algebraMap K L))).range ≤
          Subgroup.comap (Units.map e.toMulEquiv.toMonoidHom) (Units.posSubgroup ℝ) := by
        rw [show NK.GlobalCFT.Place.localNormInfinite w (w.comap (algebraMap K L))
            = Units.map (Algebra.norm (w.comap (algebraMap K L)).Completion :
                w.Completion →* (w.comap (algebraMap K L)).Completion) from rfl]
        rintro x ⟨y, rfl⟩
        rw [Subgroup.mem_comap, Units.mem_posSubgroup]
        simp only [Units.coe_map]
        change 0 < e ((Algebra.norm (w.comap (algebraMap K L)).Completion) (y : w.Completion))
        rw [show e ((Algebra.norm (w.comap (algebraMap K L)).Completion) (y : w.Completion))
            = Complex.normSq ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC)
                (y : w.Completion)) from
          NK.GlobalCFTdeep.NormIndex.localNormInfinite_norm_eq_real_complex (K := K) (L := L)
            hvR hC (y : w.Completion)]
        refine Complex.normSq_pos.mpr (fun hz => Units.ne_zero y ?_)
        exact (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC).injective
          (by rw [hz, map_zero])
      have hmem : u ∈ Subgroup.comap (Units.map e.toMulEquiv.toMonoidHom) (Units.posSubgroup ℝ) := by
        refine hle ?_
        rw [← hu']
        exact ⟨u', rfl⟩
      rw [Subgroup.mem_comap, Units.mem_posSubgroup] at hmem
      have hc : ((Units.map e.toMulEquiv.toMonoidHom u : ℝˣ) : ℝ) = -1 := by
        simp [u]
      rw [hc] at hmem
      norm_num at hmem

end NK.CFTLib.Existence
