import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
import Submission.NK.CFTLib.Existence.localUnits_le_range_localNorm_of_integralIdeles
import Submission.NK.CFTLib.Existence.localNormUnits_of_fiber_prod
import Submission.NK.CFTLib.Existence.ramificationIdx_eq_one_of_localUnits_le_localNorm

/-!
# Unramifiedness from `N_{L/K} C_L ⊇ im(𝕀_K^0)` at prime degree

For a number field `K` (with **no** assumption that `K` contains a primitive `p`-th root of unity),
a finite Galois extension `L / K` of prime degree `p` whose norm class subgroup contains the image
of the integral idèles `𝕀_K^0` is unramified at every finite place (`differentIdeal = ⊤`) and at
every archimedean place.

This is a copy of `NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles` (and of
`NK.CFTLib.Existence.localUnits_le_range_localNorm_of_integralIdeles` with the unused primitive-root
argument deleted), placed in a module whose import closure **avoids**
`Submission.NK.CFTLib.unramifiedAbelianDegreeLe`, so that it can be imported alongside
`Submission.NK.CFTLib.integralIdelesLeNormImage` (the two files declare the same name
`NK.CFTLib.ramificationIdx_eq_one_of_differentIdeal_eq_top` and therefore cannot both be imported).

The single arithmetic input is isolated in the `Prop` `HasseNormOnePlace`: the "one place omitted"
form of Hilbert reciprocity (Milne, *CFT*, VIII.2 Example 2.2(ii), equivalently VII.8.1(a)), i.e.
`NK.CFTLib.IdeleHasse.badSet_not_singleton`.
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

/-- **Hilbert reciprocity in the "one place omitted" form** (Milne, *CFT*, VII.8.1(a)): a global
element which is a local norm at every place except possibly one is a global idèlic norm. -/
def HasseNormOnePlace : Prop :=
  ∀ {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    IsCyclic (L ≃ₐ[K] L) →
    ∀ {x : Kˣ} {v₀ : Place K},
      (∀ v : Place K, v ≠ v₀ → ∃ y : Idele L,
        Idele.principalIdele K x v = Idele.normIdeleFun K L y v) →
      Idele.principalIdele K x ∈ Idele.normImage K L

/-- **`differentIdeal = ⊤` from the ramification indices being one at the height one primes.** -/
theorem differentIdeal_eq_top_of_ramificationIdx_heightOne_safe
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

/-- **The local extraction without a primitive root of unity.**

Copy of `NK.CFTLib.Existence.localUnits_le_range_localNorm_of_integralIdeles` with the
`(p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)` arguments deleted (they do not occur
in the proof).  Given `hgap` — the "one place omitted" form of Hilbert reciprocity
(`NK.CFTLib.Existence.localNormImage_of_forall_ne`) — and `hray`, the idèles which are local units
at all finite places are local norms:

* at every finite place `q | Q`, every local unit of `K_Q` is the norm of a local unit of `L_q`;
* at every infinite place, the local norm `L_w^× → K_v^×` is surjective. -/
theorem localUnits_le_range_localNorm_of_integralIdeles_safe
    {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} [Fact p.Prime]
    (hdeg : Module.finrank K L = p)
    (hgap : ∀ {x : Kˣ} {v₀ : NK.GlobalCFT.Place K},
      (∀ v : NK.GlobalCFT.Place K, v ≠ v₀ → ∃ y : NK.GlobalCFT.Idele L,
        NK.GlobalCFT.Idele.principalIdele K x v = NK.GlobalCFT.Idele.normIdeleFun K L y v) →
      NK.GlobalCFT.Idele.principalIdele K x ∈ NK.GlobalCFT.Idele.normImage K L)
    (hray : (NK.GlobalCFT.Idele.integralIdeles K).map (NK.GlobalCFT.IdeleClassGroup.mk K) ≤
      NK.GlobalCFT.Idele.normClassSubgroup K L) :
    (∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
       (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
       (hq : q.asIdeal.LiesOver Q.asIdeal),
        ∀ u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q),
          ∃ u' ∈ NK.GlobalCFT.Place.localUnits L (NK.GlobalCFT.Place.ofFinite q),
            NK.GlobalCFT.Place.localNormFinite q Q hq u' = u) ∧
    (∀ (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v]
       (u : v.Completionˣ), ∃ u' : w.Completionˣ,
        NK.GlobalCFT.Place.localNormInfinite w v u' = u) := by
  classical
  constructor
  · -- finite places
    intro Q q hq u hu
    set a : Idele K :=
      NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofFinite Q) u with ha_def
    have ha_int : a ∈ Idele.integralIdeles K := by
      intro v hv
      obtain ⟨Q', rfl⟩ := Place.isFinite_iff.mp hv
      by_cases h : Q' = Q
      · subst h
        rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_self]
        exact hu
      · rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_of_ne
          (w := Place.ofFinite Q) (w' := Place.ofFinite Q') (u := u) (by simpa using h)]
        exact Subgroup.one_mem _
    have ha_off : ∀ v, v ≠ Place.ofFinite Q → a v = 1 := by
      intro v hv
      cases v with
      | inl w' =>
          rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_of_ne
            (w := Place.ofFinite Q) (w' := Place.ofInfinite w') (u := u) (by simpa using hv)]
      | inr Q' =>
          rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_of_ne
            (w := Place.ofFinite Q) (w' := Place.ofFinite Q') (u := u) hv]
    obtain ⟨x, hx⟩ :=
      Idele.mem_normImage.mp (mem_normImage_of_eq_one_off hray hgap ha_int ha_off)
    have hprod : u = ∏ q' ∈ (Place.primesOverFinite Q).attach,
        (Place.localNormFinite (q' : HeightOneSpectrum (𝓞 L)) Q
          ((Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q')).mp q'.2))
          (x (Place.ofFinite q'.1)) := by
      have h := hx (Place.ofFinite Q)
      rw [ha_def, NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele_apply_self,
        Idele.normIdeleFun_ofFinite] at h
      exact h
    exact localNormUnits_of_fiber_prod (Fact.out) hdeg Q q hq u hu x hprod
  · -- infinite places
    intro v w hwv u
    haveI hwl : w.LiesOver v := hwv
    rcases v.isReal_or_isComplex with hvR | hvC
    · rcases w.isReal_or_isComplex with hwR | hwC
      · have htop := NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real
          (K := K) (L := L) (v := v) (w := w) hvR hwR
        have hmem : u ∈ (Place.localNormInfinite w v).range := by
          rw [show Place.localNormInfinite w v =
            Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl, htop]
          exact Subgroup.mem_top u
        exact MonoidHom.mem_range.mp hmem
      · exact (false_of_isReal_of_isComplex hgap hray v w hvR hwC).elim
    · have hwC : w.IsComplex :=
        NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
      have htop := NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex
        (K := K) (L := L) (v := v) (w := w) hvC hwC
      have hmem : u ∈ (Place.localNormInfinite w v).range := by
        rw [show Place.localNormInfinite w v =
          Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl, htop]
        exact Subgroup.mem_top u
      exact MonoidHom.mem_range.mp hmem

/-! ## The main theorem -/

theorem isUnramified_of_normClassSubgroup_le_integralIdeles_safe
    {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = p)
    (hgap : HasseNormOnePlace)
    (hray : (NK.GlobalCFT.Idele.integralIdeles K).map (NK.GlobalCFT.IdeleClassGroup.mk K) ≤
      NK.GlobalCFT.Idele.normClassSubgroup K L) :
    differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤ ∧
      IsUnramifiedAtInfinitePlaces K L := by
  classical
  -- `Gal(L/K)` is cyclic of order `p`
  have hcyc : IsCyclic (L ≃ₐ[K] L) := by
    refine isCyclic_of_prime_card (p := p) ?_
    rw [IsGalois.card_aut_eq_finrank K L]
    exact hdeg
  -- the local extraction, with `hgap` the "one place omitted" form of Hilbert reciprocity
  obtain ⟨hfin, hinf⟩ :=
    localUnits_le_range_localNorm_of_integralIdeles_safe (K := K) (L := L) (p := p) hdeg
      (fun {x v₀} hx => hgap hcyc hx) hray
  constructor
  · -- finite places: the ramification index of every height one prime is one
    refine differentIdeal_eq_top_of_ramificationIdx_heightOne_safe ?_
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
