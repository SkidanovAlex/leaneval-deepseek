import Mathlib
import Submission.NK.CFTLib.Existence.ConductorNotes
import Submission.NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles_kummer
import Submission.NK.CFTLib.Existence.localNormImage_of_forall_ne
import Submission.NK.CFTLib.Existence.localUnits_le_range_localNorm_of_integralIdeles
import Submission.NK.CFTLib.IdeleHasse.badSet_not_singleton
import Submission.NK.CFTLib.Existence.ramificationIdx_eq_one_of_localUnits_le_localNorm

/-!
# Unramifiedness from `N_{L/K} C_L ⊇ im(𝕀_K⁰)` at prime degree, without a root of unity

For a number field `K` (with **no** assumption that `K` contains a primitive `p`-th root of unity),
a finite Galois extension `L / K` of prime degree `p` whose norm class subgroup contains the image
of the integral idèles `𝕀_K⁰` is unramified at every finite place (`differentIdeal = ⊤`) and at
every archimedean place.

This is the same statement as
`NK.CFTLib.Existence.isUnramified_of_normClassSubgroup_le_integralIdeles_kummer`, whose
hypothesis `{ζ : K} (hζ : IsPrimitiveRoot ζ p)` is **never used**: in that file the only occurrence
of `hζ` is as an argument to
`NK.CFTLib.Existence.localUnits_le_range_localNorm_of_integralIdeles`, and in *that* lemma the
argument `hζ` does not occur in the proof either (the proof only uses `hgap`, `hray`, `hdeg`, and
`localNormUnits_of_fiber_prod` / the archimedean norm computations).  So it suffices to repeat the
two proofs with the `hζ` argument dropped, which is what this file does.

The proof structure is:

* `localUnits_le_range_localNorm_of_integralIdeles'` — the local extraction, the copy of
  `NK.CFTLib.Existence.localUnits_le_range_localNorm_of_integralIdeles` with the (unused)
  primitive-root argument deleted: at every finite place the local units are local norms, and at
  every infinite place the local norm is surjective;
* the finite places via `differentIdeal_eq_top_of_ramificationIdx_heightOne` (from the Kummer file)
  together with `ramificationIdx_eq_one_of_localUnits_le_localNorm`;
* the infinite places by the case distinction `isReal_or_isComplex` on the places and the
  `NormIndex.localNormInfinite_range_eq_top_of_*` lemmas, with `false_of_isReal_of_isComplex` for
  the mixed real/complex case.

The single arithmetic input is the "one place omitted" form of Hilbert reciprocity,
`NK.CFTLib.Existence.localNormImage_of_forall_ne` (Milne, *CFT*, VIII.2 Example 2.2(ii)), which
is exactly the local–global compatibility of the global Artin map with the local Artin maps; it is
used through `hgap` below.
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

/-- **The local extraction without a primitive root of unity.**

Copy of `NK.CFTLib.Existence.localUnits_le_range_localNorm_of_integralIdeles` with the
`(p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)` arguments deleted (they do not occur
in the proof).  Given `hgap` — the "one place omitted" form of Hilbert reciprocity
(`NK.CFTLib.Existence.localNormImage_of_forall_ne`) — and `hray`, the idèles which are local units
at all finite places are local norms:

* at every finite place `q | Q`, every local unit of `K_Q` is the norm of a local unit of `L_q`;
* at every infinite place, the local norm `L_w^× → K_v^×` is surjective. -/
theorem localUnits_le_range_localNorm_of_integralIdeles'
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

/-! ## The archimedean places at odd degree (unconditional)

At odd degree no infinite place can be complexified, so for odd `p` the `IsUnramifiedAtInfinitePlaces`
half of the conclusion is a theorem of the Galois theory of completions, with no arithmetic input
at all.  This is the fragment of the main theorem which does not depend on
`NK.CFTLib.Existence.localNormImage_of_forall_ne`. -/

theorem isUnramifiedAtInfinitePlaces_of_odd_prime_finrank
    {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = p) :
    IsUnramifiedAtInfinitePlaces K L := by
  have hodd : Odd (Module.finrank K L) := by
    rw [hdeg]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2
  exact IsUnramifiedAtInfinitePlaces_of_odd_finrank hodd

/-! ## The main theorem -/

theorem isUnramified_of_normClassSubgroup_le_integralIdeles
    {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = p)
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
    localUnits_le_range_localNorm_of_integralIdeles' (K := K) (L := L) (p := p) hdeg
      (fun {x v₀} hx => NK.CFTLib.IdeleHasse.badSet_not_singleton hcyc hx) hray
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
