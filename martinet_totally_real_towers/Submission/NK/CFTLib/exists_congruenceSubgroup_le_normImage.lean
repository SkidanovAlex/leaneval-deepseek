import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage
import Submission.NK.GlobalCFTdeep.NormIndex.constrainedE_inf_TIdeles_index
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.Commons.NumberTheory.NumberField.Completion.exists_trace_eq_one_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.finite_quotient_units_range_norm_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one

/-!
# A congruence subgroup contained in the idèlic norm group

Let `L / K` be a finite Galois extension of number fields.  This file proves that there is a
modulus `m > 0` and a *congruence subgroup* `U ≤ 𝕀[K]` — the idèles which are local units outside
the primes dividing `m`, are `≡ 1 mod m` at the primes dividing `m`, and are positive at every real
place — such that `U ≤ N_{L/K} 𝕀[L]`.

This is the standard "the norm group is open, of finite index, and contains a congruence subgroup"
statement used in the idèlic proof of class field theory (Neukirch–Schmidt–Wingberg, *Cohomology
of Number Fields*, Chapter XII, the input to the reconstruction of the local correspondence in
Neukirch–Uchida).  Only the local theory of the norm map is used, no local class field theory:

* **Nonarchimedean, unramified.**  If `q | Q` is unramified then the local norm
  `N_{L_q/K_Q}` maps the local units of `L_q` *onto* the local units of `K_Q`
  (`localNormFinite_units_surjective_of_ramificationIdx_eq_one`, from
  `norm_range_of_ramificationIdx_eq_one`).
* **Nonarchimedean, ramified.**  The local norm `N_{L_q/K_Q}` is *open at the origin*: there is a
  level `n > 0` such that every `z ≡ 1 mod 𝔪^n` is a norm.  This is the elementary Newton-iteration
  computation `exists_norm_eq_of_val_sub_one_le_aux` (second order expansion of the norm, whose
  derivative is the surjective trace) packaged as `exists_level_localNormFinite`.
* **Archimedean.**  At a real place the positive elements are norms (the norm is either an
  isomorphism `ℝ ≅ ℝ`, or `N z = |z|²` for `ℂ/ℝ`); at a complex place everything is a norm
  (`posAtReal_mem_range_localNormInfinite`).

The modulus is `m = ∏_{Q ramified} N(Q)^N` where `N` is the maximum of the local levels
(`exists_modulus`), so that

* every ramified prime divides `(m)`, whence a prime not dividing `m` is unramified, and
* at a ramified prime `Q | (m)` the congruence condition of level `m` is finer than the local
  level `levelOf Q`, so the component lies in the local norm group
  (`mem_range_localNormFinite_of_val_le_levelOf`, `val_natCast_le_exp_neg_of_mem_pow`).

The per-place local data is then assembled into a global norm by
`NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField RestrictedProduct WithZero NumberField.LiesOver
open NumberField IsDedekindDomain

namespace NK.CFTLib

open NK.GlobalCFT

noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

namespace ExistsCongruence

/-! ## Choices of places of `L` above the places of `K` -/

/-- A chosen prime of `𝓞 L` above a prime of `𝓞 K`. -/
noncomputable def abovePrime (Q : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 L) :=
  Classical.choose
    (Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q)

theorem abovePrime_liesOver (Q : HeightOneSpectrum (𝓞 K)) :
    (abovePrime (K := K) (L := L) Q).asIdeal.LiesOver Q.asIdeal :=
  Classical.choose_spec
    (Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q)

/-- A chosen infinite place of `L` above an infinite place of `K`. -/
noncomputable def aboveInf (w : InfinitePlace K) : InfinitePlace L :=
  Classical.choose (InfinitePlace.comap_surjective (k := K) (K := L) w)

theorem aboveInf_liesOver (w : InfinitePlace K) : (aboveInf (K := K) (L := L) w).LiesOver w := by
  rw [Norm.liesOver_iff_comap_eq]
  exact Classical.choose_spec (InfinitePlace.comap_surjective (k := K) (K := L) w)

theorem placeAbove_ofFinite (Q : HeightOneSpectrum (𝓞 K)) :
    IdeleHasse.placeAbove (K := K) (L := L) (Place.ofFinite Q) =
      Place.ofFinite (abovePrime (K := K) (L := L) Q) := rfl

theorem placeAbove_ofInfinite (w : InfinitePlace K) :
    IdeleHasse.placeAbove (K := K) (L := L) (Place.ofInfinite w) =
      Place.ofInfinite (aboveInf (K := K) (L := L) w) := rfl

/-! ## The local norm contains a neighbourhood of `1` -/

/-- **The local norm is open at the origin.**  For a finite place `Q` of `K` and a place `q` of
`L` above it there is a level `n > 0` such that every unit `z` of `K_Q` which is `≡ 1` modulo the
`n`-th power of the maximal ideal is a norm from `L_qˣ`. -/
theorem exists_level_localNormFinite (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : (Q.adicCompletion K)ˣ,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
          ((z : Q.adicCompletion K) - 1) ≤
        (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) →
      z ∈ (Place.localNormFinite q Q hq).range := by
  obtain ⟨D, u₀, hu₀, hu₀D⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_trace_eq_one_adicCompletion
      (K := K) (L := L) Q q hq
  refine ⟨2 * D + 2, by omega, ?_⟩
  intro z hz
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  obtain ⟨x, hx⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_norm_eq_of_val_sub_one_le_aux
      (K := K) (L := L) Q q hq D u₀ hu₀ hu₀D (z : Q.adicCompletion K) hz
  haveI : Module.Free (Q.adicCompletion K) (q.adicCompletion L) :=
    Module.Free.of_divisionRing _ _
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  have hxne : x ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hx
    exact Units.ne_zero z hx.symm
  refine MonoidHom.mem_range.mpr ⟨Units.mk0 x hxne, ?_⟩
  refine Units.ext ?_
  rw [show Place.localNormFinite q Q hq =
    Units.map (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)
      from rfl]
  rw [Units.coe_map, Units.val_mk0]
  exact hx

/-- The level of the local norm at a prime of `𝓞 K`, attached to the chosen prime of `𝓞 L`
above it. -/
noncomputable def levelOf (Q : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Classical.choose (exists_level_localNormFinite (K := K) (L := L) Q
    (abovePrime (K := K) (L := L) Q) (abovePrime_liesOver Q))

theorem levelOf_pos (Q : HeightOneSpectrum (𝓞 K)) : 0 < levelOf (K := K) (L := L) Q :=
  (Classical.choose_spec (exists_level_localNormFinite Q (abovePrime Q) (abovePrime_liesOver Q))).1

/-- Every unit congruent to `1` modulo `levelOf Q` is a local norm. -/
theorem mem_range_localNormFinite_of_val_le_levelOf (Q : HeightOneSpectrum (𝓞 K))
    (z : (Q.adicCompletion K)ˣ)
    (hz : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((z : Q.adicCompletion K) - 1) ≤
      (WithZero.exp (-((levelOf (K := K) (L := L) Q : ℕ) : ℤ)) :
        WithZero (Multiplicative ℤ))) :
    z ∈ (Place.localNormFinite (abovePrime (K := K) (L := L) Q) Q
      (abovePrime_liesOver Q)).range :=
  (Classical.choose_spec (exists_level_localNormFinite Q (abovePrime Q)
    (abovePrime_liesOver Q))).2 z hz

/-! ## The ramified primes and the modulus -/

/-- The finite set of primes of `𝓞 K` which ramify in `L`. -/
noncomputable def ramPrimes : Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact (Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
    (K := K) (L := L)).toFinset.image
    (fun q => HeightOneSpectrum.under (𝓞 K) q)

theorem mem_ramPrimes_of_ramificationIdx_ne_one {Q : HeightOneSpectrum (𝓞 K)}
    {q : HeightOneSpectrum (𝓞 L)} (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h : q.asIdeal.ramificationIdx (𝓞 K) ≠ 1) : Q ∈ ramPrimes (K := K) (L := L) := by
  classical
  refine Finset.mem_image.mpr ⟨q, ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset]
    exact h
  · exact HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal, hq.over])

theorem ramificationIdx_eq_one_of_notMem_ramPrimes {Q : HeightOneSpectrum (𝓞 K)}
    (hQ : Q ∉ ramPrimes (K := K) (L := L)) {q : HeightOneSpectrum (𝓞 L)}
    (hq : q.asIdeal.LiesOver Q.asIdeal) : q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  by_contra h
  exact hQ (mem_ramPrimes_of_ramificationIdx_ne_one hq h)

/-- **The modulus.**  There is `m > 0` which is divisible, at every ramified prime `Q`, by the
`levelOf Q`-th power of `Q`. -/
theorem exists_modulus :
    ∃ m : ℕ, 0 < m ∧ ∀ Q : HeightOneSpectrum (𝓞 K), Q ∈ ramPrimes (K := K) (L := L) →
      (m : 𝓞 K) ∈ Q.asIdeal ^ levelOf (K := K) (L := L) Q := by
  classical
  refine ⟨∏ Q ∈ ramPrimes (K := K) (L := L),
      (Ideal.absNorm Q.asIdeal) ^ (ramPrimes (K := K) (L := L)).sup
        (levelOf (K := K) (L := L)), ?_, ?_⟩
  · refine Finset.prod_pos fun Q _ => pow_pos ?_ _
    exact Nat.pos_of_ne_zero fun h => Q.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  · intro Q hQ
    have hAN : (((Ideal.absNorm Q.asIdeal) ^
        (ramPrimes (K := K) (L := L)).sup (levelOf (K := K) (L := L)) : ℕ) : 𝓞 K)
        ∈ Q.asIdeal ^ (ramPrimes (K := K) (L := L)).sup (levelOf (K := K) (L := L)) := by
      rw [Nat.cast_pow]
      exact Ideal.pow_mem_pow (Ideal.absNorm_mem Q.asIdeal) _
    have hle : levelOf (K := K) (L := L) Q ≤
        (ramPrimes (K := K) (L := L)).sup (levelOf (K := K) (L := L)) := Finset.le_sup hQ
    rw [← Finset.prod_erase_mul (ramPrimes (K := K) (L := L))
      (fun Q => (Ideal.absNorm Q.asIdeal) ^ (ramPrimes (K := K) (L := L)).sup
        (levelOf (K := K) (L := L))) hQ]
    rw [Nat.cast_mul]
    refine Ideal.mul_mem_left (Q.asIdeal ^ levelOf (K := K) (L := L) Q) _ ?_
    exact Ideal.pow_le_pow_right hle hAN

/-! ## The unramified case -/

/-- At an unramified prime, every unit congruent to `1` modulo `(m)` is a local norm. -/
theorem mem_range_localNormFinite_of_congr (Q : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) {m : ℕ} (hmem : (m : 𝓞 K) ∈ Q.asIdeal)
    {z : (Q.adicCompletion K)ˣ}
    (hz : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        ((z : Q.adicCompletion K) - 1) ≤
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((m : ℕ) : Q.adicCompletion K))) :
    z ∈ (Place.localNormFinite q Q hq).range := by
  have hmlt : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (((m : ℕ) : Q.adicCompletion K)) < 1 := Arl.val_natCast_lt_one Q m hmem
  have hz1 : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      ((z : Q.adicCompletion K) - 1) < 1 := lt_of_le_of_lt hz hmlt
  have hzval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (z : Q.adicCompletion K) = 1 := by
    have h := Valuation.map_add_eq_of_lt_left
      (v := Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)))
      (x := (1 : Q.adicCompletion K)) (y := (z : Q.adicCompletion K) - 1)
      (by rw [map_one]; exact hz1)
    rw [map_one, show (1 : Q.adicCompletion K) + ((z : Q.adicCompletion K) - 1) =
      (z : Q.adicCompletion K) from by ring] at h
    exact h
  have hmem' : z ∈ Place.localUnits K (Place.ofFinite Q) :=
    Place.mem_localUnits_ofFinite_iff_valued_eq_one.mpr hzval
  obtain ⟨u, _, hua⟩ :=
    NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
      Q q hq hunr z hmem'
  exact ⟨u, hua⟩

/-! ## The archimedean places -/

/-- At an infinite place, a positive element of `K_vˣ` is a local norm. -/
theorem posAtReal_mem_range_localNormInfinite {v : InfinitePlace K} {w : InfinitePlace L}
    [hw : w.LiesOver v] {u : v.Completionˣ} (hu : Arl.PosAtReal v u) :
    u ∈ (Place.localNormInfinite w v).range := by
  have hdef : (Place.localNormInfinite w v) =
      Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) := rfl
  rcases InfinitePlace.isReal_or_isComplex v with hvR | hvC
  · rcases InfinitePlace.isReal_or_isComplex w with hwR | hwC
    · rw [hdef, NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_real_real hvR hwR]
      exact Subgroup.mem_top _
    · have hmem : u ∈ Subgroup.comap
          (Units.map ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom) :
            v.Completionˣ →* ℝˣ) (Units.posSubgroup ℝ) := by
        rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
        exact hu hvR
      have h := NK.GlobalCFTdeep.NormIndex.localNormInfinite_posSubgroup_le_range_of_real_complex
        (v := v) (w := w) hvR hwC hmem
      rwa [hdef]
  · have hwC : w.IsComplex := InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
    rw [hdef, NK.GlobalCFTdeep.NormIndex.localNormInfinite_range_eq_top_of_complex_complex hvC hwC]
    exact Subgroup.mem_top _

/-! ## The value of an integer at a finite place -/

/-- The value of the integer `m` in the completion at `Q` is bounded by `exp (-n)` as soon as
`m ∈ Q ^ n`. -/
theorem val_natCast_le_exp_neg_of_mem_pow (Q : HeightOneSpectrum (𝓞 K)) (m n : ℕ)
    (h : ((m : ℕ) : 𝓞 K) ∈ Q.asIdeal ^ n) :
    Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
        (((m : ℕ) : Q.adicCompletion K)) ≤
      (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
  have h1 : (((m : ℕ) : Q.adicCompletion K)) =
      algebraMap K (Q.adicCompletion K) ((m : K)) := (map_natCast _ m).symm
  rw [h1, Commons.NumberTheory.NumberField.Completion.valued_alg_eq]
  have h2 : ((m : K)) = algebraMap (𝓞 K) K ((m : 𝓞 K)) := (map_natCast _ m).symm
  rw [h2, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_le_pow_iff_mem Q ((m : ℕ) : 𝓞 K) n).mpr h

end ExistsCongruence

open ExistsCongruence

/-! ## The main theorem -/

theorem exists_congruenceSubgroup_le_normImage {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    ∃ m : ℕ, 0 < m ∧ ∃ U : Subgroup (NK.GlobalCFT.Idele K),
      (∀ x : NK.GlobalCFT.Idele K, x ∈ U ↔
        (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
          x (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
            NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭)) ∧
        (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal →
          Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((x (NK.GlobalCFT.Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1)
            ≤ Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (((m : ℕ) : 𝔭.adicCompletion K))) ∧
        (∀ w : NumberField.InfinitePlace K,
          NK.CFTLib.Arl.PosAtReal w (x (NK.GlobalCFT.Place.ofInfinite w)))) ∧
      U ≤ NK.GlobalCFT.Idele.normImage K L := by
  classical
  obtain ⟨m, hmpos, hmram⟩ := exists_modulus (K := K) (L := L)
  -- the local norm at the chosen place above each place of `K`
  set Φ : (v : Place K) → (Place.localField L (IdeleHasse.placeAbove v))ˣ →* (Place.localField K v)ˣ :=
    (fun v => match v with
      | Sum.inl w =>
          @Place.localNormInfinite K _ L _ _ (aboveInf (K := K) (L := L) w) w
            (aboveInf_liesOver w)
      | Sum.inr Q =>
          Place.localNormFinite (abovePrime (K := K) (L := L) Q) Q (abovePrime_liesOver Q))
    with hΦdef
  -- the finite set of primes dividing `m`
  have hfin : {Q : HeightOneSpectrum (𝓞 K) | (m : 𝓞 K) ∈ Q.asIdeal}.Finite := by
    refine (Ideal.finite_factors (R := 𝓞 K) (I := Ideal.span {((m : ℕ) : 𝓞 K)}) ?_).subset ?_
    · exact fun h0 => Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hmpos)
        (Ideal.span_singleton_eq_bot.mp h0)
    · intro Q hQ
      exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem Q.asIdeal).mpr hQ)
  set Sfin : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset with hSfindef
  have hSfinmem : ∀ Q : HeightOneSpectrum (𝓞 K), Q ∈ Sfin ↔ (m : 𝓞 K) ∈ Q.asIdeal :=
    fun Q => Set.Finite.mem_toFinset hfin
  set S : Finset (Place K) :=
    (Finset.univ.image Place.ofInfinite) ∪ (Sfin.image Place.ofFinite) with hSdef
  have hSinf : ∀ w : InfinitePlace K, Place.ofInfinite w ∈ S := by
    intro w
    rw [hSdef]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w))
  have hSfinmem' : ∀ Q : HeightOneSpectrum (𝓞 K),
      (m : 𝓞 K) ∈ Q.asIdeal → Place.ofFinite Q ∈ S := by
    intro Q hQ
    rw [hSdef]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨Q, (hSfinmem Q).mpr hQ, rfl⟩)
  have hSofFinite : ∀ Q : HeightOneSpectrum (𝓞 K),
      Place.ofFinite Q ∈ S → (m : 𝓞 K) ∈ Q.asIdeal := by
    intro Q hQ
    rw [hSdef] at hQ
    rcases Finset.mem_union.mp hQ with h | h
    · obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h
      exact absurd (hw ▸ Place.isInfinite_ofInfinite w) (Place.not_isInfinite_ofFinite Q)
    · obtain ⟨Q', hQ', hQQ'⟩ := Finset.mem_image.mp h
      have h' : Q' = Q := Place.ofFinite_inj.mp hQQ'
      exact h' ▸ (hSfinmem Q').mp hQ'
  -- the congruence subgroup of modulus `m`
  let U : Subgroup (Idele K) :=
    { carrier := {x : Idele K |
        (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
          x (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
            NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭)) ∧
        (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal →
          Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (((x (NK.GlobalCFT.Place.ofFinite 𝔭)) : 𝔭.adicCompletion K) - 1)
            ≤ Valued.v (R := 𝔭.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (((m : ℕ) : 𝔭.adicCompletion K))) ∧
        (∀ w : NumberField.InfinitePlace K,
          NK.CFTLib.Arl.PosAtReal w (x (NK.GlobalCFT.Place.ofInfinite w)))}
      one_mem' := by
        refine ⟨?_, ?_, ?_⟩
        · intro 𝔭 _
          rw [Idele.one_apply]
          exact Subgroup.one_mem _
        · intro 𝔭 _
          rw [Idele.one_apply]
          exact Arl.congrAt_one 𝔭 m
        · intro w
          rw [Idele.one_apply]
          exact Arl.posAtReal_one w
      mul_mem' := by
        intro x y hx hy
        refine ⟨?_, ?_, ?_⟩
        · intro 𝔭 h𝔭
          rw [Idele.mul_apply]
          exact Subgroup.mul_mem _ (hx.1 𝔭 h𝔭) (hy.1 𝔭 h𝔭)
        · intro 𝔭 h𝔭
          rw [Idele.mul_apply]
          exact Arl.congrAt_mul 𝔭 m h𝔭 (hx.2.1 𝔭 h𝔭) (hy.2.1 𝔭 h𝔭)
        · intro w
          rw [Idele.mul_apply]
          exact Arl.posAtReal_mul (hx.2.2 w) (hy.2.2 w)
      inv_mem' := by
        intro x hx
        refine ⟨?_, ?_, ?_⟩
        · intro 𝔭 h𝔭
          rw [Idele.inv_apply]
          exact Subgroup.inv_mem _ (hx.1 𝔭 h𝔭)
        · intro 𝔭 h𝔭
          rw [Idele.inv_apply]
          exact Arl.congrAt_inv 𝔭 m h𝔭 (hx.2.1 𝔭 h𝔭)
        · intro w
          rw [Idele.inv_apply]
          exact Arl.posAtReal_inv (hx.2.2 w) }
  refine ⟨m, hmpos, U, fun x => Iff.rfl, ?_⟩
  -- the identification of `Φ` with the local norms
  have hΦfin : ∀ Q : HeightOneSpectrum (𝓞 K),
      Φ (Place.ofFinite Q) = Place.localNormFinite (abovePrime (K := K) (L := L) Q) Q
        (abovePrime_liesOver Q) := fun Q => rfl
  have hΦinf : ∀ w : InfinitePlace K,
      Φ (Place.ofInfinite w) = @Place.localNormInfinite K _ L _ _
        (aboveInf (K := K) (L := L) w) w (aboveInf_liesOver w) := fun w => rfl
  have hbridge : ∀ (v : Place K) (u : (Place.localField L (IdeleHasse.placeAbove v))ˣ),
      Idele.normIdeleFun K L
        (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (IdeleHasse.placeAbove v) u)
        v = Φ v u := by
    intro v u
    cases v with
    | inl w =>
        exact NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofInfinite
          (v := w) (w := aboveInf (K := K) (L := L) w) (hw := aboveInf_liesOver w) u
    | inr Q =>
        exact NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite
          Q (abovePrime Q) (abovePrime_liesOver Q) u
  -- the congruence subgroup lies in the constrained idèles
  have hU : U ≤ NK.GlobalCFTdeep.constrainedE S (fun v : ↥S => (Φ ↑v).range) := by
    intro x hx
    rw [NK.GlobalCFTdeep.mem_constrainedE]
    refine ⟨fun v => ?_, fun v hvS => ?_⟩
    · rcases hv : (↑v : Place K) with w | Q
      · have hpos : Arl.PosAtReal w (x (Place.ofInfinite w)) := hx.2.2 w
        rw [hΦinf w]
        exact posAtReal_mem_range_localNormInfinite (v := w) (w := aboveInf (K := K) (L := L) w)
          (hw := aboveInf_liesOver w) hpos
      · have hv' : (↑v : Place K) = Place.ofFinite Q := hv
        have hmem : (m : 𝓞 K) ∈ Q.asIdeal := hSofFinite Q (hv' ▸ v.2)
        by_cases hram : Q ∈ ramPrimes (K := K) (L := L)
        · have hpow : (m : 𝓞 K) ∈ Q.asIdeal ^ levelOf (K := K) (L := L) Q := hmram Q hram
          have hvalm : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (((m : ℕ) : Q.adicCompletion K)) ≤
              (WithZero.exp (-((levelOf (K := K) (L := L) Q : ℕ) : ℤ)) :
                WithZero (Multiplicative ℤ)) :=
            val_natCast_le_exp_neg_of_mem_pow Q m (levelOf (K := K) (L := L) Q) hpow
          have hz : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
              (((x (Place.ofFinite Q) : (Q.adicCompletion K)ˣ) : Q.adicCompletion K) - 1) ≤
              (WithZero.exp (-((levelOf (K := K) (L := L) Q : ℕ) : ℤ)) :
                WithZero (Multiplicative ℤ)) :=
            le_trans (hx.2.1 Q hmem) hvalm
          have hmemr := mem_range_localNormFinite_of_val_le_levelOf Q (x (Place.ofFinite Q)) hz
          rwa [hΦfin Q]
        · have hunr : (abovePrime (K := K) (L := L) Q).asIdeal.ramificationIdx (𝓞 K) = 1 :=
            ramificationIdx_eq_one_of_notMem_ramPrimes hram (abovePrime_liesOver Q)
          have hmemr := mem_range_localNormFinite_of_congr Q (abovePrime Q)
            (abovePrime_liesOver Q) hunr hmem (hx.2.1 Q hmem)
          rwa [hΦfin Q]
    · cases v with
      | inl w => exact absurd (hSinf w) hvS
      | inr Q => exact hx.1 Q (fun hmem => hvS (hSfinmem' Q hmem))
  -- outside `S` the local norm is surjective on the local units
  have hunit : ∀ v : Place K, v ∉ S → ∀ a ∈ Place.localUnits K v,
      ∃ u ∈ Place.localUnits L (IdeleHasse.placeAbove v), Φ v u = a := by
    intro v
    cases v with
    | inl w => exact fun hvS => absurd (hSinf w) hvS
    | inr Q =>
      intro hvS a ha
      have hnotm : (m : 𝓞 K) ∉ Q.asIdeal := fun hmem => hvS (hSfinmem' Q hmem)
      have hnotram : Q ∉ ramPrimes (K := K) (L := L) := fun hram =>
        hnotm (Ideal.pow_le_self (n := levelOf (K := K) (L := L) Q)
          (levelOf_pos Q).ne' (hmram Q hram))
      have hunr : (abovePrime (K := K) (L := L) Q).asIdeal.ramificationIdx (𝓞 K) = 1 :=
        ramificationIdx_eq_one_of_notMem_ramPrimes hnotram (abovePrime_liesOver Q)
      obtain ⟨u, hu, hua⟩ :=
        NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
          Q (abovePrime Q) (abovePrime_liesOver Q) hunr a ha
      refine ⟨u, ?_, ?_⟩
      · show u ∈ Place.localUnits L (Place.ofFinite (abovePrime (K := K) (L := L) Q))
        exact hu
      · show (Place.localNormFinite (abovePrime (K := K) (L := L) Q) Q
          (abovePrime_liesOver Q)) u = a
        exact hua
  exact hU.trans (NK.GlobalCFTdeep.NormIndex.constrainedE_le_normImage S (fun v : ↥S => (Φ ↑v).range)
    IdeleHasse.placeAbove IdeleHasse.liesOver_placeAbove Φ hbridge (fun v => le_rfl) hunit)

end

end NK.CFTLib
