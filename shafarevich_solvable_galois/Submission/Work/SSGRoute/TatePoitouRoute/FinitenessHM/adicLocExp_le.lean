import Mathlib
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocAux
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExpInertia
import Submission.Work.SSGRoute.Finiteness.inertiaFieldFinrank
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.differentIdeal_inertiaRing_eq_top
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.inertiaRing_span_p_isMaximal
import Submission.Work.SSGRoute.Finiteness.inertiaRingLocal
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.Standalone.inertia_ordAt_algebraMap
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.Standalone.inertia_ordAt_natCast
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.Standalone.inertia_derivative_bound
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.helpersTotallyRamified
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.aeval_derivative_sum
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.ordAt_sum_le
import Submission.Commons.NumberTheory.NumberField.charZero_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB
import Submission.Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one
import Submission.Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open scoped NumberField WithZero
open IsDedekindDomain

noncomputable section

/-- **The local different bound.**  For the `p`-adic completion `L = Q.adicCompletion K` of a
number field `K` at a prime `Q` over `(p)`, the exponent `adicLocExp Q0 Q hQ` of the maximal ideal
in the relative different of `𝒪_L` over `ℤ_p` is at most `e * (1 + e * v_p e)` with
`e = e(Q/p) = Q.asIdeal.ramificationIdx (𝓞 ℚ)`.

Proof plan (classical, entirely inside the local field; see
`FinitenessHM/NOTE_completion_route_and_locExp_flaw.md` §2):

* let `ζ ∈ 𝒪_L` be a primitive `(|κ_L| - 1)`-st root of unity with residue generating `κ_L^×`
  (`Commons.…Completion.exists_isPrimitiveRoot_lift_adicCompletionB` with base `ℚ`, extension `K`);
  `E := ℚ_p(ζ) ⊆ L` is unramified of degree `f = Q.asIdeal.inertiaDeg (𝓞 ℚ)` over `ℚ_p`
  (`card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg` for the residue cardinality), and
  `[L : E] = e` (`finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg` combined with
  `[L : ℚ_p] = e*f`), so `L/E` is totally ramified (the ramification index of `L/E` is `e` and
  this is the degree);
* `𝒪_L = 𝒪_E[π]` for a uniformiser `π`
  (`Commons.…Completion.exists_uniformizer_val_eq_exp_neg_one`); then
  `𝓡_{L/E} = (F'(π))` for `F = minpoly 𝒪_E π` (`conductor_mul_differentIdeal`, conductor `1`);
* `𝓡_{L/ℚ_p} = 𝓡_{L/E}` because `𝓡_{E/ℚ_p} = ⊤` (`E/ℚ_p` unramified: compare
  `not_dvd_differentIdeal_iff` / `differentIdeal_eq_top_of_ramificationIdx`), via the tower formula
  `differentIdeal_eq_differentIdeal_mul_differentIdeal` for `ℤ_p ⊆ 𝒪_E ⊆ 𝒪_L`;
* the orders of the summands `τ_j = (j+1)*F.coeff (j+1)*π^j` of `F'(π)` are `≡ j (mod e)` because
  `ordAt (π) = 1` and, for `c ∈ 𝒪_E`, `ordAt (algebraMap c) = e * ordAt c`
  (`ordAt_algebraMap_eq_mul_ramificationIdx`); the `e` residues are pairwise distinct, so
  `ordAt (F'(π)) = min_j ordAt (τ_j) ≤ ordAt (τ_{e-1}) = e * v_p(e) + e - 1`
  (`aeval_derivative_sum` + `ordAt_sum_le`, both proved in this directory and stated for arbitrary
  Dedekind domains);
* finally `e * v_p(e) + e - 1 ≤ e * (1 + e * v_p(e))` (`arith_count_le` in
  `differentIdeal_count_le_proved.lean`).

Useful existing API: `Finrank`/`ramificationIdx` for completions in
`Submission/Commons/NumberTheory/NumberField/Completion/`, the Henselian/uniformiser apparatus in
`Submission/Commons/RingTheory/Henselian/`, and `NK.RamificationDeep.uniformizerData_of_isGalois`
for the uniformiser/inertia-field data of a Galois-stable valuation ring. -/
theorem adicLocExp_le {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hQ0 : Q0.asIdeal = Ideal.span
      ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : Q.asIdeal.LiesOver Q0.asIdeal) :
    Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExp Q0 Q hQ ≤
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
      (1 + Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) *
        padicValNat p (Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ))) := by
  classical
  -- the elementary arithmetic used at the very end of the argument
  have harith : ∀ e v : ℕ, e * v + e - 1 ≤ e * (1 + e * v) := by
    intro e v
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp
    · have hv : v ≤ e * v := le_mul_of_one_le_left (Nat.zero_le v) h
      have h2 : e * (1 + e * v) = e + e * (e * v) := by ring
      rw [h2]
      have h3 := Nat.mul_le_mul_left e hv
      omega
  haveI hQinst : Q.asIdeal.LiesOver Q0.asIdeal := hQ
  haveI hcharZero : CharZero (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion (K := K) Q
  -- ## the Teichmüller lift of a generator of the residue field
  obtain ⟨ζ, hζ, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB
      Q0 Q hQ
  -- ## the interface facts about the inertia field
  have hfin := Work.SSGRoute.Finiteness.finrank_inertiaField_eq (K := K) p Q0 hQ0 Q ζ hζ
  have hD := differentIdeal_inertiaRing_eq_top (K := K) p Q0 hQ0 Q ζ hζ
  obtain ⟨hmax, -⟩ := inertiaRing_span_p_isMaximal (K := K) p Q0 hQ0 Q ζ hζ hfin
  have hordn := Standalone.inertia_ordAt_natCast (K := K) p Q0 hQ0 Q ζ hζ hD hmax
  have hunder : Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)) =
      (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).comap
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) := by
    have hpne : ((p : ℕ) : Q.adicCompletion K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hpmem : (p : Q.adicCompletionIntegers K) ∈
        IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) := by
      rw [← pow_one (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)),
        mem_maximalIdeal_pow_iff_le_adicValExp Q hpne 1]
      rw [show ((p : Q.adicCompletionIntegers K) : Q.adicCompletion K) =
        ((p : ℕ) : Q.adicCompletion K) from map_natCast
          (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)) p]
      rw [adicValExp_natCast (K := K) (p := p) (Q := Q) Q0 hQ0 hQ p
        (Fact.out : p.Prime).ne_zero]
      simp only [padicValNat_self, mul_one]
      exact_mod_cast (Ideal.ramificationIdx_pos (R := NumberField.RingOfIntegers ℚ) (q := Q.asIdeal))
    have hle : Ideal.span ({(p : ↥(inertiaRing Q0 Q ζ))} : Set ↥(inertiaRing Q0 Q ζ)) ≤
        (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).comap
          (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      refine Ideal.mem_comap.mpr ?_
      rw [map_natCast]
      exact hpmem
    have hprime : ((IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).comap
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K))).IsPrime :=
      inferInstance
    exact hmax.eq_of_le hprime.ne_top hle
  have hordc := Standalone.inertia_ordAt_algebraMap (K := K) p Q0 hQ0 Q ζ hζ hfin hmax hunder
  -- ## a uniformiser
  obtain ⟨π, hπ, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_val_eq_exp_neg_one Q
  -- ## the congruence bound for the derivative of the minimal polynomial of `π` over `𝒪_E`
  obtain ⟨hdegπ, hbound⟩ := Standalone.inertia_derivative_bound (K := K) p Q0 hQ0 Q ζ hζ hfin hmax
    hunder hordc hordn π hπ
  -- ## `E(π) = L`, so that Mathlib's derivative lemma applies
  have hcoee : (π : Q.adicCompletion K) =
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) π := rfl
  have hCint : IsIntegral ↥(inertiaRing Q0 Q ζ) π :=
    IsIntegralClosure.isIntegral ↥(inertiaRing Q0 Q ζ) (Q.adicCompletion K) π
  have hmin : (minpoly ↥(inertiaField Q0 Q ζ) (π : Q.adicCompletion K)).natDegree =
      (minpoly ↥(inertiaRing Q0 Q ζ) π).natDegree := by
    have hmap := minpoly.isIntegrallyClosed_eq_field_fractions ↥(inertiaField Q0 Q ζ)
      (Q.adicCompletion K) hCint
    have hinj : Function.Injective
        (algebraMap ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)) := fun a b hab => Subtype.ext hab
    rw [hcoee, hmap, Polynomial.natDegree_map_eq_of_injective hinj]
  have hfpos : 0 < Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) :=
    Ideal.inertiaDeg_pos (R := NumberField.RingOfIntegers ℚ) (q := Q.asIdeal)
  have hLE : Module.finrank ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) =
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) := by
    have hL := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := ℚ) (L := K) Q0 Q hQ
    have hmul := Module.finrank_mul_finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ)
      (Q.adicCompletion K)
    rw [← hL, hfin] at hmul
    have h2 : Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) *
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) =
        Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) *
          Module.finrank ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K) := by
      rw [mul_comm]
      exact hmul.symm
    exact (Nat.mul_left_cancel hfpos h2).symm
  have hgen : Algebra.adjoin ↥(inertiaField Q0 Q ζ)
      {algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) π} = ⊤ := by
    rw [← hcoee, ← IntermediateField.adjoin_eq_top_iff]
    rw [Field.primitive_element_iff_minpoly_natDegree_eq]
    rw [hmin, hdegπ]
    exact hLE.symm
  -- ## the element `f'(π) ∈ 𝔇_{𝒪_L/ℤ_p}`
  have hcompat : ∀ q : Polynomial ↥(inertiaRing Q0 Q ζ),
      algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) (Polynomial.aeval π q) =
        Polynomial.aeval ((algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)) π)
          (q.map (algebraMap ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ))) := by
    intro q
    have hhom : (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K)).comp
        (algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) =
        (algebraMap ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K)).comp
          (algebraMap ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)) := by
      refine RingHom.ext fun c => ?_
      show (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K))
          ((algebraMap ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)) c) =
        (algebraMap ↥(inertiaField Q0 Q ζ) (Q.adicCompletion K))
          ((algebraMap ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)) c)
      rw [← IsScalarTower.algebraMap_apply ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)
        (Q.adicCompletion K)]
      rw [← IsScalarTower.algebraMap_apply ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)
        (Q.adicCompletion K)]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map,
      hhom]
  have hpoly : Polynomial.derivative
      (minpoly ↥(inertiaField Q0 Q ζ) (π : Q.adicCompletion K)) =
      (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)).map
        (algebraMap ↥(inertiaRing Q0 Q ζ) ↥(inertiaField Q0 Q ζ)) := by
    rw [hcoee, minpoly.isIntegrallyClosed_eq_field_fractions ↥(inertiaField Q0 Q ζ)
      (Q.adicCompletion K) hCint, Polynomial.derivative_map]
  have hgmem : Polynomial.aeval π
      (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)) ∈
      differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) := by
    have h1 : Polynomial.aeval π (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)) ∈
        differentIdeal ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K) :=
      aeval_derivative_mem_differentIdeal (A := ↥(inertiaRing Q0 Q ζ))
        (K := ↥(inertiaField Q0 Q ζ)) (B := Q.adicCompletionIntegers K)
        (L := Q.adicCompletion K) π hgen
    have htow := differentIdeal_eq_differentIdeal_mul_differentIdeal
      (Q0.adicCompletionIntegers ℚ) ↥(inertiaRing Q0 Q ζ) (Q.adicCompletionIntegers K)
    rw [htow, hD, Ideal.map_top, Ideal.mul_top]
    exact h1
  have hgne : Polynomial.aeval π
      (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)) ≠ 0 := by
    intro h0
    have hne := (Algebra.IsSeparable.isSeparable ↥(inertiaField Q0 Q ζ)
      (π : Q.adicCompletion K)).aeval_derivative_ne_zero
      (minpoly.aeval ↥(inertiaField Q0 Q ζ) (π : Q.adicCompletion K))
    rw [hpoly, hcoee] at hne
    rw [← hcompat (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π))] at hne
    exact hne (by rw [h0, map_zero])
  -- ## the count bound
  have h1 : adicLocExp Q0 Q hQ ≤ ordAt (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
      (Polynomial.aeval π (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π))) := by
    rw [adicLocExp]
    letI : Algebra (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
      RingHom.toAlgebra
        (Commons.NumberTheory.NumberField.Completion.adicCompletionMapIntegers Q0 Q hQ)
    haveI : Module.IsTorsionFree (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
      adicLocExpIsTorsionFreeIntegers Q0 Q
    have hspan : Ideal.span (singleton (Polynomial.aeval π
        (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)))) ≠ ⊥ := by
      simpa [Ideal.span_singleton_eq_bot] using hgne
    have hle : Ideal.span (singleton (Polynomial.aeval π
        (Polynomial.derivative (minpoly ↥(inertiaRing Q0 Q ζ) π)))) ≤
        differentIdeal (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgmem)
    have hprime : (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)).IsPrime :=
      (IsLocalRing.maximalIdeal.isMaximal _).isPrime
    have hbot : IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K) ≠ ⊥ := by
      intro h
      exact IsDiscreteValuationRing.not_isField (Q.adicCompletionIntegers K)
        ((IsLocalRing.isField_iff_maximalIdeal_eq (R := Q.adicCompletionIntegers K)).mpr h)
    have := count_normalizedFactors_le_of_le (R := Q.adicCompletionIntegers K) hprime hbot
      hspan hle
    simpa [ordAt] using this
  -- ## conclusion
  refine le_trans h1 (le_trans hbound ?_)
  exact harith _ _

end

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
