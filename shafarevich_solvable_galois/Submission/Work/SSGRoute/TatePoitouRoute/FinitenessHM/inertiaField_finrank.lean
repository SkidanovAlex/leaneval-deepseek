import Mathlib
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExpInertia
import Submission.Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB
import Submission.Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Work.Sha2Lib.inertiaDeg_cyclotomic_level
import Submission.Commons.NumberTheory.NumberField.Completion.exists_ringEquiv_adicCompletion_of_residue_ringEquiv
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.finrank_le_natDegree_of_aeval_eq_zero
import Submission.Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open IsDedekindDomain
open scoped IntermediateField

/-- **Two cyclotomic extensions of the same level over the same base field have the same degree.**
This is the uniqueness of the cyclotomic extension of a given level, in degrees:
`IsCyclotomicExtension.algEquiv`. -/
theorem finrank_eq_of_isCyclotomicExtension {K L L' : Type*} [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L'] {m : ℕ} [NeZero m]
    [IsCyclotomicExtension {m} K L] [IsCyclotomicExtension {m} K L'] :
    Module.finrank K L = Module.finrank K L' :=
  (IsCyclotomicExtension.algEquiv {m} K L L').toLinearEquiv.finrank_eq

-- TEMPORARY local copy of the delegated lemma `exists_cyclotomic_completion_finrank`
-- (module `...FinitenessHM.exists_cyclotomic_completion_finrank`); replaced by the import once
-- the delegate lands.
theorem witAux (p f : ℕ) [Fact p.Prime] (hf : 0 < f)
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hQ0 : Q0.asIdeal = Ideal.span
      ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ))) :
    ∃ (M : Type) (_ : Field M) (_ : Algebra (Q0.adicCompletion ℚ) M)
      (_ : FiniteDimensional (Q0.adicCompletion ℚ) M) (w : M),
      IsPrimitiveRoot w (p ^ f - 1) ∧
      Module.finrank (Q0.adicCompletion ℚ) M = f := by sorry

-- TEMPORARY local copy of the delegated lemma `residueField_pow_generated_by_residue`.
theorem genAux {K : Type*} [Field K] [NumberField K]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [hQ : Q.asIdeal.LiesOver Q0.asIdeal]
    (ζ : Q.adicCompletionIntegers K)
    (hζ : IsPrimitiveRoot (ζ : Q.adicCompletion K)
      (Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) - 1)) :
    ∀ y : IsLocalRing.ResidueField (Q.adicCompletionIntegers K), y ≠ 0 →
      ∃ j : ℕ, y = (IsLocalRing.residue (Q.adicCompletionIntegers K) ζ) ^ j := by sorry

theorem inertiaField_finrank {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hQ0 : Q0.asIdeal = Ideal.span
      ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ)))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [hQ : Q.asIdeal.LiesOver Q0.asIdeal]
    (ζ : Q.adicCompletionIntegers K)
    (hζ : IsPrimitiveRoot (ζ : Q.adicCompletion K)
      (Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) - 1)) :
    Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) =
      Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) := by
  classical
  have hp : p.Prime := Fact.out
  set f := Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) with hf
  have hmem : (p : NumberField.RingOfIntegers ℚ) ∈ Q0.asIdeal := by
    rw [hQ0]; exact Ideal.mem_span_singleton_self _
  have hcard : Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) = p ^ f := by
    simpa [hf] using
      (Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
        Q0 p hp hmem K Q hQ)
  haveI : Finite (IsLocalRing.ResidueField (Q.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K Q
  have hcard2 : 2 ≤ p ^ f := by
    rw [← hcard]; exact Finite.one_lt_card
  have hm : 0 < p ^ f - 1 := by omega
  have hfpos : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hcard2; omega
    · exact h0
  haveI : NeZero (p ^ f - 1) := ⟨hm.ne'⟩
  have hζm : IsPrimitiveRoot (ζ : Q.adicCompletion K) (p ^ f - 1) := by
    rw [← hcard]; exact hζ
  -- ## The upper bound `[ℚ_p(ζ) : ℚ_p] ≤ f`
  obtain ⟨M, hMf, hMA, hMfin, w, hwprim, hwfin⟩ := witAux p f hfpos Q0 hQ0
  letI : Field M := hMf
  letI : Algebra (Q0.adicCompletion ℚ) M := hMA
  haveI : Module.Finite (Q0.adicCompletion ℚ) M := hMfin
  haveI : Algebra.IsIntegral (Q0.adicCompletion ℚ) M :=
    Algebra.IsIntegral.of_finite (Q0.adicCompletion ℚ) M
  let A : IntermediateField (Q0.adicCompletion ℚ) M :=
    IntermediateField.adjoin (Q0.adicCompletion ℚ) {w}
  haveI hEcyc : IsCyclotomicExtension {p ^ f - 1} (Q0.adicCompletion ℚ)
      ↥(inertiaField Q0 Q ζ) :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension
      (K := Q0.adicCompletion ℚ) (n := p ^ f - 1) hζm
  haveI hAcyc : IsCyclotomicExtension {p ^ f - 1} (Q0.adicCompletion ℚ) ↥A :=
    IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension
      (K := Q0.adicCompletion ℚ) (n := p ^ f - 1) hwprim
  have hcmp : Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) =
      Module.finrank (Q0.adicCompletion ℚ) ↥A :=
    finrank_eq_of_isCyclotomicExtension (K := Q0.adicCompletion ℚ)
      (L := ↥(inertiaField Q0 Q ζ)) (L' := ↥A) (m := p ^ f - 1)
  have hAle : Module.finrank (Q0.adicCompletion ℚ) ↥A ≤ Module.finrank (Q0.adicCompletion ℚ) M :=
    Submodule.finrank_le A.toSubmodule
  have hupper : Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) ≤ f := by
    rw [hcmp]
    exact hAle.trans_eq hwfin
  -- ## The lower bound `f ≤ [ℚ_p(ζ) : ℚ_p]`
  have hlower : f ≤ Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) := by
    -- the residue fields carry the canonical algebra structure of Mathlib
    haveI hlies : Ideal.LiesOver (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        (IsLocalRing.maximalIdeal (Q0.adicCompletionIntegers ℚ)) :=
      Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
        Q0 Q hQ
    haveI hloc : IsLocalHom
        (algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)) := inferInstance
    set Fp := IsLocalRing.ResidueField (Q0.adicCompletionIntegers ℚ) with hFp
    set kw := IsLocalRing.ResidueField (Q.adicCompletionIntegers K) with hkw
    set ζbar : kw := IsLocalRing.residue (Q.adicCompletionIntegers K) ζ with hζbar
    -- `kw` is generated over `Fp` by `ζbar`
    have hgen : Algebra.adjoin Fp ({ζbar} : Set kw) = ⊤ := by
      refine eq_top_iff.mpr fun y _ => ?_
      rcases eq_or_ne y 0 with rfl | hy
      · exact Subalgebra.zero_mem _
      · obtain ⟨j, hj⟩ := genAux Q0 Q ζ hζ y hy
        rw [hj]
        exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζbar)) j
    -- the minimal polynomial of `ζ` over `ℤ_p`
    set g : Polynomial (Q0.adicCompletionIntegers ℚ) :=
      minpoly (Q0.adicCompletionIntegers ℚ) ζ with hg
    have hint : IsIntegral (Q0.adicCompletionIntegers ℚ) ζ :=
      IsIntegralClosure.isIntegral (Q0.adicCompletionIntegers ℚ) (Q.adicCompletion K) ζ
    have hgmonic : g.Monic := minpoly.monic hint
    have hcompat : (algebraMap Fp kw).comp
          (IsLocalRing.residue (Q0.adicCompletionIntegers ℚ)) =
        (IsLocalRing.residue (Q.adicCompletionIntegers K)).comp
          (algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)) :=
      RingHom.ext fun r => IsLocalRing.ResidueField.algebraMap_residue r
    have haeval : Polynomial.aeval ζbar
        (g.map (IsLocalRing.residue (Q0.adicCompletionIntegers ℚ))) = 0 := by
      have hkey := Polynomial.map_aeval_eq_aeval_map (R := Q0.adicCompletionIntegers ℚ)
        (S := Q.adicCompletionIntegers K) (T := Fp) (U := kw)
        (φ := IsLocalRing.residue (Q0.adicCompletionIntegers ℚ))
        (ψ := IsLocalRing.residue (Q.adicCompletionIntegers K)) hcompat g ζ
      rw [hg] at hkey
      rw [show (Polynomial.aeval ζ) (minpoly (Q0.adicCompletionIntegers ℚ) ζ) = 0 from
        minpoly.aeval _ _, map_zero] at hkey
      exact hkey.symm
    have hdim := finrank_le_natDegree_of_aeval_eq_zero
      (x := ζbar) (g := g.map (IsLocalRing.residue (Q0.adicCompletionIntegers ℚ)))
      (hgmonic.map _) haeval hgen
    have hdeg : (g.map (IsLocalRing.residue (Q0.adicCompletionIntegers ℚ))).natDegree =
        g.natDegree := by
      refine Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ ?_
      rw [hgmonic.leadingCoeff, map_one]; exact one_ne_zero
    have hdeg2 : g.natDegree = Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) := by
      have hrel : minpoly (Q0.adicCompletion ℚ) (ζ : Q.adicCompletion K) =
          g.map (algebraMap (Q0.adicCompletionIntegers ℚ) (Q0.adicCompletion ℚ)) := by
        rw [hg]
        exact minpoly.isIntegrallyClosed_eq_field_fractions (Q0.adicCompletion ℚ)
          (Q.adicCompletion K) hint
      have hmap : (g.map (algebraMap (Q0.adicCompletionIntegers ℚ)
          (Q0.adicCompletion ℚ))).natDegree = g.natDegree := by
        refine Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ ?_
        rw [hgmonic.leadingCoeff, map_one]; exact one_ne_zero
      have hadj : Module.finrank (Q0.adicCompletion ℚ)
            ↥(IntermediateField.adjoin (Q0.adicCompletion ℚ) {(ζ : Q.adicCompletion K)}) =
          (minpoly (Q0.adicCompletion ℚ) (ζ : Q.adicCompletion K)).natDegree :=
        IntermediateField.adjoin.finrank (liftElem_isIntegral Q0 Q ζ)
      have heq : inertiaField Q0 Q ζ =
          IntermediateField.adjoin (Q0.adicCompletion ℚ) {(ζ : Q.adicCompletion K)} := rfl
      calc g.natDegree = (g.map (algebraMap (Q0.adicCompletionIntegers ℚ)
              (Q0.adicCompletion ℚ))).natDegree := hmap.symm
        _ = (minpoly (Q0.adicCompletion ℚ) (ζ : Q.adicCompletion K)).natDegree :=
            (congrArg Polynomial.natDegree hrel).symm
        _ = Module.finrank (Q0.adicCompletion ℚ)
              ↥(IntermediateField.adjoin (Q0.adicCompletion ℚ) {(ζ : Q.adicCompletion K)}) :=
            hadj.symm
        _ = Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) := by rw [heq]
    have hcardFp : Nat.card Fp = p :=
      Commons.NumberTheory.NumberField.Completion.residueCard_adicCompletionIntegers_rat
        Q0 p hp hmem
    haveI : Module.Finite Fp kw := Module.Finite.of_finite
    have hnat := Module.natCard_eq_pow_finrank (K := Fp) (V := kw)
    have hfrank : Module.finrank Fp kw = f := by
      have h3 : p ^ f = p ^ Module.finrank Fp kw := by
        rw [← hcard, hnat, hcardFp]
      exact Nat.pow_right_injective hp.two_le h3.symm
    calc f = Module.finrank Fp kw := hfrank.symm
      _ ≤ (g.map (IsLocalRing.residue (Q0.adicCompletionIntegers ℚ))).natDegree := hdim
      _ = g.natDegree := hdeg
      _ = Module.finrank (Q0.adicCompletion ℚ) ↥(inertiaField Q0 Q ζ) := hdeg2
  exact (le_antisymm hupper hlower).trans hf

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
