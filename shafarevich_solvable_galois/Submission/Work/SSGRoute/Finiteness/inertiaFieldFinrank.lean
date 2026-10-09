import Mathlib
import Submission.Work.SSGRoute.Finiteness.residueFieldZpowers
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicLocExpInertia
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.finrank_le_natDegree_of_aeval_eq_zero
import Submission.Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB
import Submission.Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree of the inertia field `ℚ_p(ζ)`

`[ℚ_p(ζ) : ℚ_p] = f(Q/p)`, where `ζ ∈ 𝒪_{K_Q}` is a Teichmüller lift of a generator of the
residue field and `f(Q/p)` the inertia degree of `Q` over `p`.

The upper bound is obtained from a "big" finite extension `M / ℚ_p` of degree `f` (the completion
of a global unramified extension of `ℚ` of degree `f` at a prime over `p`) that contains a primitive
`(p^f - 1)`-st root of unity; the cyclotomic extensions `ℚ_p(ζ)` and `ℚ_p(w)` have the same degree,
which is at most `f` since one of them sits inside `M`.  The lower bound is the observation that
the residue field of `𝒪_E` is `𝔽_p(ζ̄)`, of degree `f` over `𝔽_p`.
-/

open scoped NumberField
open IsDedekindDomain

set_option linter.style.haveILetI false

namespace Work.SSGRoute.Finiteness

open Work.SSGRoute.TatePoitouRoute.FinitenessHM

/-- **A global extension of `ℚ` which is unramified of inertia degree `n` at a prime over `p`.**

This is `Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg`
specialised to the base field `ℚ`, with the `ℚ`-algebra structure on the extension normalised to
the canonical one (`DivisionRing.toRatAlgebra`), so that statements whose type mentions
`NumberField`-derived instances can be applied directly. -/
theorem exists_unramified_extension_of_inertiaDeg_rat (n : ℕ) (hn : 0 < n)
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L)
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
      q.asIdeal.LiesOver Q0.asIdeal ∧
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1 ∧
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) = n := by
  obtain ⟨L, hLf, hLnf, hLalg, q, hq, he, hfq, _hfr⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg Q0 n hn
  letI : Field L := hLf
  letI : NumberField L := hLnf
  have hcan : (@NumberField.inst_ringOfIntegersAlgebra ℚ L Rat.instField hLf hLalg) =
      (@NumberField.inst_ringOfIntegersAlgebra ℚ L Rat.instField hLf
        (DivisionRing.toRatAlgebra : Algebra ℚ L)) :=
    congrArg _ (Subsingleton.elim hLalg (DivisionRing.toRatAlgebra : Algebra ℚ L))
  refine ⟨L, hLf, hLnf, q, ?_, ?_, ?_⟩
  · exact hcan ▸ hq
  · exact hcan ▸ he
  · exact hcan ▸ hfq

/-- **A `ℚ_p`-field of degree `f` containing a primitive `(p^f - 1)`-st root of unity.**

Take the completion at a prime over `p` of a global extension of `ℚ` which is unramified of inertia
degree `f` at that prime. -/
theorem exists_unramified_completion_finrank (p f : ℕ) [Fact p.Prime] (hf : 0 < f)
    (Q0 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hQ0 : Q0.asIdeal = Ideal.span
      ({(p : NumberField.RingOfIntegers ℚ)} : Set (NumberField.RingOfIntegers ℚ))) :
    ∃ (M : Type) (_ : Field M) (_ : Algebra (Q0.adicCompletion ℚ) M)
      (_ : FiniteDimensional (Q0.adicCompletion ℚ) M) (w : M),
      IsPrimitiveRoot w (p ^ f - 1) ∧
      Module.finrank (Q0.adicCompletion ℚ) M = f := by
  classical
  have hp : p.Prime := Fact.out
  have hmem : (p : NumberField.RingOfIntegers ℚ) ∈ Q0.asIdeal := by
    rw [hQ0]; exact Ideal.mem_span_singleton_self _
  obtain ⟨L, hLf, hLnf, q, hq, he, hfq⟩ :=
    exists_unramified_extension_of_inertiaDeg_rat f hf Q0
  letI : Field L := hLf
  letI : NumberField L := hLnf
  letI : Algebra (Q0.adicCompletion ℚ) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q0 q hq)
  haveI hfmod : Module.Finite (Q0.adicCompletion ℚ) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q0 q hq
  obtain ⟨ζ, hζ, _⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB
      (K := ℚ) (L := L) Q0 q hq
  have hcard : Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) = p ^ f := by
    rw [Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
      Q0 p hp hmem L q hq, hfq]
  have hfinrank : Module.finrank (Q0.adicCompletion ℚ) (q.adicCompletion L) = f := by
    have h := Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := ℚ) (L := L) Q0 q hq
    rw [he, one_mul, hfq] at h
    exact h.symm
  rw [hcard] at hζ
  exact ⟨q.adicCompletion L, inferInstance, inferInstance, hfmod,
    (ζ : q.adicCompletion L), hζ, hfinrank⟩

/-- **Two cyclotomic extensions of the same level over the same base field have the same degree.** -/
theorem finrank_eq_of_isCyclotomicExtension {K L L' : Type*} [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L'] {m : ℕ} [NeZero m]
    [IsCyclotomicExtension {m} K L] [IsCyclotomicExtension {m} K L'] :
    Module.finrank K L = Module.finrank K L' :=
  (IsCyclotomicExtension.algEquiv {m} K L L').toLinearEquiv.finrank_eq

/-- **The degree of the inertia field.**  `[ℚ_p(ζ) : ℚ_p] = f(Q/p)`, where `ζ ∈ 𝒪_{K_Q}` is a
Teichmüller lift of a generator of the residue field of `K_Q`. -/
theorem finrank_inertiaField_eq {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
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
  obtain ⟨M, hMf, hMA, hMfin, w, hwprim, hwfin⟩ :=
    Work.SSGRoute.Finiteness.exists_unramified_completion_finrank p f hfpos Q0 hQ0
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
    haveI hlies : Ideal.LiesOver (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K))
        (IsLocalRing.maximalIdeal (Q0.adicCompletionIntegers ℚ)) :=
      Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
        Q0 Q hQ
    haveI hloc : IsLocalHom
        (algebraMap (Q0.adicCompletionIntegers ℚ) (Q.adicCompletionIntegers K)) := inferInstance
    set Fp := IsLocalRing.ResidueField (Q0.adicCompletionIntegers ℚ) with hFp
    set kw := IsLocalRing.ResidueField (Q.adicCompletionIntegers K) with hkw
    set ζbar : kw := IsLocalRing.residue (Q.adicCompletionIntegers K) ζ with hζbar
    have hgen : Algebra.adjoin Fp ({ζbar} : Set kw) = ⊤ := by
      refine eq_top_iff.mpr fun y _ => ?_
      rcases eq_or_ne y 0 with rfl | hy
      · exact Subalgebra.zero_mem _
      · obtain ⟨j, hj⟩ := residueField_pow_generated_by_residue (Q := Q) (ζ := ζ) hζ y hy
        rw [hj]
        exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζbar)) j
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

end Work.SSGRoute.Finiteness
