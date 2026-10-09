import Submission.Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Degree

open IsDedekindDomain

/-- The Teichmüller lift of a primitive root of unity: if `n ≠ 0` divides `N - 1` where `N` is the
residue field cardinality of `L_q`, then `L_q` contains a primitive `n`-th root of unity.

Use `Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB`
(module `Submission.Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB`),
which produces `ζ : q.adicCompletionIntegers L` that is a primitive `(N - 1)`-st root of unity in
`q.adicCompletion L`; raise it to the power `(N - 1) / n` (`IsPrimitiveRoot.pow_of_dvd`,
`Nat.div_div_self`). -/
theorem exists_isPrimitiveRoot_adicCompletion_of_dvd {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) {n : ℕ} (hn : n ≠ 0)
    (hdvd : n ∣ Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) - 1) :
    ∃ ψ : q.adicCompletion L, IsPrimitiveRoot ψ n := by
  -- The Teichmüller lift: a primitive `(N - 1)`-st root of unity in `L_q`, `N` the cardinality
  -- of the (finite) residue field.
  obtain ⟨ζ, hζ, _⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB
      Q q hq
  -- The residue field is finite, hence (being a field) has at least two elements, so `N - 1 ≠ 0`.
  haveI hfin : Finite (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion L q
  haveI : Fintype (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) := Fintype.ofFinite _
  have h1 : 1 < Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  set N := Nat.card (IsLocalRing.ResidueField (q.adicCompletionIntegers L)) with hN
  have hpos : 0 < N - 1 := by omega
  have hNne : N - 1 ≠ 0 := by omega
  -- Raise `ζ` to the power `(N - 1) / n`; since `n ≠ 0` and `n ∣ N - 1`, this has order `n`.
  have hp : (N - 1) / n ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨hn, Nat.le_of_dvd hpos hdvd⟩
  have h := hζ.pow_of_dvd (p := (N - 1) / n) hp (Nat.div_dvd_of_dvd hdvd)
  rw [Nat.div_div_self hdvd hNne] at h
  exact ⟨_, h⟩

end NK.TameStructureDeep.Degree
