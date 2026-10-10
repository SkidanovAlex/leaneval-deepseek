import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Submission.NK.LocalStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalStructure.Tame

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

/-- **The residue field of a number field at a finite prime is a power of its characteristic.**

Let `K` be a number field, `𝔭` a finite prime of `K`, and `p` a prime number which is the
characteristic of the residue field `κ_𝔭` of the `𝔭`-adic completion of `K`. Then
`q = #κ_𝔭 = residueCard K 𝔭` is a positive power of `p`.

This is the `q_eq` field of `NK.LocalTame.TameStructureInput`.  The content is that the
residue field is a *finite* field: it is `𝓞 K / 𝔭`, which is finite because `𝔭` is maximal
(`Ideal.finiteQuotientOfFreeOfNeBot`), and a finite field of characteristic `p` has cardinality
`p ^ n` with `n > 0` (`FiniteField.card`). -/
theorem residueCard_eq_pow_of_charP {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime) (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    ∃ f : ℕ, 0 < f ∧ NK.LocalStructure.residueCard K 𝔭 = p ^ f := by
  classical
  -- `𝓞 K / 𝔭` is finite (it is the residue field of a number field, `𝔭` being maximal)
  haveI : Finite ((NumberField.RingOfIntegers K) ⧸ 𝔭.asIdeal) := inferInstance
  haveI : Fintype ((NumberField.RingOfIntegers K) ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  -- the residue field of the `𝔭`-adic completion is `𝓞 K / 𝔭`, hence finite
  obtain ⟨e⟩ := Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists 𝔭
  haveI : Fintype (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    Fintype.ofEquiv _ e.symm.toEquiv
  -- a finite field of characteristic `p` has cardinality `p ^ n` with `n > 0`
  haveI := hchar
  obtain ⟨n, _hn, hcard⟩ :=
    FiniteField.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p
  refine ⟨n, n.2, ?_⟩
  rw [NK.LocalStructure.residueCard, Nat.card_eq_fintype_card]
  exact hcard

end NK.LocalStructure.Tame
