/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `[κ(μ_n) : κ] = ord_n(q)` for `n` prime to `p`

For a `p`-adic field `κ = K_𝔭` with residue field of `q = p^f` elements and `n` prime to `p`, the
cyclotomic extension `κ(μ_n)` is **unramified of degree `ord_n(q)`**:

  `[κ(ζ_n) : κ] = ord_n(q)`,  equivalently  `Gal(κ(μ_n)/κ) ≅ ℤ/ord_n(q)`.

This is the classical statement that makes `κ^ur = κ(μ_{p'})` and hence
`Gal(κ^ur/κ) ≅ Gal(𝔽̄_q/𝔽_q) ≅ Ẑ` — the field `unramifiedQuotient` of
`NK.TameStructureDeep.TameRamificationCore`.

It is assembled here from the two inequalities:

* `NK.TameStructureDeep.Degree.natDegree_minpoly_le_orderOf` — the upper bound: `μ_n` is contained
  in the unramified extension of degree `ord_n(q)` (Teichmüller lift of a primitive `n`-th root of
  the residue field `𝔽_{q^{ord_n(q)}}`), so `κ(μ_n)` has degree at most `ord_n(q)`;
* `NK.TameStructureDeep.Degree.orderOf_dvd_natDegree_minpoly` — the lower bound: the reduction
  map is injective on the `n`-th roots of unity of `κ(μ_n)` (as `n` is prime to the residue
  characteristic), so `n ∣ q^{[κ(μ_n):κ]} - 1` and `ord_n(q)` divides the degree.

The degree is `(minpoly κ ζ).natDegree` for any primitive `n`-th root `ζ`.
-/
import Submission.NK.TameStructureDeep.Degree.natDegree_minpoly_le_orderOf
import Submission.NK.TameStructureDeep.Degree.orderOf_dvd_natDegree_minpoly
import Submission.NK.Mine.ResidueCharAutomatic

open scoped Classical

namespace NK.TameStructureDeep.Degree

universe u

noncomputable section

/-- **`[κ(ζ_n) : κ] = ord_n(q)`** for `n` prime to the residue characteristic `p`: the degree of the
minimal polynomial of a primitive `n`-th root of unity over `κ = K_𝔭` is the multiplicative order
of the residue field cardinality `q` modulo `n`.  Equivalently `κ(μ_n)/κ` is unramified of degree
`ord_n(q)`. -/
theorem natDegree_minpoly_eq_orderOf {K : Type u} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {n : ℕ} (hn0 : n ≠ 0)
    (hn : ¬ ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ∣ n)
    {ζ : K'} (hζ : IsPrimitiveRoot ζ n) :
    (minpoly (𝔭.adicCompletion K) ζ).natDegree =
      orderOf ((NK.LocalStructure.residueCard K 𝔭 : ZMod n)) := by
  haveI : NeZero n := ⟨hn0⟩
  have hp := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hpc := NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
  obtain ⟨f, hf, hqf⟩ :=
    NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hp hpc
  have hcop : Nat.Coprime (NK.LocalStructure.residueCard K 𝔭) n := by
    rw [hqf]
    exact ((hp.coprime_iff_not_dvd).mpr hn).pow_left f
  have hpos : 0 < orderOf ((NK.LocalStructure.residueCard K 𝔭 : ZMod n)) := by
    let u : (ZMod n)ˣ := IsUnit.unit ((ZMod.isUnit_iff_coprime _ _).mpr hcop)
    have hcoe : (u : ZMod n) = (NK.LocalStructure.residueCard K 𝔭 : ZMod n) :=
      IsUnit.unit_spec _
    have h1 : 0 < orderOf u := orderOf_pos u
    rwa [← orderOf_units, hcoe] at h1
  have hint : Algebra.IsIntegral (𝔭.adicCompletion K) K' := inferInstance
  have hdegpos := minpoly.natDegree_pos (hint.isIntegral ζ)
  refine le_antisymm ?_ ?_
  · exact natDegree_minpoly_le_orderOf 𝔭 hn0 hn hζ
  · exact Nat.le_of_dvd hdegpos (orderOf_dvd_natDegree_minpoly 𝔭 hn0 hn hζ)

/-- **`[κ(μ_n) : κ] = ord_n(q)`** in the form in which the unramified quotient is computed: the
`κ`-dimension of `κ⟮ζ⟯` is `ord_n(q)`. -/
theorem finrank_adjoin_eq_orderOf {K : Type u} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {n : ℕ} (hn0 : n ≠ 0)
    (hn : ¬ ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) ∣ n)
    {ζ : K'} (hζ : IsPrimitiveRoot ζ n) :
    Module.finrank (𝔭.adicCompletion K)
        ↥(IntermediateField.adjoin (𝔭.adicCompletion K) {ζ}) =
      orderOf ((NK.LocalStructure.residueCard K 𝔭 : ZMod n)) := by
  have hint : Algebra.IsIntegral (𝔭.adicCompletion K) K' := inferInstance
  rw [IntermediateField.adjoin.finrank (hint.isIntegral ζ),
    natDegree_minpoly_eq_orderOf 𝔭 hn0 hn hζ]

end

end NK.TameStructureDeep.Degree
