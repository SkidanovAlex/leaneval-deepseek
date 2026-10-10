import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalStructure.Main
import Submission.NK.TameStructureDeep.Tame.units_mem_pow_of_residue_pow_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Tame

/-- **The residue field of the `𝔭`-adic completion has at least two elements.**

The residue field `k = 𝒪_κ/𝔪_κ` of `κ = K_𝔭` is finite
(`Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion`) and, being a
field, non-trivial, so `#k = NK.LocalStructure.residueCard K 𝔭 ≥ 2`.  In particular
`residueCard K 𝔭 - 1 ≠ 0`, which is what makes `μ_{q-1}` a genuine (non-trivial) finite group. -/
theorem two_le_residueCard_adicCompletion (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    2 ≤ NK.LocalStructure.residueCard K 𝔭 := by
  have hfin : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
    Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
  letI : Fintype (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := Fintype.ofFinite _
  rw [NK.LocalStructure.residueCard, Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- **The Teichmüller lift of a generator of the residue units.**  The local field `κ = K_𝔭`
contains a primitive `(q-1)`-st root of unity, `q = NK.LocalStructure.residueCard K 𝔭` being the
cardinality of its residue field.

This is the arithmetic content of the "tame torsion is unramified" statement: `k_κ^×` is cyclic of
order `q - 1`, `q - 1` is prime to the residue characteristic, and Hensel's lemma lifts a generator
of `k_κ^×` to a primitive `(q-1)`-st root of unity in `κ` (the Teichmüller representative of that
generator).  It is obtained from
`Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB` applied
to the pair `(𝔭, 𝔭)` (a prime lies over itself), which works for an *arbitrary* number field `K`
and an *arbitrary* finite prime `𝔭`, so that no extension of number fields has to be manufactured
here. -/
theorem exists_isPrimitiveRoot_adicCompletion_self (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ ζ : 𝔭.adicCompletion K, IsPrimitiveRoot ζ (NK.LocalStructure.residueCard K 𝔭 - 1) := by
  have hlies : 𝔭.asIdeal.LiesOver 𝔭.asIdeal := by
    refine ⟨?_⟩
    rw [Ideal.under, Algebra.algebraMap_self, Ideal.comap_id]
  obtain ⟨ζ, hζ, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB
      𝔭 𝔭 hlies
  exact ⟨ζ, hζ⟩

theorem mu_residueCard_sub_one (K : Type*) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] :
    (Nat.card ↥(rootsOfUnity (NK.LocalStructure.residueCard K 𝔭 - 1) K') =
        NK.LocalStructure.residueCard K 𝔭 - 1) ∧
      (∀ σ : Gal(K'/(𝔭.adicCompletion K)),
        ∀ z ∈ rootsOfUnity (NK.LocalStructure.residueCard K 𝔭 - 1) K', σ (z : K') = z) := by
  classical
  set n := NK.LocalStructure.residueCard K 𝔭 - 1 with hn_def
  have hn : n ≠ 0 := by
    have hq2 := two_le_residueCard_adicCompletion K 𝔭
    omega
  haveI : NeZero n := ⟨hn⟩
  -- A primitive `n`-th root of unity in `κ = K_𝔭`, and its image in `K'`.
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_adicCompletion_self K 𝔭
  have hinj : Function.Injective (algebraMap (𝔭.adicCompletion K) K') :=
    (algebraMap (𝔭.adicCompletion K) K').injective
  have hζ' : IsPrimitiveRoot (algebraMap (𝔭.adicCompletion K) K' ζ) n := hζ.map_of_injective hinj
  refine ⟨hζ'.card_rootsOfUnity, ?_⟩
  -- Every `n`-th root of unity of `K'` is a power of the image of `ζ`, hence is fixed by every
  -- `κ`-algebra automorphism of `K'`.
  intro σ z hz
  have hzpow : (z : K') ^ n = 1 := by
    have h := (mem_rootsOfUnity n (z : (K')ˣ)).mp hz
    simpa using congrArg (fun u : (K')ˣ => (u : K')) h
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hzpow
  rw [← hi, ← map_pow]
  exact σ.commutes (ζ ^ i)

end NK.TameStructureDeep.Tame
