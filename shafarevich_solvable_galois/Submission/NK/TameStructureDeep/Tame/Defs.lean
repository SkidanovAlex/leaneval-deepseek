import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.NK.TameStructureDeep.Support.mem_unramifiedClosure_of_isPrimitiveRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

/-- The residue characteristic of `κ = K_𝔭`: the characteristic of the residue field of the
integers of the completion. -/
abbrev resCharAt : ℕ := ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))

/-- **`π` is a uniformiser of the completion `κ = K_𝔭`**: it generates the maximal ideal of the
discrete valuation ring `𝒪_κ = 𝔭.adicCompletionIntegers K`. -/
def IsUniformizerAt (π : 𝔭.adicCompletionIntegers K) : Prop :=
  IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) = Ideal.span {π}

/-- **The Kummer input of the tamely ramified structure theorem.**

There is a uniformiser `π` of `κ = K_𝔭` with no `n`-th root in the maximal unramified extension
`κ^{ur}` of `κ` (realised in `K'` as `NK.LocalAnabelian.unramifiedClosure p`), for every
`n ≥ 2` prime to the residue characteristic `p`.

Equivalently: `π ∉ (κ^{ur}ˣ) ^ n`.  This is the statement that `κ^{ur}` is linearly disjoint from
the totally ramified extension `κ(π^{1/n})`; by Kummer theory (`X ^ n - C π` is irreducible over
`κ^{ur}`, Mathlib's `FieldTheory.KummerPolynomial`) it gives
`Gal(κ^{ur}(π^{1/n})/κ^{ur}) ≅ ℤ/n` with the Kummer pairing `σ ↦ σ(π^{1/n})/π^{1/n} ∈ μ_n`. -/
def UnramifiedNoPow (K' : Type*) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] : Prop :=
  ∃ π : 𝔭.adicCompletionIntegers K, IsUniformizerAt 𝔭 π ∧
    ∀ n : ℕ, 2 ≤ n → Nat.Coprime n (resCharAt 𝔭) →
      ∀ α : K',
        α ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (resCharAt 𝔭) →
          α ^ n ≠ algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)

/-- The *pointwise* form of `UnramifiedNoPow`, with the uniformiser and the coprimality hypotheses
made explicit: the form in which the arithmetic content is proved. -/
def NoPowRootAt (π : 𝔭.adicCompletionIntegers K) (K' : Type*) [Field K']
    [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] : Prop :=
  IsUniformizerAt 𝔭 π ∧
    ∀ n : ℕ, 2 ≤ n → Nat.Coprime n (resCharAt 𝔭) →
      ∀ α : K',
        α ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (resCharAt 𝔭) →
          α ^ n ≠ algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)

theorem unramifiedNoPow_iff_exists_noPowRootAt (K' : Type*) [Field K']
    [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] :
    UnramifiedNoPow 𝔭 K' ↔ ∃ π, NoPowRootAt 𝔭 π K' :=
  Iff.rfl

end

end NK.TameStructureDeep.Tame
