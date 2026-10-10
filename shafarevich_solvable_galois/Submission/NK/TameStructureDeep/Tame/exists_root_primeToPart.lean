import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.TameStructureDeep.Tame.TameClosure
import Submission.NK.TameStructureDeep.Tame.UnramifiedNoPow
import Submission.NK.TameStructureDeep.Tame.primeToPart
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `d₀`-th root of a uniformiser lies in the maximal tamely ramified extension

For a place `𝔭` of a number field `K`, a separable closure `K'` of the completion
`κ = K_𝔭`, a uniformiser `π` of `κ` and `m > 0`, the prime-to-`p` part
`d₀ = primeToPart 𝔭 m` (the largest divisor of `m` coprime to the residue characteristic `p`)
admits a `d₀`-th root of `π` inside the maximal tamely ramified extension `κ^{tr} = tameClosure`:

  `∃ γ ∈ κ^{tr},  γ ^ d₀ = π`.

This is the *existence* half of the description `κ^{tr} = κ^{ur}(π^{1/n} : p ∤ n)`: the defining
Kummer fields of `κ^{tr}` are non-trivial.  Note that the statement only needs `π ≠ 0`, hence
it holds for an arbitrary uniformiser; the arithmetic input `UnramifiedNoPow` (the *non*-existence
of `n`-th roots in the maximal *unramified* extension `κ^{ur}`) is what makes
`κ^{ur}(π^{1/n})/κ^{ur}` nontrivial, and it is not used here.

The only field-theoretic input is that `K'` is separably closed *and* `char K' = 0` (a completion
of a number field has characteristic `0`), so that `X ^ n - π` is separable for every `n ≠ 0`.
-/
set_option linter.style.haveILetI false

open scoped Classical
open IntermediateField

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The completion `κ = K_𝔭` of a number field is a field of characteristic zero, hence so is
every field extension `K'` of `κ`: the structure map `ℕ → K'` factors through the (injective)
structure maps `ℕ → K` and `K → κ → K'`. -/
theorem charZero_of_algebra_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] : CharZero K' := by
  refine ⟨fun a b h => ?_⟩
  have h2 : ((a : ℕ) : 𝔭.adicCompletion K) = ((b : ℕ) : 𝔭.adicCompletion K) := by
    apply RingHom.injective (algebraMap (𝔭.adicCompletion K) K')
    simpa only [map_natCast] using h
  have h3 : (a : K) = (b : K) := by
    apply RingHom.injective (algebraMap K (𝔭.adicCompletion K))
    simpa only [map_natCast] using h2
  simpa using h3

/-- Any `n ≠ 0` is nonzero in `K'`, since `char K' = 0`. -/
theorem natCast_ne_zero_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] {n : ℕ} (hn : n ≠ 0) : (n : K') ≠ 0 := by
  haveI := charZero_of_algebra_adicCompletion 𝔭 (K' := K')
  exact (Nat.cast_ne_zero).mpr hn

theorem exists_root_primeToPart {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {m : ℕ} (hm : 0 < m) {π : 𝔭.adicCompletionIntegers K}
    (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π) :
    ∃ γ : K', γ ^ NK.TameStructureDeep.Tame.primeToPart 𝔭 m =
        algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) ∧
      γ ∈ NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K) := by
  haveI : CharZero K' := charZero_of_algebra_adicCompletion 𝔭
  haveI : IsSepClosed K' := IsSepClosure.sep_closed (𝔭.adicCompletion K)
  -- `d₀ = primeToPart 𝔭 m` is nonzero, hence nonzero in `K'`, so `X ^ d₀ - C π` is separable
  haveI : NeZero ((NK.TameStructureDeep.Tame.primeToPart 𝔭 m : ℕ) : K') :=
    ⟨natCast_ne_zero_adicCompletion 𝔭 (K' := K')
      (NK.TameStructureDeep.Tame.primeToPart_ne_zero 𝔭 hm)⟩
  -- separably closed fields contain `n`-th roots
  obtain ⟨γ, hγ⟩ := IsSepClosed.exists_pow_nat_eq (k := K')
      (algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K))
      (NK.TameStructureDeep.Tame.primeToPart 𝔭 m)
  refine ⟨γ, hγ, ?_⟩
  -- `γ` is a `d₀`-th root of `π` with `d₀` prime to `p`, hence generates a Kummer layer of `κ^{tr}`
  have hmem : γ ∈ NK.TameStructureDeep.Tame.tameRootSet (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) :=
    ⟨NK.TameStructureDeep.Tame.primeToPart 𝔭 m,
      NK.TameStructureDeep.Tame.not_dvd_primeToPart 𝔭 hm.ne', hγ⟩
  have h1 : γ ∈ IntermediateField.adjoin (𝔭.adicCompletion K)
      (NK.TameStructureDeep.Tame.tameRootSet (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)
        ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) :=
    IntermediateField.subset_adjoin _ _ hmem
  have h2 : (IntermediateField.adjoin (𝔭.adicCompletion K)
      (NK.TameStructureDeep.Tame.tameRootSet (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)
        ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) :
        IntermediateField (𝔭.adicCompletion K) K') ≤
      NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)
        ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) := by
    rw [NK.TameStructureDeep.Tame.tameClosure]
    exact le_sup_right
  exact h2 h1

end

end NK.TameStructureDeep.Tame
