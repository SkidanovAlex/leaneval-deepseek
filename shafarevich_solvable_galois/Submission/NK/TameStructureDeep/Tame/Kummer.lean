import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.TameStructureDeep.Tame.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open Polynomial IntermediateField

set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))

/-- **The Kummer input, pointwise**: a uniformiser `π` of `κ = K_𝔭` has no `n`-th power
representing it inside `κ^{ur}`, for `n ≥ 2` prime to `p`. -/
theorem pow_ne_of_uniformizer {K' : Type*} [Field K']
    [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    (h : UnramifiedNoPow 𝔭 K') {n : ℕ} (hn : 2 ≤ n) (hcop : Nat.Coprime n (resCharAt 𝔭)) :
    ∃ π : 𝔭.adicCompletionIntegers K, IsUniformizerAt 𝔭 π ∧
      ∀ α : K',
        α ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (resCharAt 𝔭) →
        α ^ n ≠ algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) := by
  rw [UnramifiedNoPow] at h
  exact ⟨h.choose, h.choose_spec.1, fun α hα => h.choose_spec.2 n hn hcop α hα⟩

/-! ## Kummer over `κ^{ur}` -/

/-- The element `π`, as an element of the maximal unramified extension `κ^{ur} ⊆ K'`. -/
noncomputable def uniformizerInClosure {K' : Type*} [Field K']
    [Algebra (𝔭.adicCompletion K) K'] (π : 𝔭.adicCompletionIntegers K) :
    ↥(NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭)) :=
  algebraMap (𝔭.adicCompletion K) _ (π : 𝔭.adicCompletion K)

/-- **Kummer over `κ^{ur}`.**  If a uniformiser `π` of `κ` has no `ℓ`-th root in `κ^{ur}` (`ℓ` a
prime different from `p`), then `X ^ ℓ - π` is irreducible over `κ^{ur}`.

Hence `κ^{ur}(π^{1/ℓ})/κ^{ur}` is cyclic of degree `ℓ` with Galois group `μ_ℓ` under the Kummer
pairing: the first step of `Gal(κ^{tr}/κ^{ur}) ≅ ∏_{ℓ ≠ p} ℤ_ℓ`. -/
theorem irreducible_X_pow_sub_C_unramifiedClosure {K' : Type*} [Field K']
    [Algebra (𝔭.adicCompletion K) K'] {π : 𝔭.adicCompletionIntegers K}
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ resCharAt 𝔭)
    (h : ∀ α : K',
      α ∈ NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (resCharAt 𝔭) →
      α ^ ℓ ≠ algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K)) :
    Irreducible (X ^ ℓ - C (uniformizerInClosure 𝔭 (K' := K') π)) := by
  refine X_pow_sub_C_irreducible_of_prime hℓ fun b hb => ?_
  -- `b ^ ℓ = π` in `κ^{ur}` contradicts the Kummer input
  have hb' : (b : K') ^ ℓ = algebraMap (𝔭.adicCompletion K) K' (π : 𝔭.adicCompletion K) := by
    have := congrArg (Subtype.val) hb
    simpa [uniformizerInClosure] using this
  exact h (b : K') b.2 hb'

end

end NK.TameStructureDeep.Tame
