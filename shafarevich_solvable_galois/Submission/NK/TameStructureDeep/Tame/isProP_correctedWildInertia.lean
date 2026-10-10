import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.TameStructureDeep.Tame.relIndex_wildInertia_prime_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The corrected wild inertia `V_κ = Gal(K'/κ^{tr})` is a pro-`p` group

Let `κ = K_𝔭`, `p = resCharAt 𝔭`, `T = κ^{tr} = tameClosure p π` and
`V = correctedWildInertia p π = Gal(K'/T)`.  The proof is an assembly of two proved lemmas:

* `NK.TameStructureDeep.Tame.isProP_fixingSubgroup_of_relIndex_prime_pow`: `IsProP p ↥V`
  follows from the finite-level arithmetic statement `h` that for every finite Galois extension
  `M/κ` inside `K'` the relative index `[V : V ⊓ Gal(K'/M)] = [M : M ⊓ κ^{tr}]` is a `p`-power
  (cofinality of the finite levels plus the Galois correspondence);

* `NK.TameStructureDeep.Tame.relIndex_wildInertia_prime_pow`: that statement.  For `M/κ` finite
  Galois, `M ⊓ κ^{tr}` is the fixed field of the wild inertia `G_1(M/κ)` — the inclusion
  `Fix(G_1) ⊆ κ^{tr}` is `NK.TameStructureDeep.Tame.tamelyRamified_le_tameClosure`, whose
  input is the `ℓ`-divisibility of `κ^{tr*}` for `ℓ ≠ p`
  (`NK.TameStructureDeep.Tame.tameClosure_pow_surjective`), together with Kummer theory over
  the unramified part; and `[M : Fix(G_1)] = #G_1 = p^k` is the fixed-field dictionary
  (`NK.RamificationDeep.finrank_fixedField_ramificationSubgroup`) applied to the valuation ring
  of `M` produced by `NK.RamificationAdic.exists_valuationRingData`
  (`NK.RamificationDeep.isProP_ramificationSubgroup_one`).

Consequently `V_κ` is pro-`p`, which is the missing inclusion
`V_κ ≤ W_κ` (join of the normal pro-`p` subgroups) of
`NK.TameStructureDeep.Tame.wildInertiaSubgroup_eq_correctedWildInertia`.
-/

namespace NK.TameStructureDeep.Tame

open scoped Classical

theorem isProP_correctedWildInertia {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π) :
    NK.LocalTame.IsProP (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      ↥(NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)) := by
  refine isProP_fixingSubgroup_of_relIndex_prime_pow 𝔭 hπ ?_
  intro M hfd hgal
  haveI := hfd
  haveI := hgal
  exact relIndex_wildInertia_prime_pow 𝔭 hπ M

end NK.TameStructureDeep.Tame
