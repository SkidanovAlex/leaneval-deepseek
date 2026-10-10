import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.TameStructureDeep.Support.isProCyclic_quotientImage_iff
import Submission.NK.TameStructureDeep.Tame.exists_root_primeToPart
import Submission.NK.TameStructureDeep.Tame.isProCyclic_quotient_of_forall_isCyclic_powSpan
import Submission.NK.TameStructureDeep.Tame.powSpanCyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

/-!
# The tame inertia `I_κ/V_κ` for the *corrected* wild inertia is pro-cyclic

`NK.LocalTame.IsProCyclic ↥(quotientImage V_κ I_κ)` where `V_κ = Gal(K'/κ^{tr})`
(`NK.TameStructureDeep.Tame.correctedWildInertia`) is the fixing subgroup of the maximal tamely
ramified extension `κ^{tr} = κ^{ur}(π^{1/n} : p ∤ n)` and `I_κ = Gal(K'/κ^{ur})`.

The group `↥(quotientImage V_κ I_κ)` is `I_κ/V_κ = Gal(κ^{tr}/κ^{ur})`, and the classical
computation is `Gal(κ^{tr}/κ^{ur}) ≅ lim_n μ_n = ∏_{ℓ ≠ p} ℤ_ℓ`, which is pro-cyclic.  The
arithmetic input is the *proved* Kummer statement `UnramifiedNoPow` (a uniformiser of `κ = K_𝔭`
has no `n`-th root in `κ^{ur}` for `p ∤ n`, `n ≥ 2`), together with the layer computation proved
in `Tame/powSpanCyclic.lean`: for `γ^{d₀} = π` with `d₀ = primeToPart 𝔭 m` the largest divisor of
`m` prime to `p`,

* the subgroup `V_κ ⊔ ⟨σ ^ m : σ ∈ I_κ⟩` is closed — it is the image of the compact set
  `V_κ × I_κ` under `(v, σ) ↦ v σ ^ m`, and equals the set of products `v * σ ^ m`;
* hence, by the infinite Galois correspondence, its fixing subgroup is exactly
  `L.fixingSubgroup` for the layer `L = κ^{ur} ⊔ κ⟮γ⟯` (`mem_adjoin_root_of_fixed` gives the hard
  inclusion);
* the Kummer pairing `σ ↦ σ γ / γ` therefore identifies `I_κ/(V_κ ⊔ ⟨σ^m⟩)` with a subgroup of the
  cyclic group `μ_{d₀}`, so that quotient is cyclic;
* the group-theoretic criterion `isProCyclic_quotient_of_forall_isCyclic_powSpan` then gives the
  pro-cyclicity of `I_κ/V_κ`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

theorem isProCyclic_correctedWildInertia {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    [hV : (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) π).Normal] :
    NK.LocalTame.IsProCyclic
      ↥(NK.LocalTame.quotientImage
        (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) π)
        (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭))) := by
  classical
  -- rewrite the inertia subgroup as the fixing subgroup of `κ^{ur}`
  rw [NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
    (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭)]
  refine (NK.TameStructureDeep.Support.isProCyclic_quotientImage_iff).mpr ?_
  refine isProCyclic_quotient_of_forall_isCyclic_powSpan
    (NK.TameStructureDeep.Tame.correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) π)
    (NK.TameStructureDeep.Tame.Isub 𝔭 K') ?_
  intro m hm
  obtain ⟨γ, hγ, hγtr⟩ := exists_root_primeToPart (K' := K') 𝔭 (π := π) hm hπ
  exact isCyclic_quotient_normalClosure 𝔭 K' hm hπ
    (hVn := Vsub_normal 𝔭 K' hπ) (hP := powSpanSub_normal 𝔭 K' hπ m) γ hγ hγtr

end NK.TameStructureDeep.Tame
