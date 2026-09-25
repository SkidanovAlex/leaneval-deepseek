import Mathlib
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.TameStructureDeep.Tame.TameClosure
import Submission.NK.TameStructureDeep.Tame.mem_tameClosure_of_pow_mem_unramifiedClosure

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace NK.TameStructureDeep.Tame

/-- **A finite cyclic subextension of `M/κ` whose Kummer data is prime to `p` and unramified
lies in the maximal tamely ramified extension.**  Let `κ = K_𝔭`, `K'` a separable closure,
`p = resCharAt 𝔭`, `π` a uniformiser, `T = κ^{tr} = tameClosure p π`, and `M/κ` a finite
extension inside `K'`.  Let `F ≤ L` be intermediate fields of `M/κ` with `L/F` finite Galois
cyclic, `e = [L : F]` prime to `p`, `μ_e ⊆ F`, and `F` contained in `κ^{ur}` (all as subsets of
`K'`).  Then every element of `L` lies in `T`.

Route: Kummer theory over `F` (`Polynomial.KummerExtension.exists_root_adjoin_eq_top_of_isCyclic`)
gives `α ∈ L` with `L = F⟮α⟯` and `α ^ e ∈ F ⊆ κ^{ur}`; since `e` is prime to `p`,
`α ∈ T` by `mem_tameClosure_of_pow_mem_unramifiedClosure`, and `F ⊆ κ^{ur} ⊆ T` too, so
`L = F⟮α⟯ ⊆ T`. -/
theorem le_comap_tameClosure_of_cyclic_extendScalars {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    (M : IntermediateField (𝔭.adicCompletion K) K') [FiniteDimensional (𝔭.adicCompletion K) M]
    (F L : IntermediateField (𝔭.adicCompletion K) M) (hFL : F ≤ L)
    (hfin : FiniteDimensional ↥F ↥(IntermediateField.extendScalars hFL))
    (hgal : IsGalois ↥F ↥(IntermediateField.extendScalars hFL))
    (hcyc : IsCyclic (↥(IntermediateField.extendScalars hFL) ≃ₐ[↥F] ↥(IntermediateField.extendScalars hFL)))
    (hμ : (primitiveRoots (Module.finrank ↥F ↥(IntermediateField.extendScalars hFL)) ↥F).Nonempty)
    (hnp : ¬ (NK.TameStructureDeep.Tame.resCharAt 𝔭) ∣
      Module.finrank ↥F ↥(IntermediateField.extendScalars hFL))
    (hFU : ∀ y : ↥F, ((y : M) : K') ∈
      NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K')
        (NK.TameStructureDeep.Tame.resCharAt 𝔭)) :
    L ≤ IntermediateField.comap M.val (NK.TameStructureDeep.Tame.tameClosure
      (κ := 𝔭.adicCompletion K) (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      (π : 𝔭.adicCompletion K)) := by
  classical
  -- `L` viewed over the smaller base field `F`
  let E : IntermediateField ↥F M := IntermediateField.extendScalars hFL
  haveI : FiniteDimensional ↥F ↥E := hfin
  haveI : IsGalois ↥F ↥E := hgal
  haveI : IsCyclic (↥E ≃ₐ[↥F] ↥E) := hcyc
  -- Kummer theory over `F`: `E = F⟮α⟯` with `α ^ e ∈ F`
  obtain ⟨α, hαpow, hαtop⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic (K := ↥F) (L := ↥E) hμ
  obtain ⟨a, ha⟩ := hαpow
  have hfpos : 0 < Module.finrank ↥F ↥E := Module.finrank_pos
  -- the tame and unramified closures inside `K'`
  let T : IntermediateField (𝔭.adicCompletion K) K' :=
    tameClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) (π : 𝔭.adicCompletion K)
  let U : IntermediateField (𝔭.adicCompletion K) K' :=
    NK.LocalAnabelian.unramifiedClosure (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
  have hUT : U ≤ T := unramifiedClosure_le_tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) (π : 𝔭.adicCompletion K)
  -- `α` is tame, because its `e`-th power is unramified and `e` is prime to `p`
  have hαT : ((α : M) : K') ∈ T := by
    have haM : (a : M) = (α : M) ^ (Module.finrank ↥F ↥E) := by
      have h := congrArg (fun z : ↥E => (z : M)) ha
      simpa using h
    have haU : ((a : M) : K') ∈ U := hFU a
    refine mem_tameClosure_of_pow_mem_unramifiedClosure 𝔭 hπ hfpos hnp ?_
    change (M.val (α : M)) ^ (Module.finrank ↥F ↥E) ∈ U
    rw [← map_pow M.val (α : M) (Module.finrank ↥F ↥E), ← haM]
    exact haU
  -- `F` is unramified, hence also tame
  have hF_ur : F ≤ IntermediateField.comap M.val U := fun x hx => hFU ⟨x, hx⟩
  have hFS : F ≤ IntermediateField.comap M.val T := fun x hx => hUT (hF_ur hx)
  -- the subfield of `E` cut out by `T`: it contains `F` and `α`, hence all of `E`
  let S : IntermediateField ↥F M := IntermediateField.extendScalars hFS
  let L₀ : IntermediateField ↥F ↥E := IntermediateField.comap (IntermediateField.val E) S
  have hαL : α ∈ L₀ := hαT
  have htop : (⊤ : IntermediateField ↥F ↥E) ≤ L₀ := by
    rw [← hαtop]
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hαL)
  intro x hx
  have hxE : x ∈ (E : Set M) := hx
  have hy : (⟨x, hxE⟩ : ↥E) ∈ L₀ := htop trivial
  have h1 : ((⟨x, hxE⟩ : ↥E) : M) ∈ IntermediateField.comap M.val T := hy
  simpa using h1

end NK.TameStructureDeep.Tame
