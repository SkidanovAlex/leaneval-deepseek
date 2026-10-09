import Mathlib
import Submission.NK.TameStructureDeep.Tame.TameClosure
import Submission.NK.TameStructureDeep.Tame.isGalois_tameClosure
import Submission.NK.LocalTame.Basic
import Submission.NK.TameStructureDeep.Tame.isProP_correctedWildInertia_indep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000

/-!
# The relative index `[V_κ : V_κ ⊓ Gal(K'/M)]` is a power of the residue characteristic

For a number field `K`, a finite place `𝔭`, `κ = K_𝔭`, a separable closure `K'`, a uniformiser `π`
of `κ` and the maximal tamely ramified extension `T = κ^{tr} = κ^ur(π^{1/n} : p ∤ n)`
(`NK.TameStructureDeep.Tame.tameClosure`), the *corrected wild inertia* is

  `V = V_κ = T.fixingSubgroup = Gal(K'/κ^{tr})`

(`NK.TameStructureDeep.Tame.correctedWildInertia`).  The lemma proved here is the finite level
form of `V` being pro-`p`: for every finite dimensional Galois extension `M/κ` inside `K'`,

  `[V : V ⊓ Gal(K'/M)]` is a power of `p = resCharAt 𝔭`.

Equivalently `[M : M ⊓ κ^{tr}]` is a power of `p`: the degree of `M` over its maximal tamely
ramified subextension is the order of the wild inertia `G_1(M/κ)`, a `p`-power
(`NK.RamificationDeep.isProP_ramificationSubgroup_one`, with the valuation ring supplied by
`NK.RamificationAdic.exists_valuationRingData`).

The mathematical content is entirely concentrated in the statement

> `NK.LocalTame.IsProP p ↥V`

(the wild inertia is pro-`p`), which is the classical tame structure theorem and is obtained
elsewhere.  Everything else — that the relative index occurring in the statement is finite, that
the relevant subgroup of `V` is normal, and that pro-`p`-ness of `V` transfers to it — is the
profinite bookkeeping done in this file.
-/

open scoped Classical
open IntermediateField

namespace NK.TameStructureDeep.Tame

noncomputable section

/-! ## Two bookkeeping lemmas about fixing subgroups -/

/-- **The kernel of the restriction homomorphism is the fixing subgroup.**  For an intermediate
field `L` of a Galois extension `K'/κ` which is normal over `κ`, the kernel of
`AlgEquiv.restrictNormalHom ↥L : Gal(K'/κ) →* Gal(↥L/κ)` is `L.fixingSubgroup`. -/
theorem restrictNormalHom_ker_eq_fixingSubgroup {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] (L : IntermediateField κ K') [Normal κ ↥L] :
    (AlgEquiv.restrictNormalHom (F := κ) (K₁ := K') ↥L).ker = L.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    have h2 : (((AlgEquiv.restrictNormalHom (F := κ) (K₁ := K') ↥L) σ) ⟨y, hy⟩ : ↥L) =
        ⟨y, hy⟩ := by
      rw [h]
      exact AlgEquiv.one_apply _
    have h3 := AlgEquiv.restrictNormalHom_apply (F := κ) L σ ⟨y, hy⟩
    rw [h2] at h3
    exact h3.symm
  · intro h
    have h4 : ∀ y : ↥L, (AlgEquiv.restrictNormalHom (F := κ) (K₁ := K') ↥L) σ y = y := by
      intro y
      apply Subtype.ext
      rw [AlgEquiv.restrictNormalHom_apply (F := κ) L σ y]
      exact h y y.2
    exact AlgEquiv.ext h4

/-- **The fixing subgroup of a normal intermediate field is normal.** -/
theorem fixingSubgroup_normal {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    (L : IntermediateField κ K') [Normal κ ↥L] : L.fixingSubgroup.Normal := by
  rw [← restrictNormalHom_ker_eq_fixingSubgroup L]
  infer_instance

/-! ## The relative index is finite -/

/-- **The relative index `[V_κ : V_κ ⊓ Gal(K'/M)]` is finite** for every finite dimensional Galois
`M/κ` inside `K'`.

Indeed, the restriction map `ρ : Gal(K'/κ) →* Gal(↥M/κ)` has kernel `Gal(K'/M)`, and for the
(infinite) fixing subgroup `V = Gal(K'/κ^{tr})` the relative index `Gal(K'/M).relIndex V` is the
cardinality of the image `ρ V ≤ Gal(↥M/κ)`, which is finite because `M/κ` is finite dimensional
Galois. -/
theorem relIndex_fixingSubgroup_ne_zero {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    (M : IntermediateField (𝔭.adicCompletion K) K') [FiniteDimensional (𝔭.adicCompletion K) M]
    [IsGalois (𝔭.adicCompletion K) M] :
    ((NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup ⊓
        M.fixingSubgroup).relIndex
      (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup ≠ 0 := by
  classical
  have hker : (AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K) (K₁ := K') ↥M).ker =
      M.fixingSubgroup :=
    restrictNormalHom_ker_eq_fixingSubgroup M
  have hfin : Finite ↥(Subgroup.map (AlgEquiv.restrictNormalHom (F := 𝔭.adicCompletion K)
      (K₁ := K') ↥M) ((NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K)
      (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup)) :=
    Finite.of_injective (fun x : ↥(Subgroup.map (AlgEquiv.restrictNormalHom
        (F := 𝔭.adicCompletion K) (K₁ := K') ↥M) ((NK.TameStructureDeep.Tame.tameClosure
        (κ := 𝔭.adicCompletion K) (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭)
        (π : 𝔭.adicCompletion K)).fixingSubgroup)) => (x : ↥M ≃ₐ[𝔭.adicCompletion K] ↥M))
      Subtype.val_injective
  have hmain : (M.fixingSubgroup).relIndex ((NK.TameStructureDeep.Tame.tameClosure
      (κ := 𝔭.adicCompletion K) (K' := K') (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      (π : 𝔭.adicCompletion K)).fixingSubgroup) ≠ 0 := by
    rw [← hker, Subgroup.relIndex_ker]
    exact Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, hfin⟩
  rw [inf_comm, Subgroup.inf_relIndex_right]
  exact hmain

/-! ## From `V_κ` pro-`p` to the finite level index -/

/-- **`V_κ` pro-`p` implies the finite level statement.**  If the corrected wild inertia
`V = Gal(K'/κ^{tr})` is pro-`p`, then every finite level relative index `[V : V ⊓ Gal(K'/M)]` is a
power of `p`.

This is immediate from the definition of `NK.LocalTame.IsProP` and the finiteness of the relative
index (`relIndex_fixingSubgroup_ne_zero`); it is recorded separately because the arithmetic input
(`IsProP`) is the only unproved ingredient of the main theorem. -/
theorem relIndex_wildInertia_prime_pow_of_isProP {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    (hpro : NK.LocalTame.IsProP (NK.TameStructureDeep.Tame.resCharAt 𝔭)
      ↥((NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
          (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup))
    (M : IntermediateField (𝔭.adicCompletion K) K') [FiniteDimensional (𝔭.adicCompletion K) M]
    [IsGalois (𝔭.adicCompletion K) M] :
    ∃ k : ℕ,
      ((NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
            (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup ⊓
          M.fixingSubgroup).relIndex
        (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
            (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup
        = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ k := by
  classical
  let T : IntermediateField (𝔭.adicCompletion K) K' :=
    NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)
  change ∃ k : ℕ,
    ((T.fixingSubgroup ⊓ M.fixingSubgroup).relIndex T.fixingSubgroup)
      = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ k
  have hp : (NK.TameStructureDeep.Tame.resCharAt 𝔭).Prime :=
    NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hπ0 : (π : 𝔭.adicCompletion K) ≠ 0 := by
    intro h0
    have hbot : IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) = ⊥ := by
      rw [hπ]
      exact Ideal.span_singleton_eq_bot.mpr (Subtype.ext h0)
    exact IsDiscreteValuationRing.not_isField _
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot)
  haveI : IsGalois (𝔭.adicCompletion K) ↥T :=
    NK.TameStructureDeep.Tame.isGalois_tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) hp hπ0
  haveI hVnorm : T.fixingSubgroup.Normal := fixingSubgroup_normal T
  haveI hMnorm : M.fixingSubgroup.Normal := fixingSubgroup_normal M
  have hne : ((T.fixingSubgroup ⊓ M.fixingSubgroup).relIndex T.fixingSubgroup) ≠ 0 :=
    relIndex_fixingSubgroup_ne_zero 𝔭 hπ M
  let U : Subgroup ↥(T.fixingSubgroup) :=
    (T.fixingSubgroup ⊓ M.fixingSubgroup).subgroupOf T.fixingSubgroup
  have hne' : U.index ≠ 0 := hne
  haveI : U.Normal := inferInstance
  obtain ⟨k, hk⟩ := hpro U ⟨hne'⟩
  exact ⟨k, hk⟩

theorem relIndex_wildInertia_prime_pow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    (M : IntermediateField (𝔭.adicCompletion K) K') [FiniteDimensional (𝔭.adicCompletion K) M]
    [IsGalois (𝔭.adicCompletion K) M] :
    ∃ k : ℕ,
      ((NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
            (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup ⊓
          M.fixingSubgroup).relIndex
        (NK.TameStructureDeep.Tame.tameClosure (κ := 𝔭.adicCompletion K) (K' := K')
            (NK.TameStructureDeep.Tame.resCharAt 𝔭) (π : 𝔭.adicCompletion K)).fixingSubgroup
        = (NK.TameStructureDeep.Tame.resCharAt 𝔭) ^ k :=
  relIndex_wildInertia_prime_pow_of_isProP 𝔭 hπ
    (NK.TameStructureDeep.Tame.isProP_correctedWildInertia_indep 𝔭 hπ) M

end

end NK.TameStructureDeep.Tame
