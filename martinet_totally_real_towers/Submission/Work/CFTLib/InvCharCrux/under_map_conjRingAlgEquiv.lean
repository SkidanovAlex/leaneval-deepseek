import Mathlib
import Submission.Work.CFTLib.InvCharCrux.ConjField

open NumberField

namespace Work.CFTLib.InvCharCrux

/-- **Coercion of a scalar from an intermediate field.**  For `M` an intermediate field of
`K' / K` and `x : K`, the element `algebraMap K ↥M x` of `↥M`, viewed in `K'`, is
`algebraMap K K' x`.  This is `rfl`, but stating it as a lemma keeps the coercion bookkeeping
out of later proofs. -/
lemma coe_algebraMap_intermediateField {K K' : Type} [Field K] [Field K'] [Algebra K K']
    (M : IntermediateField K K') (x : K) :
    ((algebraMap K ↥M x : ↥M) : K') = algebraMap K K' x := rfl

/-- **Contraction of a prime along the ring isomorphism of the conjugate field.**

Let `M : IntermediateField K K'` and `g : K' ≃ₐ[F] K'`, and let
`Work.CFTLib.InvCharCrux.conjField g M` be the conjugate `K`-subfield (the image `g(M)`, which is
a `K`-subfield since `g(K) = K`; see the module
`Submission.Work.CFTLib.InvCharCrux.ConjField`).  Let `φ = Work.CFTLib.InvCharCrux.conjRingAlgEquiv
g M : 𝓞 ↥M ≃ₐ[𝓞 F] 𝓞 ↥(conjField g M)` be the induced isomorphism of rings of integers, and
`e = (RingOfIntegers.mapAlgEquiv (g.restrictNormal K)).toRingEquiv` the ring equivalence of `𝓞 K`
induced by the restriction `ḡ = g.restrictNormal K` of `g` to `K`.

Since `φ` extends the action of `g`, whose restriction to `𝓞 K` is `e`, the contraction of the
image `P.map φ` of a prime `P` of `𝓞 ↥M` is the image of the contraction of `P` under `e`.

Element-wise: for `x ∈ 𝓞 K`,
`x ∈ (P.map φ).under (𝓞 K) ↔ φ⁻¹ x ∈ P ↔ ḡ⁻¹ x ∈ P ↔ x ∈ e (P.under (𝓞 K))`. -/
theorem under_map_conjRingAlgEquiv {F K K' : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Field K'] [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K']
    [IsScalarTower F K K'] [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K]
    [IsGalois F K'] (g : K' ≃ₐ[F] K') (M : IntermediateField K K') [FiniteDimensional K M]
    [IsGalois K M] (P : Ideal (NumberField.RingOfIntegers ↥M)) [P.IsPrime] :
    ((P.map (Work.CFTLib.InvCharCrux.conjRingAlgEquiv g M).toRingHom).under
        (NumberField.RingOfIntegers K))
      = (P.under (NumberField.RingOfIntegers K)).map
          ((NumberField.RingOfIntegers.mapAlgEquiv
            (g.restrictNormal K)).toRingEquiv) := by
  have hsurj : Function.Surjective (conjRingAlgEquiv g M).toRingHom :=
    fun y => ⟨(conjRingAlgEquiv g M).symm y, by simp⟩
  have hesurj : Function.Surjective
      (((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K))).toRingEquiv) :=
    fun y => ⟨((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K))).toRingEquiv.symm y,
      by simp⟩
  -- The isomorphism `φ` on rings of integers extends the action of `g` on `𝓞 K`.
  have hkey : ∀ y : 𝓞 K, (conjRingAlgEquiv g M) (algebraMap (𝓞 K) (𝓞 ↥M) y)
      = algebraMap (𝓞 K) (𝓞 ↥(conjField g M))
          ((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K)) y) := by
    intro y
    apply RingOfIntegers.ext
    apply Subtype.ext
    rw [conjRingAlgEquiv_apply]
    simp only [RingHom.algebraMap_toAlgebra, RingOfIntegers.mapRingHom_apply]
    have hm : (((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K)) y : 𝓞 K) : K)
        = (g.restrictNormal K) (y : K) := rfl
    rw [hm, coe_algebraMap_intermediateField M (y : K),
      coe_algebraMap_intermediateField (conjField g M) ((g.restrictNormal K) (y : K))]
    rw [AlgEquiv.restrictNormal_commutes g K (y : K)]
  ext x
  rw [Ideal.mem_under]
  constructor
  · -- `algebraMap x ∈ P.map φ` gives `φ⁻¹ (algebraMap x) = algebraMap (e⁻¹ x)` in `P`.
    intro hx
    obtain ⟨p, hp, hpx⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hx
    have h1 : (conjRingAlgEquiv g M) (algebraMap (𝓞 K) (𝓞 ↥M)
        (((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K))).toRingEquiv.symm x))
        = algebraMap (𝓞 K) (𝓞 ↥(conjField g M)) x := by
      have h := hkey
        (((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K))).toRingEquiv.symm x)
      rwa [show ((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K))
            (((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K))).toRingEquiv.symm x)) = x
          from by simp] at h
    have hp2 : p = algebraMap (𝓞 K) (𝓞 ↥M)
        (((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K))).toRingEquiv.symm x) :=
      (conjRingAlgEquiv g M).injective (hpx.trans h1.symm)
    rw [hp2] at hp
    have hmem : (((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K))).toRingEquiv.symm x)
        ∈ P.under (𝓞 K) := by
      rw [Ideal.mem_under]
      exact hp
    simpa using Ideal.mem_map_of_mem
      (((NumberField.RingOfIntegers.mapAlgEquiv (g.restrictNormal K))).toRingEquiv) hmem
  · -- conversely `x = e y` with `algebraMap y ∈ P` gives `algebraMap x = φ (algebraMap y)`.
    intro hx
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective _ hesurj).mp hx
    rw [Ideal.mem_under] at hy
    have h3 : algebraMap (𝓞 K) (𝓞 ↥(conjField g M)) x
        = (conjRingAlgEquiv g M) (algebraMap (𝓞 K) (𝓞 ↥M) y) := by
      rw [← hyx]
      exact (hkey y).symm
    rw [h3]
    exact Ideal.mem_map_of_mem (conjRingAlgEquiv g M).toRingHom hy

end Work.CFTLib.InvCharCrux
