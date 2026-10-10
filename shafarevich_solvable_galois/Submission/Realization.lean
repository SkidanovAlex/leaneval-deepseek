import Mathlib.FieldTheory.Galois.Basic

namespace Submission

open scoped Classical

/-- `RealizableOver k G` means: there is a finite Galois extension `K/k` whose Galois
group is isomorphic to `G`. -/
def RealizableOver (k : Type*) [Field k] (G : Type*) [Group G] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K) (_ : IsGalois k K),
    Nonempty (G ≃* (K ≃ₐ[k] K))

/-- Realizability is invariant under group isomorphism. -/
theorem RealizableOver.of_mulEquiv {k : Type*} [Field k] {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : RealizableOver k G) : RealizableOver k H := by
  obtain ⟨K, hF, hA, hFD, hG, ⟨f⟩⟩ := h
  exact ⟨K, hF, hA, hFD, hG, ⟨e.symm.trans f⟩⟩

/-- A quotient of a realizable group is realizable. -/
theorem RealizableOver.of_surjective {k : Type*} [Field k] {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (h : RealizableOver k G) :
    RealizableOver k H := by
  obtain ⟨K, hKf, hKa, hKfd, hKg, ⟨e⟩⟩ := h
  letI : Algebra k K := hKa
  letI : FiniteDimensional k K := hKfd
  letI : IsGalois k K := hKg
  -- the kernel of `f`, transported to `Gal(K/k)`
  let N : Subgroup (K ≃ₐ[k] K) := f.ker.map e.toMonoidHom
  haveI hN : N.Normal := f.normal_ker.map e.toMonoidHom e.surjective
  let K' : IntermediateField k K := IntermediateField.fixedField N
  haveI : FiniteDimensional k ↥K' := IntermediateField.finiteDimensional_left K'
  haveI : IsGalois k ↥K' := IsGalois.of_fixedField_normal_subgroup N
  refine ⟨↥K', inferInstance, inferInstance, inferInstance, inferInstance, ⟨?iso⟩⟩
  have h1 : H ≃* G ⧸ f.ker := (QuotientGroup.quotientKerEquivOfSurjective f hf).symm
  have h2 : G ⧸ f.ker ≃* (K ≃ₐ[k] K) ⧸ N :=
    QuotientGroup.congr f.ker N e (by simp [N])
  have h3 : (K ≃ₐ[k] K) ⧸ N ≃* (↥K' ≃ₐ[k] ↥K') :=
    IsGalois.normalAutEquivQuotient N
  exact h1.trans (h2.trans h3)

end Submission
