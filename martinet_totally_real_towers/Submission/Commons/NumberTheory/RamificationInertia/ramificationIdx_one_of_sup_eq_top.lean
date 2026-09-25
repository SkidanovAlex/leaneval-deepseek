import Mathlib.Order.CompletePartialOrder
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.RamificationInertia.inertia_map_restrictNormalHom_le

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.RamificationInertia

open NumberField in
/-- **Unramifiedness is preserved by composita (finite primes).**

Let `X/F` be a finite Galois extension of number fields and let `L M : IntermediateField F X` be
finite-dimensional Galois intermediate fields with `L ⊔ M = ⊤`.  If every prime of `𝓞 L` and of
`𝓞 M` lying over a prime `𝔭` of `𝓞 F` has ramification index `1`, then so does every prime `𝔓` of
`𝓞 X` lying over `𝔭`.

Proof: let `I := Ideal.inertia Gal(X/F) 𝔓`.  By
`Commons.NumberTheory.RamificationInertia.inertia_map_restrictNormalHom_le` the restriction of `I`
to `L` lies in the inertia group of `𝔓.under (𝓞 L)`, which is trivial by
`Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one`; likewise
for `M`.  Hence `I ≤ ker(restriction to L) ⊓ ker(restriction to M) = ⊥` because a
`Gal(X/F)`-automorphism fixing both `L` and `M` fixes `L ⊔ M = ⊤`
(`IntermediateField.fixingSubgroup_sup`, `IntermediateField.fixingSubgroup_top`,
`IntermediateField.restrictNormalHom_ker`).  Finally
`Ideal.inertia_eq_bot_iff_ramificationIdx_eq_one` converts `I = ⊥` into the ramification index
statement. -/
theorem ramificationIdx_one_of_sup_eq_top {F X : Type*} [Field F] [Field X] [Algebra F X]
    [NumberField F] [NumberField X] [FiniteDimensional F X] [IsGalois F X]
    (L M : IntermediateField F X) [FiniteDimensional F ↥L] [FiniteDimensional F ↥M]
    [IsGalois F ↥L] [IsGalois F ↥M] (hsup : L ⊔ M = ⊤)
    (𝔭 : Ideal (RingOfIntegers F)) (h𝔭 : 𝔭.IsPrime) (h𝔭ne : 𝔭 ≠ ⊥)
    (𝔓 : Ideal (RingOfIntegers X)) [𝔓.IsPrime] [𝔓.LiesOver 𝔭]
    (hL : ∀ 𝔓L : Ideal (RingOfIntegers ↥L), 𝔓L ∈ 𝔭.primesOver (RingOfIntegers ↥L) →
      𝔓L.ramificationIdx (RingOfIntegers F) = 1)
    (hM : ∀ 𝔓M : Ideal (RingOfIntegers ↥M), 𝔓M ∈ 𝔭.primesOver (RingOfIntegers ↥M) →
      𝔓M.ramificationIdx (RingOfIntegers F) = 1) :
    𝔓.ramificationIdx (RingOfIntegers F) = 1 := by
  haveI : 𝔭.IsPrime := h𝔭
  -- Generic step: for any intermediate field `N` in which every prime over `𝔭` is unramified,
  -- the inertia group of `𝔓` is contained in `ker (restrict NormalHom N)`.
  have key : ∀ (N : IntermediateField F X) [FiniteDimensional F ↥N] [IsGalois F ↥N]
      (hN : ∀ 𝔓N : Ideal (RingOfIntegers ↥N), 𝔓N ∈ 𝔭.primesOver (RingOfIntegers ↥N) →
        𝔓N.ramificationIdx (RingOfIntegers F) = 1),
      Ideal.inertia (X ≃ₐ[F] X) 𝔓 ≤ N.fixingSubgroup := by
    intro N _ _ hN σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    -- The prime of `𝓞 N` below `𝔓`.
    set 𝔓N : Ideal (RingOfIntegers ↥N) := 𝔓.under (RingOfIntegers ↥N) with h𝔓N
    haveI : 𝔓N.IsPrime := by rw [h𝔓N]; infer_instance
    haveI : 𝔓N.LiesOver 𝔭 := by
      rw [h𝔓N]
      exact Ideal.LiesOver.tower_bot (𝔓 := 𝔓) (P := 𝔓.under (RingOfIntegers ↥N)) (p := 𝔭)
    -- It is unramified over `𝔭`, by hypothesis.
    have hramN : 𝔓N.ramificationIdx (RingOfIntegers F) = 1 :=
      hN 𝔓N ⟨inferInstance, inferInstance⟩
    have hbotN : Ideal.inertia (↥N ≃ₐ[F] ↥N) 𝔓N = ⊥ :=
      (inertia_eq_bot_iff_ramificationIdx_eq_one 𝔭 𝔓N).mpr hramN
    -- Restricting `σ` to `N` lands in that trivial inertia group.
    have hle := inertia_map_restrictNormalHom_le (F := F) (L := ↥N) (M := X) 𝔭 𝔓N 𝔓
    have hmem : (AlgEquiv.restrictNormalHom (F := F) (K₁ := X) (E := ↥N)) σ ∈
        Ideal.inertia (↥N ≃ₐ[F] ↥N) 𝔓N := hle ⟨σ, hσ, rfl⟩
    rw [hbotN] at hmem
    have hone : (AlgEquiv.restrictNormalHom (F := F) (K₁ := X) (E := ↥N)) σ = 1 := hmem
    have h2 : σ.restrictNormal N = 1 := by
      simpa [AlgEquiv.restrictNormalHom] using hone
    exact (AlgEquiv.restrictNormal_eq_one_iff N σ).mp h2 x hx
  -- Hence the inertia group is contained in the intersection of the two kernels, which is
  -- the fixing subgroup of `L ⊔ M = ⊤`, i.e. trivial.
  have hbot : Ideal.inertia (X ≃ₐ[F] X) 𝔓 ≤ ⊥ := by
    intro σ hσ
    have h1 : σ ∈ L.fixingSubgroup := key L hL hσ
    have h2 : σ ∈ M.fixingSubgroup := key M hM hσ
    have h3 : σ ∈ (L ⊔ M).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨h1, h2⟩
    rw [hsup, IntermediateField.fixingSubgroup_top] at h3
    exact h3
  exact (inertia_eq_bot_iff_ramificationIdx_eq_one 𝔭 𝔓).mp (le_bot_iff.mp hbot)

end Commons.NumberTheory.RamificationInertia