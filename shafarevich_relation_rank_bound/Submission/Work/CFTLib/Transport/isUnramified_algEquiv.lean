import Mathlib

/-!
# Ramification data is invariant under isomorphism of number field extensions

If `L` and `L'` are number fields that are isomorphic as `K`-algebras (`K` a number field), then
`L/K` is unramified at all finite places (its relative different ideal is the unit ideal) if and
only if `L'/K` is, and likewise for unramifiedness at the infinite places.

The proof of the finite-place statement goes through the trace-dual characterisation of the
different ideal: `𝓓(B/A) = ⊤ ↔ Bᵛ ≤ B`, where `Bᵛ` is the trace dual of the unit submodule. This
description is manifestly invariant under an isomorphism of `A`-algebras, since the trace form
`Tr_{L/K}(xy)` is preserved by a `K`-algebra isomorphism.
-/

open NumberField

namespace Work.CFTLib.Transport

section Helpers

/-- The different ideal is the whole ring iff the trace dual of the unit submodule is contained in
the unit submodule. (AKLB setting.) -/
theorem differentIdeal_eq_top_iff_traceDual_le_one
    {A K B L : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A] [IsDedekindDomain B]
    [Module.IsTorsionFree A B] [IsFractionRing B L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L] :
    differentIdeal A B = ⊤ ↔ Submodule.traceDual A K (1 : Submodule B L) ≤ 1 := by
  have h1 : differentIdeal A B = ⊤ ↔
      IsLocalization.coeSubmodule L (differentIdeal A B) = 1 := by
    refine ⟨fun h => by rw [h, IsLocalization.coeSubmodule_top], fun h => ?_⟩
    rw [eq_top_iff]
    intro b _
    have hb : algebraMap B L b ∈ IsLocalization.coeSubmodule L (differentIdeal A B) := by
      rw [h]; exact Submodule.mem_one.mpr ⟨b, rfl⟩
    obtain ⟨y, hy, hyb⟩ :=
      (IsLocalization.mem_coeSubmodule L (differentIdeal A B)).mp hb
    rw [IsFractionRing.injective B L hyb] at hy
    exact hy
  rw [h1, coeSubmodule_differentIdeal A K (L := L) B]
  constructor
  · intro h
    exact Submodule.one_le_one_div.mp h.ge
  · intro h
    refine le_antisymm ?_ (Submodule.one_le_one_div.mpr h)
    intro x hx
    have h1D : (1 : L) ∈ Submodule.traceDual A K (1 : Submodule B L) :=
      Submodule.one_le_traceDual_one (Submodule.mem_one.mpr ⟨1, by simp⟩)
    have := (Submodule.mem_div_iff_forall_mul_mem.mp hx) 1 h1D
    simpa using this

/-- Membership in the trace dual of the unit submodule. -/
lemma mem_traceDual_one_iff {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] {x : L} :
    x ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L) ↔
      ∀ b : 𝓞 L, IsIntegral (𝓞 K) (Algebra.traceForm K L x (b : L)) := by
  rw [Submodule.mem_traceDual_iff_isIntegral]
  constructor
  · intro h b; exact h _ (Submodule.mem_one.mpr ⟨b, rfl⟩)
  · intro h a ha; obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha; exact h b

/-- Membership in the unit submodule of `L` over `𝓞 L` is integrality over `𝓞 K`. -/
lemma mem_one_iff_isIntegral {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] {x : L} :
    x ∈ (1 : Submodule (𝓞 L) L) ↔ IsIntegral (𝓞 K) x := by
  rw [Submodule.mem_one]
  exact IsIntegralClosure.isIntegral_iff.symm

/-- The trace form is preserved by a `K`-algebra isomorphism (compatibly with the rings of
integers). -/
lemma traceForm_map {K L L' : Type} [Field K] [Field L] [Field L']
    [NumberField K] [NumberField L] [NumberField L'] [Algebra K L] [Algebra K L']
    (e : L ≃ₐ[K] L') (x : L) (b : 𝓞 L) :
    Algebra.traceForm K L' (e x) (NumberField.RingOfIntegers.mapAlgEquiv e b : L') =
      Algebra.traceForm K L x (b : L) := by
  rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
  rw [show ((NumberField.RingOfIntegers.mapAlgEquiv e b : L')) = e (b : L) from rfl]
  rw [← map_mul]
  exact Algebra.trace_eq_of_algEquiv e (x * (b : L))

/-- The condition `𝓞 Lᵛ ≤ 𝓞 L` is invariant under isomorphism of `K`-algebras. -/
theorem traceDualTransport {K L L' : Type} [Field K] [Field L] [Field L']
    [NumberField K] [NumberField L] [NumberField L'] [Algebra K L] [Algebra K L']
    (e : L ≃ₐ[K] L') :
    (Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L) ≤ 1) ↔
      (Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L') L') ≤ 1) := by
  rw [SetLike.le_def, SetLike.le_def]
  constructor
  · intro h x' hx'
    have key : ∀ b : 𝓞 L,
        IsIntegral (𝓞 K) (Algebra.traceForm K L (e.symm x') (b : L)) := by
      intro b
      have hb := (mem_traceDual_one_iff (K := K) (L := L')).mp hx'
        (NumberField.RingOfIntegers.mapAlgEquiv e b)
      rw [show x' = e (e.symm x') from (AlgEquiv.apply_symm_apply e x').symm,
        traceForm_map e (e.symm x') b] at hb
      exact hb
    have h2 : IsIntegral (𝓞 K) (e.symm x') :=
      (mem_one_iff_isIntegral (K := K) (L := L)).mp
        (h (x := e.symm x') ((mem_traceDual_one_iff (K := K) (L := L)).mpr key))
    rw [mem_one_iff_isIntegral (K := K) (L := L')]
    exact (isIntegral_algEquiv (e.symm.restrictScalars (𝓞 K)) (x := x')).mp h2
  · intro h x hx
    have key : ∀ b' : 𝓞 L',
        IsIntegral (𝓞 K) (Algebra.traceForm K L' (e x) (b' : L')) := by
      intro b'
      obtain ⟨b, rfl⟩ := (NumberField.RingOfIntegers.mapAlgEquiv e).surjective b'
      have hb := (mem_traceDual_one_iff (K := K) (L := L)).mp hx b
      rw [traceForm_map e x b]
      exact hb
    have h2 : IsIntegral (𝓞 K) (e x) :=
      (mem_one_iff_isIntegral (K := K) (L := L')).mp
        (h (x := e x) ((mem_traceDual_one_iff (K := K) (L := L')).mpr key))
    rw [mem_one_iff_isIntegral (K := K) (L := L)]
    exact (isIntegral_algEquiv (e.restrictScalars (𝓞 K)) (x := x)).mp h2

/-- Unramifiedness at the infinite places is invariant under isomorphism of `K`-algebras. -/
theorem unramifiedAtInfinitePlaces_algEquiv {K L L' : Type} [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L'] (e : L ≃ₐ[K] L') :
    IsUnramifiedAtInfinitePlaces K L → IsUnramifiedAtInfinitePlaces K L' := by
  intro h
  refine ⟨fun w' => ?_⟩
  -- The two places `w'` and `w'.comap e` have the same multiplicity.
  have hm : InfinitePlace.mult (w'.comap (e : L →+* L')) = InfinitePlace.mult w' := by
    have hiff : (w'.comap (e : L →+* L')).IsReal ↔ w'.IsReal :=
      InfinitePlace.isReal_comap_iff (e.toRingEquiv) (w := w')
    by_cases hw : (w'.comap (e : L →+* L')).IsReal <;> by_cases hw' : w'.IsReal
    · rw [hw.mult_eq_one, hw'.mult_eq_one]
    · exact absurd (hiff.mp hw) hw'
    · exact absurd (hiff.mpr hw') hw
    · rw [(NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw).mult_eq_two,
          (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw').mult_eq_two]
  -- `w'.comap (algebraMap K L')` is the restriction of `w'.comap e` along `K → L`.
  have h1 : (w'.comap (e : L →+* L')).comap (algebraMap K L) =
      w'.comap (algebraMap K L') := by
    rw [← InfinitePlace.comap_comp]
    congr 1
    ext x
    exact e.commutes x
  show InfinitePlace.mult (w'.comap (algebraMap K L')) = InfinitePlace.mult w'
  rw [← h1]
  exact (h.1 (w'.comap (e : L →+* L'))).trans hm

end Helpers

theorem isUnramified_algEquiv {K L L' : Type} [Field K] [Field L] [Field L'] [NumberField K]
    [NumberField L] [NumberField L'] [Algebra K L] [Algebra K L'] (e : L ≃ₐ[K] L') :
    (differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤ ∧
        IsUnramifiedAtInfinitePlaces K L) →
      (differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L') = ⊤ ∧
        IsUnramifiedAtInfinitePlaces K L') := by
  rintro ⟨hdiff, hunr⟩
  refine ⟨?_, unramifiedAtInfinitePlaces_algEquiv e hunr⟩
  have hL : Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L) ≤ 1 :=
    (differentIdeal_eq_top_iff_traceDual_le_one (A := 𝓞 K) (K := K) (B := 𝓞 L) (L := L)).mp hdiff
  rw [differentIdeal_eq_top_iff_traceDual_le_one (A := 𝓞 K) (K := K) (B := 𝓞 L') (L := L')]
  exact (traceDualTransport e).mp hL

end Work.CFTLib.Transport
