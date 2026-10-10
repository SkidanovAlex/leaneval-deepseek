import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of the inertia predicate `IsInertiaAt` along a `K`-algebra isomorphism

`SSGRoute.PTExt.IsInertiaAt (k := k) q σ` says that `σ ∈ Gal(L/k)` acts trivially on the residue
field at the finite place `q`, i.e. that it fixes `(𝓞 L)/q`.  If `e : A ≃ₐ[K] B` is an isomorphism
of number fields over `K` and `q'` is the prime of `B` obtained from the prime `q` of `A` by
transporting along `e` (`q'.asIdeal = q.asIdeal.map e`), then an automorphism `σ` of `B/k` lies in
the inertia group at `q'` if and only if its transport `(autCongr (e|_k)).symm σ = e⁻¹ σ e` lies in
the inertia group at `q`.

The proof is a transport along the induced isomorphism
`𝓞 A ≃ₐ[𝓞 K] 𝓞 B` of rings of integers: `IsInertiaAt q' σ` unfolds to "`q'.valuation B` of
`σ y - y` is `< 1` for all `y ∈ 𝓞 B`", and `v.valuation L x < 1 ↔ x ∈ v.asIdeal` for `x` in the ring
of integers; the ideal membership is then transported by `Ideal.mem_map_iff_of_surjective`.
-/

namespace Work.SSGRoute.Sha2Lib

open NumberField

/-- The value of `NumberField.RingOfIntegers.mapAlgEquiv e` on a ring of integers is the value of
`e` on the underlying field element. -/
lemma mapAlgEquiv_ringOfIntegers_coe {k K L E : Type} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [EquivLike E K L] [AlgEquivClass E k K L] (e : E)
    (x : NumberField.RingOfIntegers K) :
    ((NumberField.RingOfIntegers.mapAlgEquiv e x : NumberField.RingOfIntegers L) : L)
      = e (x : K) := rfl

theorem isInertiaAt_map_algEquiv {k K A B : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field A] [NumberField A] [Field B] [NumberField B]
    [Algebra k K] [Algebra K A] [Algebra K B] [Algebra k A] [Algebra k B]
    [IsScalarTower k K A] [IsScalarTower k K B]
    (e : A ≃ₐ[K] B) (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers A))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers B))
    (hq' : q'.asIdeal = q.asIdeal.map (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv)
    (σ : B ≃ₐ[k] B) :
    SSGRoute.PTExt.IsInertiaAt (k := k) q' σ ↔
      SSGRoute.PTExt.IsInertiaAt (k := k) q
        ((AlgEquiv.autCongr (e.restrictScalars k)).symm σ) := by
  -- `E` is the induced isomorphism of rings of integers, `φ` and `τ` are `e` and its
  -- conjugate `(autCongr φ).symm σ = φ⁻¹ σ φ` on the field level, and `S`, `T` their
  -- restrictions to the rings of integers.
  let E : 𝓞 A ≃ₐ[𝓞 K] 𝓞 B := NumberField.RingOfIntegers.mapAlgEquiv e
  let φ : A ≃ₐ[k] B := e.restrictScalars k
  let τ : A ≃ₐ[k] A := (AlgEquiv.autCongr φ).symm σ
  let S : 𝓞 B ≃ₐ[𝓞 k] 𝓞 B := NumberField.RingOfIntegers.mapAlgEquiv σ
  let T : 𝓞 A ≃ₐ[𝓞 k] 𝓞 A := NumberField.RingOfIntegers.mapAlgEquiv τ
  -- `e ∘ τ = σ ∘ e` by definition of `τ = e⁻¹ σ e`.
  have hconj : ∀ a : A, e (τ a) = σ (e a) := by
    intro a
    have h1 : (AlgEquiv.autCongr φ) τ = σ := MulEquiv.apply_symm_apply _ _
    have h2 := congrFun (congrArg DFunLike.coe h1) (φ a)
    have h3 : φ (τ a) = σ (φ a) := by
      rw [← h2, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
        AlgEquiv.symm_apply_apply]
    exact h3
  -- Consequently `E (T x) = S (E x)` on the rings of integers.
  have hT : ∀ x : 𝓞 A, E (T x) = S (E x) := by
    intro x
    show NumberField.RingOfIntegers.mapAlgEquiv e (NumberField.RingOfIntegers.mapAlgEquiv τ x)
      = NumberField.RingOfIntegers.mapAlgEquiv σ (NumberField.RingOfIntegers.mapAlgEquiv e x)
    apply NumberField.RingOfIntegers.ext
    simp only [mapAlgEquiv_ringOfIntegers_coe]
    exact hconj (x : A)
  -- Transport of membership in the prime ideal along `E`.
  have hmem : ∀ a : 𝓞 A, E a ∈ q'.asIdeal ↔ a ∈ q.asIdeal := by
    intro a
    have h1 : q'.asIdeal = q.asIdeal.map (E : 𝓞 A →+* 𝓞 B) := hq'
    rw [h1, Ideal.mem_map_iff_of_surjective (E : 𝓞 A →+* 𝓞 B) E.surjective]
    constructor
    · rintro ⟨b, hb, hbE⟩
      have hba : b = a := E.injective hbE
      rw [← hba]
      exact hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  -- The coherence of the coercion to the field.
  have hcoeS : ∀ y : 𝓞 B, ((S y - y : 𝓞 B) : B) = σ (y : B) - (y : B) := by
    intro y
    simp only [S, map_sub, mapAlgEquiv_ringOfIntegers_coe]
  have hcoeT : ∀ x : 𝓞 A, ((T x - x : 𝓞 A) : A) = τ (x : A) - (x : A) := by
    intro x
    simp only [T, map_sub, mapAlgEquiv_ringOfIntegers_coe]
  -- Rewriting `IsInertiaAt` as membership of `S y - y (resp. T x - x)` in the prime.
  have hA : SSGRoute.PTExt.IsInertiaAt (k := k) q' σ ↔ ∀ y : 𝓞 B, S y - y ∈ q'.asIdeal := by
    constructor
    · intro h y
      have hy := h y
      rw [← hcoeS y] at hy
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := B) q' (S y - y)).mp hy
    · intro h y
      rw [← hcoeS y]
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := B) q' (S y - y)).mpr (h y)
  have hB : SSGRoute.PTExt.IsInertiaAt (k := k) q τ ↔ ∀ x : 𝓞 A, T x - x ∈ q.asIdeal := by
    constructor
    · intro h x
      have hx := h x
      rw [← hcoeT x] at hx
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := A) q (T x - x)).mp hx
    · intro h x
      rw [← hcoeT x]
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := A) q (T x - x)).mpr (h x)
  -- The two membership conditions are exchanged by `E`.
  have hmain : (∀ y : 𝓞 B, S y - y ∈ q'.asIdeal) ↔ (∀ x : 𝓞 A, T x - x ∈ q.asIdeal) := by
    constructor
    · intro h x
      have h1 : S (E x) - E x ∈ q'.asIdeal := h (E x)
      rw [← hT x, ← map_sub] at h1
      exact (hmem (T x - x)).mp h1
    · intro h y
      have h1 : T (E.symm y) - E.symm y ∈ q.asIdeal := h (E.symm y)
      have h2 : E (T (E.symm y) - E.symm y) ∈ q'.asIdeal := (hmem _).mpr h1
      rw [map_sub, hT (E.symm y), E.apply_symm_apply] at h2
      exact h2
  change SSGRoute.PTExt.IsInertiaAt (k := k) q' σ ↔ SSGRoute.PTExt.IsInertiaAt (k := k) q τ
  rw [hA, hB]
  exact hmain

end Work.SSGRoute.Sha2Lib
