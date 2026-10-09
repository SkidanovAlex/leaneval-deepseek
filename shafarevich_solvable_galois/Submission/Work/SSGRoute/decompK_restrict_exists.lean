import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The decomposition group of a place above a place: restriction exists

Let `k ⊆ K ⊆ L` be a tower of number fields, `w` a place of `K` and `w'` a place of `L` lying over
`w`.  Then the restriction `Gal(L/k) →* Gal(K/k)`, `σ ↦ σ|_K`, maps the stabiliser
(decomposition group) of `w'` into the stabiliser of `w`.

The mathematical content is the compatibility of the action on places with restriction: the place
of `K` below `σ • w'` is `(σ|_K) • w`.  This is `NK.HassePrinciple.liesOver_smul_of_restrict`,
applied to `τ = σ : L ≃ₐ[k] L` and `A = galRes k K L σ : K ≃ₐ[k] K`, the coherence hypothesis
being `AlgEquiv.restrictNormal_commutes`.  Combined with the uniqueness of the place below a
given place (`place_liesOver_unique` below), this gives the required monoid homomorphism.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Work.SSGRoute

/-- **Unfolding `Place.LiesOver` below an archimedean place.**  A place of `K` below
`ofInfinite w` is `ofInfinite v'` for a unique infinite place `v'` of `K` below `w`. -/
theorem place_liesOver_ofInfinite_iff {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (w : NumberField.InfinitePlace L) (v : NK.GlobalCFT.Place K) :
    NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite w) v ↔
      ∃ v' : NumberField.InfinitePlace K, v = NK.GlobalCFT.Place.ofInfinite v' ∧ w.LiesOver v' := by
  constructor
  · rintro (⟨w', v', h1, h2, h3⟩ | ⟨q, Q, h1, h2, _⟩)
    · rw [NK.GlobalCFT.Place.ofInfinite_inj] at h1
      exact ⟨v', h2, h1.symm ▸ h3⟩
    · exact absurd h1 Sum.inl_ne_inr
  · rintro ⟨v', rfl, h⟩
    exact Or.inl ⟨w, v', rfl, rfl, h⟩

/-- **Unfolding `Place.LiesOver` below a nonarchimedean place.**  A place of `K` below
`ofFinite q` is `ofFinite Q` for a nonzero prime `Q` of `𝓞 K` below `q`. -/
theorem place_liesOver_ofFinite_iff {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (v : NK.GlobalCFT.Place K) :
    NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q) v ↔
      ∃ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v = NK.GlobalCFT.Place.ofFinite Q ∧ q.asIdeal.LiesOver Q.asIdeal := by
  constructor
  · rintro (⟨w', v', h1, h2, _⟩ | ⟨q', Q', h1, h2, h3⟩)
    · exact absurd h1 Sum.inr_ne_inl
    · rw [NK.GlobalCFT.Place.ofFinite_inj] at h1
      exact ⟨Q', h2, h1.symm ▸ h3⟩
  · rintro ⟨Q, rfl, h⟩
    exact Or.inr ⟨q, Q, rfl, rfl, h⟩

/-- **The place of `K` below a place of `L` is unique.** -/
theorem place_liesOver_unique {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (w' : NK.GlobalCFT.Place L) {w w₂ : NK.GlobalCFT.Place K}
    (h₁ : NK.GlobalCFT.Place.LiesOver w' w) (h₂ : NK.GlobalCFT.Place.LiesOver w' w₂) :
    w = w₂ := by
  cases w' with
  | inl w'' =>
    obtain ⟨v₁, rfl, hv₁⟩ := (place_liesOver_ofInfinite_iff w'' w).mp h₁
    obtain ⟨v₂, h₂', hv₂⟩ := (place_liesOver_ofInfinite_iff w'' w₂).mp h₂
    rw [h₂', NK.GlobalCFT.Place.ofInfinite_inj]
    haveI := hv₁
    haveI := hv₂
    exact (NumberField.InfinitePlace.LiesOver.comap_eq w'' v₁).symm.trans
      (NumberField.InfinitePlace.LiesOver.comap_eq w'' v₂)
  | inr q =>
    obtain ⟨Q₁, rfl, hQ₁⟩ := (place_liesOver_ofFinite_iff q w).mp h₁
    obtain ⟨Q₂, h₂', hQ₂⟩ := (place_liesOver_ofFinite_iff q w₂).mp h₂
    rw [h₂', NK.GlobalCFT.Place.ofFinite_inj]
    apply IsDedekindDomain.HeightOneSpectrum.ext
    haveI := hQ₁
    haveI := hQ₂
    rw [Ideal.LiesOver.over (A := NumberField.RingOfIntegers K) (P := q.asIdeal)
        (p := Q₁.asIdeal),
      Ideal.LiesOver.over (A := NumberField.RingOfIntegers K) (P := q.asIdeal)
        (p := Q₂.asIdeal)]

/-- **The restriction of `Gal(L/k)` to `Gal(K/k)` maps the decomposition group of `w'` into the
decomposition group of the place `w` below it.** -/
theorem decompK_restrict_exists (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w) :
    ∃ f : MulAction.stabilizer (L ≃ₐ[k] L) w' →*
        MulAction.stabilizer (K ≃ₐ[k] K) w,
      ∀ σ, ((f σ : MulAction.stabilizer (K ≃ₐ[k] K) w) : K ≃ₐ[k] K)
        = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L) := by
  refine ⟨MonoidHom.codRestrict
    ((SSGRoute.PTExt.galRes k K L).comp (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype)
    (MulAction.stabilizer (K ≃ₐ[k] K) w) (fun σ => ?_), fun σ => rfl⟩
  rw [MulAction.mem_stabilizer_iff]
  have hσ : (σ : L ≃ₐ[k] L) • w' = w' := MulAction.mem_stabilizer_iff.mp σ.2
  have h2 := NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := L)
    (σ : L ≃ₐ[k] L) (SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
    (fun y => AlgEquiv.restrictNormal_commutes (σ : L ≃ₐ[k] L) K y) hw'
  rw [hσ] at h2
  exact (place_liesOver_unique (w := w)
    (w₂ := SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L) • w) w' hw' h2).symm

end Work.SSGRoute
