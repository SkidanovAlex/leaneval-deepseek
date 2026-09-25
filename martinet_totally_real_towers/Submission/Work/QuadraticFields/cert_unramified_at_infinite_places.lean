import Mathlib
import Submission.Work.QuadraticFields.GenusCertificate
import Submission.Work.QuadraticFields.WideNarrow

/-!
# The genus certificate `M/F` is unramified at the infinite places

The base field `F = ℚ(√-3556995)` of the genus certificate is an *imaginary* quadratic field: its
generator `y = ∏ a ∈ certPrimes, certRoot a` satisfies `y ^ 2 = -3556995 < 0`.  Hence `F` has no
real infinite place at all (a real embedding would produce a real square root of a negative
rational number), so any extension of `F` -- in particular `M/F` -- is unramified at the infinite
places.

## Main results

* `Work.QuadraticFields.nrRealPlaces_eq_zero_of_sq_eq_neg` -- a number field containing a square
  root of a negative rational has no real place.
* `Work.QuadraticFields.cert_unramified_at_infinite_places` -- `M/F` is unramified at infinity.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

noncomputable section

open NumberField

/-- **A number field whose element `y` squares to a negative rational has no real infinite
place.**  Indeed, if `w` were a real place with embedding `f : F →+* ℝ`, then
`f y ^ 2 = f (y ^ 2) = (a : ℝ) < 0`, contradicting `f y ^ 2 ≥ 0`. -/
theorem nrRealPlaces_eq_zero_of_sq_eq_neg {F : Type*} [Field F] [NumberField F] [Algebra ℚ F]
    (a : ℚ) (ha : a < 0) (y : F) (hy : y ^ 2 = (a : F)) :
    NumberField.InfinitePlace.nrRealPlaces F = 0 := by
  rw [NumberField.nrRealPlaces_eq_zero_iff]
  refine ⟨fun w => ?_⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  let f : F →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal hw
  have h1 : f (y ^ 2) = (a : ℝ) := by rw [hy, map_ratCast]
  rw [map_pow] at h1
  have h2 : (0 : ℝ) ≤ (f y) ^ 2 := sq_nonneg _
  have h3 : (a : ℝ) < 0 := by exact_mod_cast ha
  linarith

/-- **`M/F` is unramified at the infinite places.**  The base field `F = ℚ(√-3556995)` is
imaginary quadratic -- its generator squares to the negative rational `-3556995` -- so it has no
real place, and no place of `M` can ramify over a real place of `F`. -/
theorem cert_unramified_at_infinite_places : IsUnramifiedAtInfinitePlaces ↥certF certM := by
  have hmem : (∏ a ∈ certPrimes, certRoot a) ∈ (certF : Set certM) := by
    rw [certF, prodSubfield]
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
  have hprod : (∏ a ∈ certPrimes, certRoot a) ^ 2 = algebraMap ℚ certM (-3556995 : ℚ) := by
    rw [← Finset.prod_pow]
    rw [Finset.prod_congr rfl (fun a ha => certRoot_sq a ha)]
    rw [← map_prod]
    congr 1
    exact_mod_cast certPrimes_prod
  have hy : (⟨∏ a ∈ certPrimes, certRoot a, hmem⟩ : ↥certF) ^ 2
      = ((-3556995 : ℚ) : ↥certF) := by
    apply Subtype.ext
    change (∏ a ∈ certPrimes, certRoot a) ^ 2 = algebraMap ℚ certM (-3556995 : ℚ)
    exact hprod
  have h0 : NumberField.InfinitePlace.nrRealPlaces ↥certF = 0 :=
    nrRealPlaces_eq_zero_of_sq_eq_neg (-3556995) (by norm_num) _ hy
  exact isUnramifiedAtInfinitePlaces_of_nrRealPlaces_eq_zero (F := ↥certF) (M := certM) h0

end

end Work.QuadraticFields
