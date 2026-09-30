import Mathlib
import Submission.Work.BW.BWGradedBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **The `hmin` hypothesis makes the cut of `p` by `r` Artinian after localising at `q`.**

Let `R` be Noetherian, `p ≤ q` primes, and assume the dimension-one condition on `q`:
every `r ∉ p` lying in `q` satisfies `q ∈ (p + (r)).minimalPrimes`. Let `r ∈ R_q` be outside the
prime `p·R_q`. Then the ring `R_q ⧸ (p·R_q + (r))` is Artinian.

Route. If `r` is not in the maximal ideal `q·R_q` then `r` is a unit of `R_q`, so
`p·R_q + (r) = ⊤` and the quotient is the zero ring. Otherwise write `r = β / t` with `β ∈ R`,
`t ∉ q`; then `r ∉ p·R_q` gives `β ∉ p` (as `p·R_q ∩ R = p`), and `r ∈ q·R_q` gives `β ∈ q` (as
`q·R_q ∩ R = q`), so `hmin` applies and `q ∈ (p + (β)).minimalPrimes`. In `R_q` this says that the
only prime containing `p·R_q + (β)` is the maximal ideal `q·R_q`, so the local ring
`(R_q) ⧸ (p·R_q + (r))` is zero-dimensional; being also Noetherian it is Artinian. Concretely the
primes of `R_q` correspond to primes of `R` contained in `q`, so a prime `Q` of `R_q` containing
`p·R_q + (β)` satisfies `Q ∩ R ⊇ p + (β)` and `Q ∩ R ⊆ q`, hence `Q ∩ R = q` by minimality, hence
`Q = q·R_q`; the localised quotient is therefore zero-dimensional. -/
theorem hmin_cut_artinian {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q)
    (hmin : ∀ r : R, r ∉ p → r ∈ q → q ∈ (p ⊔ Ideal.span {r}).minimalPrimes)
    (r : Localization.AtPrime q)
    (hr : r ∉ p.map (algebraMap R (Localization.AtPrime q))) :
    IsArtinianRing (Localization.AtPrime q ⧸
      (p.map (algebraMap R (Localization.AtPrime q)) ⊔ Ideal.span {r})) := by
  let S := Localization.AtPrime q
  let f := algebraMap R S
  -- Case 1: `r` is a unit of `S`, hence `(r) = ⊤` and the quotient is the zero ring.
  by_cases hspan : Ideal.span {r} = ⊤
  · rw [hspan, sup_top_eq]
    infer_instance
  -- Case 2: `r` lies in the maximal ideal of `S`; write `r = β / t`.
  · obtain ⟨⟨β, t⟩, hx⟩ := IsLocalization.surj q.primeCompl r
    -- `f ↑t` is a unit, so `(r) = (f β)` in `S`.
    have hu : IsUnit (f ↑t) := IsLocalization.map_units S t
    have hspanβ : Ideal.span ({f β} : Set S) = Ideal.span ({r} : Set S) := by
      have h1 : f β = f ↑t * r := by rw [mul_comm, ← hx]
      rw [h1]
      exact Ideal.span_singleton_mul_left_unit hu r
    -- Since `span {r} ≠ ⊤`, the element `r` is not a unit, hence lies in the maximal ideal.
    have hrq : r ∈ IsLocalRing.maximalIdeal S := by
      by_contra h
      have hunit : IsUnit r := by
        by_contra hnu
        exact h ((IsLocalRing.mem_maximalIdeal r).mpr hnu)
      exact hspan (Ideal.span_singleton_eq_top.mpr hunit)
    -- Hence `β = r * f t ∈ q·S`, and `β ∉ p` since otherwise `r ∈ p·S`.
    have hβq : β ∈ q := by
      have h1 : f β ∈ IsLocalRing.maximalIdeal S := by
        rw [← hx]
        exact Ideal.mul_mem_right (f ↑t) _ hrq
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S q β).mp h1
    have hβp : β ∉ p := by
      intro hβ
      refine hr ?_
      have hmem : f β ∈ p.map f := Ideal.mem_map_of_mem f hβ
      have hle : Ideal.span ({f β} : Set S) ≤ p.map f :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
      exact hle (hspanβ ▸ Ideal.mem_span_singleton_self r)
    -- `hmin` now says that `q` is a minimal prime over `p + (β)`.
    have hminβ : q ∈ (p ⊔ Ideal.span {β}).minimalPrimes := hmin β hβp hβq
    -- The extension of `p + (β)` to `S` is `p·S + (r)`.
    have hJmap : (p ⊔ Ideal.span {β}).map f = p.map f ⊔ Ideal.span {r} := by
      rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hspanβ]
    -- Minimal primes of the extension extend those of `p + (β)`, and the maximal ideal of `S`
    -- contracts to `q`.
    have hmem : IsLocalRing.maximalIdeal S ∈ (p.map f ⊔ Ideal.span {r}).minimalPrimes := by
      rw [← hJmap, IsLocalization.minimalPrimes_map q.primeCompl S (p ⊔ Ideal.span {β})]
      simp only [Set.mem_preimage]
      rw [Localization.AtPrime.under_maximalIdeal (I := q)]
      exact hminβ
    exact IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmem

end Work.BW
