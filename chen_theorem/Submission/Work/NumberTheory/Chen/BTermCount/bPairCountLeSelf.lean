import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# `bPairCount Y N ≤ N`

`bPairCount Y N` counts the pairs `(q₂, q₃)` of primes `≥ Y` with `q₂ ≤ q₃` and
`q₂ q₃ ≤ N`.  Because the product of two primes `q₂ ≤ q₃` determines the pair
(the smaller prime is the smallest prime factor of the product, and unique
factorisation then fixes the other), the product map is injective on this pair
set, whose image is contained in `{1, …, N}`.  Hence `bPairCount Y N ≤ N`.

This is the crude `Σ_v ‖bCoeff Y v‖² ≤ N` estimate used to normalise the
`b`-side of the B-term bilinear large sieve.
-/

/-- The product map `(a, b) ↦ a * b` is injective on `bPairSet Y N`: if
`a ≤ b` and `c ≤ d` are primes with `a b = c d`, then `a = c` and `b = d`. -/
theorem injOn_mul_bPairSet (Y N : ℕ) :
    Set.InjOn (fun t : ℕ × ℕ => t.1 * t.2) ↑(bPairSet Y N) := by
  rintro ⟨a, b⟩ ht ⟨c, d⟩ hs h
  change a * b = c * d at h
  simp only [bPairSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, Prod.mk.injEq] at ht hs ⊢
  obtain ⟨⟨-, -⟩, ha, hb, hab, -⟩ := ht
  obtain ⟨⟨-, -⟩, hc, hd, hcd, -⟩ := hs
  have ha1 : a ≠ 1 := ha.ne_one
  have hdvd : a ∣ c * d := ⟨b, h.symm⟩
  rcases (ha.dvd_mul).mp hdvd with hca | hda
  · -- `a ∣ c`, so `a = c`, and cancelling gives `b = d`.
    have hca' : c = a := (hc.dvd_iff_eq ha1).mp hca
    rw [hca'] at h
    exact ⟨hca'.symm, mul_left_cancel₀ ha.ne_zero h⟩
  · -- `a ∣ d`, so `a = d`; cancelling gives `b = c`, and the orderings force everything equal.
    have hda' : d = a := (hd.dvd_iff_eq ha1).mp hda
    rw [hda', mul_comm c a] at h
    have hbc : b = c := mul_left_cancel₀ ha.ne_zero h
    omega

/-- `bPairCount Y N ≤ N`: the pairs counted lie over the `N` values `1, …, N`. -/
theorem bPairCountLeSelf (Y N : ℕ) : bPairCount Y N ≤ N := by
  rw [bPairCount_eq_card]
  calc (bPairSet Y N).card
      = ((bPairSet Y N).image (fun t : ℕ × ℕ => t.1 * t.2)).card :=
        (Finset.card_image_of_injOn (injOn_mul_bPairSet Y N)).symm
    _ ≤ (Finset.Icc 1 N).card := by
        apply Finset.card_le_card
        intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨⟨a, b⟩, ht, rfl⟩ := hv
        simp only [bPairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢
        obtain ⟨⟨-, -⟩, ha, hb, -, habN⟩ := ht
        refine ⟨?_, habN⟩
        have h1 : 2 ≤ a := ha.two_le
        have h2 : 2 ≤ b := hb.two_le
        nlinarith
    _ = N := by simp

end Work.NumberTheory.Chen.BTermCount
