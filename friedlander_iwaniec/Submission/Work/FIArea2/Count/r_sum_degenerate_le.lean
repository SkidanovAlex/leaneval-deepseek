import Mathlib
import Submission.Work.FIArea2.Count.sec9_Z_defs
import Submission.Work.FIArea2.Count.class_delta_sum_le

namespace Work.FIArea2.Count

open Finset

/-! ## Reindexing the degenerate half

The degenerate half `Re Λ = 0` of the §9 weight sum is grouped in the *imaginary* coordinates
`(s₁,s₂)`; its arithmetic core is the counting statement `class_delta_sum_le`, which is stated for
a linear form over a rectangle of *pairs* `p = (p₁,p₂)`.  The lemma below is the purely formal
bridge: it rewrites the double sum over `(r₁,r₂) ∈ I²` (with the linear form `r₁s₂ − r₂s₁`) as a sum
over the filtered product `I × I`, with the two coordinates interchanged so that the fixed
coefficients `s₁,s₂` play the role of the coefficients of the linear form. -/

private lemma r_sum_degenerate_rewrite (R : ℤ) (s1 s2 : ℤ) (d : ℕ) :
    (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
        (if (d : ℤ) ∣ (r1 * s2 - r2 * s1) ∧ (r1 * s2 - r2 * s1) ≠ 0 then
          (((dlt r1 s1 r2 s2).divisors.card : ℝ)) ^ 3 / ((dlt r1 s1 r2 s2 : ℕ) : ℝ)
        else 0))
      = (∑ p ∈ ((Finset.Icc (-R) R).product (Finset.Icc (-R) R)).filter
          (fun p : ℤ × ℤ => (d : ℤ) ∣ (s2 * p.2 - s1 * p.1) ∧ (s2 * p.2 - s1 * p.1) ≠ 0),
        ((((s2 * p.2 - s1 * p.1).natAbs.divisors.card : ℝ)) ^ 3
          / (((s2 * p.2 - s1 * p.1).natAbs : ℕ) : ℝ))) := by
  simp only [dlt]
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x hx
  apply Finset.sum_congr rfl; intro y hy
  rw [show s2 * y - s1 * x = y * s2 - x * s1 from by ring]

/-- The degenerate half of the §9 weight sum, grouped in `(r₁,r₂)`: the `(d ∣ r₁s₂ − r₂s₁)`-part of
the sum is bounded by `C (1 + (s₁,s₂)(2R+1)/|s₂|) τ(d)³ d^{-1} (log D + 2)^8`, the `(s₁,s₂)`-count
of *FI* §9 ("given `(r₁,r₂)` and any `Δ`, the number of pairs with `r₁s₂ − r₂s₁ = Δ` is
`O(1 + (r₁,r₂)|I|/|r₁|)`").  This is `class_delta_sum_le` with the linear form
`s₂·r₁ − s₁·r₂` in the two box variables `(r₂,r₁)`, so that `r₁ = s₂` and `r₂ = s₁` become the
coefficients — the reindexing being `r_sum_degenerate_rewrite` above. -/
theorem r_sum_degenerate_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (s1 s2 : ℤ) (D d : ℕ),
      0 ≤ R → 1 ≤ D → 1 ≤ d → s2 ≠ 0 →
      (∀ r1 ∈ Finset.Icc (-R) R, ∀ r2 ∈ Finset.Icc (-R) R, dlt r1 s1 r2 s2 ≤ D) →
      (∑ r1 ∈ Finset.Icc (-R) R, ∑ r2 ∈ Finset.Icc (-R) R,
          (if (d : ℤ) ∣ (r1 * s2 - r2 * s1) ∧ (r1 * s2 - r2 * s1) ≠ 0 then
            (((dlt r1 s1 r2 s2).divisors.card : ℝ)) ^ 3 / ((dlt r1 s1 r2 s2 : ℕ) : ℝ)
          else 0))
        ≤ C * (1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
              / ((s2.natAbs : ℕ) : ℝ))
            * ((((d.divisors.card : ℝ)) ^ 3 / (d : ℝ))) * (Real.log ((D : ℕ) : ℝ) + 2) ^ 8 := by
  obtain ⟨C0, hC0pos, hC0⟩ := class_delta_sum_le
  refine ⟨C0, hC0pos, ?_⟩
  intro R s1 s2 D d hR hD hd hs2 hbound
  have hbound' : ∀ p : ℤ × ℤ, p.1 ∈ Finset.Icc (-R) R → p.2 ∈ Finset.Icc (-R) R →
      (s2 * p.2 - s1 * p.1).natAbs ≤ D := by
    intro p hp1 hp2
    have h := hbound p.2 hp2 p.1 hp1
    simp only [dlt] at h
    rwa [show p.2 * s2 - p.1 * s1 = s2 * p.2 - s1 * p.1 from by ring] at h
  have hkey := hC0 s2 s1 hs2 d hd D hD (-R) R (-R) R hbound'
  rw [r_sum_degenerate_rewrite R s1 s2 d]
  refine le_trans hkey ?_
  refine le_of_eq ?_
  have hg : (Int.gcd s2 s1 : ℕ) = Nat.gcd s1.natAbs s2.natAbs := by
    rw [Int.gcd_eq_natAbs, Nat.gcd_comm]
  have hl : R - (-R) + 1 = 2 * R + 1 := by ring
  rw [hg, hl]

end Work.FIArea2.Count
