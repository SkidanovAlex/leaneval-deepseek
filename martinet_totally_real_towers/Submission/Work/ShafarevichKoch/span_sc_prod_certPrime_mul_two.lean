import Mathlib
import Submission.Work.ShafarevichKoch.GenusConj
import Submission.Work.ClassFieldTower.exists_imaginaryQuadratic_classGroupTwoRank_ge_five

open NumberField
open scoped NumberField

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

noncomputable section

set_option maxHeartbeats 800000

/-- **The product of two ramified prime ideals.**  For coprime `a b` with `a * b ∣ 30030` one has
`⟨a, √-30030⟩ * ⟨b, √-30030⟩ = ⟨a*b, √-30030⟩`.

Expanding the product with `Ideal.span_pair_mul_span_pair` gives the ideal spanned by
`a*b, a·scR, b·scR, scR²`; the first inclusion uses `scR² = -30030 = -a*b*k`, the reverse one
Bézout for the coprime `a, b`: `a*b ∈ ⟨a,scR⟩·⟨b,scR⟩` and
`scR = (p·a)·scR + (q·scR)·b` when `p·a + q·b = 1`. -/
theorem span_mul_span_of_mul_dvd {a b : ℕ} (hab : Nat.Coprime a b) (hdvd : a * b ∣ 30030) :
    Ideal.span ({(↑a : 𝓞 Kc), scR} : Set (𝓞 Kc)) * Ideal.span ({(↑b : 𝓞 Kc), scR} : Set (𝓞 Kc))
      = Ideal.span ({(↑(a * b) : 𝓞 Kc), scR} : Set (𝓞 Kc)) := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_pair_mul_span_pair]
    rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · rw [h, ← Nat.cast_mul]
      exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [h]
      exact Ideal.mul_mem_left _ _
        (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton scR))))
    · rw [h]
      exact Ideal.mul_mem_right _ _
        (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton scR))))
    · rw [h, scR_sq]
      obtain ⟨k, hk⟩ := hdvd
      have hmul : (↑(30030 : ℕ) : 𝓞 Kc) = (↑(a * b) : 𝓞 Kc) * (↑k : 𝓞 Kc) := by
        rw [hk, Nat.cast_mul]
      rw [show (30030 : 𝓞 Kc) = (↑(30030 : ℕ) : 𝓞 Kc) from rfl, hmul]
      have hneg : -(↑(a * b) * (↑k : 𝓞 Kc)) = (-(↑k) : 𝓞 Kc) * (↑(a * b) : 𝓞 Kc) := by ring
      rw [hneg]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h, Nat.cast_mul]
      exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_insert _ _))
        (Ideal.subset_span (Set.mem_insert _ _))
    · rw [h]
      obtain ⟨p, q, hpq⟩ := Nat.isCoprime_iff_coprime.mpr hab
      have hpq' : (↑p : 𝓞 Kc) * (↑a : 𝓞 Kc) + (↑q : 𝓞 Kc) * (↑b : 𝓞 Kc) = 1 := by
        have h := congrArg (fun z : ℤ => (z : 𝓞 Kc)) hpq
        push_cast at h
        exact h
      have heq : (↑p : 𝓞 Kc) * (↑a : 𝓞 Kc) * scR + (↑q : 𝓞 Kc) * scR * (↑b : 𝓞 Kc) = scR := by
        calc (↑p : 𝓞 Kc) * (↑a : 𝓞 Kc) * scR + (↑q : 𝓞 Kc) * scR * (↑b : 𝓞 Kc)
            = ((↑p : 𝓞 Kc) * (↑a : 𝓞 Kc) + (↑q : 𝓞 Kc) * (↑b : 𝓞 Kc)) * scR := by ring
          _ = 1 * scR := by rw [hpq']
          _ = scR := by rw [one_mul]
      have hcomb : (↑p : 𝓞 Kc) * (↑a : 𝓞 Kc) * scR + (↑q : 𝓞 Kc) * scR * (↑b : 𝓞 Kc) ∈
          Ideal.span ({(↑a : 𝓞 Kc), scR} : Set (𝓞 Kc))
            * Ideal.span ({(↑b : 𝓞 Kc), scR} : Set (𝓞 Kc)) := by
        apply Ideal.add_mem
        · exact Ideal.mul_mem_mul
            (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
            (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton scR))))
        · exact Ideal.mul_mem_mul
            (Ideal.mul_mem_left _ _
              (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton scR)))))
            (Ideal.subset_span (Set.mem_insert _ _))
      rw [heq] at hcomb
      exact hcomb

/-- **The dyadic step of the ramified-prime factorisation.**  For coprime `a b` with `a * b = 30030`
one has `⟨a, √-30030⟩ * ⟨b, √-30030⟩ = (√-30030)`: `a*b = 30030 = -scR²`, so every generator of
the product of the two spans is a multiple of `scR`, and conversely `a, b` coprime gives
`scR = (p·a)·scR + (q·scR)·b ∈ ⟨a,scR⟩·⟨b,scR⟩` from Bézout. -/
theorem span_mul_span_eq_span_scR {a b : ℕ} (hab : Nat.Coprime a b) (hmul : a * b = 30030) :
    Ideal.span ({(↑a : 𝓞 Kc), scR} : Set (𝓞 Kc)) * Ideal.span ({(↑b : 𝓞 Kc), scR} : Set (𝓞 Kc))
      = Ideal.span ({scR} : Set (𝓞 Kc)) := by
  have hsc : scR ∈ Ideal.span ({scR} : Set (𝓞 Kc)) := Ideal.subset_span (Set.mem_singleton scR)
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_pair_mul_span_pair]
    rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · rw [h, ← Nat.cast_mul, hmul]
      rw [show (↑(30030 : ℕ) : 𝓞 Kc) = -(scR * scR) from by rw [scR_sq]; ring]
      exact neg_mem (Ideal.mul_mem_left _ _ hsc)
    · rw [h]; exact Ideal.mul_mem_left _ _ hsc
    · rw [h]; exact Ideal.mul_mem_right _ _ hsc
    · rw [h]; exact Ideal.mul_mem_left _ _ hsc
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    obtain ⟨p, q, hpq⟩ := Nat.isCoprime_iff_coprime.mpr hab
    have hpq' : (↑p : 𝓞 Kc) * (↑a : 𝓞 Kc) + (↑q : 𝓞 Kc) * (↑b : 𝓞 Kc) = 1 := by
      have h := congrArg (fun z : ℤ => (z : 𝓞 Kc)) hpq
      push_cast at h
      exact h
    have heq : (↑p : 𝓞 Kc) * (↑a : 𝓞 Kc) * scR + (↑q : 𝓞 Kc) * scR * (↑b : 𝓞 Kc) = scR := by
      calc (↑p : 𝓞 Kc) * (↑a : 𝓞 Kc) * scR + (↑q : 𝓞 Kc) * scR * (↑b : 𝓞 Kc)
          = ((↑p : 𝓞 Kc) * (↑a : 𝓞 Kc) + (↑q : 𝓞 Kc) * (↑b : 𝓞 Kc)) * scR := by ring
        _ = 1 * scR := by rw [hpq']
        _ = scR := by rw [one_mul]
    have hcomb : (↑p : 𝓞 Kc) * (↑a : 𝓞 Kc) * scR + (↑q : 𝓞 Kc) * scR * (↑b : 𝓞 Kc) ∈
        Ideal.span ({(↑a : 𝓞 Kc), scR} : Set (𝓞 Kc))
          * Ideal.span ({(↑b : 𝓞 Kc), scR} : Set (𝓞 Kc)) := by
      apply Ideal.add_mem
      · exact Ideal.mul_mem_mul
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
          (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton scR))))
      · exact Ideal.mul_mem_mul
          (Ideal.mul_mem_left _ _
            (Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton scR)))))
          (Ideal.subset_span (Set.mem_insert _ _))
    rw [heq] at hcomb
    exact hcomb

/-- `𝓞 Kc = ℤ[√-30030]`, `scR = √-30030`, and `certPrime = ![3,5,7,11,13]`.  Since
`(√-30030) = ∏_{p | 30030} (p, √-30030)`, the product of the five ideals `⟨3,scR⟩, …, ⟨13,scR⟩`
with `⟨2, scR⟩` is the principal ideal generated by `√-30030`.  Hints: the six ideals are pairwise
comaximal, the product has norm `2·3·5·7·11·13 = 30030 = |norm(scR)|`, and every product generator
is a multiple of `scR` (using `scR² = -30030`), so the product is `(scR)` by equal norms.  The
five odd cases are `Work.ClassFieldTower.Pideal` with `span_pair_sq`/`absNorm_Pideal`. -/
theorem span_sc_prod_certPrime_mul_two :
    (∏ i : Fin 5, Ideal.span ({(↑(Work.ClassFieldTower.certPrime i) :
        NumberField.RingOfIntegers Work.ClassFieldTower.Kc), Work.ClassFieldTower.scR}
        : Set (NumberField.RingOfIntegers Work.ClassFieldTower.Kc)))
      * Ideal.span ({(2 : NumberField.RingOfIntegers Work.ClassFieldTower.Kc), Work.ClassFieldTower.scR}
        : Set (NumberField.RingOfIntegers Work.ClassFieldTower.Kc))
      = Ideal.span ({Work.ClassFieldTower.scR}
        : Set (NumberField.RingOfIntegers Work.ClassFieldTower.Kc)) := by
  have h35 : Ideal.span ({(3 : 𝓞 Kc), scR} : Set (𝓞 Kc))
      * Ideal.span ({(5 : 𝓞 Kc), scR} : Set (𝓞 Kc))
      = Ideal.span ({(15 : 𝓞 Kc), scR} : Set (𝓞 Kc)) := by
    have h := span_mul_span_of_mul_dvd (a := 3) (b := 5) (by decide) (by decide)
    simpa using h
  have h157 : Ideal.span ({(15 : 𝓞 Kc), scR} : Set (𝓞 Kc))
      * Ideal.span ({(7 : 𝓞 Kc), scR} : Set (𝓞 Kc))
      = Ideal.span ({(105 : 𝓞 Kc), scR} : Set (𝓞 Kc)) := by
    have h := span_mul_span_of_mul_dvd (a := 15) (b := 7) (by decide) (by decide)
    simpa using h
  have h10511 : Ideal.span ({(105 : 𝓞 Kc), scR} : Set (𝓞 Kc))
      * Ideal.span ({(11 : 𝓞 Kc), scR} : Set (𝓞 Kc))
      = Ideal.span ({(1155 : 𝓞 Kc), scR} : Set (𝓞 Kc)) := by
    have h := span_mul_span_of_mul_dvd (a := 105) (b := 11) (by decide) (by decide)
    simpa using h
  have h115513 : Ideal.span ({(1155 : 𝓞 Kc), scR} : Set (𝓞 Kc))
      * Ideal.span ({(13 : 𝓞 Kc), scR} : Set (𝓞 Kc))
      = Ideal.span ({(15015 : 𝓞 Kc), scR} : Set (𝓞 Kc)) := by
    have h := span_mul_span_of_mul_dvd (a := 1155) (b := 13) (by decide) (by decide)
    simpa using h
  have hlast : Ideal.span ({(15015 : 𝓞 Kc), scR} : Set (𝓞 Kc))
      * Ideal.span ({(2 : 𝓞 Kc), scR} : Set (𝓞 Kc))
      = Ideal.span ({scR} : Set (𝓞 Kc)) := by
    have h := span_mul_span_eq_span_scR (a := 15015) (b := 2) (by decide) (by norm_num)
    simpa using h
  rw [Fin.prod_univ_five]
  norm_num [certPrime]
  rw [h35, h157, h10511, h115513, hlast]

end

end Work.ShafarevichKoch
