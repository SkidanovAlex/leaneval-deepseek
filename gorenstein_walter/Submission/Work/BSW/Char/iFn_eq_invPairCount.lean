import Mathlib
import Submission.Work.BSW.Vocab

namespace Work.BSW.Char

/-- Bender's `i` and the pair count agree when `x` is not an involution: the map
`u ↦ (u, u * x)` is a bijection between the involutions inverting `x` and the ordered pairs
`(u, v)` of involutions with `u * v = x` (its inverse is `(u,v) ↦ u`, with `v = u * x` because
`u * u = 1`).  For an involution `x` the extra solution `u = x`, `v = 1` makes the two counts
differ by one. -/
theorem iFn_eq_invPairCount {G : Type} [Group G] {x : G} (hx : x * x ≠ 1) :
    Work.BSW.iFn G x = Work.BSW.invPairCount G x := by
  rw [Work.BSW.iFn, Work.BSW.invPairCount]
  refine Set.ncard_congr (fun u _ => (u, u * x)) ?_ ?_ ?_
  · rintro u ⟨hu2, hux⟩
    have hu : u * u = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
    have huxu : u * x * u = x⁻¹ := by rw [huinv] at hux; exact hux
    refine ⟨hu2, ?_, ?_⟩
    · have hvne : u * x ≠ 1 := by
        intro h
        apply hx
        have hx' : x = u := by
          have := eq_inv_of_mul_eq_one_right h
          rwa [huinv] at this
        rw [hx', hu]
      have hvv : (u * x) * (u * x) = 1 := by
        rw [← mul_assoc (u * x) u x, huxu, inv_mul_cancel]
      have hdvd : orderOf (u * x) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hvv)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hvne
      · exact h2
    · rw [← mul_assoc u u x, hu, one_mul]
  · rintro u v ⟨hu2, _⟩ ⟨hv2, _⟩ heq
    exact (Prod.mk.inj heq).1
  · rintro ⟨u, v⟩ ⟨hu2, hv2, huv⟩
    have hu : u * u = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2
    have hv : v * v = 1 := Work.BSW.mul_self_eq_one_of_orderOf_eq_two hv2
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv
    have hmem : u⁻¹ * x * u = x⁻¹ := by
      rw [huinv, ← huv, mul_inv_rev, huinv, hvinv, ← mul_assoc u u v, hu, one_mul]
    refine ⟨u, ⟨hu2, hmem⟩, ?_⟩
    have hux : u * x = v := by rw [← huv, ← mul_assoc u u v, hu, one_mul]
    rw [hux]

end Work.BSW.Char
