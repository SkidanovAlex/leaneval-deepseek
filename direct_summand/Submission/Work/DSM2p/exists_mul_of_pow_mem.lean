import Mathlib
import Submission.Work.DSM2p.Basic

namespace Work.DSM2p

theorem exists_mul_of_pow_mem {S : Type*} [CommRing S] {p : ℕ} (R : Subring S) {ϖ : S}
    (hclosed : IsPIntegrallyClosedIn p R) (hunit : IsUnit ϖ) {x : S} (hx : x ∈ R)
    (h : ∃ c ∈ R, x ^ p = ϖ ^ p * c) : ∃ y ∈ R, x = ϖ * y := by
  obtain ⟨c, hc, hxc⟩ := h
  obtain ⟨u, rfl⟩ := hunit
  refine ⟨(↑(u⁻¹) : S) * x, ?_, ?_⟩
  · apply hclosed
    have key : ((↑(u⁻¹) : S) * x) ^ p = c := by
      have h2 : ((↑(u⁻¹) : S)) ^ p * (↑u : S) ^ p = 1 := by
        rw [← mul_pow, Units.inv_mul, one_pow]
      rw [mul_pow, hxc, ← mul_assoc, h2, one_mul]
    rw [key]
    exact hc
  · rw [← mul_assoc, Units.mul_inv, one_mul]

end Work.DSM2p
