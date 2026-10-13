import Mathlib

universe a

namespace Work.DSM4p

theorem exists_mul_eq_pow_of_mul_eq {S : Type a} [CommRing S] {p n : ℕ} (hp : 1 ≤ p)
    {a z w c : S} (h1 : a * z = w ^ n) (h2 : (p : S) = c * w ^ p) :
    ∃ y : S, a * y = (p : S) ^ n := by
  refine ⟨c ^ n * a ^ (p - 1) * z ^ p, ?_⟩
  have ha : a * a ^ (p - 1) = a ^ p := by
    rw [← pow_succ']
    congr 1
    exact Nat.sub_add_cancel hp
  calc a * (c ^ n * a ^ (p - 1) * z ^ p)
      = c ^ n * (a * a ^ (p - 1)) * z ^ p := by ring
    _ = c ^ n * a ^ p * z ^ p := by rw [ha]
    _ = c ^ n * (a ^ p * z ^ p) := by ring
    _ = c ^ n * (a * z) ^ p := by rw [← mul_pow]
    _ = c ^ n * (w ^ n) ^ p := by rw [h1]
    _ = c ^ n * w ^ (n * p) := by rw [← pow_mul]
    _ = c ^ n * w ^ (p * n) := by rw [Nat.mul_comm n p]
    _ = c ^ n * (w ^ p) ^ n := by rw [pow_mul]
    _ = (c * w ^ p) ^ n := by rw [← mul_pow]
    _ = (p : S) ^ n := by rw [h2]

end Work.DSM4p
