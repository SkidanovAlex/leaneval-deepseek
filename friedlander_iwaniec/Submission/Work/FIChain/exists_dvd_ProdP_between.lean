import Mathlib
import Submission.Work.FIChain.BpWinDefs

namespace Work.FIChain

/-- Given `b₁ ∣ Π(Pz) = ∏_{p ≤ Pz} p` with `b₁ > D ≥ 1`, there is a divisor `d` of `b₁`
(hence of `Π(Pz)`) with `D < d ≤ D * Pz`.

Proof: take `d` the *least* divisor of `b₁` exceeding `D` (it exists since `b₁` itself does).
Let `p` be a prime divisor of `d` (possible as `d ≥ 2`).  Then `d / p` is a divisor of `b₁`
strictly smaller than `d`, so `d / p ≤ D` by minimality; and `p ∣ d ∣ b₁ ∣ Π(Pz)` forces
`p ≤ Pz` by `Nat.Prime.dvd_primorial_iff`.  Hence `d = p · (d / p) ≤ Pz · D = D · Pz`. -/
theorem exists_dvd_ProdP_between {Pz b₁ D : ℕ} (hPz : 2 ≤ Pz) (hD1 : 1 ≤ D)
    (hb : b₁ ∣ Work.FIChain.ProdP Pz) (hDb : D < b₁) :
    ∃ d : ℕ, d ∣ Work.FIChain.ProdP Pz ∧ d ∣ b₁ ∧ D < d ∧ d ≤ D * Pz := by
  have _ := hPz
  classical
  -- the set of divisors of `b₁` exceeding `D` is nonempty
  have hex : ∃ e : ℕ, e ∣ b₁ ∧ D < e := ⟨b₁, dvd_rfl, hDb⟩
  -- let `d` be its least element
  set d := Nat.find hex with hddef
  have hd : d ∣ b₁ ∧ D < d := by
    have h := Nat.find_spec hex
    rwa [← hddef] at h
  -- minimality of `d`
  have hmin : ∀ e : ℕ, e ∣ b₁ → e < d → e ≤ D := by
    intro e he hlt
    by_contra hcon
    exact Nat.find_min hex (by rw [← hddef]; exact hlt) ⟨he, Nat.lt_of_not_le hcon⟩
  have hd2 : 2 ≤ d := by omega
  -- a prime divisor `p` of `d`
  obtain ⟨p, hpprime, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hmul : p * (d / p) = d := Nat.mul_div_cancel' hpd
  have hp2 : 2 ≤ p := hpprime.two_le
  -- `d / p` is a smaller divisor of `b₁`, hence `≤ D`
  have hqdvd : d / p ∣ b₁ := dvd_trans (Nat.div_dvd_of_dvd hpd) hd.1
  have hqpos : 1 ≤ d / p := by
    rcases Nat.eq_zero_or_pos (d / p) with h | h
    · rw [h, mul_zero] at hmul; omega
    · exact h
  have hqlt : d / p < d := by nlinarith
  have hqD : d / p ≤ D := hmin _ hqdvd hqlt
  -- `p ≤ Pz` since `p ∣ b₁ ∣ Π(Pz)`
  have hpPz : p ≤ Pz := by
    have hpB : p ∣ Work.FIChain.ProdP Pz := dvd_trans hpd (dvd_trans hd.1 hb)
    exact (hpprime.dvd_primorial_iff).1 hpB
  exact ⟨d, dvd_trans hd.1 hb, hd.1, hd.2,
    calc d = p * (d / p) := hmul.symm
      _ ≤ Pz * D := Nat.mul_le_mul hpPz hqD
      _ = D * Pz := Nat.mul_comm _ _⟩

end Work.FIChain
