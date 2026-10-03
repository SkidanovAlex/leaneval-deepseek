import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea4.S15red

/-- Given `(d : ℤ) ∣ Δ(z,w)` and `(z.re, 2 z.im) = 1`, the common divisor `(d, z.re)` of `d` and
`z.re` already divides `w.re`.  This is the heart of the symmetry statement
`gcd d z₁.re = gcd d z₂.re` for the determinant `Δ(z₁,z₂) = r₁s₂ - r₂s₁`. -/
private lemma gcd_gcd_re_dvd_re {d : ℕ} {z w : GaussianInt}
    (hz : Nat.Coprime z.re.natAbs (2 * z.im.natAbs))
    (hD : (d : ℤ) ∣ Work.FIPlan.Delta z w) :
    Nat.gcd d z.re.natAbs ∣ w.re.natAbs := by
  set g := Nat.gcd d z.re.natAbs with hg
  have hgd : g ∣ d := Nat.gcd_dvd_left d z.re.natAbs
  have hgr : g ∣ z.re.natAbs := Nat.gcd_dvd_right d z.re.natAbs
  have hgz : (g : ℤ) ∣ Work.FIPlan.Delta z w := dvd_trans (by exact_mod_cast hgd) hD
  have hdid : Work.FIPlan.Delta z w = z.re * w.im - w.re * z.im := by
    unfold Work.FIPlan.Delta; simp [GaussianInt]; ring
  rw [hdid] at hgz
  -- `g ∣ z.re`, hence `g ∣ z.re * w.im`, hence `g ∣ w.re * z.im`.
  have hgzre : (g : ℤ) ∣ z.re := by
    have h1c : (g : ℤ) ∣ (z.re.natAbs : ℤ) := by exact_mod_cast hgr
    have h2c : (z.re.natAbs : ℤ) ∣ z.re := by
      rcases Int.natAbs_eq z.re with h | h <;> rw [h] <;> simp
    exact dvd_trans h1c h2c
  have h1' : (g : ℤ) ∣ z.re * w.im := dvd_mul_of_dvd_left hgzre w.im
  have h2' : (g : ℤ) ∣ w.re * z.im := by
    have hsub : (g : ℤ) ∣ z.re * w.im - (z.re * w.im - w.re * z.im) := dvd_sub h1' hgz
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsub
  -- `(g, z.im) = 1` because `g ∣ z.re` and `(z.re, 2 z.im) = 1`.
  have hcop2 : Nat.Coprime g (2 * z.im.natAbs) := hz.coprime_dvd_left hgr
  have hcop : Nat.Coprime g z.im.natAbs := hcop2.coprime_dvd_right ⟨2, by ring⟩
  have hiscop : IsCoprime (g : ℤ) (z.im : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hcop
  have hwr : (g : ℤ) ∣ w.re := IsCoprime.dvd_of_dvd_mul_right hiscop h2'
  simpa using (Int.natAbs_dvd_natAbs).mpr hwr

theorem gcd_re_eq_of_delta {d : ℕ} {z1 z2 : GaussianInt}
    (h1 : Nat.Coprime z1.re.natAbs (2 * z1.im.natAbs))
    (h2 : Nat.Coprime z2.re.natAbs (2 * z2.im.natAbs))
    (hΔ : (d : ℤ) ∣ Work.FIPlan.Delta z1 z2) :
    Nat.gcd d z1.re.natAbs = Nat.gcd d z2.re.natAbs := by
  have hA : Nat.gcd d z1.re.natAbs ∣ Nat.gcd d z2.re.natAbs :=
    Nat.dvd_gcd (Nat.gcd_dvd_left d z1.re.natAbs) (gcd_gcd_re_dvd_re h1 hΔ)
  have hΔ' : (d : ℤ) ∣ Work.FIPlan.Delta z2 z1 := by
    have : Work.FIPlan.Delta z2 z1 = -(Work.FIPlan.Delta z1 z2) := by
      unfold Work.FIPlan.Delta; simp [GaussianInt]; ring
    rw [this]; exact dvd_neg.mpr hΔ
  have hB : Nat.gcd d z2.re.natAbs ∣ Nat.gcd d z1.re.natAbs :=
    Nat.dvd_gcd (Nat.gcd_dvd_left d z2.re.natAbs) (gcd_gcd_re_dvd_re h2 hΔ')
  exact Nat.dvd_antisymm hA hB

end Work.FIArea4.S15red
