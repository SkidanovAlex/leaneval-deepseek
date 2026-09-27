import Mathlib

namespace Work.EQ.FanTri

/-- **Numerical absorption for the first coordinate** (pure real arithmetic; no analysis).
With `0 < lam < 1`, `0 < rho`, `0 < beta ≤ q`, `0 ≤ P`, `0 ≤ Lm`, and the two hypotheses
`C(𝔹+𝒟lam)²K²lam²ρ ≤ 𝒞(1-lam²)β²` and `Lm·lam^(m+1) ≤ K·lam`, one has
`C(𝔹+𝒟lam)²Lm²P²/q² ≤ (1-lam²)𝒞(lam⁻¹)^(2(m+1))P²/ρ`.
(This is the quadratic-slack consumption of the `Work.EQ.FanTri.branchComp_radius` induction:
`Lm = wLam a w' = ∏|σ_j|`, and `Lm·lam^(m+1) ≤ K·lam` is `Λ_m·λ^n ≤ Kλ` with `n = m+1` and
`Λ_mλ^m = wWt a w' ≤ K`.)
Route: square `Lm·lam^(m+1) ≤ K·lam` to get `Lm²lam^(2(m+1)) ≤ K²lam²`, combine with
`C(𝔹+𝒟lam)²K²lam²ρ ≤ 𝒞(1-lam²)β² ≤ 𝒞(1-lam²)q²`, and use
`(lam⁻¹)^(2(m+1)) = 1/lam^(2(m+1))` (`inv_pow`, `inv_mul_cancel₀`). -/
theorem absorb_coord1 {lam rho q beta Cc C Bb Dd Lm K P : ℝ} (m : ℕ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hrho : 0 < rho) (hq : 0 < q) (hbeta : 0 < beta)
    (hbq : beta ≤ q) (hCc : 0 ≤ Cc) (hCpos : 0 < C) (hLm : 0 ≤ Lm) (hK : 0 < K)
    (hP : 0 ≤ P)
    (hR2 : C * (Bb + Dd * lam) ^ 2 * K ^ 2 * lam ^ 2 * rho ≤ Cc * (1 - lam ^ 2) * beta ^ 2)
    (hKL : Lm * lam ^ (m + 1) ≤ K * lam) :
    C * (Bb + Dd * lam) ^ 2 * Lm ^ 2 * P ^ 2 / q ^ 2
      ≤ (1 - lam ^ 2) * Cc * ((lam)⁻¹) ^ (2 * (m + 1)) * P ^ 2 / rho := by
  -- Notation: `u = (lam⁻¹)^(2(m+1))`, the reciprocal of `lam^(2(m+1))`.
  set u : ℝ := (lam)⁻¹ ^ (2 * (m + 1)) with hu_def
  have hlam2pos : 0 < lam ^ (2 * (m + 1)) := pow_pos hlam0 _
  have hut : lam ^ (2 * (m + 1)) * u = 1 := by
    rw [hu_def, inv_pow]
    exact mul_inv_cancel₀ (ne_of_gt hlam2pos)
  have hu_nonneg : 0 ≤ u := by
    rw [hu_def]; positivity
  have hA : 0 ≤ C * (Bb + Dd * lam) ^ 2 := by positivity
  have hP2 : 0 ≤ P ^ 2 := pow_nonneg hP 2
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  have h1ml : 0 ≤ 1 - lam ^ 2 := by
    have h : lam * lam < 1 * lam := mul_lt_mul_of_pos_right hlam1 hlam0
    nlinarith
  -- Square the growth hypothesis `Lm·lam^(m+1) ≤ K·lam`.
  have hLm2 : Lm ^ 2 * lam ^ (2 * (m + 1)) ≤ K ^ 2 * lam ^ 2 := by
    have hKlam : 0 ≤ K * lam := by positivity
    have hLmpow : 0 ≤ Lm * lam ^ (m + 1) := by positivity
    have hsq : (Lm * lam ^ (m + 1)) ^ 2 ≤ (K * lam) ^ 2 :=
      sq_le_sq' (by linarith) hKL
    calc Lm ^ 2 * lam ^ (2 * (m + 1))
        = (Lm * lam ^ (m + 1)) ^ 2 := by rw [mul_pow, ← pow_mul, Nat.mul_comm 2 (m+1)]
      _ ≤ (K * lam) ^ 2 := hsq
      _ = K ^ 2 * lam ^ 2 := by rw [mul_pow]
  -- Absorb the reciprocal power: `Lm² ≤ K²lam²u`.
  have hLm2' : Lm ^ 2 ≤ K ^ 2 * lam ^ 2 * u := by
    have h := mul_le_mul_of_nonneg_right hLm2 hu_nonneg
    rw [mul_assoc, hut, mul_one] at h
    exact h
  have hbeta2 : beta ^ 2 ≤ q ^ 2 := by nlinarith [hbeta, hq, hbq]
  -- Key numerical bound `C(𝔹+𝒟lam)²K²lam²ρ ≤ 𝒞(1-lam²)q²`.
  have hkey : C * (Bb + Dd * lam) ^ 2 * K ^ 2 * lam ^ 2 * rho ≤ Cc * (1 - lam ^ 2) * q ^ 2 := by
    have hCc1 : 0 ≤ Cc * (1 - lam ^ 2) := mul_nonneg hCc h1ml
    have h := mul_le_mul_of_nonneg_left hbeta2 hCc1
    linarith [hR2, h]
  -- Clear the denominators.
  rw [div_le_div_iff₀ hq2 hrho]
  -- First factor: replace `Lm²` by `K²lam²u`.
  have hstep1 : C * (Bb + Dd * lam) ^ 2 * Lm ^ 2 * P ^ 2 * rho
      ≤ C * (Bb + Dd * lam) ^ 2 * (K ^ 2 * lam ^ 2 * u) * P ^ 2 * rho := by
    have h1 : C * (Bb + Dd * lam) ^ 2 * Lm ^ 2
        ≤ C * (Bb + Dd * lam) ^ 2 * (K ^ 2 * lam ^ 2 * u) :=
      mul_le_mul_of_nonneg_left hLm2' hA
    have h2 := mul_le_mul_of_nonneg_right h1 hP2
    exact mul_le_mul_of_nonneg_right h2 (le_of_lt hrho)
  -- Second factor: consume the numerical slack `hkey`, scaled by `u·P²`.
  have hstep2 : C * (Bb + Dd * lam) ^ 2 * (K ^ 2 * lam ^ 2 * u) * P ^ 2 * rho
      ≤ (1 - lam ^ 2) * Cc * u * P ^ 2 * q ^ 2 := by
    have hpu : 0 ≤ u * P ^ 2 := mul_nonneg hu_nonneg hP2
    have h := mul_le_mul_of_nonneg_right hkey hpu
    linarith [h]
  linarith [hstep1, hstep2]

end Work.EQ.FanTri
