import Mathlib

namespace Work.EQ.FanTri

/-- **Numerical absorption for the second coordinate's second-order correction** (pure real
arithmetic; no analysis).  With `0 < lam < 1`, `0 < rho`, `0 < beta ≤ q`, `0 ≤ A, Cc, Bb, Dd`,
`0 < C, Lm, K`, `0 ≤ P`, `1/3 ≤ |sig|`, `Ln = |sig|·Lm`, `Lm·lam^(m+1) ≤ K·lam`, and the three
hypotheses `9C(𝔹+𝒟lam)𝔸ρ ≤ 𝒟(1-lam)β²`, `9C(𝔹+𝒟lam)𝒞ρlam² ≤ 𝒟(1-lam)β²`,
`9C(𝔹+𝒟lam)²K·lam·ρ ≤ 𝒟(1-lam)β²`, one has
`C((𝔹+𝒟lam)LmP)((𝔸 + 𝒞lam²(lam⁻¹)^(m+1) + (𝔹+𝒟lam)Lm)P)/q² ≤ (1-lam)𝒟·Ln·(lam⁻¹)^(m+1)·P²/ρ`.
(This is the slack consumption of the `branchComp_radius` induction: the linearised inner
deviation is `‖p‖ ≤ (𝔸 + 𝒞λ²u^n + 𝔻Λ_m)P` with `u = lam⁻¹`, `n = m+1`, `𝔻 = 𝔹+𝒟lam`, and the
quadratic slack around the next centre is `(1-lam)𝒟Λ_n u^n P²/ρ` with `Λ_n = |sig|Λ_m`.)
Route: divide by `Lm·P²`; the three pieces are `C𝔻𝔸ρ/q² ≤ (1-lam)𝒟/9` (since `β ≤ q`),
`C𝔻𝒞ρlam²u^n/q² ≤ (1-lam)𝒟u^n/9`, and `C𝔻²Lmρ/q² ≤ (1-lam)𝒟u^n/9` (via `Lm·lam^(m+1) ≤ Klam`),
total `≤ (1-lam)𝒟(1+2u^n)/9 ≤ (1-lam)𝒟|sig|u^n` using `u^n ≥ 1` and `|sig| ≥ 1/3`.
Handle the case `P = 0` first (both sides vanish) before dividing by `P²`. -/
theorem absorb_coord2 {lam rho q beta A Cc Bb Dd Lm Ln C K P sig : ℝ} (m : ℕ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hrho : 0 < rho) (hq : 0 < q) (hbeta : 0 < beta)
    (hbq : beta ≤ q) (hA : 0 ≤ A) (hCc : 0 ≤ Cc) (hDd : 0 ≤ Dd) (hCpos : 0 < C)
    (hLm : 0 < Lm) (hK : 0 < K) (hP : 0 ≤ P) (hBb : 0 ≤ Bb)
    (hsig : 1 / 3 ≤ |sig|) (hLn : Ln = |sig| * Lm)
    (hR3a : 9 * C * (Bb + Dd * lam) * A * rho ≤ Dd * (1 - lam) * beta ^ 2)
    (hR3b : 9 * C * (Bb + Dd * lam) * Cc * rho * lam ^ 2 ≤ Dd * (1 - lam) * beta ^ 2)
    (hR3c : 9 * C * (Bb + Dd * lam) ^ 2 * K * lam * rho ≤ Dd * (1 - lam) * beta ^ 2)
    (hKL : Lm * lam ^ (m + 1) ≤ K * lam) :
    C * ((Bb + Dd * lam) * Lm * P) *
        ((A + Cc * lam ^ 2 * ((lam)⁻¹) ^ (m + 1) + (Bb + Dd * lam) * Lm) * P) / q ^ 2
      ≤ (1 - lam) * Dd * Ln * ((lam)⁻¹) ^ (m + 1) * P ^ 2 / rho := by
  have hlamne : lam ≠ 0 := ne_of_gt hlam0
  -- abbreviations: `a = 𝔹 + 𝒟lam`, `X = (lam⁻¹)^(m+1)`
  set a := Bb + Dd * lam with ha
  set X := ((lam)⁻¹) ^ (m + 1) with hX
  -- `β² ≤ q²`
  have hbq2 : beta ^ 2 ≤ q ^ 2 := by nlinarith only [hbeta, hbq, hq]
  have hg0 : 0 ≤ (1 - lam) * Dd := by
    have h1l : (0:ℝ) < 1 - lam := by linarith only [hlam1]
    exact mul_nonneg (le_of_lt h1l) hDd
  have hsq : Dd * (1 - lam) * beta ^ 2 ≤ Dd * (1 - lam) * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hbq2 hg0
    nlinarith only [h]
  -- `X ≥ 0`, `X ≥ 1`, and `lam^(m+1) * X = 1`
  have hXnn : 0 ≤ X := by
    rw [hX]; exact pow_nonneg (inv_nonneg.mpr (le_of_lt hlam0)) _
  have hX1 : 1 ≤ X := by
    rw [hX]; exact one_le_pow₀ ((one_le_inv₀ hlam0).mpr (le_of_lt hlam1))
  have hprod : lam ^ (m + 1) * X = 1 := by
    rw [hX, ← mul_pow, mul_inv_cancel₀ hlamne, one_pow]
  -- `Lm ≤ K·lam·X`
  have hLmK : Lm ≤ K * lam * X := by
    have h1 : Lm * lam ^ (m + 1) * X ≤ K * lam * X :=
      mul_le_mul_of_nonneg_right hKL hXnn
    have h2 : Lm * lam ^ (m + 1) * X = Lm := by rw [mul_assoc, hprod, mul_one]
    rwa [h2] at h1
  -- the three absorption hypotheses with `β²` replaced by `q²`
  have hR3a' : 9 * C * a * A * rho ≤ Dd * (1 - lam) * q ^ 2 := le_trans hR3a hsq
  have hR3b' : 9 * C * a * Cc * rho * lam ^ 2 ≤ Dd * (1 - lam) * q ^ 2 := le_trans hR3b hsq
  have hR3c' : 9 * C * a ^ 2 * K * lam * rho ≤ Dd * (1 - lam) * q ^ 2 := le_trans hR3c hsq
  -- the three pieces
  have ha_ : C * a * A * rho / q ^ 2 ≤ (1 - lam) * Dd / 9 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < q ^ 2)]
    nlinarith only [hR3a']
  have hb_ : C * a * Cc * lam ^ 2 * X * rho / q ^ 2 ≤ (1 - lam) * Dd * X / 9 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < q ^ 2)]
    have h2 : 9 * C * a * Cc * rho * lam ^ 2 - Dd * (1 - lam) * q ^ 2 ≤ 0 := by
      linarith only [hR3b']
    have hmul : X * (9 * C * a * Cc * rho * lam ^ 2 - Dd * (1 - lam) * q ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hXnn h2
    nlinarith only [hmul]
  have hc_ : C * a ^ 2 * Lm * rho / q ^ 2 ≤ (1 - lam) * Dd * X / 9 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < q ^ 2)]
    have hCn : 0 ≤ C * a ^ 2 * rho := by positivity
    have hstep1 : C * a ^ 2 * Lm * rho ≤ C * a ^ 2 * (K * lam * X) * rho := by
      have h := mul_le_mul_of_nonneg_left hLmK hCn
      nlinarith only [h]
    have h3 : 9 * C * a ^ 2 * K * lam * rho - Dd * (1 - lam) * q ^ 2 ≤ 0 := by
      linarith only [hR3c']
    have hmul : X * (9 * C * a ^ 2 * K * lam * rho - Dd * (1 - lam) * q ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hXnn h3
    have hstep2 : C * a ^ 2 * (K * lam * X) * rho ≤ (1 - lam) * Dd * X / 9 * q ^ 2 := by
      nlinarith only [hmul]
    linarith only [hstep1, hstep2]
  -- the reduced inequality (obtained from the original by dividing by `Lm·P²/ρ`)
  have hred : C * a * (A + Cc * lam ^ 2 * X + a * Lm) * rho / q ^ 2
      ≤ (1 - lam) * Dd * |sig| * X := by
    have e : C * a * (A + Cc * lam ^ 2 * X + a * Lm) * rho / q ^ 2
        = C * a * A * rho / q ^ 2 + C * a * Cc * lam ^ 2 * X * rho / q ^ 2
          + C * a ^ 2 * Lm * rho / q ^ 2 := by ring
    rw [e]
    have h1 : (1 - lam) * Dd / 9 + (1 - lam) * Dd * X / 9 + (1 - lam) * Dd * X / 9
        ≤ (1 - lam) * Dd * X / 3 := by
      have hneg : (1 - lam) * Dd * (1 - X) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hg0 (by linarith only [hX1])
      nlinarith only [hneg]
    have h2 : (1 - lam) * Dd * X / 3 ≤ (1 - lam) * Dd * |sig| * X := by
      have hgX : 0 ≤ (1 - lam) * Dd * X := mul_nonneg hg0 hXnn
      have h := mul_le_mul_of_nonneg_left hsig hgX
      nlinarith only [h]
    linarith only [ha_, hb_, hc_, h1, h2]
  -- multiply the reduced inequality by the nonnegative factor `Lm·P²/ρ`
  rw [hLn]
  have hgoal : C * (a * Lm * P) * ((A + Cc * lam ^ 2 * X + a * Lm) * P) / q ^ 2
      = (C * a * (A + Cc * lam ^ 2 * X + a * Lm) * rho / q ^ 2) * (Lm * P ^ 2 / rho) := by
    field_simp [hrho.ne']
  have hgoal2 : (1 - lam) * Dd * (|sig| * Lm) * X * P ^ 2 / rho
      = ((1 - lam) * Dd * |sig| * X) * (Lm * P ^ 2 / rho) := by ring
  rw [hgoal, hgoal2]
  exact mul_le_mul_of_nonneg_right hred (by positivity : (0:ℝ) ≤ Lm * P ^ 2 / rho)

end Work.EQ.FanTri
