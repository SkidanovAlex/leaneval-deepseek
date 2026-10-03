import Mathlib

namespace Work.KMTAreas.A4

/-- Elementary arithmetic endgame for the Area A4 "g-half" chain.

From the single small-ball inequality
`ε ^ 2 * N ^ (2 * d + 2) ≤ CS * S ^ 2 * Bf * B1 * μ`,
with `ε = δ ^ KA / (CE * (CA + 1))`, `Bf = CE * (CA + 1) * CA * δ⁻¹ ^ KA`,
`B1 = Bf * N ^ d`, `0 < δ ≤ 1`, `KA > 0` and `S ≤ CN3 * N`, one deduces the explicit
lower bound `δ ^ (8 * KA) * N ^ d / (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2) ≤ μ`.

The three ingredients are: `ε ^ 2 * Bf ^ 2 = CA ^ 2 * δ ^ (4*KA)`-type cancellations
(more precisely `δ ^ (8*KA) * Bf ^ 2 = (CE*(CA+1)*CA)^2 * δ ^ (6*KA)`), the exponent
monotonicity `δ ^ (6*KA) ≤ δ ^ (2*KA)` coming from `δ ≤ 1`, and the crude bound
`S ^ 2 ≤ (CN3 * N) ^ 2`. -/
theorem lip2GenMuArith {CA KA CE CS CN3 ε S Bf B1 μ δ : ℝ} {N : ℕ} {d : ℕ}
    (hCA : 0 < CA) (hKA : 0 < KA) (hCE : 0 < CE) (hCS : 0 < CS) (hCN3 : 0 < CN3)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N) (hS0 : 0 < S)
    (hε : ε = δ ^ KA / (CE * (CA + 1)))
    (hBf : Bf = CE * (CA + 1) * CA * δ⁻¹ ^ KA)
    (hB1 : B1 = Bf * (N : ℝ) ^ d)
    (hS : S ≤ CN3 * (N : ℝ))
    (hineq : ε ^ 2 * (N : ℝ) ^ (2 * d + 2) ≤ CS * S ^ 2 * Bf * B1 * μ) :
    δ ^ (8 * KA) * (N : ℝ) ^ d / (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2) ≤ μ := by
  have hD0 : 0 < CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2 := by positivity
  have hBf0 : 0 < Bf := by rw [hBf]; positivity
  have hB10 : 0 < B1 := by rw [hB1]; positivity
  have hBpos : 0 < CS * S ^ 2 * Bf * B1 := by positivity
  -- the two real-power bookkeeping identities
  have h8t : δ ^ (8 * KA) * (δ⁻¹ ^ KA) ^ 2 = δ ^ (6 * KA) := by
    have h2 : (δ⁻¹ ^ KA) ^ 2 = δ ^ (-(2 * KA)) := by
      rw [sq, ← Real.rpow_add (inv_pos.mpr hδ0) KA KA, Real.inv_rpow hδ0.le,
        Real.rpow_neg hδ0.le, show KA + KA = 2 * KA by ring]
    rw [h2, ← Real.rpow_add hδ0, show 8 * KA + -(2 * KA) = 6 * KA by ring]
  have h2sq : (δ ^ KA) ^ 2 = δ ^ (2 * KA) := by
    rw [sq, ← Real.rpow_add hδ0, show KA + KA = 2 * KA by ring]
  -- the elementary estimates
  have hδ6 : δ ^ (6 * KA) ≤ δ ^ (2 * KA) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have hSsq : S ^ 2 ≤ CN3 ^ 2 * (N : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ hS0.le hS 2
    rwa [mul_pow] at h
  have hred : δ ^ (6 * KA) * S ^ 2 ≤ δ ^ (2 * KA) * (CN3 ^ 2 * (N : ℝ) ^ 2) :=
    calc δ ^ (6 * KA) * S ^ 2 ≤ δ ^ (2 * KA) * S ^ 2 :=
          mul_le_mul_of_nonneg_right hδ6 (sq_nonneg _)
      _ ≤ δ ^ (2 * KA) * (CN3 ^ 2 * (N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hSsq (Real.rpow_nonneg hδ0.le _)
  -- the collapsed form of the two sides
  have hP : δ ^ (8 * KA) * Bf ^ 2 = (CE * (CA + 1) * CA) ^ 2 * δ ^ (6 * KA) := by
    rw [hBf, mul_pow]
    calc δ ^ (8 * KA) * ((CE * (CA + 1) * CA) ^ 2 * (δ⁻¹ ^ KA) ^ 2)
        = (CE * (CA + 1) * CA) ^ 2 * (δ ^ (8 * KA) * (δ⁻¹ ^ KA) ^ 2) := by ring
      _ = (CE * (CA + 1) * CA) ^ 2 * δ ^ (6 * KA) := by rw [h8t]
  have hQ : ε ^ 2 * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2)
      = CS * CN3 ^ 2 * (CE * (CA + 1) * CA) ^ 2 * δ ^ (2 * KA) := by
    rw [hε, div_pow, h2sq]
    field_simp
  have hnd : (N : ℝ) ^ d * (N : ℝ) ^ d = (N : ℝ) ^ (2 * d) := by
    rw [← pow_add]; congr 1; omega
  have hnd2 : (N : ℝ) ^ (2 * d + 2) = (N : ℝ) ^ (2 * d) * (N : ℝ) ^ 2 := by
    rw [show 2 * d + 2 = 2 * d + 2 by omega, pow_add]
  -- the single cleared inequality
  have hcore : δ ^ (8 * KA) * (N : ℝ) ^ d * (CS * S ^ 2 * Bf * B1)
      ≤ ε ^ 2 * (N : ℝ) ^ (2 * d + 2) * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2) := by
    have hLHS : δ ^ (8 * KA) * (N : ℝ) ^ d * (CS * S ^ 2 * Bf * B1)
        = (CE * (CA + 1) * CA) ^ 2 * CS * (N : ℝ) ^ (2 * d) * (δ ^ (6 * KA) * S ^ 2) := by
      rw [hB1]
      have hre : δ ^ (8 * KA) * (N : ℝ) ^ d * (CS * S ^ 2 * Bf * (Bf * (N : ℝ) ^ d))
          = (δ ^ (8 * KA) * Bf ^ 2) * (CS * S ^ 2) * ((N : ℝ) ^ d * (N : ℝ) ^ d) := by ring
      rw [hre, hP, hnd]
      ring
    have hRHS : ε ^ 2 * (N : ℝ) ^ (2 * d + 2) * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2)
        = (CE * (CA + 1) * CA) ^ 2 * CS * (N : ℝ) ^ (2 * d)
            * (δ ^ (2 * KA) * (CN3 ^ 2 * (N : ℝ) ^ 2)) := by
      rw [hnd2]
      have hre : ε ^ 2 * ((N : ℝ) ^ (2 * d) * (N : ℝ) ^ 2)
            * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2)
          = (ε ^ 2 * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2))
              * ((N : ℝ) ^ (2 * d) * (N : ℝ) ^ 2) := by ring
      rw [hre, hQ]
      ring
    rw [hLHS, hRHS]
    exact mul_le_mul_of_nonneg_left hred (by positivity)
  have hμlow : ε ^ 2 * (N : ℝ) ^ (2 * d + 2) / (CS * S ^ 2 * Bf * B1) ≤ μ :=
    (div_le_iff₀ hBpos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hineq)
  have hμD : δ ^ (8 * KA) * (N : ℝ) ^ d
      ≤ μ * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2) := by
    have hstep : δ ^ (8 * KA) * (N : ℝ) ^ d
        ≤ ε ^ 2 * (N : ℝ) ^ (2 * d + 2) * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2)
            / (CS * S ^ 2 * Bf * B1) :=
      (le_div_iff₀ hBpos).mpr hcore
    calc δ ^ (8 * KA) * (N : ℝ) ^ d
        ≤ ε ^ 2 * (N : ℝ) ^ (2 * d + 2) * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2)
            / (CS * S ^ 2 * Bf * B1) := hstep
      _ = (ε ^ 2 * (N : ℝ) ^ (2 * d + 2) / (CS * S ^ 2 * Bf * B1))
            * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2) := by ring
      _ ≤ μ * (CS * CE ^ 4 * (CA + 1) ^ 4 * CA ^ 2 * CN3 ^ 2) :=
          mul_le_mul_of_nonneg_right hμlow hD0.le
  exact (div_le_iff₀ hD0).mpr hμD

end Work.KMTAreas.A4
