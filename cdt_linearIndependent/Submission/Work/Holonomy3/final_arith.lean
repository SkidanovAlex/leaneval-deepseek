import Mathlib

namespace Work.Holonomy3

/-- The final arithmetic estimate of the box principle: with `κ = 4 A₀^d + 2 B/D` and
`E = d log (m(D+1)) + Ch (d ⌈(m+δ)D⌉ + d)`, the four threshold inequalities `h1`–`h4` imply
`2 κ E ≤ ε d D`.

Route: `2κE` splits into the four summands `8A₀^d d log(m(D+1))`, `8A₀^d Ch d (⌈(m+δ)D⌉+1)`,
`4(Bdd/D) d log(m(D+1))` and `4(Bdd/D)Ch d(⌈(m+δ)D⌉+1)`; each is at most `εdD/4`:
`log(m(D+1)) ≤ m(D+1) ≤ 2mD` (as `D ≥ 1`), `⌈(m+δ)D⌉+1 ≤ (m+δ)D+2 ≤ (m+δ+2)D` (as `D ≥ 1`),
together with `h1 : 16 m A₀^d ≤ ε/4`, `h2 : 8Ch(m+δ+2)A₀^d ≤ ε/4`, `h3 : 32Bdd m ≤ εD`,
`h4 : 16Bdd Ch(m+δ+2) ≤ εD`. -/
theorem final_arith {m d D : ℕ} {ε δ Ch A₀ Bdd : ℝ}
    (hd : 0 < d) (hm : 1 ≤ m) (hε : 0 < ε) (hCh : 0 ≤ Ch) (hA : 0 ≤ A₀) (hB : 0 ≤ Bdd)
    (hδ0 : 0 ≤ δ) (hδm : δ ≤ m) (hD : 1 ≤ D)
    (h1 : 16*(m:ℝ) * A₀^d ≤ ε/4)
    (h2 : 8*Ch*((m:ℝ)+δ+2) * A₀^d ≤ ε/4)
    (h3 : 32*Bdd*(m:ℝ) ≤ ε*(D:ℝ))
    (h4 : 16*Bdd*Ch*((m:ℝ)+δ+2) ≤ ε*(D:ℝ)) :
    2 * (4*A₀^d + 2*(Bdd/(D:ℝ))) *
      ((d:ℝ) * Real.log ((m:ℝ) * ((D:ℝ)+1)) +
        Ch * ((d:ℝ) * (Nat.ceil ((m+δ)*D) : ℝ) + (d:ℝ))) ≤ ε * d * D := by
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := lt_of_lt_of_le one_pos hD1
  have hDne : (D:ℝ) ≠ 0 := ne_of_gt hDpos
  have hm0 : (0:ℝ) ≤ (m:ℝ) := by positivity
  have hd0 : (0:ℝ) ≤ (d:ℝ) := by positivity
  have hP : (0:ℝ) ≤ A₀^d := pow_nonneg hA d
  set L : ℝ := Real.log ((m:ℝ) * ((D:ℝ)+1)) with hLdef
  set C : ℝ := (Nat.ceil ((m+δ)*D) : ℝ) with hCdef
  -- `log (m(D+1)) ≤ m(D+1) ≤ 2 m D`
  have hLbound : L ≤ 2*(m:ℝ)*(D:ℝ) := by
    rw [hLdef]
    have hargnn : (0:ℝ) ≤ (m:ℝ)*((D:ℝ)+1) := by positivity
    have h := Real.log_le_self hargnn
    nlinarith [h, hm0, hD1]
  -- `⌈(m+δ)D⌉ + 1 ≤ (m+δ+2) D`
  have hCbound : C + 1 ≤ ((m:ℝ)+δ+2)*(D:ℝ) := by
    rw [hCdef]
    have hz0 : (0:ℝ) ≤ ((m:ℝ)+δ)*(D:ℝ) := by positivity
    have hlt := Nat.ceil_lt_add_one hz0
    nlinarith [hlt, hD1, hδ0, hm0]
  -- first summand
  have bA : 8*A₀^d*(d:ℝ)*L ≤ ε*(d:ℝ)*(D:ℝ)/4 := by
    have step1 : 8*A₀^d*(d:ℝ)*L ≤ 8*A₀^d*(d:ℝ)*(2*(m:ℝ)*(D:ℝ)) := by
      apply mul_le_mul_of_nonneg_left hLbound; positivity
    have step3 : 16*(m:ℝ)*A₀^d * ((d:ℝ)*(D:ℝ)) ≤ (ε/4) * ((d:ℝ)*(D:ℝ)) := by
      apply mul_le_mul_of_nonneg_right h1; positivity
    calc 8*A₀^d*(d:ℝ)*L ≤ 8*A₀^d*(d:ℝ)*(2*(m:ℝ)*(D:ℝ)) := step1
      _ = 16*(m:ℝ)*A₀^d * ((d:ℝ)*(D:ℝ)) := by ring
      _ ≤ (ε/4) * ((d:ℝ)*(D:ℝ)) := step3
      _ = ε*(d:ℝ)*(D:ℝ)/4 := by ring
  -- second summand
  have bB : 8*A₀^d*Ch*(d:ℝ)*(C + 1) ≤ ε*(d:ℝ)*(D:ℝ)/4 := by
    have key : 8*A₀^d*Ch*(d:ℝ)*((m:ℝ)+δ+2)*(D:ℝ) ≤ ε*(d:ℝ)*(D:ℝ)/4 := by
      have h := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ (d:ℝ)*(D:ℝ))
      calc 8*A₀^d*Ch*(d:ℝ)*((m:ℝ)+δ+2)*(D:ℝ)
          = (8*Ch*((m:ℝ)+δ+2) * A₀^d) * ((d:ℝ)*(D:ℝ)) := by ring
        _ ≤ (ε/4) * ((d:ℝ)*(D:ℝ)) := h
        _ = ε*(d:ℝ)*(D:ℝ)/4 := by ring
    have hle : 8*A₀^d*Ch*(d:ℝ)*(C + 1) ≤ 8*A₀^d*Ch*(d:ℝ)*(((m:ℝ)+δ+2)*(D:ℝ)) := by
      apply mul_le_mul_of_nonneg_left hCbound; positivity
    calc 8*A₀^d*Ch*(d:ℝ)*(C + 1) ≤ 8*A₀^d*Ch*(d:ℝ)*(((m:ℝ)+δ+2)*(D:ℝ)) := hle
      _ = 8*A₀^d*Ch*(d:ℝ)*((m:ℝ)+δ+2)*(D:ℝ) := by ring
      _ ≤ ε*(d:ℝ)*(D:ℝ)/4 := key
  -- third summand
  have bC : 4*(Bdd/(D:ℝ))*(d:ℝ)*L ≤ ε*(d:ℝ)*(D:ℝ)/4 := by
    have step1 : 4*(Bdd/(D:ℝ))*(d:ℝ)*L ≤ 4*(Bdd/(D:ℝ))*(d:ℝ)*(2*(m:ℝ)*(D:ℝ)) := by
      apply mul_le_mul_of_nonneg_left hLbound; positivity
    have hkey : 8*Bdd*(m:ℝ)*(d:ℝ) ≤ ε*(D:ℝ)*(d:ℝ)/4 := by
      have h := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ (d:ℝ))
      calc 8*Bdd*(m:ℝ)*(d:ℝ) = (32*Bdd*(m:ℝ))*(d:ℝ)/4 := by ring
        _ ≤ (ε*(D:ℝ))*(d:ℝ)/4 := by linarith [h]
        _ = ε*(D:ℝ)*(d:ℝ)/4 := by ring
    calc 4*(Bdd/(D:ℝ))*(d:ℝ)*L ≤ 4*(Bdd/(D:ℝ))*(d:ℝ)*(2*(m:ℝ)*(D:ℝ)) := step1
      _ = 8*Bdd*(m:ℝ)*(d:ℝ) := by field_simp <;> ring
      _ ≤ ε*(D:ℝ)*(d:ℝ)/4 := hkey
      _ = ε*(d:ℝ)*(D:ℝ)/4 := by ring
  -- fourth summand
  have bD : 4*(Bdd/(D:ℝ))*Ch*(d:ℝ)*(C + 1) ≤ ε*(d:ℝ)*(D:ℝ)/4 := by
    have step1 : 4*(Bdd/(D:ℝ))*Ch*(d:ℝ)*(C + 1)
        ≤ 4*(Bdd/(D:ℝ))*Ch*(d:ℝ)*(((m:ℝ)+δ+2)*(D:ℝ)) := by
      apply mul_le_mul_of_nonneg_left hCbound; positivity
    have hkey : 4*Bdd*Ch*((m:ℝ)+δ+2)*(d:ℝ) ≤ ε*(D:ℝ)*(d:ℝ)/4 := by
      have h := mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ (d:ℝ))
      calc 4*Bdd*Ch*((m:ℝ)+δ+2)*(d:ℝ) = (16*Bdd*Ch*((m:ℝ)+δ+2))*(d:ℝ)/4 := by ring
        _ ≤ (ε*(D:ℝ))*(d:ℝ)/4 := by linarith [h]
        _ = ε*(D:ℝ)*(d:ℝ)/4 := by ring
    calc 4*(Bdd/(D:ℝ))*Ch*(d:ℝ)*(C + 1)
        ≤ 4*(Bdd/(D:ℝ))*Ch*(d:ℝ)*(((m:ℝ)+δ+2)*(D:ℝ)) := step1
      _ = 4*Bdd*Ch*((m:ℝ)+δ+2)*(d:ℝ) := by field_simp <;> ring
      _ ≤ ε*(D:ℝ)*(d:ℝ)/4 := hkey
      _ = ε*(d:ℝ)*(D:ℝ)/4 := by ring
  calc 2 * (4*A₀^d + 2*(Bdd/(D:ℝ))) * ((d:ℝ)*L + Ch*((d:ℝ)*C + (d:ℝ)))
      = 8*A₀^d*(d:ℝ)*L + 8*A₀^d*Ch*(d:ℝ)*(C+1)
        + 4*(Bdd/(D:ℝ))*(d:ℝ)*L + 4*(Bdd/(D:ℝ))*Ch*(d:ℝ)*(C+1) := by ring
    _ ≤ ε*(d:ℝ)*(D:ℝ)/4 + ε*(d:ℝ)*(D:ℝ)/4 + ε*(d:ℝ)*(D:ℝ)/4 + ε*(d:ℝ)*(D:ℝ)/4 := by
        linarith [bA, bB, bC, bD]
    _ = ε*(d:ℝ)*(D:ℝ) := by ring

end Work.Holonomy3
