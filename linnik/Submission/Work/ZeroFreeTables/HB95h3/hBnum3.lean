import Mathlib

namespace Work.ZeroFreeTables.HB95h3

/-- Core numeric inequality underlying `hBnum3`.

For `0 < P ≤ 4`, `m ≥ 1`, and lower bounds `g ≥ 1000`, `h ≥ 1000` on the two
quantities `g = L δ²` and `h = g ε`, the linear combination of the three
`R`-bounds is dominated by the two terms on the right.  The proof splits on
whether `m ≤ 48` (then the `P ε`-term alone suffices) or `m ≥ 48` (then the
`m - 1`-term alone suffices). -/
lemma hBnum3_core {P m g h : ℝ} (hP : 0 < P) (hP4 : P ≤ 4) (hm : 1 ≤ m)
    (hg : 1000 ≤ g) (hh : 1000 ≤ h) :
    650080 * P * m ≤ 65280 * (m - 1) * g + 31738 * P * h := by
  rcases le_or_gt m 48 with hm48 | hm48
  · -- Small `m`: the `P ε`-term alone dominates.
    have hm48' : 650080 * m ≤ 31738000 := by nlinarith
    have hPm : 650080 * P * m ≤ 31738000 * P := by nlinarith [hm48']
    have hnonneg : 0 ≤ 65280 * (m - 1) * g := by nlinarith [hm, hg]
    have hPh : 31738000 * P ≤ 31738 * P * h := by nlinarith [hh, hP]
    nlinarith [hPm, hnonneg, hPh]
  · -- Large `m`: the `m - 1`-term alone dominates.
    have hmge : (48 : ℝ) ≤ m := le_of_lt hm48
    have hPm : 650080 * P * m ≤ 2600320 * m := by nlinarith [hP4, hm]
    have hg' : 65280000 * (m - 1) ≤ 65280 * (m - 1) * g := by nlinarith [hg, hm]
    have hnum : 2600320 * m ≤ 65280000 * (m - 1) := by nlinarith [hmge]
    have hRh : 0 ≤ 31738 * P * h := by nlinarith [hP, hh]
    nlinarith [hPm, hg', hnum, hRh]

theorem hBnum3 {P L δ ε R1 R2 R4 m : ℝ} (hP : 0 < P) (hL : 0 < L) (hδ : 0 < δ) (hε : 0 < ε) (hP4 : P ≤ 4) (hm : 1 ≤ m) (hk : ∃ k : ℕ, m = (k : ℝ)) (h1 : R1 ≤ (P / L) * (16 * m / δ ^ 2)) (h2 : R2 ≤ (P / L) * (16 * m / δ ^ 2)) (h4 : R4 ≤ (P / L) * (16 * m / δ ^ 2)) (hLδ : 1000 ≤ δ ^ 2 * L) (hLε : 1000 ≤ δ ^ 2 * ε * L) : 24480 * R1 + 14900 * R2 + 1250 * R4 ≤ 65280 * (m - 1) + 31738 * P * ε := by
  have hg : 0 < L * δ ^ 2 := by positivity
  -- Clearing the common denominator `L δ²` from the three upper bounds.
  have hkey : (L * δ ^ 2) * ((P / L) * (16 * m / δ ^ 2)) = 16 * P * m := by field_simp
  have hr1 : (L * δ ^ 2) * R1 ≤ 16 * P * m := by
    calc (L * δ ^ 2) * R1 ≤ (L * δ ^ 2) * ((P / L) * (16 * m / δ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hg)
      _ = 16 * P * m := hkey
  have hr2 : (L * δ ^ 2) * R2 ≤ 16 * P * m := by
    calc (L * δ ^ 2) * R2 ≤ (L * δ ^ 2) * ((P / L) * (16 * m / δ ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hg)
      _ = 16 * P * m := hkey
  have hr4 : (L * δ ^ 2) * R4 ≤ 16 * P * m := by
    calc (L * δ ^ 2) * R4 ≤ (L * δ ^ 2) * ((P / L) * (16 * m / δ ^ 2)) :=
          mul_le_mul_of_nonneg_left h4 (le_of_lt hg)
      _ = 16 * P * m := hkey
  have hA : (L * δ ^ 2) * (24480 * R1 + 14900 * R2 + 1250 * R4) ≤ 650080 * P * m := by
    nlinarith [hr1, hr2, hr4]
  -- Rewrite the hypotheses `hLδ`, `hLε` into the form used by `hBnum3_core`.
  have hg1000 : 1000 ≤ L * δ ^ 2 := by nlinarith [hLδ]
  have hge : 1000 ≤ (L * δ ^ 2) * ε := by nlinarith [hLε]
  have hcore := hBnum3_core hP hP4 hm hg1000 hge
  have hB : 650080 * P * m ≤ (L * δ ^ 2) * (65280 * (m - 1) + 31738 * P * ε) := by
    have hexp : (L * δ ^ 2) * (65280 * (m - 1) + 31738 * P * ε)
        = 65280 * (m - 1) * (L * δ ^ 2) + 31738 * P * ((L * δ ^ 2) * ε) := by ring
    rw [hexp]; exact hcore
  have hfin : (L * δ ^ 2) * (24480 * R1 + 14900 * R2 + 1250 * R4)
      ≤ (L * δ ^ 2) * (65280 * (m - 1) + 31738 * P * ε) := le_trans hA hB
  exact (mul_le_mul_iff_of_pos_left hg).mp hfin

end Work.ZeroFreeTables.HB95h3
