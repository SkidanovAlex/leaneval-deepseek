import Mathlib

namespace Work.LinnikAreas.JutilaPieces

theorem LogFloorGap (N z : ℕ) (hz : 2 ≤ z) (hzN : z ≤ N) :
    |Real.log ((N : ℝ) / (z : ℝ)) - Real.log ((N / z : ℕ) : ℝ)| ≤ Real.log 2 := by
  set q : ℕ := N / z with hq
  have hzposnat : 0 < z := by omega
  have hzpos : (0 : ℝ) < z := by exact_mod_cast hzposnat
  have hNpos : (0 : ℝ) < N := by
    have h : (0 : ℕ) < N := by omega
    exact_mod_cast h
  have hqpos_nat : 0 < q := by
    rw [hq]; exact Nat.div_pos hzN hzposnat
  have hq1 : 1 ≤ q := hqpos_nat
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos_nat
  have hmodlt : N % z < z := Nat.mod_lt N hzposnat
  have hdecomp_nat : z * q + N % z = N := by
    rw [hq]; exact Nat.div_add_mod N z
  have hdecomp : (N : ℝ) = (z : ℝ) * (q : ℝ) + ((N % z : ℕ) : ℝ) := by
    have h : ((z * q + N % z : ℕ) : ℝ) = (N : ℝ) := by rw [hdecomp_nat]
    push_cast at h
    linarith [h]
  have hrnn : (0 : ℝ) ≤ ((N % z : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrlt : ((N % z : ℕ) : ℝ) < (z : ℝ) := by exact_mod_cast hmodlt
  have hqz1 : (z : ℝ) ≤ (q : ℝ) * (z : ℝ) := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    nlinarith [hzpos]
  have hlower : (q : ℝ) ≤ (N : ℝ) / (z : ℝ) := by
    rw [le_div_iff₀ hzpos]
    nlinarith [hdecomp, hrnn]
  have hupper : (N : ℝ) / (z : ℝ) ≤ 2 * (q : ℝ) := by
    rw [div_le_iff₀ hzpos]
    nlinarith [hdecomp, hrlt, hqz1]
  have hXpos : 0 < (N : ℝ) / (z : ℝ) := div_pos hNpos hzpos
  have hle1 : Real.log (q : ℝ) ≤ Real.log ((N : ℝ) / (z : ℝ)) :=
    Real.log_le_log hqpos hlower
  have hle2 : Real.log ((N : ℝ) / (z : ℝ)) ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_le_log hXpos hupper
  have hlog2q : Real.log (2 * (q : ℝ)) = Real.log 2 + Real.log (q : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hqpos)]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_le]
  constructor <;> linarith

end Work.LinnikAreas.JutilaPieces
