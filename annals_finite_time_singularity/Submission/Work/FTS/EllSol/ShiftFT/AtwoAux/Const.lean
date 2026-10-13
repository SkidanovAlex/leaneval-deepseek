import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false


/-- The arithmetic of the constants: with `K = 3 + 3·(Kd(1+2/4096))² + 196608·M²/4096⁴` one
has `3 ≤ K`, `3·(Kd/N + 2Kd/(4096N))² ≤ K/N`, and `12·N·Aphi ≤ K/N` for
`Aphi ≤ 16384·N·(M/(4096N)²)²` and `N ≥ 2`. -/
theorem uTrAtwo_const (N Kd M Aphi : ℝ) (hN : 2 ≤ N) (hKd : 0 ≤ Kd)
    (hAphi : Aphi ≤ 16384 * N * (M / (4096 * N) ^ 2) ^ 2) :
    (3 : ℝ) ≤ 3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4
    ∧ 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2 + 12 * N * Aphi
      ≤ (3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N := by
  have hN0 : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set c : ℝ := Kd * (1 + 2 / 4096) with hc
  set K : ℝ := 3 + 3 * c ^ 2 + 196608 * M ^ 2 / 4096 ^ 4 with hK
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hM2 : 0 ≤ 196608 * M ^ 2 / 4096 ^ 4 := by positivity
  have hK3 : (3 : ℝ) ≤ K := by rw [hK]; linarith
  have hKcc : 3 * c ^ 2 + 196608 * M ^ 2 / 4096 ^ 4 ≤ K := by rw [hK]; linarith
  have hcf : Kd / N + 2 * (Kd / (4096 * N)) = c / N := by
    rw [hc]
    field_simp
    try ring
  have hAphi' : Aphi ≤ 16384 * M ^ 2 / (4096 ^ 4 * N ^ 3) := by
    refine hAphi.trans (le_of_eq ?_)
    rw [div_pow]
    field_simp
    try ring
  refine ⟨hK3, ?_⟩
  rw [hcf]
  have hB : 3 * (c / N) ^ 2 ≤ (3 * c ^ 2) / N := by
    have h1 : 3 * (c / N) ^ 2 = (3 * c ^ 2) / N ^ 2 := by ring
    rw [h1, div_le_div_iff₀ (pow_pos hN0 2) hN0]
    have h2 : 3 * c ^ 2 * N ≤ 3 * c ^ 2 * N ^ 2 := by
      have hNN : (1 : ℝ) * N ≤ N * N := by nlinarith [hN1]
      nlinarith [hc2, hN1]
    linarith [h2]
  have hC : 12 * N * Aphi ≤ (196608 * M ^ 2 / 4096 ^ 4) / N := by
    rw [le_div_iff₀ hN0]
    have hstep : 12 * N ^ 2 * Aphi ≤ 196608 * M ^ 2 / (4096 ^ 4 * N) := by
      have h1 : 12 * N ^ 2 * Aphi ≤ 12 * N ^ 2 * (16384 * M ^ 2 / (4096 ^ 4 * N ^ 3)) :=
        mul_le_mul_of_nonneg_left hAphi' (by positivity)
      have h2 : 12 * N ^ 2 * (16384 * M ^ 2 / (4096 ^ 4 * N ^ 3))
          = 196608 * M ^ 2 / (4096 ^ 4 * N) := by
        field_simp
        try ring
      linarith [h1, h2.le, h2.ge]
    have hstep2 : 196608 * M ^ 2 / (4096 ^ 4 * N) ≤ 196608 * M ^ 2 / 4096 ^ 4 := by
      have h1 : 196608 * M ^ 2 / (4096 ^ 4 * N) = (196608 * M ^ 2 / 4096 ^ 4) / N := by ring
      rw [h1]
      have h2 : (196608 * M ^ 2 / 4096 ^ 4) / N ≤ (196608 * M ^ 2 / 4096 ^ 4) / 1 :=
        div_le_div_of_nonneg_left hM2 (by norm_num) hN1
      have h3 : (196608 * M ^ 2 / 4096 ^ 4) / 1 = 196608 * M ^ 2 / 4096 ^ 4 := by ring
      linarith [h2, h3.le]
    have h4 : 12 * N * Aphi * N = 12 * N ^ 2 * Aphi := by ring
    linarith [hstep, hstep2, h4.le, h4.ge]
  have hsum : 3 * (c / N) ^ 2 + 12 * N * Aphi
      ≤ (3 * c ^ 2) / N + (196608 * M ^ 2 / 4096 ^ 4) / N := add_le_add hB hC
  have hcomb : (3 * c ^ 2) / N + (196608 * M ^ 2 / 4096 ^ 4) / N
      = (3 * c ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N := by ring
  have hlast : (3 * c ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N ≤ K / N :=
    div_le_div_of_nonneg_right hKcc (le_of_lt hN0)
  linarith [hsum, hcomb.le, hcomb.ge, hlast]

end

end Work.FTS.EllSol.ShiftFT
