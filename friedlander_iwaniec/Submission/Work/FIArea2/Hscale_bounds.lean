import Mathlib
import Submission.Work.FITop.Defs

namespace Work.FIArea2

/-- **(*FI* (9.3))**, with the strictness corrected to what `Params` supplies: the paper writes
`x^η < H < N^{1/2}` for the scale `H = M^{-1/4}N^{3/4}` of (9.2)/(Lemma 7.1); the upper bound is
`≤` here because `Params` has `N ≤ M` (not `N < M`) and `M = N` gives `H = N^{1/2}` exactly.
Proof: `hMNx : M*N ≤ x` gives `M ≤ x/N`, hence
`H = (N³/M)^{1/4} ≥ (N⁴/x)^{1/4} = N/x^{1/4} > x^η` by `hNlo : x^{1/4+η} < N`; and
`H ≤ N^{1/2} ⟺ N ≤ M`, which is `hMge`.  All quantities are positive (`hN1`, `hM1`, `hx`). -/
theorem Hscale_bounds (Pa : Work.FITop.Params) :
    (Pa.x : ℝ) ^ Pa.η < Work.FIPlan.Hscale Pa.M Pa.N ∧
      Work.FIPlan.Hscale Pa.M Pa.N ≤ Real.sqrt Pa.N := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hMpos : (0 : ℝ) < Pa.M := by linarith [Pa.hM1]
  have hMNpos : (0 : ℝ) < Pa.M * Pa.N := mul_pos hMpos hNpos
  have hM14 : (0 : ℝ) < Pa.M ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hMpos _
  have hx14 : (0 : ℝ) < (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hxpos _
  have hHpos : 0 < Work.FIPlan.Hscale Pa.M Pa.N := by
    rw [Work.FIPlan.Hscale]
    exact mul_pos (Real.rpow_pos_of_pos hMpos _) (Real.rpow_pos_of_pos hNpos _)
  constructor
  · -- lower bound: `x^{1/4} * H ≥ N`
    have hMrpow : Pa.M ^ (-(1 : ℝ) / 4) * Pa.M ^ ((1 : ℝ) / 4) = 1 := by
      rw [← Real.rpow_add hMpos, show -(1 : ℝ) / 4 + (1 : ℝ) / 4 = 0 by norm_num,
        Real.rpow_zero]
    have hNrpw : Pa.N ^ ((3 : ℝ) / 4) * Pa.N ^ ((1 : ℝ) / 4) = Pa.N := by
      rw [← Real.rpow_add hNpos, show (3 : ℝ) / 4 + (1 : ℝ) / 4 = 1 by norm_num, Real.rpow_one]
    have hcle : Work.FIPlan.Hscale Pa.M Pa.N * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) = Pa.N := by
      rw [Work.FIPlan.Hscale, Real.mul_rpow (le_of_lt hMpos) (le_of_lt hNpos)]
      calc Pa.M ^ (-(1 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
              * (Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((1 : ℝ) / 4))
          = (Pa.M ^ (-(1 : ℝ) / 4) * Pa.M ^ ((1 : ℝ) / 4))
              * (Pa.N ^ ((3 : ℝ) / 4) * Pa.N ^ ((1 : ℝ) / 4)) := by ring
        _ = 1 * Pa.N := by rw [hMrpow, hNrpw]
        _ = Pa.N := by ring
    have hx14ge : (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (le_of_lt hMNpos) Pa.hMNx (by norm_num)
    have hHx : Pa.N ≤ Work.FIPlan.Hscale Pa.M Pa.N * (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
      calc Pa.N = Work.FIPlan.Hscale Pa.M Pa.N * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) := hcle.symm
        _ ≤ Work.FIPlan.Hscale Pa.M Pa.N * (Pa.x : ℝ) ^ ((1 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_left hx14ge (le_of_lt hHpos)
    have h1 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η)
        = (Pa.x : ℝ) ^ ((1 : ℝ) / 4) * (Pa.x : ℝ) ^ Pa.η := Real.rpow_add hxpos _ _
    have h2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) * (Pa.x : ℝ) ^ Pa.η <
        (Pa.x : ℝ) ^ ((1 : ℝ) / 4) * Work.FIPlan.Hscale Pa.M Pa.N := by
      have hlt := lt_of_lt_of_le Pa.hNlo hHx
      rwa [h1, mul_comm (Work.FIPlan.Hscale Pa.M Pa.N)] at hlt
    exact (mul_lt_mul_iff_of_pos_left hx14).mp h2
  · -- upper bound: `H ≤ N^{1/2}`
    have hle : Pa.N ^ ((1 : ℝ) / 4) ≤ Pa.M ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (le_of_lt hNpos) Pa.hMge (by norm_num)
    have hMneg : Pa.M ^ (-(1 : ℝ) / 4) = (Pa.M ^ ((1 : ℝ) / 4))⁻¹ := by
      rw [show -(1 : ℝ) / 4 = -((1 : ℝ) / 4) by norm_num]
      exact Real.rpow_neg (le_of_lt hMpos) _
    have hkey : Pa.M ^ (-(1 : ℝ) / 4) * Pa.N ^ ((1 : ℝ) / 4) ≤ 1 := by
      rw [hMneg, inv_mul_le_iff₀ hM14]
      simpa using hle
    have hsplit : Pa.N ^ ((1 : ℝ) / 4) * Pa.N ^ ((1 : ℝ) / 2) = Pa.N ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_add hNpos, show (1 : ℝ) / 4 + (1 : ℝ) / 2 = (3 : ℝ) / 4 by norm_num]
    rw [Work.FIPlan.Hscale, Real.sqrt_eq_rpow]
    calc Pa.M ^ (-(1 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
        = (Pa.M ^ (-(1 : ℝ) / 4) * Pa.N ^ ((1 : ℝ) / 4)) * Pa.N ^ ((1 : ℝ) / 2) := by
          rw [mul_assoc, hsplit]
      _ ≤ 1 * Pa.N ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg (le_of_lt hNpos) _)
      _ = Pa.N ^ ((1 : ℝ) / 2) := one_mul _

end Work.FIArea2
