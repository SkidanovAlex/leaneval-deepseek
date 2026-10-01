import Mathlib
import Submission.Work.ZeroDensity.Ingham.perronIntDeps

namespace Work.ZeroDensity.Ingham

/-- **Exponential decay of `Γ` on any vertical line `Re = c` with `-1 < c`, `c ≤ 3`**, uniformly for
`|Im| ≥ 1`: `∃ C > 0, ∀ t, 1 ≤ |t| → ‖Γ (c + i t)‖ ≤ C (1+|t|)^6 exp (-(π/2)|t|)`.

The ingredients live in `Submission/Commons/Analysis/Complex/Gamma_vertical_norm_bounds.lean`
(re-exported by `Work.ZeroDensity.Ingham.perronIntDeps`):
`Commons.Analysis.Complex.gamma_strip_upper (u t) (hu0 : 0 < u) (hu6 : u ≤ 6) (ht : 1 ≤ |t|)`
gives `‖Γ (u + it)‖ ≤ K6 (1+|t|)^6 exp (-(π/2)|t|)` for `u ∈ (0,6]`, and
`Commons.Analysis.Complex.norm_Gamma_le_shift_nat (z) (hk : 1 ≤ |z.im|)` gives
`‖Γ z‖ ≤ ‖Γ (z + k)‖`.  For `0 < c ≤ 3` apply `gamma_strip_upper` at `u = c`; for `-1 < c ≤ 0`
apply `norm_Gamma_le_shift_nat` with `k = 2` (so that `Re (z+2) = c + 2 ∈ (1,2] ⊂ (0,6]`) and then
`gamma_strip_upper` at `u = c + 2`.  In both cases `K6` works as the constant. -/
theorem gammaLineBound (c : ℝ) (hc_lo : -1 < c) (hc_hi : c ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + |t|) ^ 6 * Real.exp (-(Real.pi / 2) * |t|) := by
  refine ⟨Commons.Analysis.Complex.K6, Commons.Analysis.Complex.K6_pos, ?_⟩
  intro t ht
  have harg : (c : ℂ) + (t : ℂ) * Complex.I = (c : ℂ) + Complex.I * (t : ℂ) := by
    rw [mul_comm]
  rw [harg]
  have hkey : ‖Complex.Gamma ((c : ℂ) + Complex.I * (t : ℂ))‖ ≤
      Commons.Analysis.Complex.K6 * (1 + |t|) ^ (6 : ℝ) *
        Real.exp (-(Real.pi / 2) * |t|) := by
    by_cases hc : 0 < c
    · exact Commons.Analysis.Complex.gamma_strip_upper c t hc (by linarith) ht
    · have hu0 : 0 < c + 2 := by linarith
      have hu6 : c + 2 ≤ 6 := by linarith
      have him : (((c : ℂ) + Complex.I * (t : ℂ)).im) = t := by simp
      have hshift := Commons.Analysis.Complex.norm_Gamma_le_shift_nat
        ((c : ℂ) + Complex.I * (t : ℂ)) (k := 2) (by rw [him]; exact ht)
      have hst := Commons.Analysis.Complex.gamma_strip_upper (c + 2) t hu0 hu6 ht
      have harg2 : ((c : ℂ) + Complex.I * (t : ℂ)) + (2 : ℂ) =
          ((c + 2 : ℝ) : ℂ) + Complex.I * (t : ℂ) := by
        apply Complex.ext <;> simp
      calc
        ‖Complex.Gamma ((c : ℂ) + Complex.I * (t : ℂ))‖
            ≤ ‖Complex.Gamma (((c : ℂ) + Complex.I * (t : ℂ)) + (2 : ℂ))‖ := hshift
        _ = ‖Complex.Gamma (((c + 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ := by rw [harg2]
        _ ≤ Commons.Analysis.Complex.K6 * (1 + |t|) ^ (6 : ℝ) *
              Real.exp (-(Real.pi / 2) * |t|) := hst
  calc
    ‖Complex.Gamma ((c : ℂ) + Complex.I * (t : ℂ))‖
        ≤ Commons.Analysis.Complex.K6 * (1 + |t|) ^ (6 : ℝ) *
            Real.exp (-(Real.pi / 2) * |t|) := hkey
    _ = Commons.Analysis.Complex.K6 * (1 + |t|) ^ 6 *
          Real.exp (-(Real.pi / 2) * |t|) := by
        norm_num

end Work.ZeroDensity.Ingham
