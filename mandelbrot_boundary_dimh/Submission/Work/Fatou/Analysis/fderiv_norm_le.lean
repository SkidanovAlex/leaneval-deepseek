import Mathlib

namespace Work.Fatou.Analysis

/-- A real-linear map `ℂ → ℂ` is the sum of its complex-linear and
complex-antilinear parts; writing `w = (L 1 - i·(L i))/2` and
`z = (L 1 + i·(L i))/2` one has `L u = w * u + z * conj u` for every `u`. -/
private lemma apply_eq_linear_add_antilinear (L : ℂ →L[ℝ] ℂ) (u : ℂ) :
    L u = ((L 1 - Complex.I * L Complex.I) / 2) * u
        + ((L 1 + Complex.I * L Complex.I) / 2) * (starRingEnd ℂ) u := by
  set w : ℂ := (L 1 - Complex.I * L Complex.I) / 2 with hw
  set z : ℂ := (L 1 + Complex.I * L Complex.I) / 2 with hz
  have hLu : L u = (u.re : ℂ) * L 1 + (u.im : ℂ) * L Complex.I := by
    have hu : u = (u.re : ℝ) • (1 : ℂ) + (u.im : ℝ) • (Complex.I : ℂ) := by
      rw [Complex.real_smul, Complex.real_smul, mul_one]
      exact (Complex.re_add_im u).symm
    calc L u = L ((u.re : ℝ) • (1 : ℂ) + (u.im : ℝ) • (Complex.I : ℂ)) := congrArg L hu
      _ = (u.re : ℝ) • L 1 + (u.im : ℝ) • L Complex.I := by rw [map_add, map_smul, map_smul]
      _ = (u.re : ℂ) * L 1 + (u.im : ℂ) * L Complex.I := by
            rw [Complex.real_smul, Complex.real_smul]
  have hwz : w + z = L 1 := by rw [hw, hz]; ring_nf
  have hwzI : (w - z) * Complex.I = L Complex.I := by
    rw [hw, hz]; ring_nf; rw [pow_two, Complex.I_mul_I]; ring
  have hexp : w * u + z * (starRingEnd ℂ) u
      = (u.re : ℂ) * (w + z) + (u.im : ℂ) * ((w - z) * Complex.I) := by
    conv_lhs => rw [← Complex.re_add_im u]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  have h2 : w * u + z * (starRingEnd ℂ) u
      = (u.re : ℂ) * L 1 + (u.im : ℂ) * L Complex.I := by
    rw [hexp, hwz, hwzI]
  rw [h2, ← hLu]

theorem fderiv_norm_le (L : ℂ →L[ℝ] ℂ) :
    ‖L‖ ≤ ‖(L 1 - Complex.I * L Complex.I) / 2‖ + ‖(L 1 + Complex.I * L Complex.I) / 2‖ := by
  have hbound : ∀ u : ℂ,
      ‖L u‖ ≤ (‖(L 1 - Complex.I * L Complex.I) / 2‖
              + ‖(L 1 + Complex.I * L Complex.I) / 2‖) * ‖u‖ := by
    intro u
    rw [apply_eq_linear_add_antilinear L u]
    calc ‖((L 1 - Complex.I * L Complex.I) / 2) * u
            + ((L 1 + Complex.I * L Complex.I) / 2) * (starRingEnd ℂ) u‖
        ≤ ‖((L 1 - Complex.I * L Complex.I) / 2) * u‖
            + ‖((L 1 + Complex.I * L Complex.I) / 2) * (starRingEnd ℂ) u‖ := norm_add_le _ _
      _ = ‖(L 1 - Complex.I * L Complex.I) / 2‖ * ‖u‖
            + ‖(L 1 + Complex.I * L Complex.I) / 2‖ * ‖u‖ := by
            rw [norm_mul, norm_mul, Complex.norm_conj]
      _ = (‖(L 1 - Complex.I * L Complex.I) / 2‖
            + ‖(L 1 + Complex.I * L Complex.I) / 2‖) * ‖u‖ := by ring
  exact ContinuousLinearMap.opNorm_le_bound L (by positivity) hbound

end Work.Fatou.Analysis
