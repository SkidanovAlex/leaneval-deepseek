import Mathlib.Analysis.Real.Sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSrc

/-- **Squaring the AM–GM bound.**  If `x ≤ K · (t/2 + M/(2t))` for every `t > 0` and `K ≠ ⊤`,
then `x² ≤ K² M` in `ℝ≥0∞`.  The bound is applied at `t = √M` (giving `t/2 + M/(2t) = √M`);
the degenerate cases `K = 0`, `M = ⊤` and `M = 0` are handled separately (for `M = 0` the bound
is applied at `t = 2ε/K` and the limit `ε → 0⁺` is taken via `ENNReal.le_of_forall_pos_le_add`). -/
theorem sq_le_of_forall_mul {x M K : ENNReal} (hK : K ≠ ⊤)
    (h : ∀ t : ℝ, 0 < t → x ≤ K * (ENNReal.ofReal (t / 2) + M * ENNReal.ofReal ((2 * t)⁻¹))) :
    x ^ 2 ≤ K ^ 2 * M := by
  rcases eq_or_ne K 0 with hK0 | hK0
  · subst hK0
    have hx0 : x = 0 := le_bot_iff.mp (by simpa using h 1 zero_lt_one)
    subst hx0
    simp
  · rcases eq_or_ne M ⊤ with hMtop | hMtop
    · rw [hMtop, ENNReal.mul_top (ENNReal.pow_ne_zero hK0 2)]
      exact le_top
    · set s : ℝ := Real.sqrt M.toReal with hs
      have hsnn : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg M.toReal
      have hs2 : s ^ 2 = M.toReal := by rw [hs]; exact Real.sq_sqrt ENNReal.toReal_nonneg
      have hMsq : ENNReal.ofReal s * ENNReal.ofReal s = M := by
        rw [← ENNReal.ofReal_mul hsnn, ← pow_two, hs2, ENNReal.ofReal_toReal hMtop]
      have hMsq' : ENNReal.ofReal s ^ 2 = M := by rw [pow_two, hMsq]
      have hxle : x ≤ K * ENNReal.ofReal s := by
        rcases eq_or_ne M.toReal 0 with hm0 | hm0
        · have hM0 : M = 0 := by
            rw [← ENNReal.ofReal_toReal hMtop, hm0, ENNReal.ofReal_zero]
          have hs0 : s = 0 := by rw [hs, hm0, Real.sqrt_zero]
          rw [hs0, ENNReal.ofReal_zero, mul_zero]
          refine ENNReal.le_of_forall_pos_le_add ?_
          intro ε hε _
          rw [zero_add]
          have hKpos : 0 < K.toReal := ENNReal.toReal_pos hK0 hK
          have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
          have ht : 0 < 2 * (ε : ℝ) / K.toReal := by positivity
          have hh := h (2 * (ε : ℝ) / K.toReal) ht
          rw [hM0, zero_mul, add_zero] at hh
          have hb : K * ENNReal.ofReal ((2 * (ε : ℝ) / K.toReal) / 2) ≠ ⊤ :=
            ne_of_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hK) ENNReal.ofReal_lt_top)
          have hxtr : x.toReal ≤ (ε : ℝ) := by
            calc x.toReal
                ≤ (K * ENNReal.ofReal ((2 * (ε : ℝ) / K.toReal) / 2)).toReal :=
                  ENNReal.toReal_mono hb hh
              _ = K.toReal * ((2 * (ε : ℝ) / K.toReal) / 2) := by
                  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
              _ = (ε : ℝ) := by field_simp
          calc x = ENNReal.ofReal x.toReal :=
                (ENNReal.ofReal_toReal (ne_top_of_le_ne_top hb hh)).symm
            _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal hxtr
            _ = (ε : ENNReal) := ENNReal.ofReal_coe_nnreal
        · have hMpos : 0 < M.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hm0)
          have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hMpos
          have hsne : s ≠ 0 := ne_of_gt hspos
          refine le_trans (h s hspos) ?_
          have key : ENNReal.ofReal (s / 2) + M * ENNReal.ofReal ((2 * s)⁻¹)
              = ENNReal.ofReal s := by
            have h2 : M * ENNReal.ofReal ((2 * s)⁻¹) = ENNReal.ofReal (s / 2) := by
              rw [← hMsq, ← ENNReal.ofReal_mul hsnn,
                ← ENNReal.ofReal_mul (mul_nonneg hsnn hsnn)]
              congr 1
              field_simp
            rw [h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
          rw [key]
      calc x ^ 2 ≤ (K * ENNReal.ofReal s) ^ 2 := ENNReal.pow_le_pow_left hxle
        _ = K ^ 2 * M := by rw [mul_pow, hMsq']

end Work.FTS.StrongEps.EpsSrc
