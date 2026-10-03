import Mathlib
import Submission.Work.Repel.boxes_v3
import Submission.Work.Repel.chain_v9_geom

/-!
# `Work.Repel.box_piExp_surj`

The half-open box
`B η n = {w | n ≤ Re w < n + 1, η + log(1/2)/2π < Im w < η + log(3/2)/2π}`
is mapped **bijectively** by `π w = exp (2πi w)` onto the annulus
`{ζ | 2 e^{-2πη}/3 < ‖ζ‖ < 2 e^{-2πη}}`.

Indeed, writing `w = x + iy`, `π w = e^{-2πy} · e^{2πix}`, so `y` is forced by `‖ζ‖ = e^{-2πy}`
(hence `y = -log ‖ζ‖ / 2π`, which lies in the required imaginary interval exactly because of
`h1`/`h2`), and `x` is then determined modulo `1`, with a unique representative in `[n, n+1)`.

The preimage is produced explicitly as `t + k` where `t = log ζ / (2πi)` satisfies `π t = ζ`
(the imaginary part of `t` is `-log ‖ζ‖ / 2π` and adding an integer does not change it) and `k` is
the integer making `Re (t + k)` lie in `[n, n+1)`.
-/

namespace Work.Repel

open Complex Set Metric Filter Topology MandelDim

noncomputable section

private lemma piExp_aux_add (x y : ℂ) :
    MandelDim.piExp (x + y) = MandelDim.piExp x * MandelDim.piExp y := by
  have h : (2 * Real.pi * I) * (x + y) = (2 * Real.pi * I) * x + (2 * Real.pi * I) * y := by
    ring
  simp only [MandelDim.piExp]
  rw [h, Complex.exp_add]

private lemma piExp_aux_intCast (k : ℤ) : MandelDim.piExp (k : ℂ) = 1 := by
  simp only [MandelDim.piExp]
  rw [show 2 * Real.pi * I * (k : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ) * I) by ring,
    Complex.exp_int_mul_two_pi_mul_I]

private lemma piExp_aux_log_div (z : ℂ) (hz : z ≠ 0) :
    MandelDim.piExp (Complex.log z / (2 * Real.pi * I)) = z := by
  rw [MandelDim.piExp, mul_div_cancel₀ _ Complex.two_pi_I_ne_zero, Complex.exp_log hz]

private lemma piExp_aux_eq_iff {x y : ℂ} :
    MandelDim.piExp x = MandelDim.piExp y ↔ ∃ k : ℤ, x = y + k := by
  have hne : (2 * (Real.pi : ℂ) * I) ≠ 0 := Complex.two_pi_I_ne_zero
  constructor
  · intro h
    rw [MandelDim.piExp] at h
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    refine ⟨m, ?_⟩
    refine mul_left_cancel₀ hne ?_
    rw [hm]; ring
  · rintro ⟨m, rfl⟩
    rw [MandelDim.piExp, MandelDim.piExp, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨m, by ring⟩

/-- For `z ≠ 0`, the imaginary part of `log z / (2πi)` is `-log ‖z‖ / 2π`. -/
private lemma log_div_two_pi_I_im (z : ℂ) :
    (Complex.log z / (2 * Real.pi * I)).im = -(Real.log ‖z‖) / (2 * Real.pi) := by
  rw [Complex.div_im]
  have h1 : (2 * Real.pi * I : ℂ).re = 0 := by simp
  have h2 : (2 * Real.pi * I : ℂ).im = 2 * Real.pi := by simp
  have h3 : Complex.normSq (2 * Real.pi * I : ℂ) = (2 * Real.pi) ^ 2 := by
    rw [Complex.normSq_apply, h1, h2]; ring
  rw [h1, h2, h3, Complex.log_re]
  field_simp
  ring

theorem box_piExp_surj {η : ℝ} {n : ℤ} {ζ : ℂ} (hη : 0 < η)
    (h1 : 2 * Real.exp (-(2 * Real.pi * η)) / 3 < ‖ζ‖)
    (h2 : ‖ζ‖ < 2 * Real.exp (-(2 * Real.pi * η))) :
    ∃! w : ℂ, (n : ℝ) ≤ w.re ∧ w.re < (n : ℝ) + 1 ∧
      η + Real.log (1 / 2) / (2 * Real.pi) < w.im ∧
      w.im < η + Real.log (3 / 2) / (2 * Real.pi) ∧ MandelDim.piExp w = ζ := by
  have hζpos : 0 < ‖ζ‖ := by
    have hp := Real.exp_pos (-(2 * Real.pi * η))
    linarith
  have hζne : ζ ≠ 0 := norm_pos_iff.mp hζpos
  set c : ℝ := 2 * Real.pi * η with hc
  have hcpos : 0 < c := by
    rw [hc]; exact mul_pos (by positivity : (0 : ℝ) < 2 * Real.pi) hη
  -- logarithmic forms of the two side conditions
  have hlog2 : Real.log ‖ζ‖ < Real.log 2 - c := by
    have h := Real.log_lt_log hζpos h2
    have he : Real.log (2 * Real.exp (-(2 * Real.pi * η))) = Real.log 2 - c := by
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp, hc]
      ring
    linarith
  have hlog1 : Real.log 2 - c - Real.log 3 < Real.log ‖ζ‖ := by
    have hpos : (0 : ℝ) < 2 * Real.exp (-(2 * Real.pi * η)) / 3 := by positivity
    have h := Real.log_lt_log hpos h1
    have he : Real.log (2 * Real.exp (-(2 * Real.pi * η)) / 3) = Real.log 2 - c - Real.log 3 := by
      rw [Real.log_div (by positivity) (by norm_num : (3 : ℝ) ≠ 0),
        Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp, hc]
      ring
    linarith
  -- the model preimage `t = log ζ / (2πi)`
  set t : ℂ := Complex.log ζ / (2 * Real.pi * I) with ht
  have htπ : MandelDim.piExp t = ζ := piExp_aux_log_div ζ hζne
  have htim : t.im = -(Real.log ‖ζ‖) / (2 * Real.pi) := log_div_two_pi_I_im ζ
  have hA : η + Real.log (1 / 2) / (2 * Real.pi) < t.im := by
    rw [htim]
    have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    rw [hloghalf, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hsimp : (η + (-Real.log 2) / (2 * Real.pi)) * (2 * Real.pi)
        = 2 * Real.pi * η - Real.log 2 := by
      field_simp; ring
    rw [hsimp, ← hc]
    linarith
  have hB : t.im < η + Real.log (3 / 2) / (2 * Real.pi) := by
    rw [htim]
    have hlog32 : Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num)]
    rw [hlog32, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hsimp : (η + (Real.log 3 - Real.log 2) / (2 * Real.pi)) * (2 * Real.pi)
        = 2 * Real.pi * η + Real.log 3 - Real.log 2 := by
      field_simp; ring
    rw [hsimp, ← hc]
    linarith
  -- choose the integer shift putting the real part in `[n, n+1)`
  have hk : ∃ k : ℤ, (n : ℝ) ≤ t.re + (k : ℝ) ∧ t.re + (k : ℝ) < (n : ℝ) + 1 := by
    refine ⟨n - ⌊t.re⌋, ?_, ?_⟩
    · push_cast
      have h := Int.self_sub_floor t.re
      have hf := Int.fract_nonneg t.re
      linarith
    · push_cast
      have h := Int.self_sub_floor t.re
      have hf := Int.fract_lt_one t.re
      linarith
  obtain ⟨k, hk1, hk2⟩ := hk
  have hre : (t + (k : ℂ)).re = t.re + (k : ℝ) := by simp
  have him : (t + (k : ℂ)).im = t.im := by simp
  have hpi : MandelDim.piExp (t + (k : ℂ)) = ζ := by
    rw [piExp_aux_add, piExp_aux_intCast, mul_one, htπ]
  refine ⟨t + (k : ℂ), ⟨?_, ?_, ?_, ?_, hpi⟩, ?_⟩
  · rw [hre]; exact hk1
  · rw [hre]; exact hk2
  · rw [him]; exact hA
  · rw [him]; exact hB
  · -- uniqueness: any other preimage differs from `t + k` by an integer, which forces it to be `0`
    intro w hw
    obtain ⟨hwre1, hwre2, _hwim1, _hwim2, hwπ⟩ := hw
    have hπeq : MandelDim.piExp w = MandelDim.piExp (t + (k : ℂ)) := by rw [hwπ, hpi]
    obtain ⟨j, hj⟩ := piExp_aux_eq_iff.mp hπeq
    have hjre : (j : ℝ) = w.re - (t + (k : ℂ)).re := by
      have hh := congrArg Complex.re hj
      rw [Complex.add_re] at hh
      have hk' : ((j : ℤ) : ℂ).re = (j : ℝ) := by simp
      linarith [hh, hk']
    have hjlt : j < 1 := by
      have : (j : ℝ) < 1 := by linarith [hjre, hk1, hwre2]
      exact_mod_cast this
    have hjgt : -1 < j := by
      have : (-1 : ℝ) < (j : ℝ) := by linarith [hjre, hwre1, hk2]
      exact_mod_cast this
    have hj0 : j = 0 := by omega
    rw [hj0] at hj
    simpa using hj

end

end Work.Repel
