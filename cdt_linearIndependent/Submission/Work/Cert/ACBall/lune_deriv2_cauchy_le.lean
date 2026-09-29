import Mathlib
import Submission.Work.Cert.ACBall.LuneChain
import Submission.Work.Cert.ACBall.LuneAnalytic

/-! # The Cauchy second-derivative bound `M2c` of the lune stage

`lM2c st w = ⌈2S²/⌊d²/S⌋⌉` with `d = S − zU − ρ − 1` (in units of `1/S`) is the "Cauchy"
mantissa of the lune stage: on the input disc of the stage (centre `−c`, radius `ρ/S`) the second
derivative of `lune (36/5)` is bounded by `M2c/S`.

We prove `Work.Cert.ACBall.lune_deriv2_cauchy_le`: if the `okM` flag holds (so `‖c‖ ≤ zU/S`) and
`zU + ρ + 1 < S`, then for every `u` with `‖u + c‖ ≤ ρ/S`,

`‖lune''(36/5)(u)‖ ≤ M2c/S`.

Chain of inequalities:
* `‖u‖ ≤ ‖u + c‖ + ‖c‖ ≤ ρ/S + zU/S = (zU+ρ)/S`, hence
  `d/S = (S − zU − ρ − 1)/S ≤ 1 − ‖u‖`;
* Cauchy's estimate (`lune_deriv2_le_cauchy`) gives `‖lune''(u)‖ ≤ 2/(d/S)² = 2S²/d²`;
* `M2c/S ≥ 2S²/d²` because `M2c ≥ 2S²/⌊d²/S⌋ ≥ 2S²/(d²/S) = 2S³/d²` (`dvu_ge`, `md_le`). -/

namespace Work.Cert.ACBall
open Complex

/-- The `okM` flag bounds the centre: `‖c‖ ≤ zU/S`. -/
lemma norm_cIn_le {st : St} {w : LuneW} (hokM : lokM st w = true) :
    ‖cIn st‖ ≤ (w.zU : ℝ) / S := by
  have h := hokM
  simp only [lokM, Bool.and_eq_true, decide_eq_true_eq] at h
  have hzU : 0 ≤ w.zU := h.1.1.1.1.1.1.1.2
  have hcc : st.cr * st.cr + st.ci * st.ci ≤ w.zU * w.zU := h.1.1.1.1.1.1.2
  rw [cIn]
  exact norm_cx_le_of_sq_le st.cr st.ci w.zU hzU hcc

/-- If `lM2c` is not `INF`, the `M2c` branch is taken and `ld`, `ldsq` are positive. -/
lemma lM2c_of_ne_INF (st : St) (w : LuneW) (hC : lM2c st w ≠ INF) :
    lM2c st w = dvu (2 * S) (ldsq st w) ∧ 0 < ld st w ∧ 0 < ldsq st w := by
  unfold lM2c at hC
  by_cases h : (decide (0 < ld st w) && decide (0 < ldsq st w)) = true
  · exact ⟨if_pos h, of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).2⟩
  · rw [if_neg h] at hC
    exact absurd rfl hC

/-- The Cauchy mantissa dominates `2S²/d²`. -/
lemma lM2c_lower (st : St) (w : LuneW) (hld : 0 < ld st w) (hldsq : 0 < ldsq st w) :
    2 / (((ld st w : ℤ) : ℝ) / (S : ℝ)) ^ 2 ≤
      ((dvu (2 * S) (ldsq st w) : ℤ) : ℝ) / (S : ℝ) := by
  have hs : (0 : ℝ) < (S : ℝ) := S_posR
  have hQ : (0 : ℝ) < ((ldsq st w : ℤ) : ℝ) := by exact_mod_cast hldsq
  -- `dvu_ge`: `2S·S/ldsq ≤ dvu (2S) ldsq`
  have hD : 2 * (S : ℝ) * (S : ℝ) / ((ldsq st w : ℤ) : ℝ)
      ≤ ((dvu (2 * S) (ldsq st w) : ℤ) : ℝ) := by
    have h := dvu_ge (a := 2 * S) (b := ldsq st w) hldsq
    push_cast at h
    exact h
  -- `md_le`: `ldsq ≤ ld·ld/S`
  have hQle : ((ldsq st w : ℤ) : ℝ)
      ≤ ((ld st w : ℤ) : ℝ) * ((ld st w : ℤ) : ℝ) / (S : ℝ) :=
    md_le (ld st w) (ld st w)
  have hDsnn : 0 ≤ ((dvu (2 * S) (ldsq st w) : ℤ) : ℝ) :=
    le_trans (div_nonneg (by positivity) hQ.le) hD
  have hD' : 2 * (S : ℝ) * (S : ℝ)
      ≤ ((dvu (2 * S) (ldsq st w) : ℤ) : ℝ) * ((ldsq st w : ℤ) : ℝ) :=
    (div_le_iff₀ hQ).mp hD
  have hQle' : ((ldsq st w : ℤ) : ℝ) * (S : ℝ)
      ≤ ((ld st w : ℤ) : ℝ) * ((ld st w : ℤ) : ℝ) :=
    (le_div_iff₀ hs).mp hQle
  -- multiply: `2S³ ≤ M2c·ld²`
  have h3 : 2 * (S : ℝ) * (S : ℝ) * (S : ℝ)
      ≤ ((dvu (2 * S) (ldsq st w) : ℤ) : ℝ) * (((ld st w : ℤ) : ℝ) * ((ld st w : ℤ) : ℝ)) := by
    have ha : 2 * (S : ℝ) * (S : ℝ) * (S : ℝ)
        ≤ ((dvu (2 * S) (ldsq st w) : ℤ) : ℝ) * (((ldsq st w : ℤ) : ℝ) * (S : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_right hD' hs.le]
    have hb : ((dvu (2 * S) (ldsq st w) : ℤ) : ℝ) * (((ldsq st w : ℤ) : ℝ) * (S : ℝ))
        ≤ ((dvu (2 * S) (ldsq st w) : ℤ) : ℝ) * (((ld st w : ℤ) : ℝ) * ((ld st w : ℤ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hQle' hDsnn
    linarith [ha, hb]
  have hL2 : (0 : ℝ) < ((ld st w : ℤ) : ℝ) ^ 2 := by positivity
  have heq : 2 / (((ld st w : ℤ) : ℝ) / (S : ℝ)) ^ 2
      = 2 * (S : ℝ) ^ 2 / ((ld st w : ℤ) : ℝ) ^ 2 := by
    rw [div_pow]; field_simp
  rw [heq, div_le_div_iff₀ hL2 hs]
  nlinarith [h3]

theorem lune_deriv2_cauchy_le (st : St) (w : LuneW) (hokM : lokM st w = true) (hrho : 0 ≤ st.rho)
    (hzU : w.zU + st.rho + 1 < S) (hC : lM2c st w ≠ INF) {u : ℂ}
    (hu : ‖u - (-(cIn st))‖ ≤ (st.rho : ℝ) / S) :
    ‖deriv (deriv (Submission.CDTPlan.lune (36 / 5))) u‖ ≤ (lM2c st w : ℝ) / S := by
  obtain ⟨hM2c, hldpos, hldsqpos⟩ := lM2c_of_ne_INF st w hC
  have hcIn := norm_cIn_le (st := st) (w := w) hokM
  have hspos : (0 : ℝ) < (S : ℝ) := S_posR
  have hdpos : 0 < ((ld st w : ℤ) : ℝ) / (S : ℝ) :=
    div_pos (by exact_mod_cast hldpos) hspos
  -- `‖u‖ ≤ (zU + ρ)/S`
  have hnu : ‖u‖ ≤ ((w.zU + st.rho : ℤ) : ℝ) / (S : ℝ) := by
    have h1 : ‖u‖ ≤ ‖u - (-(cIn st))‖ + ‖cIn st‖ := by
      have hsplit : u = (u - (-(cIn st))) + (-(cIn st)) := by ring
      rw [hsplit]
      simpa using norm_add_le (u - (-(cIn st))) (-(cIn st))
    calc ‖u‖ ≤ ‖u - (-(cIn st))‖ + ‖cIn st‖ := h1
      _ ≤ (st.rho : ℝ) / (S : ℝ) + (w.zU : ℝ) / (S : ℝ) := add_le_add hu hcIn
      _ = ((w.zU + st.rho : ℤ) : ℝ) / (S : ℝ) := by push_cast; ring
  -- `d/S ≤ 1 − ‖u‖`
  have hdle : ((ld st w : ℤ) : ℝ) / (S : ℝ) ≤ 1 - ‖u‖ := by
    have h2 : ((ld st w : ℤ) : ℝ) ≤ (S : ℝ) - ((w.zU + st.rho : ℤ) : ℝ) := by
      simp only [ld]; push_cast; linarith
    calc ((ld st w : ℤ) : ℝ) / (S : ℝ)
        ≤ ((S : ℝ) - ((w.zU + st.rho : ℤ) : ℝ)) / (S : ℝ) :=
          div_le_div_of_nonneg_right h2 hspos.le
      _ = 1 - ((w.zU + st.rho : ℤ) : ℝ) / (S : ℝ) := by
          rw [sub_div, div_self hspos.ne']
      _ ≤ 1 - ‖u‖ := by linarith [hnu]
  have hlt : ‖u‖ < 1 := by linarith [hdle, hdpos]
  have hfinal : 2 / (((ld st w : ℤ) : ℝ) / (S : ℝ)) ^ 2 ≤ (lM2c st w : ℝ) / S := by
    rw [hM2c]
    exact lM2c_lower st w hldpos hldsqpos
  exact le_trans (lune_deriv2_le_cauchy hlt hdpos hdle) hfinal

end Work.Cert.ACBall
