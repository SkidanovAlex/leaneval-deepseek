import Mathlib
import Submission.Work.EQ.Defs

open scoped Topology
open Filter

namespace Work.EQ

/-- `0 < eqLam a` for `0 < a < 1`. -/
private theorem eqLam_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; positivity

/-- `eqLam a < 1` for `0 < a < 1`. -/
private theorem eqLam_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]
  linarith

/-- For a stable germ, the linearising parameter satisfies `h u / u → -1` as `u → 0`
(`h 0 = 0` together with `h' 0 = -1`). -/
theorem germ_slope {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (hh : IsStableGerm a h r) :
    Tendsto (fun u : ℂ => h u / u) (𝓝[≠] (0 : ℂ)) (𝓝 (-1)) := by
  have hAn : AnalyticAt ℂ h 0 := hh.2.1 0 (by simp [Metric.mem_ball, hh.1])
  have hd : HasDerivAt h (-1) 0 := by
    have hs := hAn.hasStrictDerivAt
    rw [hh.2.2.2.1] at hs
    exact hs.hasDerivAt
  have h2 : (fun u : ℂ => h u / u) = slope h 0 := by
    funext u
    rw [slope_def_field, hh.2.2.1]
    simp
  rw [h2]
  exact hd.tendsto_slope

/-- For `z` close to `-1`, the real part of `z` is below `-1 + d`. -/
private theorem re_lt_of_dist {z : ℂ} {d : ℝ} (hz : dist z (-1) < d) : z.re < -1 + d := by
  have h5 : |z.re + 1| < d := by
    have h2 : |(z + 1).re| ≤ ‖z + 1‖ := Complex.abs_re_le_norm _
    have h4 : dist z (-1) = ‖z + 1‖ := by simp [dist_eq_norm]
    have h6 : |(z + 1).re| < d := by rw [h4] at hz; exact lt_of_le_of_lt h2 hz
    simpa using h6
  have := (abs_lt.mp h5).2
  linarith

/-- For `z` close to `-1`, the real part of `z` is above `-1 - d`. -/
private theorem lt_re_of_dist {z : ℂ} {d : ℝ} (hz : dist z (-1) < d) : -1 - d < z.re := by
  have h5 : |z.re + 1| < d := by
    have h2 : |(z + 1).re| ≤ ‖z + 1‖ := Complex.abs_re_le_norm _
    have h4 : dist z (-1) = ‖z + 1‖ := by simp [dist_eq_norm]
    have h6 : |(z + 1).re| < d := by rw [h4] at hz; exact lt_of_le_of_lt h2 hz
    simpa using h6
  have := (abs_lt.mp h5).1
  linarith

/-- Small-parameter facts about the stable germ (`Submission/Work/EQ/Defs.lean`).  For `0 < a < 1`
and a stable germ `h` (analytic on `ball 0 r`, `h 0 = 0`, `h' 0 = -1`, real on the real axis),
there is `ε > 0` such that for every real `0 < t < ε`: `t`, `λ t`, `λ² t` (`λ = eqLam a ∈ (0,1)`)
lie in `(-r, r)`; `h t`, `h (λ t)`, `h (λ² t)` are real; and `h t < 0`, `h t < h (λ t)`,
`h (λ t) < h (λ² t)`.  Reason: `h u / u → -1` as `u → 0` (`h 0 = 0`, `h' 0 = -1`), so
`h t = t (h t / t) < 0` for small `t > 0`, while
`h (λt) - h t = t (λ (h (λt)/(λt)) - h t / t) → (1-λ) t > 0`. -/
theorem germPt_smallData {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      |t| < r ∧ |eqLam a * t| < r ∧ |eqLam a * (eqLam a * t)| < r ∧
      (h (t : ℂ)).im = 0 ∧ (h ((eqLam a : ℂ) * (t : ℂ))).im = 0 ∧
      (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * (t : ℂ)))).im = 0 ∧
      (h (t : ℂ)).re < 0 ∧
      (h (t : ℂ)).re < (h ((eqLam a : ℂ) * (t : ℂ))).re ∧
      (h ((eqLam a : ℂ) * (t : ℂ))).re < (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * (t : ℂ)))).re := by
  set s := eqLam a with hsdef
  have hspos : 0 < s := by rw [hsdef]; exact eqLam_pos ha0 ha1
  have hslt : s < 1 := by rw [hsdef]; exact eqLam_lt_one ha0 ha1
  set δ0 := (1 - s) / (2 * (1 + s)) with hδ0def
  have hδ0pos : 0 < δ0 := by rw [hδ0def]; positivity
  have hδ0lt : δ0 < 1 := by
    rw [hδ0def, div_lt_one (by linarith)]
    linarith
  have hkey : δ0 * (1 + s) = (1 - s) / 2 := by rw [hδ0def]; field_simp
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.tendsto_nhdsWithin_nhds (s := ({0} : Set ℂ)ᶜ)).mp (germ_slope hh) δ0 hδ0pos
  refine ⟨min r δ, lt_min hh.1 hδpos, ?_⟩
  intro t ht0 htε
  have e1 : (s : ℂ) * (t : ℂ) = ((s * t : ℝ) : ℂ) := (Complex.ofReal_mul s t).symm
  have e2 : (s : ℂ) * ((s * t : ℝ) : ℂ) = ((s * (s * t) : ℝ) : ℂ) :=
    (Complex.ofReal_mul s (s * t)).symm
  rw [e1, e2]
  have htr : |t| < r := by
    rw [abs_of_pos ht0]; exact lt_of_lt_of_le htε (min_le_left _ _)
  have htδ : |t| < δ := by
    rw [abs_of_pos ht0]; exact lt_of_lt_of_le htε (min_le_right _ _)
  have htr' : t < r := by rwa [abs_of_pos ht0] at htr
  have htδ' : t < δ := by rwa [abs_of_pos ht0] at htδ
  have hst_pos : 0 < s * t := mul_pos hspos ht0
  have hst_le : s * t ≤ t := by
    calc s * t ≤ 1 * t := mul_le_mul_of_nonneg_right (le_of_lt hslt) (le_of_lt ht0)
      _ = t := one_mul t
  have hsst_le : s * (s * t) ≤ s * t := by
    calc s * (s * t) ≤ 1 * (s * t) :=
          mul_le_mul_of_nonneg_right (le_of_lt hslt) (le_of_lt hst_pos)
      _ = s * t := one_mul _
  have hsst_pos : 0 < s * (s * t) := mul_pos hspos hst_pos
  have hstr : |s * t| < r := by
    rw [abs_of_pos hst_pos]; exact lt_of_le_of_lt hst_le htr'
  have hsstr : |s * (s * t)| < r := by
    rw [abs_of_pos hsst_pos]
    exact lt_of_le_of_lt hsst_le (lt_of_le_of_lt hst_le htr')
  have hstδ : s * t < δ := lt_of_le_of_lt hst_le htδ'
  have hsstδ : s * (s * t) < δ := lt_of_le_of_lt hsst_le hstδ
  have him1 : (h (t : ℂ)).im = 0 := hh.2.2.2.2.1 t htr
  have him2 : (h ((s * t : ℝ) : ℂ)).im = 0 := hh.2.2.2.2.1 (s * t) hstr
  have him3 : (h ((s * (s * t) : ℝ) : ℂ)).im = 0 := hh.2.2.2.2.1 (s * (s * t)) hsstr
  -- the slope bounds at the three points `t`, `s t`, `s (s t)`
  have key : ∀ v : ℝ, 0 < v → v < δ →
      dist (h ((v : ℝ) : ℂ) / ((v : ℝ) : ℂ)) (-1) < δ0 ∧
      (h ((v : ℝ) : ℂ)).re = v * (h ((v : ℝ) : ℂ) / ((v : ℝ) : ℂ)).re := by
    intro v hv0 hvδ
    have hvne : ((v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hv0)
    have hdist : dist (((v : ℝ) : ℂ)) (0 : ℂ) < δ := by
      simpa [dist_eq_norm, abs_of_pos hv0] using hvδ
    refine ⟨hδ (x := ((v : ℝ) : ℂ)) (by simpa using hvne) hdist, ?_⟩
    have hmul : ((v : ℝ) : ℂ) * (h ((v : ℝ) : ℂ) / ((v : ℝ) : ℂ)) = h ((v : ℝ) : ℂ) := by
      field_simp
    have h2 := congrArg Complex.re hmul.symm
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using h2
  obtain ⟨hTd, hTe⟩ := key t ht0 htδ'
  obtain ⟨hSd, hSe⟩ := key (s * t) hst_pos hstδ
  obtain ⟨hQd, hQe⟩ := key (s * (s * t)) hsst_pos hsstδ
  have upT : (h (t : ℂ) / (t : ℂ)).re < -1 + δ0 := re_lt_of_dist hTd
  have loS : -1 - δ0 < (h ((s * t : ℝ) : ℂ) / ((s * t : ℝ) : ℂ)).re := lt_re_of_dist hSd
  have upS : (h ((s * t : ℝ) : ℂ) / ((s * t : ℝ) : ℂ)).re < -1 + δ0 := re_lt_of_dist hSd
  have loQ : -1 - δ0 < (h ((s * (s * t) : ℝ) : ℂ) / ((s * (s * t) : ℝ) : ℂ)).re :=
    lt_re_of_dist hQd
  have hpos1 : 0 < s * (h ((s * t : ℝ) : ℂ) / ((s * t : ℝ) : ℂ)).re
      - (h (t : ℂ) / (t : ℂ)).re := by
    have h1 : s * (-1 - δ0) < s * (h ((s * t : ℝ) : ℂ) / ((s * t : ℝ) : ℂ)).re :=
      mul_lt_mul_of_pos_left loS hspos
    have h2 : s * (-1 - δ0) - (-1 + δ0) < s * (-1 - δ0) - (h (t : ℂ) / (t : ℂ)).re :=
      sub_lt_sub_left upT _
    have h3 : 0 < s * (-1 - δ0) - (-1 + δ0) := by nlinarith [hkey]
    linarith
  have hpos2 : 0 < s * (h ((s * (s * t) : ℝ) : ℂ) / ((s * (s * t) : ℝ) : ℂ)).re
      - (h ((s * t : ℝ) : ℂ) / ((s * t : ℝ) : ℂ)).re := by
    have h1 : s * (-1 - δ0) < s * (h ((s * (s * t) : ℝ) : ℂ) / ((s * (s * t) : ℝ) : ℂ)).re :=
      mul_lt_mul_of_pos_left loQ hspos
    have h2 : s * (-1 - δ0) - (-1 + δ0) <
        s * (-1 - δ0) - (h ((s * t : ℝ) : ℂ) / ((s * t : ℝ) : ℂ)).re :=
      sub_lt_sub_left upS _
    have h3 : 0 < s * (-1 - δ0) - (-1 + δ0) := by nlinarith [hkey]
    linarith
  have hneg : (h (t : ℂ)).re < 0 := by
    rw [hTe]
    have h1 : t * (h (t : ℂ) / (t : ℂ)).re < t * (-1 + δ0) := mul_lt_mul_of_pos_left upT ht0
    have h2 : t * (-1 + δ0) < 0 := mul_neg_of_pos_of_neg ht0 (by linarith)
    linarith
  have hstep1 : (h (t : ℂ)).re < (h ((s * t : ℝ) : ℂ)).re := by
    have hpos : 0 < (h ((s * t : ℝ) : ℂ)).re - (h (t : ℂ)).re := by
      rw [hSe, hTe]
      have hring : (s * t) * (h ((s * t : ℝ) : ℂ) / ((s * t : ℝ) : ℂ)).re
          - t * (h (t : ℂ) / (t : ℂ)).re
          = t * (s * (h ((s * t : ℝ) : ℂ) / ((s * t : ℝ) : ℂ)).re
              - (h (t : ℂ) / (t : ℂ)).re) := by ring
      rw [hring]
      exact mul_pos ht0 hpos1
    exact sub_pos.mp hpos
  have hstep2 : (h ((s * t : ℝ) : ℂ)).re < (h ((s * (s * t) : ℝ) : ℂ)).re := by
    have hpos : 0 < (h ((s * (s * t) : ℝ) : ℂ)).re - (h ((s * t : ℝ) : ℂ)).re := by
      rw [hQe, hSe]
      have hring : (s * (s * t)) * (h ((s * (s * t) : ℝ) : ℂ) / ((s * (s * t) : ℝ) : ℂ)).re
          - (s * t) * (h ((s * t : ℝ) : ℂ) / ((s * t : ℝ) : ℂ)).re
          = (s * t) * (s * (h ((s * (s * t) : ℝ) : ℂ) / ((s * (s * t) : ℝ) : ℂ)).re
              - (h ((s * t : ℝ) : ℂ) / ((s * t : ℝ) : ℂ)).re) := by ring
      rw [hring]
      exact mul_pos hst_pos hpos2
    exact sub_pos.mp hpos
  exact ⟨htr, hstr, hsstr, him1, him2, him3, hneg, hstep1, hstep2⟩

end Work.EQ
