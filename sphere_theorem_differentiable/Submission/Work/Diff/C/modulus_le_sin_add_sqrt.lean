import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The one-dimensional Sturm/Grönwall comparison for the modulus of a Jacobi field

The strategy (`v := u / sin`, so that `(log v)' ≤ ε / sin`): put

`Ψ t = log u t - log (sin t) - ε log (tan (t/2))`,

whose derivative is `w t - cot t - ε / sin t ≤ 0` (because `d/dt log (tan (t/2)) = 1 / sin t`); hence
`Ψ` is antitone, giving the sharp Grönwall estimate

`u d ≤ u δ · (sin d / sin δ) · (tan (d/2) / tan (δ/2)) ^ ε`

for every `0 < δ < d < π`.  Taking `δ = √ε / 2` (where the asymptotics `|u t - a t| ≤ C t³` are
available and `u δ ≈ a δ`), and using `sin δ ≥ δ (1 - δ²/6)`, `tan (δ/2) ≥ δ/2` and
`tan (d/2) · sin d ≤ 2` (i.e. `tan (d/2) ≤ 2 / sin d`), the estimate becomes

`u d ≤ (a + Cε)(1 + ε/12) · (8/√ε)^ε · (sin d)^{1-ε}`,

and the elementary estimates `rpow_eight_div_sqrt` and `rpow_one_sub_le` turn this into the bound
`a sin d + 8 √ε (a + C)`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Topology

namespace Work.Diff.C

/-- `√ε * √ε = ε`. -/
theorem sqrt_mul_self_eq {ε : ℝ} (hε : 0 ≤ ε) : Real.sqrt ε * Real.sqrt ε = ε := by
  rw [← sq]
  exact Real.sq_sqrt hε

/-- `√ε ≤ 1/4` for `ε ≤ 1/16`. -/
theorem sqrt_le_quarter {ε : ℝ} (hε1 : ε ≤ 1 / 16) : Real.sqrt ε ≤ 1 / 4 := by
  have h1 : Real.sqrt ε ≤ Real.sqrt (1 / 16 : ℝ) := Real.sqrt_le_sqrt hε1
  have h2 : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  linarith [h1, h2.le]

/-- **Derivative of the Grönwall comparison function.**  The derivative of
`Ψ t = log u t - log (sin t) - ε log (tan (t/2))` is `w t - cot t - ε / sin t`. -/
theorem psi_deriv {u w : ℝ → ℝ} {d δ ε t : ℝ} (hδ : 0 < δ)
    (hpos : ∀ s ∈ Set.Ioo (0 : ℝ) d, 0 < u s)
    (hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) d, HasDerivAt (fun z : ℝ => Real.log (u z)) (w s) s)
    (hdπ : d ≤ Real.pi) (ht : t ∈ Set.Ioo δ d) :
    HasDerivAt (fun s : ℝ => Real.log (u s) - Real.log (Real.sin s)
      - ε * Real.log (Real.tan (s / 2))) (w t - Real.cot t - ε / Real.sin t) t := by
  have hpi := Real.pi_pos
  have ht0 : t ∈ Set.Ioo (0 : ℝ) d := ⟨lt_trans hδ ht.1, ht.2⟩
  have htpi : t ∈ Set.Ioo (0 : ℝ) Real.pi := ⟨ht0.1, lt_of_lt_of_le ht0.2 hdπ⟩
  have hlogu := hderiv t ht0
  have hlogsin : HasDerivAt (fun s : ℝ => Real.log (Real.sin s)) (Real.cot t) t := by
    have h1 : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htpi.1 htpi.2
    have h := (Real.hasDerivAt_sin t).log h1.ne'
    rw [Real.cot_eq_cos_div_sin]
    exact h
  have hlogtan : HasDerivAt (fun s : ℝ => Real.log (Real.tan (s / 2))) (1 / Real.sin t) t := by
    have ht2 : t / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [htpi.1], by linarith [htpi.2]⟩
    have hcos : Real.cos (t / 2) ≠ 0 := (Real.cos_pos_of_mem_Ioo ht2).ne'
    have hsin2 : 0 < Real.sin (t / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [htpi.1]) (by linarith [htpi.2])
    have htan : Real.tan (t / 2) ≠ 0 := by
      rw [Real.tan_eq_sin_div_cos]
      exact div_ne_zero hsin2.ne' hcos
    have hlin : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const 2
    have h2 : HasDerivAt (Real.tan ∘ fun s : ℝ => s / 2)
        ((1 / Real.cos (t / 2) ^ 2) * (1 / 2)) t :=
      (Real.hasDerivAt_tan hcos).comp t hlin
    have hcomp : (Real.tan ∘ fun s : ℝ => s / 2) = (fun s : ℝ => Real.tan (s / 2)) := rfl
    rw [hcomp] at h2
    have h := h2.log htan
    convert h using 1
    rw [Real.tan_eq_sin_div_cos]
    have hs2 : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
      have h := Real.sin_two_mul (t / 2)
      rwa [show 2 * (t / 2) = t from by ring] at h
    rw [hs2]
    field_simp
  have hsub := (hlogu.sub hlogsin).sub (hlogtan.const_mul ε)
  convert hsub using 1
  ring

/-- **The elementary `rpow` estimate `s ^ (1 - ε) ≤ s + ε`** for `0 < s ≤ 1`, `0 < ε ≤ 1`. -/
theorem rpow_one_sub_le {ε s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) :
    s ^ (1 - ε) ≤ s + ε := by
  have h1s : -1 ≤ 1 / s - 1 := by
    have h : 0 ≤ 1 / s := by positivity
    linarith
  have hkey : (1 / s) ^ ε ≤ 1 + ε * (1 / s - 1) := by
    have h := rpow_one_add_le_one_add_mul_self (s := 1 / s - 1) h1s (p := ε) hε.le hε1
    have he : 1 + (1 / s - 1) = 1 / s := by ring
    rwa [he] at h
  have hinv : (1 / s) ^ ε = s ^ (-ε) := by
    rw [one_div, Real.inv_rpow hs.le ε]
    exact (Real.rpow_neg hs.le ε).symm
  have hL : s * s ^ (-ε) = s ^ (1 - ε) := by
    rw [show (1 : ℝ) - ε = 1 + (-ε) from by ring, Real.rpow_add hs 1 (-ε), Real.rpow_one]
  have hmul : s * (1 / s) ^ ε ≤ s * (1 + ε * (1 / s - 1)) :=
    mul_le_mul_of_nonneg_left hkey hs.le
  rw [hinv, hL] at hmul
  have hR : s * (1 + ε * (1 / s - 1)) = s + ε * (1 - s) := by
    field_simp
  rw [hR] at hmul
  nlinarith [hmul, hε.le, hs1]

/-- **The exponential factor is at most `1 + 4 √ε`.**  This is the quantitative form of
`exp(ε ∫_δ^d ds/sin s) ≤ (d/δ)^{πε/2} ≤ 1 + C √ε` used in the module docstring. -/
theorem rpow_eight_div_sqrt {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 16) :
    (1 + ε / 12) * (8 / Real.sqrt ε) ^ ε ≤ 1 + 4 * Real.sqrt ε := by
  have hsq : Real.sqrt ε * Real.sqrt ε = ε := sqrt_mul_self_eq hε.le
  have hsqle : Real.sqrt ε ≤ 1 / 4 := sqrt_le_quarter hε1
  have hsqnn : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hbase : 0 < 8 / Real.sqrt ε := by positivity
  -- `log (1/ε) ≤ 2/√ε`
  have hlog1 : Real.log (1 / ε) ≤ 2 / Real.sqrt ε := by
    have h := Real.log_le_rpow_div (x := 1 / ε) (ε := 1 / 2) (by positivity) (by norm_num)
    have h2 : (1 / ε) ^ ((1 : ℝ) / 2) = 1 / Real.sqrt ε := by
      rw [← Real.sqrt_eq_rpow, show (1 : ℝ) / ε = ε⁻¹ by ring, Real.sqrt_inv]
      ring
    rw [h2] at h
    have h3 : (1 / Real.sqrt ε) / (1 / 2) = 2 / Real.sqrt ε := by ring
    linarith [h, h3.le]
  -- `log 8 ≤ 3`
  have hlog8 : Real.log 8 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have h2 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  -- `ε log (1/√ε) = (ε/2) log (1/ε) ≤ √ε`
  have hlog_sqrt : Real.log (1 / Real.sqrt ε) = (1 / 2) * Real.log (1 / ε) := by
    have heq : (1 : ℝ) / Real.sqrt ε = (1 / ε) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, show (1 : ℝ) / ε = ε⁻¹ by ring, Real.sqrt_inv]
      ring
    rw [heq, Real.log_rpow (by positivity : (0 : ℝ) < 1 / ε)]
  have hεdiv : ε * (2 / Real.sqrt ε) = 2 * Real.sqrt ε := by
    have hdiv : ε / Real.sqrt ε = Real.sqrt ε := by
      rw [div_eq_iff (Real.sqrt_pos_of_pos hε).ne']; exact hsq.symm
    calc ε * (2 / Real.sqrt ε) = 2 * (ε / Real.sqrt ε) := by ring
      _ = 2 * Real.sqrt ε := by rw [hdiv]
  have hb1 : ε * Real.log (1 / Real.sqrt ε) ≤ Real.sqrt ε := by
    rw [hlog_sqrt]
    have h := mul_le_mul_of_nonneg_left hlog1 hε.le
    have h3 : ε * (1 / 2 * Real.log (1 / ε)) = (1 / 2) * (ε * Real.log (1 / ε)) := by ring
    rw [h3]
    linarith [h, hεdiv]
  have hb2 : ε * Real.log 8 ≤ (3 / 4) * Real.sqrt ε := by
    have h := mul_le_mul_of_nonneg_left hlog8 hε.le
    have h4 : ε ≤ (1 / 4) * Real.sqrt ε := by nlinarith [hsq, hsqle, hε.le, hsqnn]
    linarith
  have hbound : ε * Real.log (8 / Real.sqrt ε) ≤ (7 / 4) * Real.sqrt ε := by
    have hsplit : Real.log (8 / Real.sqrt ε) = Real.log 8 + Real.log (1 / Real.sqrt ε) := by
      rw [show (8 : ℝ) / Real.sqrt ε = 8 * (1 / Real.sqrt ε) by ring,
        Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by positivity : (1 / Real.sqrt ε) ≠ 0)]
    have h3 : ε * Real.log (8 / Real.sqrt ε)
        = ε * Real.log 8 + ε * Real.log (1 / Real.sqrt ε) := by
      rw [hsplit]; ring
    rw [h3]
    linarith [hb1, hb2]
  -- `log (1 + 3.5 √ε) ≥ (7/4) √ε`
  have hlog35 : (7 / 4) * Real.sqrt ε ≤ Real.log (1 + 3.5 * Real.sqrt ε) := by
    have hy0 : 0 < 1 + 3.5 * Real.sqrt ε := by positivity
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 + 3.5 * Real.sqrt ε) by positivity)
    have h2 : Real.log (1 / (1 + 3.5 * Real.sqrt ε)) = -Real.log (1 + 3.5 * Real.sqrt ε) := by
      rw [one_div, Real.log_inv]
    rw [h2] at h1
    have h3 : (1 : ℝ) - 1 / (1 + 3.5 * Real.sqrt ε)
        = 3.5 * Real.sqrt ε / (1 + 3.5 * Real.sqrt ε) := by
      field_simp
      ring
    have h4 : (7 / 4) * Real.sqrt ε ≤ 3.5 * Real.sqrt ε / (1 + 3.5 * Real.sqrt ε) := by
      rw [le_div_iff₀ hy0]
      have h5 : (7 / 4) * (1 + 3.5 * Real.sqrt ε) ≤ 3.5 := by nlinarith [hsqle]
      nlinarith [h5, hsqnn]
    linarith [h1, h3, h4]
  have hrpow : (8 / Real.sqrt ε) ^ ε ≤ 1 + 3.5 * Real.sqrt ε := by
    rw [Real.rpow_le_iff_le_log hbase (by positivity)]
    exact le_trans hbound hlog35
  calc (1 + ε / 12) * (8 / Real.sqrt ε) ^ ε
      ≤ (1 + ε / 12) * (1 + 3.5 * Real.sqrt ε) :=
        mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ ≤ 1 + 4 * Real.sqrt ε := by nlinarith [hsq, hsqle, hε.le, hε1, hsqnn]

/-! ## The core case `√ε / 2 < d < π` -/

/-- **The Grönwall comparison for `√ε / 2 < d < π`.**  The heart of the proof: the antitone
comparison function `Ψ` gives the sharp bound
`u d ≤ u δ (sin d / sin δ) (tan (d/2)/tan (δ/2))^ε` with `δ = √ε/2`, which is dominated by
`a sin d + 8 √ε (a + C)`. -/
theorem modulus_core {u w : ℝ → ℝ} {a C d ε : ℝ}
    (hd : 0 < d) (hdπ : d < Real.pi) (ha : 0 < a) (hC : 0 ≤ C)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 16)
    (hpos : ∀ t ∈ Set.Ioo (0 : ℝ) d, 0 < u t)
    (hcont : ContinuousOn u (Set.Icc (0 : ℝ) d))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) d, HasDerivAt (fun s : ℝ => Real.log (u s)) (w t) t)
    (hwb : ∀ t ∈ Set.Ioo (0 : ℝ) d, w t ≤ Real.cot t + ε / Real.sin t)
    (hasym : ∀ t ∈ Set.Ioo (0 : ℝ) (min d (Real.sqrt ε)), |u t - a * t| ≤ C * t ^ 3)
    (hδd : Real.sqrt ε / 2 < d) :
    u d ≤ a * Real.sin d + 8 * Real.sqrt ε * (a + C) := by
  have hpi := Real.pi_pos
  have hsqrtpos : 0 < Real.sqrt ε := Real.sqrt_pos_of_pos hε
  have hsqrt_le : Real.sqrt ε ≤ 1 / 4 := sqrt_le_quarter hε1
  set δ : ℝ := Real.sqrt ε / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδlt : δ < Real.sqrt ε := by rw [hδdef]; linarith
  have hδd' : δ < d := hδd
  have hδπ : δ < Real.pi / 2 := by
    rw [hδdef]
    linarith [hsqrt_le, Real.pi_gt_three]
  have hδsq : δ ^ 2 = ε / 4 := by
    rw [hδdef, div_pow, Real.sq_sqrt hε.le]
    norm_num
  by_cases hud : u d ≤ 0
  · have h1 : 0 ≤ a * Real.sin d :=
      mul_nonneg ha.le (Real.sin_nonneg_of_nonneg_of_le_pi hd.le hdπ.le)
    have h2 : 0 < 8 * Real.sqrt ε * (a + C) :=
      mul_pos (by positivity) (by linarith)
    linarith
  push Not at hud
  have hδmem : δ ∈ Set.Ioo (0 : ℝ) (min d (Real.sqrt ε)) := ⟨hδpos, lt_min hδd hδlt⟩
  have huδ_le : u δ ≤ a * δ + C * δ ^ 3 := by
    have h := (abs_le.mp (hasym δ hδmem)).2
    linarith
  have hsind : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd hdπ
  have hsinδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδpos (by linarith)
  have htand : 0 < Real.tan (d / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have htanδ : 0 < Real.tan (δ / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have huδpos : 0 < u δ := hpos δ ⟨hδpos, hδd⟩
  set Ψ : ℝ → ℝ := fun s => Real.log (u s) - Real.log (Real.sin s)
    - ε * Real.log (Real.tan (s / 2)) with hΨdef
  have hΨderiv : ∀ t ∈ Set.Ioo δ d, HasDerivAt Ψ (w t - Real.cot t - ε / Real.sin t) t := by
    intro t ht
    exact psi_deriv hδpos hpos hderiv hdπ.le ht
  have hanti : AntitoneOn Ψ (Set.Icc δ d) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc δ d) ?_ ?_ ?_
    · have hsub : Set.Icc δ d ⊆ Set.Icc (0 : ℝ) d := fun x hx => ⟨le_trans hδpos.le hx.1, hx.2⟩
      have hcontu : ContinuousOn (fun s : ℝ => Real.log (u s)) (Set.Icc δ d) :=
        (hcont.mono hsub).log (fun x hx => by
          rcases eq_or_lt_of_le hx.2 with h | h
          · rw [h]; exact hud.ne'
          · exact (hpos x ⟨lt_of_lt_of_le hδpos hx.1, h⟩).ne')
      have hcontsin : ContinuousOn (fun s : ℝ => Real.log (Real.sin s)) (Set.Icc δ d) :=
        Real.continuous_sin.continuousOn.log (fun x hx =>
          (Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hδpos hx.1)
            (lt_of_le_of_lt hx.2 hdπ)).ne')
      have hconttan : ContinuousOn (fun s : ℝ => Real.log (Real.tan (s / 2))) (Set.Icc δ d) := by
        have hhalf : ContinuousOn (fun s : ℝ => s / 2) (Set.Icc δ d) := continuousOn_id.div_const 2
        have hsin : ContinuousOn (fun s : ℝ => Real.sin (s / 2)) (Set.Icc δ d) :=
          Real.continuous_sin.comp_continuousOn hhalf
        have hcos : ContinuousOn (fun s : ℝ => Real.cos (s / 2)) (Set.Icc δ d) :=
          Real.continuous_cos.comp_continuousOn hhalf
        have hcne : ∀ x ∈ Set.Icc δ d, Real.cos (x / 2) ≠ 0 := fun x hx =>
          (Real.cos_pos_of_mem_Ioo ⟨by linarith [hδpos, hx.1],
            by linarith [hx.2, hdπ]⟩).ne'
        have hdiv : ContinuousOn (fun s : ℝ => Real.sin (s / 2) / Real.cos (s / 2))
            (Set.Icc δ d) := hsin.div hcos hcne
        have htancont : ContinuousOn (fun s : ℝ => Real.tan (s / 2)) (Set.Icc δ d) := by
          simpa only [Real.tan_eq_sin_div_cos] using hdiv
        exact htancont.log (fun x hx =>
          (Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [hδpos, hx.1])
            (by linarith [hx.2, hdπ])).ne')
      exact (hcontu.sub hcontsin).sub (hconttan.const_mul ε)
    · rw [interior_Icc]
      intro x hx
      exact (hΨderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hΨderiv x hx).deriv]
      have hx0 : x ∈ Set.Ioo (0 : ℝ) d := ⟨lt_trans hδpos hx.1, hx.2⟩
      linarith [hwb x hx0]
  have hPsi_le : Ψ d ≤ Ψ δ :=
    hanti ⟨le_refl δ, hδd'.le⟩ ⟨hδd'.le, le_refl d⟩ hδd'.le
  set R : ℝ := u δ * (Real.sin d / Real.sin δ)
    * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    exact mul_pos (mul_pos huδpos (div_pos hsind hsinδ))
      (Real.rpow_pos_of_pos (div_pos htand htanδ) ε)
  have hlogR : Real.log R = Real.log (u δ) + (Real.log (Real.sin d) - Real.log (Real.sin δ))
      + ε * (Real.log (Real.tan (d / 2)) - Real.log (Real.tan (δ / 2))) := by
    have h1 : Real.log (u δ * (Real.sin d / Real.sin δ))
        = Real.log (u δ) + Real.log (Real.sin d / Real.sin δ) :=
      Real.log_mul huδpos.ne' (div_ne_zero hsind.ne' hsinδ.ne')
    have h2 : Real.log (Real.sin d / Real.sin δ) = Real.log (Real.sin d) - Real.log (Real.sin δ) :=
      Real.log_div hsind.ne' hsinδ.ne'
    have h3 : Real.log ((Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε)
        = ε * Real.log (Real.tan (d / 2) / Real.tan (δ / 2)) :=
      Real.log_rpow (div_pos htand htanδ) ε
    have h4 : Real.log (Real.tan (d / 2) / Real.tan (δ / 2))
        = Real.log (Real.tan (d / 2)) - Real.log (Real.tan (δ / 2)) :=
      Real.log_div htand.ne' htanδ.ne'
    rw [hRdef, Real.log_mul (mul_ne_zero huδpos.ne' (div_ne_zero hsind.ne' hsinδ.ne'))
      (Real.rpow_pos_of_pos (div_pos htand htanδ) ε).ne', h1, h2, h3, h4]
  have hlog_le : Real.log (u d) ≤ Real.log R := by
    rw [hlogR]
    have h := hPsi_le
    simp only [hΨdef] at h
    linarith
  have hud_le_R : u d ≤ R := (Real.log_le_log_iff hud hRpos).mp hlog_le
  -- bound `u δ / sin δ`
  have hδ2 : δ ^ 2 ≤ 1 / 64 := by
    rw [hδsq]; linarith [hε1]
  have hR1 : u δ / Real.sin δ ≤ (a + C * ε) * (1 + ε / 12) := by
    have hsinlb : δ * (1 - δ ^ 2 / 6) ≤ Real.sin δ := by
      have h := Real.sin_gt_sub_cube hδpos
      nlinarith [h]
    have hden : 0 < δ * (1 - δ ^ 2 / 6) := by
      have h : δ ^ 2 / 6 < 1 := by linarith [hδ2]
      positivity
    have hnum : 0 ≤ a * δ + C * δ ^ 3 := by positivity
    have h1 : u δ / Real.sin δ ≤ (a * δ + C * δ ^ 3) / Real.sin δ :=
      div_le_div_of_nonneg_right huδ_le hsinδ.le
    have h2 : (a * δ + C * δ ^ 3) / Real.sin δ ≤ (a * δ + C * δ ^ 3) / (δ * (1 - δ ^ 2 / 6)) :=
      div_le_div_of_nonneg_left hnum hden hsinlb
    have h3 : (a * δ + C * δ ^ 3) / (δ * (1 - δ ^ 2 / 6)) = (a + C * δ ^ 2) / (1 - δ ^ 2 / 6) := by
      field_simp
    have h4 : (a + C * δ ^ 2) / (1 - δ ^ 2 / 6) ≤ (a + C * δ ^ 2) * (1 + δ ^ 2 / 3) := by
      have hz : 0 < 1 - δ ^ 2 / 6 := by linarith [hδ2]
      rw [div_le_iff₀ hz]
      have hprod : 1 ≤ (1 + δ ^ 2 / 3) * (1 - δ ^ 2 / 6) := by
        nlinarith [hδ2, sq_nonneg (δ ^ 2)]
      have hnn : 0 ≤ a + C * δ ^ 2 := by positivity
      nlinarith [hprod, hnn]
    have h5 : (a + C * δ ^ 2) * (1 + δ ^ 2 / 3) ≤ (a + C * ε) * (1 + ε / 12) := by
      have hC' : C * δ ^ 2 ≤ C * ε := by
        have : δ ^ 2 ≤ ε := by rw [hδsq]; linarith
        exact mul_le_mul_of_nonneg_left this hC
      have heq : δ ^ 2 / 3 = ε / 12 := by rw [hδsq]; ring
      have h1' : a + C * δ ^ 2 ≤ a + C * ε := by linarith
      have h2' : 1 + δ ^ 2 / 3 ≤ 1 + ε / 12 := by linarith
      exact mul_le_mul h1' h2' (by positivity) (by positivity)
    linarith
  -- bound the second factor
  have htan_le : Real.tan (d / 2) ≤ 2 / Real.sin d := by
    have hcos : 0 < Real.cos (d / 2) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith [hdπ]⟩
    have hsin2 : 0 < Real.sin (d / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hdπ])
    have hsind2 : Real.sin d = 2 * Real.sin (d / 2) * Real.cos (d / 2) := by
      have h := Real.sin_two_mul (d / 2)
      rwa [show 2 * (d / 2) = d from by ring] at h
    have hkey : Real.tan (d / 2) * Real.sin d = 2 * (Real.sin (d / 2)) ^ 2 := by
      rw [Real.tan_eq_sin_div_cos, hsind2]
      field_simp
    have hle2 : 2 * (Real.sin (d / 2)) ^ 2 ≤ 2 := by
      nlinarith [Real.sin_le_one (d / 2), Real.neg_one_le_sin (d / 2)]
    rw [le_div_iff₀ hsind]
    linarith
  have hratio : (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε
      ≤ (4 / (δ * Real.sin d)) ^ ε := by
    have h1 : (Real.tan (d / 2)) ^ ε ≤ (2 / Real.sin d) ^ ε :=
      Real.rpow_le_rpow htand.le htan_le hε.le
    have h2 : (δ / 2) ^ ε ≤ (Real.tan (δ / 2)) ^ ε :=
      Real.rpow_le_rpow (by positivity)
        (le_of_lt (Real.lt_tan (by linarith) (by linarith [hδπ]))) hε.le
    rw [Real.div_rpow htand.le htanδ.le ε]
    have h3 : (Real.tan (d / 2)) ^ ε / (Real.tan (δ / 2)) ^ ε
        ≤ (2 / Real.sin d) ^ ε / (δ / 2) ^ ε :=
      le_trans (div_le_div_of_nonneg_right h1 (by positivity))
        (div_le_div_of_nonneg_left (by positivity) (by positivity) h2)
    have h4 : (2 / Real.sin d) ^ ε / (δ / 2) ^ ε = (4 / (δ * Real.sin d)) ^ ε := by
      rw [← Real.div_rpow (by positivity : (0 : ℝ) ≤ 2 / Real.sin d)
        (by positivity : (0 : ℝ) ≤ δ / 2) ε]
      congr 1
      field_simp
      ring
    linarith [h3, h4.le, h4.ge]
  have h4δ : (4 : ℝ) / δ = 8 / Real.sqrt ε := by
    rw [hδdef]; field_simp; ring
  have hident : Real.sin d * (4 / (δ * Real.sin d)) ^ ε
      = (4 / δ) ^ ε * (Real.sin d) ^ (1 - ε) := by
    rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ δ) ε,
      Real.div_rpow (by norm_num : (0 : ℝ) ≤ 4)
        (by positivity : (0 : ℝ) ≤ δ * Real.sin d) ε,
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ δ) hsind.le,
      Real.rpow_sub hsind 1 ε, Real.rpow_one]
    field_simp
  have hR2 : Real.sin d * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε
      ≤ (8 / Real.sqrt ε) ^ ε * (Real.sin d) ^ (1 - ε) := by
    calc Real.sin d * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε
        ≤ Real.sin d * (4 / (δ * Real.sin d)) ^ ε :=
          mul_le_mul_of_nonneg_left hratio hsind.le
      _ = (4 / δ) ^ ε * (Real.sin d) ^ (1 - ε) := hident
      _ = (8 / Real.sqrt ε) ^ ε * (Real.sin d) ^ (1 - ε) := by rw [h4δ]
  -- assemble
  have hR_bound : R ≤ (a + C * ε) * (1 + ε / 12)
      * ((8 / Real.sqrt ε) ^ ε * (Real.sin d) ^ (1 - ε)) := by
    have hrew : R = (u δ / Real.sin δ)
        * (Real.sin d * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε) := by
      rw [hRdef]; ring
    rw [hrew]
    refine mul_le_mul hR1 hR2 ?_ ?_
    · exact mul_nonneg hsind.le (Real.rpow_nonneg (by positivity) _)
    · exact mul_nonneg (by positivity) (by positivity)
  -- final arithmetic
  have hsind1 : Real.sin d ≤ 1 := Real.sin_le_one d
  have hArith : (a + C * ε) * (1 + ε / 12)
      * ((8 / Real.sqrt ε) ^ ε * (Real.sin d) ^ (1 - ε))
      ≤ a * Real.sin d + 8 * Real.sqrt ε * (a + C) := by
    have hA1 := rpow_eight_div_sqrt hε hε1
    have hA2 := rpow_one_sub_le hε (by linarith [hε1] : ε ≤ 1) hsind hsind1
    have hK : 0 < a + C * ε := by positivity
    have hsqε : Real.sqrt ε * Real.sqrt ε = ε := sqrt_mul_self_eq hε.le
    have hsqεle : Real.sqrt ε ≤ 1 / 4 := sqrt_le_quarter hε1
    have hsqεnn : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
    have hstep1 : (a + C * ε) * ((1 + ε / 12) * (8 / Real.sqrt ε) ^ ε)
        * (Real.sin d) ^ (1 - ε)
        ≤ (a + C * ε) * (1 + 4 * Real.sqrt ε) * (Real.sin d + ε) := by
      have h1 : (1 + ε / 12) * (8 / Real.sqrt ε) ^ ε * (Real.sin d) ^ (1 - ε)
          ≤ (1 + 4 * Real.sqrt ε) * (Real.sin d + ε) :=
        mul_le_mul hA1 hA2 (Real.rpow_nonneg hsind.le _) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 hK.le
      linarith [h2]
    have hstep2 : (1 + 4 * Real.sqrt ε) * (Real.sin d + ε) ≤ Real.sin d + 8 * Real.sqrt ε := by
      have h3 : 4 * Real.sqrt ε * Real.sin d ≤ 4 * Real.sqrt ε := by
        nlinarith [hsqεnn, hsind.le, hsind1]
      have h4 : ε + 4 * ε * Real.sqrt ε ≤ 4 * Real.sqrt ε := by
        nlinarith [hsqε, hsqεle, hε.le, hsqεnn]
      nlinarith [h3, h4]
    have hstep3 : (a + C * ε) * (Real.sin d + 8 * Real.sqrt ε)
        ≤ a * Real.sin d + 8 * Real.sqrt ε * (a + C) := by
      have h1 : ε * Real.sin d + 8 * ε * Real.sqrt ε ≤ 8 * Real.sqrt ε := by
        nlinarith [hsqε, hsqεle, hε.le, hsind.le, hsind1, hsqεnn]
      nlinarith [h1, hC, ha.le]
    have hstep2' : (a + C * ε) * (1 + 4 * Real.sqrt ε) * (Real.sin d + ε)
        ≤ (a + C * ε) * (Real.sin d + 8 * Real.sqrt ε) := by
      have := mul_le_mul_of_nonneg_left hstep2 hK.le
      linarith [this]
    calc (a + C * ε) * (1 + ε / 12)
          * ((8 / Real.sqrt ε) ^ ε * (Real.sin d) ^ (1 - ε))
        = (a + C * ε) * ((1 + ε / 12) * (8 / Real.sqrt ε) ^ ε)
          * (Real.sin d) ^ (1 - ε) := by ring
      _ ≤ (a + C * ε) * (1 + 4 * Real.sqrt ε) * (Real.sin d + ε) := hstep1
      _ ≤ (a + C * ε) * (Real.sin d + 8 * Real.sqrt ε) := hstep2'
      _ ≤ a * Real.sin d + 8 * Real.sqrt ε * (a + C) := hstep3
  linarith [hud_le_R, hR_bound, hArith]

/-- **Sturm/Grönwall comparison for a positive function with `(log u)' ≤ cot + ε/sin`.**
Let `0 < d ≤ π`, `u > 0` on `(0,d)`, `u` continuous on `[0,d]`, `0 < a`, `0 ≤ C`, `0 < ε ≤ 1/16`.
Suppose `(log u)' ≤ cot t + ε / sin t` on `(0,d)` and the model asymptotics with the *fixed*
constant `C` on the interval `(0, min d (√ε))`: `|u t − a t| ≤ C t³`.  Then
`u d ≤ a sin d + 8 √ε (a + C)`.

This is the one-dimensional engine converting the pointwise shape-operator bound
`(log ‖J‖)' ≤ cot t + ε/sin t` (`Work.Diff.C.jld_log_deriv_le_cot_of_shapeOp`) into the modulus bound
for a Jacobi field `‖J‖`.  Route (`v := u/sin`, so `v' ≤ ε v/sin`): integrate the Grönwall inequality
from `δ := √ε`, where `v δ ≤ (a + Cε)(1 + O(ε))` by the fixed-constant asymptotics and
`sin δ ≥ δ(1 − δ²/6)`, and bound the exponential factor by
`exp(ε ∫_δ^d ds/sin s) ≤ (d/δ)^{πε/2} ≤ 1 + 4√ε` (using `ε log(1/ε) ≤ 4√ε` for `ε ≤ 1/16`); the
closed end follows from `ContinuousOn u (Icc 0 d)`. -/
theorem modulus_le_sin_add_sqrt {u w : ℝ → ℝ} {a C d ε : ℝ}
    (hd : 0 < d) (hdπ : d ≤ Real.pi) (ha : 0 < a) (hC : 0 ≤ C)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 16)
    (hpos : ∀ t ∈ Set.Ioo (0 : ℝ) d, 0 < u t)
    (hcont : ContinuousOn u (Set.Icc (0 : ℝ) d))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) d, HasDerivAt (fun s : ℝ => Real.log (u s)) (w t) t)
    (hwb : ∀ t ∈ Set.Ioo (0 : ℝ) d, w t ≤ Real.cot t + ε / Real.sin t)
    (hasym : ∀ t ∈ Set.Ioo (0 : ℝ) (min d (Real.sqrt ε)), |u t - a * t| ≤ C * t ^ 3) :
    u d ≤ a * Real.sin d + 8 * Real.sqrt ε * (a + C) := by
  by_cases hcase : Real.sqrt ε / 2 < d
  · by_cases hdπ' : d < Real.pi
    · exact modulus_core hd hdπ' ha hC hε hε1 hpos hcont hderiv hwb hasym hcase
    · -- `d = π`: the comparison interval degenerates, so take a limit
      have hdeq : d = Real.pi := le_antisymm hdπ (not_lt.mp hdπ')
      subst hdeq
      have hpi := Real.pi_pos
      have hspos : 0 < Real.sqrt ε / 2 := by
        have := Real.sqrt_pos_of_pos hε
        linarith
      have hpt : ∀ t ∈ Set.Ioo (Real.sqrt ε / 2) Real.pi,
          u t ≤ a * Real.sin t + 8 * Real.sqrt ε * (a + C) := by
        intro t ht
        exact modulus_core (lt_trans hspos ht.1) ht.2 ha hC hε hε1
          (fun s hs => hpos s ⟨hs.1, lt_trans hs.2 ht.2⟩)
          (hcont.mono (fun s hs => ⟨hs.1, le_of_lt (lt_of_le_of_lt hs.2 ht.2)⟩))
          (fun s hs => hderiv s ⟨hs.1, lt_trans hs.2 ht.2⟩)
          (fun s hs => hwb s ⟨hs.1, lt_trans hs.2 ht.2⟩)
          (fun s hs => hasym s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_min ht.2.le le_rfl)⟩)
          ht.1
      have hne : (𝓝[Set.Ioo (Real.sqrt ε / 2) Real.pi] Real.pi).NeBot := by
        refine (nhdsWithin_Iio_neBot (le_refl Real.pi)).mono ?_
        rw [nhdsWithin_le_iff]
        exact mem_nhdsWithin.mpr ⟨Set.Ioi (Real.sqrt ε / 2), isOpen_Ioi, hcase,
          fun x hx => hx⟩
      haveI : (𝓝[Set.Ioo (Real.sqrt ε / 2) Real.pi] Real.pi).NeBot := hne
      refine le_of_tendsto_of_tendsto
        (b := 𝓝[Set.Ioo (Real.sqrt ε / 2) Real.pi] Real.pi) (f := u)
        (g := fun t : ℝ => a * Real.sin t + 8 * Real.sqrt ε * (a + C)) ?_ ?_ ?_
      · exact (hcont.continuousWithinAt ⟨le_of_lt hpi, le_refl _⟩).mono_left
          (nhdsWithin_mono _ (fun x hx => ⟨le_of_lt (lt_trans hspos hx.1), le_of_lt hx.2⟩))
      · have hcontg : Continuous fun t : ℝ => a * Real.sin t + 8 * Real.sqrt ε * (a + C) := by
          fun_prop
        exact hcontg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact hpt t ht
  · -- `d ≤ √ε / 2`: the asymptotics at `d` (via continuity) give the claim directly
    have hd_le : d ≤ Real.sqrt ε / 2 := not_lt.mp hcase
    have hd_le_sqrt : d ≤ Real.sqrt ε := by linarith
    have hmin : min d (Real.sqrt ε) = d := min_eq_left hd_le_sqrt
    have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) d, u t ≤ a * t + C * t ^ 3 := by
      intro t ht
      have h := (abs_le.mp (hasym t (by rw [hmin]; exact ht))).2
      linarith
    have hne : (𝓝[Set.Ioo (0 : ℝ) d] d).NeBot := by
      refine (nhdsWithin_Iio_neBot (le_refl d)).mono ?_
      rw [nhdsWithin_le_iff]
      exact mem_nhdsWithin.mpr ⟨Set.Ioi (0 : ℝ), isOpen_Ioi, hd,
        fun x hx => ⟨hx.1, hx.2⟩⟩
    have hle : u d ≤ a * d + C * d ^ 3 := by
      haveI : (𝓝[Set.Ioo (0 : ℝ) d] d).NeBot := hne
      refine le_of_tendsto_of_tendsto (b := 𝓝[Set.Ioo (0 : ℝ) d] d) (f := u)
        (g := fun t : ℝ => a * t + C * t ^ 3) ?_ ?_ ?_
      · exact (hcont.continuousWithinAt ⟨hd.le, le_refl d⟩).mono_left
          (nhdsWithin_mono d Set.Ioo_subset_Icc_self)
      · have hcontg : Continuous fun t : ℝ => a * t + C * t ^ 3 := by fun_prop
        exact hcontg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact hpt t ht
    have hsind : 0 ≤ Real.sin d := Real.sin_nonneg_of_nonneg_of_le_pi hd.le hdπ
    have hd3 : d ^ 3 ≤ 8 * Real.sqrt ε := by
      have hsq : Real.sqrt ε * Real.sqrt ε = ε := sqrt_mul_self_eq hε.le
      have h1 : d ^ 3 ≤ (Real.sqrt ε) ^ 3 := pow_le_pow_left₀ hd.le hd_le_sqrt 3
      have h2 : (Real.sqrt ε) ^ 3 = ε * Real.sqrt ε := by rw [pow_three, hsq]; ring
      have h3 : ε * Real.sqrt ε ≤ 8 * Real.sqrt ε :=
        mul_le_mul_of_nonneg_right (by linarith [hε1] : ε ≤ 8) (Real.sqrt_nonneg ε)
      linarith
    have hsub : d - Real.sin d ≤ d ^ 3 / 6 := by
      have h := Real.sin_gt_sub_cube hd
      linarith
    calc u d ≤ a * d + C * d ^ 3 := hle
      _ = a * Real.sin d + (a * (d - Real.sin d) + C * d ^ 3) := by ring
      _ ≤ a * Real.sin d + (a + C) * (8 * Real.sqrt ε) := by
          have hd3nn : 0 ≤ d ^ 3 := by positivity
          have h1a : d - Real.sin d ≤ d ^ 3 := by linarith [hsub, hd3nn]
          have h1 : a * (d - Real.sin d) ≤ a * d ^ 3 :=
            mul_le_mul_of_nonneg_left h1a ha.le
          have h2 : (a + C) * d ^ 3 ≤ (a + C) * (8 * Real.sqrt ε) :=
            mul_le_mul_of_nonneg_left hd3 (by linarith)
          linarith
      _ = a * Real.sin d + 8 * Real.sqrt ε * (a + C) := by ring

end Work.Diff.C
