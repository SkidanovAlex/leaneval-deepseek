import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The anchored Sturm comparison — the *upper* bound

This is the `+ε` companion of `Work.Diff.C.geoCrux.sturm_anchored_lower` (the `-ε` "lower" bound).
If `(log v)' = w` on `[δ,d]` with `w t ≤ cot t + ε / sin t` on `(0,d)` and the anchor
`v δ ≤ exp A · sin δ`, then

`v d ≤ exp A · sin d · (tan (d/2) / tan (δ/2)) ^ ε`.

The comparison function is `Ψ t = log (v t) - log (sin t) - ε log (tan (t/2))`, whose derivative is
`w t - cot t - ε / sin t ≤ 0`; so `Ψ` is *antitone* on `[δ,d]` and `Ψ d ≤ Ψ δ` is the desired
inequality after exponentiation.

The only place where the positivity of `v` is used is at the two endpoints `δ` and `d` (where the
logarithm is exponentiated again), so the hypothesis `0 < v t` for `t` in the *interior* is not
needed: `t ↦ log (v t)` is continuous on `[δ,d]` because it is differentiable there (`hder`).
-/

namespace Work.Diff.C.geoCrux

/-- `d/dt log (tan (t/2)) = 1 / sin t` for `t ∈ (0,π)`. -/
private theorem hasDerivAt_log_tan_half_upper {t : ℝ} (ht : 0 < t) (htπ : t < Real.pi) :
    HasDerivAt (fun s : ℝ => Real.log (Real.tan (s / 2))) (1 / Real.sin t) t := by
  have ht2 : t / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hcos : Real.cos (t / 2) ≠ 0 := (Real.cos_pos_of_mem_Ioo ht2).ne'
  have hsin2 : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have htan : Real.tan (t / 2) ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_ne_zero hsin2.ne' hcos
  have hlin : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have h2 : HasDerivAt (fun s : ℝ => Real.tan (s / 2))
      ((1 / Real.cos (t / 2) ^ 2) * (1 / 2)) t :=
    HasDerivAt.comp t (Real.hasDerivAt_tan hcos) hlin
  have h := h2.log htan
  have hs2 : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    have h' := Real.sin_two_mul (t / 2)
    rwa [show 2 * (t / 2) = t from by ring] at h'
  have hval : ((1 / Real.cos (t / 2) ^ 2) * (1 / 2)) / Real.tan (t / 2) = 1 / Real.sin t := by
    rw [Real.tan_eq_sin_div_cos, hs2]
    field_simp
  rw [hval] at h
  exact h

/-- **Derivative of the upper comparison function** at an interior point: the derivative of
`Ψ t = log (v t) - log (sin t) - ε log (tan (t/2))` is `w t - cot t - ε / sin t`. -/
private theorem psiDeriv_upper {v w : ℝ → ℝ} {ε t : ℝ}
    (hder : HasDerivAt (fun z : ℝ => Real.log (v z)) (w t) t)
    (ht : 0 < t) (htπ : t < Real.pi) :
    HasDerivAt (fun s : ℝ => Real.log (v s) - Real.log (Real.sin s)
      - ε * Real.log (Real.tan (s / 2))) (w t - Real.cot t - ε / Real.sin t) t := by
  have hlogsin : HasDerivAt (fun s : ℝ => Real.log (Real.sin s)) (Real.cot t) t := by
    have h := (Real.hasDerivAt_sin t).log (Real.sin_pos_of_pos_of_lt_pi ht htπ).ne'
    rw [Real.cot_eq_cos_div_sin]
    exact h
  have hlogtan := hasDerivAt_log_tan_half_upper ht htπ
  have hsub := (hder.sub hlogsin).sub (hlogtan.const_mul ε)
  convert hsub using 1
  ring

theorem sturm_anchored_upper {v w : ℝ → ℝ} {ε δ d A : ℝ}
    (hδ : 0 < δ) (hδd : δ < d) (hε : 0 ≤ ε) (hdπ : d < Real.pi)
    (hδpos : 0 < v δ) (hdpos : 0 < v d)
    (hder : ∀ t ∈ Set.Icc δ d, HasDerivAt (fun s : ℝ => Real.log (v s)) (w t) t)
    (hwb : ∀ t ∈ Set.Ioo (0 : ℝ) d, w t ≤ Real.cot t + ε / Real.sin t)
    (hanchor : v δ ≤ Real.exp A * Real.sin δ) :
    v d ≤ Real.exp A * Real.sin d * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε := by
  have hδd' : δ ≤ d := hδd.le
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith)
  have hsd : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi (by linarith) hdπ
  set Ψ : ℝ → ℝ := fun s => Real.log (v s) - Real.log (Real.sin s)
    - ε * Real.log (Real.tan (s / 2)) with hΨ
  have hderΨ : ∀ t ∈ Set.Ioo δ d, HasDerivAt Ψ (w t - Real.cot t - ε / Real.sin t) t := by
    intro t ht
    exact psiDeriv_upper (hder t ⟨ht.1.le, ht.2.le⟩) (lt_trans hδ ht.1) (lt_trans ht.2 hdπ)
  have hcontΨ : ContinuousOn Ψ (Set.Icc δ d) := by
    have h1 : ContinuousOn (fun s : ℝ => Real.log (v s)) (Set.Icc δ d) :=
      fun x hx => ((hder x hx).continuousAt).continuousWithinAt
    have h2 : ContinuousOn (fun s : ℝ => Real.log (Real.sin s)) (Set.Icc δ d) :=
      Real.continuous_sin.continuousOn.log (fun x hx =>
        (Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hδ hx.1)
          (lt_of_le_of_lt hx.2 hdπ)).ne')
    have h3 : ContinuousOn (fun s : ℝ => Real.log (Real.tan (s / 2))) (Set.Icc δ d) := by
      have hsin : ContinuousOn (fun s : ℝ => Real.sin (s / 2)) (Set.Icc δ d) :=
        Real.continuous_sin.comp_continuousOn ((continuous_id.div_const 2).continuousOn)
      have hcos : ContinuousOn (fun s : ℝ => Real.cos (s / 2)) (Set.Icc δ d) :=
        Real.continuous_cos.comp_continuousOn ((continuous_id.div_const 2).continuousOn)
      have hcne : ∀ x ∈ Set.Icc δ d, Real.cos (x / 2) ≠ 0 := fun x hx =>
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).ne'
      have hdiv : ContinuousOn (fun s : ℝ => Real.sin (s / 2) / Real.cos (s / 2))
          (Set.Icc δ d) := hsin.div hcos hcne
      have ht : ContinuousOn (fun s : ℝ => Real.tan (s / 2)) (Set.Icc δ d) := by
        simpa only [Real.tan_eq_sin_div_cos] using hdiv
      exact ht.log (fun x hx => by
        rw [Real.tan_eq_sin_div_cos]
        exact div_ne_zero
          (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])).ne'
          (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩).ne')
    have h4 : ContinuousOn (fun s : ℝ => ε * Real.log (Real.tan (s / 2))) (Set.Icc δ d) :=
      continuousOn_const.mul h3
    rw [hΨ]
    exact (h1.sub h2).sub h4
  have hanti : AntitoneOn Ψ (Set.Icc δ d) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc δ d) hcontΨ ?_ ?_
    · rw [interior_Icc]
      intro x hx
      exact ((hderΨ x hx).differentiableAt).differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hderΨ x hx).deriv]
      have hx0 : x ∈ Set.Ioo (0 : ℝ) d := ⟨lt_trans hδ hx.1, hx.2⟩
      have h1 := hwb x hx0
      linarith
  have hle : Ψ d ≤ Ψ δ :=
    hanti ⟨le_refl δ, hδd'⟩ ⟨hδd', le_refl d⟩ hδd'
  have hle' : Real.log (v d) - Real.log (Real.sin d) - ε * Real.log (Real.tan (d / 2))
      ≤ Real.log (v δ) - Real.log (Real.sin δ) - ε * Real.log (Real.tan (δ / 2)) := hle
  have hlogv : Real.log (v d) ≤ Real.log (v δ) + (Real.log (Real.sin d) - Real.log (Real.sin δ))
      + ε * (Real.log (Real.tan (d / 2)) - Real.log (Real.tan (δ / 2))) := by
    linarith [hle']
  have hanchor' : Real.log (v δ) ≤ A + Real.log (Real.sin δ) := by
    have h1 : Real.log (v δ) ≤ Real.log (Real.exp A * Real.sin δ) :=
      Real.log_le_log hδpos hanchor
    rw [Real.log_mul (Real.exp_pos A).ne' hsδ.ne', Real.log_exp] at h1
    linarith
  have hkey : Real.log (v d) ≤ A + Real.log (Real.sin d)
      + ε * (Real.log (Real.tan (d / 2)) - Real.log (Real.tan (δ / 2))) := by
    linarith [hlogv, hanchor']
  have htanpos : 0 < Real.tan (d / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have htanposδ : 0 < Real.tan (δ / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have hb : 0 < Real.tan (d / 2) / Real.tan (δ / 2) := div_pos htanpos htanposδ
  have hposbig : 0 < Real.exp A * Real.sin d * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε :=
    mul_pos (mul_pos (Real.exp_pos A) hsd) (Real.rpow_pos_of_pos hb ε)
  have htarget_log : Real.log (Real.exp A * Real.sin d
      * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε)
      = A + Real.log (Real.sin d)
        + ε * (Real.log (Real.tan (d / 2)) - Real.log (Real.tan (δ / 2))) := by
    rw [Real.log_mul (mul_ne_zero (Real.exp_pos A).ne' hsd.ne')
        (Real.rpow_pos_of_pos hb ε).ne',
      Real.log_mul (Real.exp_pos A).ne' hsd.ne', Real.log_exp, Real.log_rpow hb,
      Real.log_div htanpos.ne' htanposδ.ne']
  rw [← Real.log_le_log_iff hdpos hposbig, htarget_log]
  exact hkey

end Work.Diff.C.geoCrux
