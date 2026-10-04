import Mathlib
import Submission.Work.Diff.C.geoCrux.rauch_sphere_map

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.geoCrux.sharp

/-- **The anchored Sturm comparison, with the anchor only at `δ`.**

This is `Work.Diff.C.geoCrux.modulus_anchored` with the hypothesis `0 < v t` for *all*
`t ∈ (0,d)` weakened to `0 < v δ` and `0 < v d`.  The interior positivity is never used in the
argument: `t ↦ log (v t)` is continuous on `[δ,d]` because it is differentiable there
(`hder`), so the comparison function `Ψ` is continuous on `[δ,d]` and has nonpositive derivative
on `(δ,d)`; only the *endpoint* logarithms are exponentiated, and those are justified by
`hδpos`/`hdpos`.  (The hypothesis is genuinely weaker: `v := 1` on `[δ,c)` and `v := -1` on
`[c,d]` for `δ < c < d` satisfies all the hypotheses with `log ∘ v ≡ 0`, but not `0 < v t` on the
whole interior.) -/
theorem modulus_anchored_pos {v w : ℝ → ℝ} {ε δ d A : ℝ}
    (hδ : 0 < δ) (hδd : δ < d) (hε : 0 ≤ ε) (hdπ : d < Real.pi)
    (hδpos : 0 < v δ) (hdpos : 0 < v d)
    (hder : ∀ t ∈ Set.Icc δ d, HasDerivAt (fun s : ℝ => Real.log (v s)) (w t) t)
    (hwb : ∀ t ∈ Set.Ioo (0 : ℝ) d, w t ≤ Real.cot t + ε / Real.sin t)
    (hanchor : v δ ≤ Real.exp A * Real.sin δ) :
    v d ≤ Real.exp A * Real.sin d * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε := by
  have hδd' : δ ≤ d := hδd.le
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith)
  have hsd : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi (by linarith) hdπ
  have hvd : 0 < v δ := hδpos
  set Ψ : ℝ → ℝ := fun s => Real.log (v s) - Real.log (Real.sin s)
    - ε * Real.log (Real.tan (s / 2)) with hΨ
  have hderΨ : ∀ t ∈ Set.Ioo δ d, HasDerivAt Ψ (w t - Real.cot t - ε / Real.sin t) t := by
    intro t ht
    exact Work.Diff.C.geoCrux.psiDeriv_anchored (v := v) (w := w) (ε := ε)
      (hder t ⟨ht.1.le, ht.2.le⟩) (lt_trans hδ ht.1) (lt_trans ht.2 hdπ)
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
      have hspos : 0 < Real.sin x :=
        Real.sin_pos_of_pos_of_lt_pi hx0.1 (lt_of_lt_of_le hx0.2 hdπ.le)
      have h1 := hwb x hx0
      have h2 : 0 ≤ ε / Real.sin x := div_nonneg hε hspos.le
      linarith
  have hle : Ψ d ≤ Ψ δ :=
    hanti ⟨le_refl δ, hδd'⟩ ⟨hδd', le_refl d⟩ hδd'
  have hle' : Real.log (v d) - Real.log (Real.sin d) - ε * Real.log (Real.tan (d / 2))
      ≤ Real.log (v δ) - Real.log (Real.sin δ) - ε * Real.log (Real.tan (δ / 2)) := hle
  have hlogv : Real.log (v d) ≤ Real.log (v δ) + (Real.log (Real.sin d) - Real.log (Real.sin δ))
      + ε * (Real.log (Real.tan (d / 2)) - Real.log (Real.tan (δ / 2))) := by linarith
  have htanpos : 0 < Real.tan (d / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have htanposδ : 0 < Real.tan (δ / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  have htarget_log : Real.log (v δ * (Real.sin d / Real.sin δ)
      * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε)
      = Real.log (v δ) + (Real.log (Real.sin d) - Real.log (Real.sin δ))
        + ε * (Real.log (Real.tan (d / 2)) - Real.log (Real.tan (δ / 2))) := by
    have hb : 0 < Real.tan (d / 2) / Real.tan (δ / 2) := div_pos htanpos htanposδ
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul hvd.ne' (by positivity),
      Real.log_div hsd.ne' hsδ.ne',
      Real.log_rpow hb,
      Real.log_div htanpos.ne' htanposδ.ne']
  have hprod : v d ≤ v δ * (Real.sin d / Real.sin δ)
      * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε := by
    rw [← Real.log_le_log_iff hdpos (by positivity)]
    rw [htarget_log]
    exact hlogv
  have hfinal : v δ * (Real.sin d / Real.sin δ)
      * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε
      ≤ Real.exp A * Real.sin d * (Real.tan (d / 2) / Real.tan (δ / 2)) ^ ε := by
    have h1 : v δ * (Real.sin d / Real.sin δ) ≤ Real.exp A * Real.sin d := by
      have h2 : v δ / Real.sin δ ≤ Real.exp A := by
        rw [div_le_iff₀ hsδ]
        exact hanchor
      have h3 : v δ * (Real.sin d / Real.sin δ) = (v δ / Real.sin δ) * Real.sin d := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_right h2 hsd.le
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by positivity) _)
  linarith [hprod, hfinal]

end Work.Diff.C.geoCrux.sharp
