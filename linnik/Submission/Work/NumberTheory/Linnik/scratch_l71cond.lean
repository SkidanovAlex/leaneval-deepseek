import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_cosconv
import Submission.Work.NumberTheory.Linnik.scratch_convcos

open Real MeasureTheory intervalIntegral Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Linnik

/-- The `g` of Heath-Brown Lemma 7.1: `g(t) = λ(1+tan²θ)(cos ζt - cos θ)` for `|t| ≤ γ` and `0`
outside, where `ζ = λ tan θ` and `γ = θ/ζ`.  (The two branches agree at `|t| = γ` since there
`cos ζt = cos θ`.) -/
noncomputable def extCosG (θ lam t : ℝ) : ℝ :=
  if |t| ≤ θ / (lam * Real.tan θ) then
    lam * (1 + Real.tan θ ^ 2) * (Real.cos ((lam * Real.tan θ) * t) - Real.cos θ)
  else 0

/-- The extremal function `f` of Heath-Brown Lemma 7.1 (the `g*g` of `extCosG`), written in the
closed form of the paper and supported on `[0, 2γ]`. -/
noncomputable def extCosF (θ lam x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x ≤ 2 * (θ / (lam * Real.tan θ)) then
    lam * (1 + Real.tan θ ^ 2) *
      (lam * (1 + Real.tan θ ^ 2) * (θ / (lam * Real.tan θ) - x / 2)
          * Real.cos ((lam * Real.tan θ) * x)
        + lam * (2 * (θ / (lam * Real.tan θ)) - x)
        + Real.sin (2 * θ - (lam * Real.tan θ) * x) / Real.sin (2 * θ)
        - 2 * (1 + Real.sin (θ - (lam * Real.tan θ) * x) / Real.sin θ))
  else 0

theorem extCosG_even (θ lam : ℝ) : ∀ t : ℝ, extCosG θ lam (-t) = extCosG θ lam t := by
  intro t
  rw [extCosG, extCosG, abs_neg]
  by_cases h : |t| ≤ θ / (lam * Real.tan θ)
  · rw [if_pos h, if_pos h]
    have h2 : (lam * Real.tan θ) * (-t) = -((lam * Real.tan θ) * t) := by ring
    rw [h2, Real.cos_neg]
  · rw [if_neg h, if_neg h]

theorem extCosG_supp {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    ∀ t : ℝ, θ / (lam * Real.tan θ) ≤ |t| → extCosG θ lam t = 0 := by
  intro t ht
  rw [extCosG]
  have htanpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1
  have hζpos : 0 < lam * Real.tan θ := mul_pos hlam htanpos
  by_cases h : |t| ≤ θ / (lam * Real.tan θ)
  · rw [if_pos h]
    have hζγ : (lam * Real.tan θ) * (θ / (lam * Real.tan θ)) = θ := by field_simp
    have hteq : |t| = θ / (lam * Real.tan θ) := le_antisymm h ht
    have habs : |(lam * Real.tan θ) * t| = θ := by
      rw [abs_mul, abs_of_pos hζpos, hteq, hζγ]
    have hcos : Real.cos ((lam * Real.tan θ) * t) = Real.cos θ := by
      rw [← Real.cos_abs, habs]
    rw [hcos]
    ring
  · rw [if_neg h]

/-- The `g` of Lemma 7.1 is non-negative. -/
theorem extCosG_nonneg {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (t : ℝ) : 0 ≤ extCosG θ lam t := by
  rw [extCosG]
  by_cases h : |t| ≤ θ / (lam * Real.tan θ)
  · rw [if_pos h]
    have htan : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1
    have hζpos : 0 < lam * Real.tan θ := mul_pos hlam htan
    have hζt : |(lam * Real.tan θ) * t| ≤ θ := by
      have h1 : (lam * Real.tan θ) * (θ / (lam * Real.tan θ)) = θ := by field_simp
      calc |(lam * Real.tan θ) * t| = (lam * Real.tan θ) * |t| := by
              rw [abs_mul, abs_of_pos hζpos]
        _ ≤ (lam * Real.tan θ) * (θ / (lam * Real.tan θ)) := mul_le_mul_of_nonneg_left h (le_of_lt hζpos)
        _ = θ := h1
    have hcos : Real.cos θ ≤ Real.cos ((lam * Real.tan θ) * t) := by
      have h' := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg ((lam * Real.tan θ) * t))
        (by linarith [hθ1, Real.pi_pos]) hζt
      rwa [Real.cos_abs] at h'
    have hA : 0 ≤ lam * (1 + Real.tan θ ^ 2) := by positivity
    exact mul_nonneg hA (by linarith)
  · rw [if_neg h]


/-- The bracket produced by the convolution identity `cosG_conv` equals the closed form of
Heath-Brown Lemma 7.1 (the two differ by the terms re-arranged in `λ(1+tan²θ)X = A·(bracket)`). -/
theorem extCos_convForm {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    let ζ : ℝ := lam * Real.tan θ
    let γ : ℝ := θ / ζ
    ∀ x : ℝ,
      (lam * (1 + Real.tan θ ^ 2)) ^ 2 *
          ((2 * γ - x) / 2 * Real.cos (ζ * x) + Real.sin (2 * θ - ζ * x) / (2 * ζ)
            - 2 * Real.cos θ * (Real.sin θ + Real.sin (θ - ζ * x)) / ζ
            + Real.cos θ ^ 2 * (2 * γ - x))
        = (lam * (1 + Real.tan θ ^ 2)) *
          ((lam * (1 + Real.tan θ ^ 2)) * (γ - x / 2) * Real.cos (ζ * x)
            + lam * (2 * γ - x) + Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
            - 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ)) := by
  intro ζ γ x
  have hζdef : ζ = lam * Real.tan θ := rfl
  have hγdef : γ = θ / ζ := rfl
  rw [hζdef, hγdef]
  have htan : Real.tan θ = Real.sin θ / Real.cos θ := Real.tan_eq_sin_div_cos θ
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθ1, Real.pi_pos]))
  have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hlam : lam ≠ 0 := ne_of_gt hlam
  have htanne : Real.tan θ ≠ 0 := ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1)
  have hlamtan : lam * Real.tan θ ≠ 0 := mul_ne_zero hlam htanne
  have hsin2ne : Real.sin (2 * θ) ≠ 0 := by
    rw [hsin2]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hsin) hcos
  have htan2 : Real.tan θ ^ 2 = Real.sin θ ^ 2 / Real.cos θ ^ 2 := by rw [htan]; ring
  set c := Real.cos ((lam * Real.tan θ) * x) with hcdef
  set s' := Real.sin (2 * θ - (lam * Real.tan θ) * x) with hsdef
  set t' := Real.sin (θ - (lam * Real.tan θ) * x) with htdef
  rw [htan2, htan, hsin2]
  have hpyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hpyth' : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by linarith [hpyth]
  field_simp
  rw [hpyth']
  ring


/-- **The convolution identity for the extremal function of Lemma 7.1**: on `[0,2γ]` the closed
form `extCosF` is the convolution of `extCosG` with itself. -/
theorem extCosF_eq_conv {θ lam x : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (hx : x ∈ Set.Icc 0 (2 * (θ / (lam * Real.tan θ)))) :
    extCosF θ lam x = ∫ s : ℝ, extCosG θ lam s * extCosG θ lam (x - s) := by
  obtain ⟨hx0, hx2⟩ := hx
  set γ : ℝ := θ / (lam * Real.tan θ) with hγdef
  have htanpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1
  have hζpos : 0 < lam * Real.tan θ := mul_pos hlam htanpos
  have hγpos : 0 < γ := by rw [hγdef]; exact div_pos hθ0 hζpos
  have hxγ : x - γ ≤ γ := by linarith
  have hxcanon : x ∈ Set.Icc 0 (2 * γ) := ⟨hx0, by simpa [hγdef] using hx2⟩
  have hA : (lam * (1 + Real.tan θ ^ 2)) = lam * (1 + Real.tan θ ^ 2) := rfl
  rw [hγdef] at hx2
  rw [extCosF, if_pos ⟨hx0, hx2⟩]
  rw [← extCos_convForm (θ := θ) (lam := lam) hθ0 hθ1 hlam x]
  rw [← cosG_conv (θ := θ) (lam := lam) hθ0 hθ1 hlam x]
  -- the integrand of the interval integral agrees with `g s * g (x-s)` on `Ioc (x-γ) γ`
  have hzero_off : ∀ s : ℝ, s ∉ Set.Ioc (x - γ) γ →
      extCosG θ lam s * extCosG θ lam (x - s) = 0 := by
    intro s hs
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs
    rcases hs with hs | hs
    · refine mul_eq_zero.mpr (Or.inr (extCosG_supp hθ0 hθ1 hlam (x - s) ?_))
      rw [abs_of_nonneg (by linarith)]
      linarith
    · refine mul_eq_zero.mpr (Or.inl (extCosG_supp hθ0 hθ1 hlam s ?_))
      rw [abs_of_pos (by linarith)]
      linarith
  have hcongr : ∀ s ∈ Set.Ioc (x - γ) γ,
      ((lam * (1 + Real.tan θ ^ 2) * (Real.cos ((lam * Real.tan θ) * s) - Real.cos θ))
          * (lam * (1 + Real.tan θ ^ 2) * (Real.cos ((lam * Real.tan θ) * (x - s)) - Real.cos θ)))
        = extCosG θ lam s * extCosG θ lam (x - s) := by
    intro s hs
    rw [Set.mem_Ioc] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have hsabs : |s| ≤ γ := by
      rw [abs_le]
      exact ⟨by linarith, hs2⟩
    have hsxabs : |x - s| ≤ γ := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    rw [extCosG, if_pos hsabs, extCosG, if_pos hsxabs]
  rw [intervalIntegral.integral_of_le hxγ]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Ioc (x - γ) γ)
    (f := fun s : ℝ => extCosG θ lam s * extCosG θ lam (x - s)) hzero_off]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s hs => hcongr s hs)


/-- `extCosG` is continuous (the two branches agree at `|t| = γ`, where `cos ζγ = cos θ`). -/
theorem extCosG_continuous {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    Continuous (extCosG θ lam) := by
  have htanpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1
  have hζpos : 0 < lam * Real.tan θ := mul_pos hlam htanpos
  have hγpos : 0 < θ / (lam * Real.tan θ) := div_pos hθ0 hζpos
  have hζγ : (lam * Real.tan θ) * (θ / (lam * Real.tan θ)) = θ := by field_simp
  have hset : {t : ℝ | |t| ≤ θ / (lam * Real.tan θ)}
      = Metric.closedBall (0:ℝ) (θ / (lam * Real.tan θ)) := by
    ext t
    simp [Metric.mem_closedBall, Real.norm_eq_abs]
  refine continuous_if ?_ ?_ ?_
  · intro a ha
    rw [hset] at ha
    have hsphere : a ∈ Metric.sphere (0:ℝ) (θ / (lam * Real.tan θ)) :=
      Metric.frontier_closedBall_subset_sphere ha
    rw [Metric.mem_sphere, dist_zero_right, Real.norm_eq_abs] at hsphere
    have habs : |(lam * Real.tan θ) * a| = θ := by
      rw [abs_mul, abs_of_pos hζpos, hsphere, hζγ]
    have hcos : Real.cos ((lam * Real.tan θ) * a) = Real.cos θ := by
      rw [← Real.cos_abs, habs]
    simp only [hcos, sub_self, mul_zero]
  · rw [hset, (Metric.isClosed_closedBall).closure_eq]
    fun_prop
  · exact continuousOn_const

/-- `extCosG` is integrable. -/
theorem extCosG_integrable {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    Integrable (extCosG θ lam) := by
  have htanpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1
  have hζpos : 0 < lam * Real.tan θ := mul_pos hlam htanpos
  have hγpos : 0 < θ / (lam * Real.tan θ) := div_pos hθ0 hζpos
  refine (extCosG_continuous hθ0 hθ1 hlam).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(θ / (lam * Real.tan θ)))
    (θ / (lam * Real.tan θ))) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  rw [Set.mem_Icc]
  by_contra hc
  rw [not_and_or, not_le, not_le] at hc
  rcases hc with hc | hc
  · exact ht (extCosG_supp hθ0 hθ1 hlam t (by rw [abs_of_neg (by linarith)]; linarith))
  · exact ht (extCosG_supp hθ0 hθ1 hlam t (by rw [abs_of_pos (by linarith)]; linarith))


/-- **Condition 2, first half, for the extremal function of HB Lemma 7.1**: `extCosF ≥ 0` on
`[0, 2γ]` (it is the convolution of two non-negative functions). -/
theorem extCosF_nonneg {θ lam x : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (hx : x ∈ Set.Icc 0 (2 * (θ / (lam * Real.tan θ)))) :
    0 ≤ extCosF θ lam x := by
  rw [extCosF_eq_conv hθ0 hθ1 hlam hx]
  exact MeasureTheory.integral_nonneg
    (fun s => mul_nonneg (extCosG_nonneg hθ0 hθ1 hlam s)
      (extCosG_nonneg hθ0 hθ1 hlam (x - s)))

end Commons.NumberTheory.Linnik
