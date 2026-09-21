import Mathlib
import Submission.Work.Odd.ball_moment_identity

namespace Work.Odd

open Filter

lemma odd_semicircle_moment_equations {f h x y : ℝ → ℝ} (n : ℕ)
    (hprof : ∀ t ∈ Set.Icc (-(1 / Real.sqrt (1 + (1 - (1 / 10 : ℝ)) ^ 2)))
        (1 / Real.sqrt (1 + (1 - (1 / 10 : ℝ)) ^ 2)), f t = Real.sqrt (1 - t ^ 2))
    (hx_eq : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → x s = 1 / Real.sqrt (1 + s ^ 2))
    (hy_eq : ∀ s : ℝ, 1 - (1 / 10 : ℝ) ≤ s → y s = 1 / Real.sqrt (1 + s ^ 2))
    (hh_zero : ∀ s : ℝ, 1 - (1 / 10 : ℝ) < s → h s = 0) :
    (∀ s : ℝ, 1 ≤ s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2)) =
        (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)) / Real.sqrt (1 + s ^ 2)) ∧
    (∀ s : ℝ, 1 ≤ s →
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) * (t + deriv h s)) = 0) := by
  have h9nn : (0:ℝ) ≤ 1 - (1/10:ℝ) := by norm_num
  -- `h` vanishes identically on the ray `(9/10, ∞)`
  have hh0 : ∀ s : ℝ, 1 ≤ s → h s = 0 := by
    intro s hs
    exact hh_zero s (by linarith)
  -- hence it is (locally) constant at every `s ≥ 1`, so its derivative vanishes there
  have hderiv0 : ∀ s : ℝ, 1 ≤ s → deriv h s = 0 := by
    intro s hs
    have hs9 : (1 - (1/10:ℝ)) < s := by linarith
    have hmem : Set.Ioi (1 - (1/10:ℝ)) ∈ nhds s := isOpen_Ioi.mem_nhds hs9
    have hev : h =ᶠ[nhds s] (fun _ : ℝ => (0:ℝ)) :=
      Filter.eventually_of_mem hmem (fun t ht => hh_zero t ht)
    have hd := Filter.EventuallyEq.deriv_eq hev
    simpa using hd
  -- `f` agrees with the unit semicircle on the relevant interval
  have hfval : ∀ s : ℝ, 1 ≤ s →
      ∀ t ∈ Set.uIcc (-(1 / Real.sqrt (1 + s^2))) (1 / Real.sqrt (1 + s^2)),
      f t = Real.sqrt (1 - t^2) := by
    intro s hs t ht
    have hspos : (0:ℝ) < 1 + s^2 := by positivity
    have hKpos : 0 < Real.sqrt (1 + s^2) := Real.sqrt_pos.mpr hspos
    have hle : -(1 / Real.sqrt (1 + s^2)) ≤ 1 / Real.sqrt (1 + s^2) := by
      have := one_div_pos.mpr hKpos; linarith
    rw [Set.uIcc_of_le hle] at ht
    obtain ⟨ht1, ht2⟩ := Set.mem_Icc.mp ht
    have habs : |t| ≤ 1 / Real.sqrt (1 + s^2) := by
      rw [abs_le]; exact ⟨ht1, ht2⟩
    have h910 : (1 - (1/10:ℝ)) ≤ s := by linarith
    have hsq : (1 - (1/10:ℝ))^2 ≤ s^2 := pow_le_pow_left₀ h9nn h910 2
    have hsqrtle : Real.sqrt (1 + (1 - (1/10:ℝ))^2) ≤ Real.sqrt (1 + s^2) :=
      Real.sqrt_le_sqrt (by linarith)
    have hrpos : 0 < Real.sqrt (1 + (1 - (1/10:ℝ))^2) := Real.sqrt_pos.mpr (by positivity)
    have hbound : 1 / Real.sqrt (1 + s^2) ≤ 1 / Real.sqrt (1 + (1 - (1/10:ℝ))^2) :=
      one_div_le_one_div_of_le hrpos hsqrtle
    have habsr := le_trans habs hbound
    refine hprof t ?_
    rw [Set.mem_Icc]
    exact ⟨by linarith [(abs_le.mp habsr).1], by linarith [(abs_le.mp habsr).2]⟩
  -- consequently `f t ^ 2 = 1 - t ^ 2` on that interval
  have hfsq : ∀ s : ℝ, 1 ≤ s →
      ∀ t ∈ Set.uIcc (-(1 / Real.sqrt (1 + s^2))) (1 / Real.sqrt (1 + s^2)),
      f t ^ 2 = 1 - t^2 := by
    intro s hs t ht
    rw [hfval s hs t ht, Real.sq_sqrt]
    have hspos : (0:ℝ) < 1 + s^2 := by positivity
    have hKpos : 0 < Real.sqrt (1 + s^2) := Real.sqrt_pos.mpr hspos
    have hK1 : 1 ≤ Real.sqrt (1 + s^2) := Real.one_le_sqrt.mpr (by linarith [sq_nonneg s])
    have hle : -(1 / Real.sqrt (1 + s^2)) ≤ 1 / Real.sqrt (1 + s^2) := by
      have := one_div_pos.mpr hKpos; linarith
    rw [Set.uIcc_of_le hle] at ht
    obtain ⟨ht1, ht2⟩ := Set.mem_Icc.mp ht
    have hsmall : 1 / Real.sqrt (1 + s^2) ≤ 1 := by
      rw [div_le_iff₀ hKpos]; linarith
    have habs1 : |t| ≤ 1 := by rw [abs_le]; exact ⟨by linarith, by linarith⟩
    rw [abs_le] at habs1
    nlinarith [habs1.1, habs1.2]
  constructor
  · intro s hs
    have h1 : Set.EqOn
        (fun t => (f t ^ 2 - (s * t + h s) ^ 2) ^ n * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2))
        (fun t => (1 - t ^ 2 - (s * t) ^ 2) ^ n * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2))
        (Set.uIcc (-(1 / Real.sqrt (1 + s^2))) (1 / Real.sqrt (1 + s^2))) := by
      intro t ht
      simp only [hfsq s hs t ht, hh0 s hs, add_zero]
    rw [hx_eq s (by linarith), hy_eq s (by linarith)]
    rw [intervalIntegral.integral_congr h1]
    exact (ball_moment_identity n hs).1
  · intro s hs
    have h2 : Set.EqOn
        (fun t => (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - (s * t + h s) ^ 2) * (t + deriv h s))
        (fun t => (1 - t ^ 2 - (s * t) ^ 2) ^ (n - 1) * Real.sqrt (1 - t ^ 2 - (s * t) ^ 2) * t)
        (Set.uIcc (-(1 / Real.sqrt (1 + s^2))) (1 / Real.sqrt (1 + s^2))) := by
      intro t ht
      simp only [hfsq s hs t ht, hh0 s hs, hderiv0 s hs, add_zero]
    rw [hx_eq s (by linarith), hy_eq s (by linarith)]
    rw [intervalIntegral.integral_congr h2]
    exact (ball_moment_identity n hs).2

end Work.Odd
