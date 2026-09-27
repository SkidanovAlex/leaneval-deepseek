import Mathlib
import Submission.Work.Drive.N2Lead.mobius_pushedStar
import Submission.Work.Drive.N2Lead.twistToolkit

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- **`mobius_pushedStar` on an arbitrary compact parameter interval.**
The proof of `mobius_pushedStar` uses only compactness of the parameter interval `Icc (-2) 2`; running
it on `Icc a b` (`a ≤ b`) gives the threshold statement verbatim.  Only the interval and its
nonemptiness witness change. -/
theorem mobius_pushedStarIcc {g : ℝ → Work.Drive.N2Lead.E3} {εs a b : ℝ}
    (hg : ContDiff ℝ 1 g) (hεs : εs = 1 ∨ εs = -1) (hab : a ≤ b)
    (hgx : ∀ w ∈ Set.Icc a b, 0 < deriv (fun u : ℝ => g u 0) w)
    (hgy : ∀ w ∈ Set.Icc a b, 0 < εs * g w 1) :
    ∃ εp₀ : ℝ, 0 < εp₀ ∧ ∀ εp : ℝ, 0 < εp → εp ≤ εp₀ →
      ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        Work.Drive.N2Lead.StarAboutZero (fun t : ℝ => Work.Drive.N2Lead.pushY D εp 1 (g t)) (Set.Icc a b) ∧
          ∀ t ∈ Set.Icc a b,
            εs * ((Work.Drive.N2Lead.pushY D εp 1 (g t)) 0 * deriv (fun u : ℝ => (Work.Drive.N2Lead.pushY D εp 1 (g u)) 1) t
              - (Work.Drive.N2Lead.pushY D εp 1 (g t)) 1 * deriv (fun u : ℝ => (Work.Drive.N2Lead.pushY D εp 1 (g u)) 0) t) < 0 := by
  have hIcc_ne : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  -- the `y`-coordinate of `g` does not vanish on the compact parameter interval
  have habs : ∀ w ∈ Set.Icc a b, |g w 1| = εs * g w 1 := by
    intro w hw
    rcases hεs with rfl | rfl
    · rw [one_mul]; exact abs_of_pos (by linarith [hgy w hw])
    · rw [neg_one_mul]; exact abs_of_neg (by linarith [hgy w hw])
  have hcont_abs : Continuous (fun w : ℝ => |g w 1|) := (continuous_coord hg 1).abs
  obtain ⟨w₀, hw₀mem, hw₀min⟩ :=
    isCompact_Icc.exists_isMinOn hIcc_ne hcont_abs.continuousOn
  have hm_pos : 0 < |g w₀ 1| := by rw [habs w₀ hw₀mem]; exact hgy w₀ hw₀mem
  refine ⟨|g w₀ 1| / 2, by linarith, ?_⟩
  intro εp hεp hεp_le
  -- the whole interval lies in the good side of the band
  have hregion : ∀ w ∈ Set.Icc a b, εp ≤ εs * g w 1 := by
    intro w hw
    have h1 : |g w₀ 1| ≤ |g w 1| := hw₀min hw
    have h2 : 2 * εp ≤ |g w₀ 1| := by linarith
    rw [← habs w hw]; linarith
  -- a bound on the angular rate over the compact interval
  obtain ⟨M, hMnonneg, hMbound⟩ :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ Set.Icc a b, |mobiusRate g w| ≤ M := by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (continuous_mobiusRate hg).continuousOn
    refine ⟨max M 0, le_max_right _ _, fun w hw => ?_⟩
    exact le_trans (by simpa [Real.norm_eq_abs] using hM w hw) (le_max_left _ _)
  -- a strictly positive lower bound on the `x`-derivative over the compact interval
  obtain ⟨t₀, ht₀mem, ht₀min⟩ :=
    isCompact_Icc.exists_isMinOn hIcc_ne (continuous_deriv_coord hg 0).continuousOn
  have hc_pos : 0 < deriv (fun u : ℝ => g u 0) t₀ := hgx t₀ ht₀mem
  have hD₀pos : 0 < M / deriv (fun u : ℝ => g u 0) t₀ + 1 := by positivity
  refine ⟨M / deriv (fun u : ℝ => g u 0) t₀ + 1, hD₀pos, ?_⟩
  intro D hD
  have hDpos : 0 < D := by linarith
  -- the pointwise sign of the pushed angular rate
  have hmain : ∀ t ∈ Set.Icc a b,
      εs * ((pushY D εp 1 (g t)) 0 * deriv (fun u : ℝ => (pushY D εp 1 (g u)) 1) t
        - (pushY D εp 1 (g t)) 1 * deriv (fun u : ℝ => (pushY D εp 1 (g u)) 0) t) < 0 := by
    intro t ht
    have hgt : εp < εs * g t 1 := by
      have h1 : |g w₀ 1| ≤ |g t 1| := hw₀min ht
      have h2 : 2 * εp ≤ |g w₀ 1| := by linarith
      rw [← habs t ht]; linarith
    have hev : ∀ᶠ u in 𝓝 t, εp ≤ εs * g u 1 := by
      have h := ((continuous_const.mul (continuous_coord hg 1)).continuousAt).tendsto
        (Ici_mem_nhds hgt)
      filter_upwards [h] with u hu
      simpa using hu
    -- the pushed coordinates and their derivatives
    have hXd : deriv (fun u : ℝ => (pushY D εp 1 (g u)) 0) t = deriv (fun u : ℝ => g u 0) t := by
      rw [show (fun u : ℝ => (pushY D εp 1 (g u)) 0) = (fun u : ℝ => g u 0) from
        funext (fun u => by simp)]
    have hYd : deriv (fun u : ℝ => (pushY D εp 1 (g u)) 1) t = deriv (fun u : ℝ => g u 1) t := by
      rw [show (fun u : ℝ => (pushY D εp 1 (g u)) 1)
            = (fun u : ℝ => pushProf D εp 1 (g u 1)) from funext (fun u => by simp)]
      exact deriv_pushProf_one_comp_of_sign hεs hεp hev
    have hXv : (pushY D εp 1 (g t)) 0 = g t 0 := by simp
    have hYv : (pushY D εp 1 (g t)) 1 = g t 1 + εs * D := by
      rw [show (pushY D εp 1 (g t)) 1 = pushProf D εp 1 (g t 1) from by simp]
      exact pushProf_one_eq_of_sign hεs hεp (hregion t ht)
    rw [hXd, hYd, hXv, hYv]
    -- the threshold
    have hsq : εs * εs = 1 := by rcases hεs with rfl | rfl <;> norm_num
    have hMt : |mobiusRate g t| ≤ M := hMbound t ht
    have hct : deriv (fun u : ℝ => g u 0) t₀ ≤ deriv (fun u : ℝ => g u 0) t := ht₀min ht
    have heA : εs * mobiusRate g t ≤ M := by
      rcases hεs with rfl | rfl
      · calc (1:ℝ) * mobiusRate g t = mobiusRate g t := one_mul _
          _ ≤ |mobiusRate g t| := le_abs_self _
          _ ≤ M := hMt
      · calc (-1:ℝ) * mobiusRate g t = -mobiusRate g t := neg_one_mul _
          _ ≤ |mobiusRate g t| := neg_le_abs _
          _ ≤ M := hMt
    have hDc : M + deriv (fun u : ℝ => g u 0) t₀ ≤ D * deriv (fun u : ℝ => g u 0) t₀ := by
      have h1 : (M / deriv (fun u : ℝ => g u 0) t₀ + 1) * deriv (fun u : ℝ => g u 0) t₀
          = M + deriv (fun u : ℝ => g u 0) t₀ := by
        rw [add_mul, div_mul_cancel₀ M hc_pos.ne', one_mul]
      calc M + deriv (fun u : ℝ => g u 0) t₀
          = (M / deriv (fun u : ℝ => g u 0) t₀ + 1) * deriv (fun u : ℝ => g u 0) t₀ := h1.symm
        _ ≤ D * deriv (fun u : ℝ => g u 0) t₀ :=
            mul_le_mul_of_nonneg_right hD hc_pos.le
    -- the pushed rate is the original rate minus `D * x'`
    have hkey : εs * (g t 0 * deriv (fun u : ℝ => g u 1) t
        - (g t 1 + εs * D) * deriv (fun u : ℝ => g u 0) t)
        = εs * mobiusRate g t - D * deriv (fun u : ℝ => g u 0) t := by
      simp only [mobiusRate]
      linear_combination (-(D * deriv (fun u : ℝ => g u 0) t)) * hsq
    rw [hkey]
    have hstep : D * deriv (fun u : ℝ => g u 0) t₀ ≤ D * deriv (fun u : ℝ => g u 0) t :=
      mul_le_mul_of_nonneg_left hct hDpos.le
    linarith
  refine ⟨?_, hmain⟩
  -- `StarAboutZero` is the case analysis on the sign of `-εs`
  rcases hεs with rfl | rfl
  · right
    intro t ht
    simpa using hmain t ht
  · left
    intro t ht
    have := hmain t ht
    linarith

end

end Work.Drive.N2Lead
