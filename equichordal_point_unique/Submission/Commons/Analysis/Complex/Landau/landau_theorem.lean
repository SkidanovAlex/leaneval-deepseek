import Mathlib
import Submission.Commons.Analysis.Complex.rouche_simple_zero

open scoped Topology
open Metric Set Filter

namespace Commons.Analysis.Complex.Landau



private lemma norm_le_of_mem_segment_zero {z w : ℂ} (hw : w ∈ segment ℝ (0:ℂ) z) : ‖w‖ ≤ ‖z‖ := by
  rw [segment_eq_image] at hw
  obtain ⟨θ, hθ, rfl⟩ := hw
  simp only [smul_zero, zero_add]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
  exact mul_le_of_le_one_left (norm_nonneg z) hθ.2

private lemma norm_deriv_sub_one_le {h : ℂ → ℂ}
    (hh : ∀ z ∈ Metric.ball (0:ℂ) 1, AnalyticAt ℂ h z) (hd0 : deriv h 0 = 1)
    (hbound : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖deriv h z‖ ≤ 2) :
    ∀ z ∈ Metric.ball (0:ℂ) 1, ‖deriv h z - 1‖ ≤ 3 * ‖z‖ := by
  intro z hz
  have hgd : DifferentiableOn ℂ (fun w => deriv h w - 1) (Metric.ball (0:ℂ) 1) := by
    intro w hw
    exact ((AnalyticAt.differentiableAt (AnalyticAt.deriv (hh w hw))).sub_const 1).differentiableWithinAt
  have hmaps : MapsTo (fun w => deriv h w - 1) (Metric.ball (0:ℂ) 1)
      (Metric.closedBall ((deriv h 0) - 1) 3) := by
    intro w hw
    have hw3 : ‖deriv h w - 1‖ ≤ 3 := by
      calc ‖deriv h w - 1‖ ≤ ‖deriv h w‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 + 1 := by
              refine add_le_add (hbound w hw) ?_
              rw [norm_one]
        _ = 3 := by norm_num
    rw [Metric.mem_closedBall, dist_eq_norm, hd0]
    simpa using hw3
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball (c:=0) (R₁:=1) (R₂:=3) hgd hmaps hz
  simpa [dist_eq_norm, hd0, mul_comm] using hsch

private lemma norm_sub_id_le {h : ℂ → ℂ}
    (hh : ∀ z ∈ Metric.ball (0:ℂ) 1, AnalyticAt ℂ h z) (h0 : h 0 = 0) (hd0 : deriv h 0 = 1)
    (hbound : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖deriv h z‖ ≤ 2) :
    ∀ z ∈ Metric.ball (0:ℂ) 1, ‖h z - z‖ ≤ 3 * ‖z‖^2 := by
  intro z hz
  have hzlt : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hdiff : ∀ w ∈ segment ℝ (0:ℂ) z, DifferentiableAt ℂ (fun y => h y - y) w := by
    intro w hw
    have hwle := norm_le_of_mem_segment_zero hw
    have hwball : w ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; linarith
    exact (AnalyticAt.differentiableAt (hh w hwball)).sub differentiableAt_id
  have hbnd : ∀ w ∈ segment ℝ (0:ℂ) z, ‖deriv (fun y => h y - y) w‖ ≤ 3 * ‖z‖ := by
    intro w hw
    have hwle := norm_le_of_mem_segment_zero hw
    have hwball : w ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; linarith
    have hder : deriv (fun y => h y - y) w = deriv h w - 1 := by
      change deriv (h - id) w = deriv h w - 1
      rw [deriv_sub (AnalyticAt.differentiableAt (hh w hwball)) differentiableAt_id, deriv_id]
    rw [hder]
    have := norm_deriv_sub_one_le hh hd0 hbound w hwball
    linarith
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbnd (convex_segment (0:ℂ) z)
      (left_mem_segment ℝ (0:ℂ) z) (right_mem_segment ℝ (0:ℂ) z)
  simpa [h0, sub_zero, sq, mul_assoc] using hmain

private theorem normalized_disc_subset {h : ℂ → ℂ}
    (hh : ∀ z ∈ Metric.ball (0:ℂ) 1, AnalyticAt ℂ h z) (h0 : h 0 = 0) (hd0 : deriv h 0 = 1)
    (hbound : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖deriv h z‖ ≤ 2) :
    Metric.ball (0:ℂ) (1/12) ⊆ h '' (Metric.ball (0:ℂ) 1) := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  simp only [sub_zero] at hw
  rw [Set.mem_image]
  have hquad := norm_sub_id_le hh h0 hd0 hbound
  have hR : (0:ℝ) < 1/6 := by norm_num
  have haw : ‖w‖ < 1/6 := by linarith
  have hsphere : ∀ z ∈ Metric.sphere (0:ℂ) (1/6), ‖h z - z‖ < ‖z - w‖ := by
    intro z hz
    have hznorm : ‖z‖ = 1/6 := by
      rw [Metric.mem_sphere, dist_eq_norm] at hz; simpa using hz
    have hzball : z ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; rw [hznorm]; norm_num
    have h1 : ‖h z - z‖ ≤ 3 * ‖z‖^2 := hquad z hzball
    have hz2 : ‖z‖^2 = 1/36 := by rw [hznorm]; norm_num
    have h1' : ‖h z - z‖ ≤ 1/12 := by rw [hz2] at h1; linarith
    have h2 : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := (abs_le.mp (abs_norm_sub_norm_le z w)).2
    have h3 : (1:ℝ)/12 < ‖z - w‖ := by rw [hznorm] at h2; linarith
    linarith
  have hf : DifferentiableOn ℂ (fun u : ℂ => u - w) (Metric.closedBall (0:ℂ) (1/6)) :=
    differentiableOn_id.sub_const w
  have hfc : ContinuousOn (fun u : ℂ => u - w) (Metric.closedBall (0:ℂ) (1/6)) := hf.continuousOn
  have hg : DifferentiableOn ℂ (fun u : ℂ => h u - u) (Metric.closedBall (0:ℂ) (1/6)) := by
    intro u hu
    have hu' : u ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hu
      simp only [sub_zero] at hu
      rw [Metric.mem_ball, dist_eq_norm]; simp only [sub_zero]; linarith
    exact ((AnalyticAt.differentiableAt (hh u hu')).sub differentiableAt_id).differentiableWithinAt
  have hgc : ContinuousOn (fun u : ℂ => h u - u) (Metric.closedBall (0:ℂ) (1/6)) := hg.continuousOn
  have hf1 : (fun u : ℂ => u - w) w = 0 := by simp
  have hder : deriv (fun u : ℂ => u - w) w ≠ 0 := by
    have h1 : deriv (fun u : ℂ => u - w) w = 1 := by
      change deriv (fun u : ℂ => id u - w) w = 1
      rw [deriv_sub_const, deriv_id]
    rw [h1]; norm_num
  have hfonly : ∀ z ∈ Metric.ball (0:ℂ) (1/6), (fun u : ℂ => u - w) z = 0 → z = w := by
    intro z hz hz0
    exact sub_eq_zero.mp hz0
  obtain ⟨z, hz, hzw, _⟩ :=
    Commons.Analysis.Complex.rouche_simple_zero hR haw hf hfc hg hgc hsphere hf1 hder hfonly
  refine ⟨z, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    simp only [sub_zero]
    have := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at this
    simp only [sub_zero] at this
    linarith
  · have : (z - w) + (h z - z) = 0 := hzw
    linear_combination this


private lemma scaled_disc_subset {H : ℂ → ℂ}
    (hH : ∀ w ∈ Metric.ball (0:ℂ) 1, AnalyticAt ℂ H w) (h0 : H 0 = 0)
    (hd0 : deriv H 0 ≠ 0)
    (hbd : ∀ w ∈ Metric.ball (0:ℂ) 1, ‖deriv H w‖ ≤ 2 * ‖deriv H 0‖) :
    Metric.ball (0:ℂ) (‖deriv H 0‖ / 12) ⊆ H '' Metric.ball (0:ℂ) 1 := by
  set k : ℂ → ℂ := fun w => H w / deriv H 0 with hk
  have hdk : ∀ w, deriv k w = deriv H w / deriv H 0 := fun w => by rw [hk, deriv_div_const]
  have han : ∀ w ∈ Metric.ball (0:ℂ) 1, AnalyticAt ℂ k w := by
    intro w hw; rw [hk]; exact (hH w hw).div_const
  have hk0 : k 0 = 0 := by rw [hk]; simp [h0]
  have hdk0 : deriv k 0 = 1 := by rw [hdk]; field_simp
  have hbnd : ∀ w ∈ Metric.ball (0:ℂ) 1, ‖deriv k w‖ ≤ 2 := by
    intro w hw
    rw [hdk, norm_div]
    rw [div_le_iff₀ (norm_pos_iff.mpr hd0)]
    exact hbd w hw
  have hnorm := normalized_disc_subset han hk0 hdk0 hbnd
  intro v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  have hv' : v / deriv H 0 ∈ Metric.ball (0:ℂ) (1/12) := by
    rw [Metric.mem_ball, dist_zero_right, norm_div]
    rw [div_lt_iff₀ (norm_pos_iff.mpr hd0)]
    linarith
  obtain ⟨w, hw, hwk⟩ := hnorm hv'
  refine ⟨w, hw, ?_⟩
  have h3 : H w / deriv H 0 = v / deriv H 0 := by
    have hh3 := hwk
    rw [hk] at hh3
    simpa using hh3
  have h2 : H w = v := by
    field_simp at h3; exact h3
  exact h2

private lemma landau_disc_subset_of_deriv_le {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r)
    (han : ∀ w ∈ Metric.ball (0:ℂ) 1, AnalyticAt ℂ f (z₀ + (r : ℂ) * w))
    (hfz : deriv f z₀ ≠ 0)
    (hbd : ∀ w ∈ Metric.ball (0:ℂ) 1, ‖deriv f (z₀ + (r : ℂ) * w)‖ ≤ 2 * ‖deriv f z₀‖)
    (hmaps : ∀ w ∈ Metric.ball (0:ℂ) 1, z₀ + (r : ℂ) * w ∈ Metric.ball (0:ℂ) 1) :
    Metric.ball (f z₀) (r * ‖deriv f z₀‖ / 12) ⊆ f '' (Metric.ball (0:ℂ) 1) := by
  set φ : ℂ → ℂ := fun w => z₀ + (r : ℂ) * w with hφ
  have hφan : ∀ w, AnalyticAt ℂ φ w := by
    intro w
    rw [hφ]
    exact analyticAt_const.add (AnalyticAt.mul (analyticAt_const (v := (r:ℂ))) analyticAt_id)
  set H : ℂ → ℂ := fun w => f (φ w) - f z₀ with hH
  have hH_an : ∀ w ∈ Metric.ball (0:ℂ) 1, AnalyticAt ℂ H w := by
    intro w hw
    rw [hH]
    exact ((AnalyticAt.comp (g := f) (f := φ) (x := w) (han w hw) (hφan w))).sub analyticAt_const
  have hH0 : H 0 = 0 := by rw [hH]; simp [hφ]
  have hφderiv : ∀ w, deriv φ w = (r:ℂ) := by
    intro w
    rw [hφ, deriv_const_add]
    rw [deriv_const_mul _ differentiableAt_id]
    simp
  have hHderiv : ∀ w ∈ Metric.ball (0:ℂ) 1, deriv H w = deriv f (φ w) * (r:ℂ) := by
    intro w hw
    have hfd : DifferentiableAt ℂ f (φ w) := (han w hw).differentiableAt
    have hφd : DifferentiableAt ℂ φ w := (hφan w).differentiableAt
    have h1 : deriv H w = deriv (fun w => f (φ w)) w := by
      rw [hH]
      exact deriv_sub_const (f := fun w => f (φ w)) (f z₀)
    rw [h1]
    change deriv (f ∘ φ) w = deriv f (φ w) * (r:ℂ)
    rw [deriv_comp w hfd hφd, hφderiv]
  have hderiv0 : deriv H 0 = deriv f z₀ * (r:ℂ) := by
    rw [hHderiv 0 (by simp [Metric.mem_ball])]
    simp [hφ]
  have hd0ne : deriv H 0 ≠ 0 := by
    rw [hderiv0]
    exact mul_ne_zero hfz (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))
  have hrnorm : ‖(r:ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hbdH : ∀ w ∈ Metric.ball (0:ℂ) 1, ‖deriv H w‖ ≤ 2 * ‖deriv H 0‖ := by
    intro w hw
    rw [hHderiv w hw, hderiv0, norm_mul, norm_mul, hrnorm]
    nlinarith [hbd w hw, norm_nonneg (deriv f (φ w)), norm_nonneg (deriv f z₀), hr]
  have hdisc := scaled_disc_subset hH_an hH0 hd0ne hbdH
  rw [hderiv0, norm_mul, hrnorm] at hdisc
  have hdisc' : Metric.ball (0:ℂ) (r * ‖deriv f z₀‖ / 12) ⊆ H '' Metric.ball (0:ℂ) 1 := by
    convert hdisc using 2
    ring
  intro v hv
  rw [Set.mem_image]
  have hv2 : v - f z₀ ∈ Metric.ball (0:ℂ) (r * ‖deriv f z₀‖ / 12) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hv
  obtain ⟨w, hw, hwH⟩ := hdisc' hv2
  refine ⟨φ w, hmaps w hw, ?_⟩
  have hh := hwH
  rw [hH] at hh
  simp only at hh
  linear_combination hh


private theorem landau_aux {f : ℂ → ℂ}
    (hf : ∀ z ∈ Metric.ball (0:ℂ) 1, AnalyticAt ℂ f z) (hd0 : deriv f 0 = 1) :
    ∃ w : ℂ, Metric.closedBall w (1/100) ⊆ f '' (Metric.ball (0:ℂ) 1) := by
  classical
  let r : ℕ → ℝ := fun n => (1/2:ℝ)^(n+1)
  let P : ℕ → ℂ → Prop := fun n zn => ∃ ζ ∈ Metric.ball zn (r n), 2 * ‖deriv f zn‖ < ‖deriv f ζ‖
  let step : ℕ → ℂ → ℂ := fun n zn => if h : P n zn then h.choose else zn
  let z : ℕ → ℂ := fun n => Nat.rec (0:ℂ) step n
  have hz0 : z 0 = 0 := by simp [z]
  have hzsucc : ∀ n, z (n+1) = step n (z n) := fun n => rfl
  have hzstep : ∀ n, z (n+1) = if h : P n (z n) then h.choose else z n := by
    intro n; rw [hzsucc]
  have hrpos : ∀ n, 0 < r n := by intro n; simp only [r]; positivity
  have hrpow : ∀ n, r n = (1/2:ℝ)^(n+1) := fun n => rfl
  have hdist : ∀ n, dist (z (n+1)) (z n) < r n := by
    intro n
    rw [hzstep n]
    by_cases h : P n (z n)
    · rw [dif_pos h]; exact (h.choose_spec).1
    · rw [dif_neg h, dist_self]; exact hrpos n
  have htri : ∀ n, ‖z (n+1)‖ ≤ ‖z n‖ + ‖z (n+1) - z n‖ := by
    intro n
    have h := norm_add_le (z n) (z (n+1) - z n)
    rwa [add_sub_cancel] at h
  have hdn : ∀ n, ‖z (n+1) - z n‖ < r n := by
    intro n
    have h := hdist n
    rwa [dist_eq_norm] at h
  have hpw : ∀ n, (1:ℝ) - (1/2)^n + (1/2)^(n+1) = 1 - (1/2)^(n+1) := by
    intro n; rw [pow_succ]; ring
  have hnorm : ∀ n, ‖z n‖ ≤ 1 - (1/2:ℝ)^n := by
    intro n
    induction n with
    | zero => rw [hz0]; simp
    | succ n ih =>
      have h1 : ‖z (n+1)‖ ≤ ‖z n‖ + ‖z (n+1) - z n‖ := htri n
      have h2 : ‖z (n+1) - z n‖ < (1/2:ℝ)^(n+1) := by rw [← hrpow n]; exact hdn n
      linarith [h1, h2, ih, hpw n]
  have hnorm_strict : ∀ n, ‖z (n+1)‖ < 1 - (1/2:ℝ)^(n+1) := by
    intro n
    have h1 : ‖z (n+1)‖ ≤ ‖z n‖ + ‖z (n+1) - z n‖ := htri n
    have h2 : ‖z (n+1) - z n‖ < (1/2:ℝ)^(n+1) := by rw [← hrpow n]; exact hdn n
    linarith [h1, h2, hnorm n, hpw n]
  have hball_sub : ∀ n, Metric.ball (z n) (r n) ⊆ Metric.ball (0:ℂ) 1 := by
    intro n w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [sub_zero]
    have h1 : ‖w‖ ≤ ‖z n‖ + ‖w - z n‖ := by
      have h := norm_add_le (z n) (w - z n); rwa [add_sub_cancel] at h
    have h2 : ‖w - z n‖ < (1/2:ℝ)^(n+1) := by rw [← hrpow n]; exact hw
    have h3 : (0:ℝ) < (1/2)^(n+1) := by positivity
    linarith [h1, h2, hnorm n, hpw n, h3]
  have hcpow : ∀ n, ‖((r n : ℝ) : ℂ)‖ = r n := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hrpos n)]
  by_cases hcase : ∃ n, ¬ P n (z n)
  · obtain ⟨n, hn_np, hn_min⟩ : ∃ n, ¬ P n (z n) ∧ (∀ k < n, P k (z k)) :=
      ⟨Nat.find hcase, Nat.find_spec hcase, fun k hk => not_not.mp (Nat.find_min hcase hk)⟩
    have hgrowth : ∀ k ≤ n, (2:ℝ)^k ≤ ‖deriv f (z k)‖ := by
      intro k
      induction k with
      | zero => intro _; rw [hz0, hd0]; norm_num
      | succ k ih =>
        intro hk
        have hklt : k < n := Nat.lt_of_succ_le hk
        have hPk : P k (z k) := hn_min k hklt
        have hz_eq : z (k+1) = hPk.choose := by rw [hzstep k]; exact dif_pos hPk
        have hspec := (hPk.choose_spec).2
        rw [← hz_eq] at hspec
        calc (2:ℝ)^(k+1) = 2 * 2^k := by rw [pow_succ]; ring
          _ ≤ 2 * ‖deriv f (z k)‖ := by linarith [ih (Nat.le_of_lt hklt)]
          _ ≤ ‖deriv f (z (k+1))‖ := le_of_lt hspec
    have hbndn : (2:ℝ)^n ≤ ‖deriv f (z n)‖ := hgrowth n le_rfl
    have h2n : (1:ℝ) ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
    have hfn_ne : deriv f (z n) ≠ 0 := by
      intro hz
      have : ‖deriv f (z n)‖ = 0 := by rw [hz, norm_zero]
      linarith
    have hle : ∀ ζ ∈ Metric.ball (z n) (r n), ‖deriv f ζ‖ ≤ 2 * ‖deriv f (z n)‖ := by
      intro ζ hζ
      by_contra hlt
      rw [not_le] at hlt
      exact hn_np ⟨ζ, hζ, hlt⟩
    have hcm : ∀ w ∈ Metric.ball (0:ℂ) 1, z n + (r n : ℂ) * w ∈ Metric.ball (z n) (r n) := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm]
      have hwlt : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
      have he : ‖z n + (r n : ℂ) * w - z n‖ = r n * ‖w‖ := by
        rw [add_sub_cancel_left, norm_mul, hcpow n]
      rw [he]
      nlinarith [hrpos n, hwlt, norm_nonneg w]
    have han : ∀ w ∈ Metric.ball (0:ℂ) 1, AnalyticAt ℂ f (z n + (r n : ℂ) * w) := by
      intro w hw
      exact hf _ (hball_sub n (hcm w hw))
    have hbd : ∀ w ∈ Metric.ball (0:ℂ) 1,
        ‖deriv f (z n + (r n : ℂ) * w)‖ ≤ 2 * ‖deriv f (z n)‖ :=
      fun w hw => hle _ (hcm w hw)
    have hmaps : ∀ w ∈ Metric.ball (0:ℂ) 1, z n + (r n : ℂ) * w ∈ Metric.ball (0:ℂ) 1 :=
      fun w hw => hball_sub n (hcm w hw)
    have hdisc := landau_disc_subset_of_deriv_le (f := f) (z₀ := z n) (r := r n) (hrpos n) han hfn_ne hbd hmaps
    have hrad : (1:ℝ)/24 ≤ r n * ‖deriv f (z n)‖ / 12 := by
      have h2 : r n * (2:ℝ)^n = 1/2 := by
        rw [hrpow n, pow_succ]
        have h4 : ((1:ℝ)/2)^n * (2:ℝ)^n = 1 := by rw [← mul_pow]; norm_num
        nlinarith [h4]
      have h3 : (1:ℝ)/2 ≤ r n * ‖deriv f (z n)‖ :=
        calc (1:ℝ)/2 = r n * (2:ℝ)^n := h2.symm
          _ ≤ r n * ‖deriv f (z n)‖ := mul_le_mul_of_nonneg_left hbndn (le_of_lt (hrpos n))
      linarith
    refine ⟨f (z n), Subset.trans ?_ hdisc⟩
    intro v hv
    rw [Metric.mem_closedBall] at hv
    rw [Metric.mem_ball]
    linarith [hv, hrad]
  · exfalso
    have hP : ∀ n, P n (z n) := fun n => not_not.mp (not_exists.mp hcase n)
    have hgrowth : ∀ n, (2:ℝ)^n ≤ ‖deriv f (z n)‖ := by
      intro n
      induction n with
      | zero => rw [hz0, hd0]; norm_num
      | succ n ih =>
        have hPn := hP n
        have hz_eq : z (n+1) = hPn.choose := by rw [hzstep n]; exact dif_pos hPn
        have hspec := (hPn.choose_spec).2
        rw [← hz_eq] at hspec
        calc (2:ℝ)^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
          _ ≤ 2 * ‖deriv f (z n)‖ := by linarith
          _ ≤ ‖deriv f (z (n+1))‖ := le_of_lt hspec
    have hdist' : ∀ n, dist (z n) (z (n+1)) ≤ (1/2:ℝ) * (1/2)^n := by
      intro n
      have h2 : r n = (1/2:ℝ) * (1/2)^n := by rw [hrpow n, pow_succ, mul_comm]
      have h1 : dist (z (n+1)) (z n) < (1/2:ℝ) * (1/2)^n := by
        have h := hdist n
        rwa [h2] at h
      rw [dist_comm]
      exact h1.le
    have hcau : CauchySeq z := cauchySeq_of_le_geometric (1/2) (1/2) (by norm_num) hdist'
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcau
    have htail : ∀ n, dist (z n) a ≤ (1/2:ℝ)^n := by
      intro n
      have h0 := dist_le_of_le_geometric_of_tendsto (1/2) (1/2) (by norm_num) hdist' ha n
      have h : (1/2:ℝ) * (1/2)^n / (1 - 1/2) = (1/2)^n := by field_simp; norm_num
      linarith [h0, h]
    have ha_lt : ‖a‖ < 1 := by
      have h1 : dist (z 1) a ≤ (1/2:ℝ)^1 := htail 1
      have h2 : ‖z 1‖ < 1 - (1/2:ℝ)^1 := hnorm_strict 0
      have h3 : ‖a‖ ≤ ‖z 1‖ + dist (z 1) a := by
        have h := norm_add_le (z 1) (a - z 1)
        calc ‖a‖ = ‖z 1 + (a - z 1)‖ := by rw [add_sub_cancel]
          _ ≤ ‖z 1‖ + ‖a - z 1‖ := h
          _ = ‖z 1‖ + dist (z 1) a := by rw [dist_comm (z 1) a, dist_eq_norm]
      norm_num at h1 h2
      linarith
    have ha_ball : a ∈ Metric.ball (0:ℂ) 1 := by
      rw [Metric.mem_ball, dist_eq_norm]; simpa using ha_lt
    have hcont : ContinuousAt (deriv f) a := (AnalyticAt.deriv (hf a ha_ball)).continuousAt
    have htend : Tendsto (fun n => deriv f (z n)) atTop (𝓝 (deriv f a)) :=
      hcont.tendsto.comp ha
    have hntend : Tendsto (fun n => ‖deriv f (z n)‖) atTop (𝓝 ‖deriv f a‖) := htend.norm
    have hev : ∀ᶠ n in atTop, ‖deriv f (z n)‖ < ‖deriv f a‖ + 1 := by
      have h1 := hntend.eventually (Metric.ball_mem_nhds (‖deriv f a‖) zero_lt_one)
      filter_upwards [h1] with n hn
      rw [Real.dist_eq] at hn
      have := (abs_lt.mp hn).2
      linarith
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (‖deriv f a‖ + 1) (by norm_num : (1:ℝ) < 2)
    obtain ⟨n, hn_ev, hn_ge⟩ := (hev.and (eventually_ge_atTop N)).exists
    have hnn : (2:ℝ)^N ≤ 2^n := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn_ge
    have := hgrowth n
    linarith



/-- **Landau's theorem.** There is a universal constant `c > 0` such that every function
`f : ℂ → ℂ` holomorphic on the open unit disc with `f 0 = 0` and `deriv f 0 = 1` has an image
containing a disc of radius `c`.

An elementary proof (Cauchy's estimate for `f''`, Taylor's formula with remainder, and Rouché):
* if `|h'| ≤ 2` on the disc then `|h z - z| ≤ |z|^2/(1-|z|)`, so for `|z| = 1/3` we get
  `|h z - z| ≤ 1/6 = |z| - |w| ≤ |z - w|` for `|w| < 1/6`; Rouché
  (`Commons.Analysis.Complex.rouche_simple_zero` with `f = · - w`, `g = h - id`) gives
  `D(0,1/6) ⊆ h(D)`.
* General case: `z₀ = 0`, `rₙ = 2^{-(n+1)}`.  If `|h'| ≤ 2 |h'(zₙ)|` on `D(zₙ, rₙ)`, rescaling the
  previous step gives a disc of radius `rₙ |h'(zₙ)| / 6 ≥ 2^{-(n+1)} 2ⁿ/6 ≥ 1/12` in the image
  (`|h'(zₙ)| ≥ 2ⁿ` by induction).  Otherwise choose `z_{n+1} ∈ D(zₙ, rₙ)` with
  `|h'(z_{n+1})| > 2 |h'(zₙ)|`; the sequence stays in `D(0, 1/2)`, converges to `z*`, and
  continuity of `h'` at `z*` contradicts `|h'(zₙ)| > 2ⁿ → ∞`.
So `c = 1/100` (or any smaller explicit constant) works. -/
theorem landau_theorem : ∃ c : ℝ, 0 < c ∧ ∀ f : ℂ → ℂ,
    (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) → f 0 = 0 → deriv f 0 = 1 →
    ∃ w : ℂ, Metric.closedBall w c ⊆ f '' (Metric.ball (0 : ℂ) 1) := by
  refine ⟨1/100, by norm_num, ?_⟩
  intro f hf _ hd0
  exact landau_aux hf hd0

end Commons.Analysis.Complex.Landau
