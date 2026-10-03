import Mathlib
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.HeckeZFR.LSeriesBound
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea6Hecke.R.heckeArch_inv_exp_growth
import Submission.Work.FIArea6Hecke.R.completion_strip_bound_strict
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Complex Metric

noncomputable section

private noncomputable def bw (C : ℝ) (d : ℕ) (z : ℂ) : ℂ :=
  (C : ℂ) * (2 : ℂ) ^ (20 : ℕ) *
    Complex.exp ((↑(20 * Real.log (d : ℝ)) : ℂ) * ((((3:ℝ)/2 : ℝ) : ℂ) - z)) *
      (z - 2) ^ (20 : ℕ)

private lemma bw_differentiable (C : ℝ) (d : ℕ) : Differentiable ℂ (bw C d) := by
  unfold bw
  fun_prop

private lemma bw_norm (C : ℝ) (hC : 0 ≤ C) (d : ℕ) (z : ℂ) :
    ‖bw C d z‖ = C * 2 ^ (20 : ℕ) *
      Real.exp (20 * Real.log (d : ℝ) * (3 / 2 - z.re)) * ‖z - 2‖ ^ (20 : ℕ) := by
  have h1 : ((((3:ℝ)/2 : ℝ) : ℂ) - z).re = (3:ℝ)/2 - z.re := by
    rw [Complex.sub_re, Complex.ofReal_re]
  have hre : ((↑(20 * Real.log (d:ℝ)) : ℂ) * ((((3:ℝ)/2 : ℝ) : ℂ) - z)).re
      = 20 * Real.log (d:ℝ) * (3/2 - z.re) := by
    rw [Complex.mul_re, h1, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  unfold bw
  simp only [norm_mul, norm_pow, Complex.norm_of_nonneg hC, Complex.norm_ofNat,
    Complex.norm_exp, hre]

private lemma bw_ne_zero (C : ℝ) (hC : 0 < C) {d : ℕ} {z : ℂ} (hz : z.re < 2) :
    bw C d z ≠ 0 := by
  unfold bw
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) (Complex.exp_ne_zero _)) (pow_ne_zero _ ?_)
  · exact_mod_cast (ne_of_gt hC)
  · norm_num
  · intro h
    have h2z : z = 2 := sub_eq_zero.mp h
    rw [h2z] at hz
    norm_num at hz

private lemma norm_sub_two_sq (z : ℂ) : ‖z - 2‖ ^ 2 = (z.re - 2) ^ 2 + z.im ^ 2 := by
  have h2 : (2:ℂ) = ((2:ℝ):ℂ) := by norm_num
  rw [Complex.sq_norm, Complex.normSq_apply, h2]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma pow20_eq_sq10 (w : ℂ) : ‖w‖ ^ (20:ℕ) = (‖w‖ ^ 2) ^ (10:ℕ) := by ring

private lemma t_sq_le (t : ℝ) : (1 + |t|) ^ (10:ℕ) ≤ 2 ^ (10:ℕ) * (1 + t^2) ^ (10:ℕ) := by
  have h1 : (1 + |t|)^2 ≤ 2 * (1 + t^2) := by
    nlinarith [sq_nonneg (|t| - 1), sq_abs t, abs_nonneg t]
  have h2 : ((1 + |t|)^2)^(5:ℕ) ≤ (2 * (1 + t^2))^(5:ℕ) :=
    pow_le_pow_left₀ (by nlinarith [abs_nonneg t]) h1 5
  have h3 : (2 * (1 + t^2))^(5:ℕ) = (2:ℝ)^(5:ℕ) * (1 + t^2)^(5:ℕ) := by rw [mul_pow]
  have h4 : (1:ℝ) ≤ (1 + t^2)^(5:ℕ) := one_le_pow₀ (by nlinarith [sq_nonneg t])
  have h5 : (2:ℝ)^(5:ℕ) * (1 + t^2)^(5:ℕ) ≤ (2:ℝ)^(10:ℕ) * (1 + t^2)^(10:ℕ) := by
    have e1 : (2:ℝ)^(10:ℕ) = (2:ℝ)^(5:ℕ) * (2:ℝ)^(5:ℕ) := by ring
    have e2 : (1 + t^2)^(10:ℕ) = (1 + t^2)^(5:ℕ) * (1 + t^2)^(5:ℕ) := by ring
    rw [e1, e2]
    nlinarith [h4, pow_nonneg (show (0:ℝ) ≤ 1+t^2 by nlinarith [sq_nonneg t]) 5,
      show (1:ℝ) ≤ (2:ℝ)^(5:ℕ) by norm_num]
  calc (1 + |t|)^(10:ℕ) = ((1 + |t|)^2)^(5:ℕ) := by ring
    _ ≤ (2 * (1 + t^2))^(5:ℕ) := h2
    _ = (2:ℝ)^(5:ℕ) * (1 + t^2)^(5:ℕ) := h3
    _ ≤ (2:ℝ)^(10:ℕ) * (1 + t^2)^(10:ℕ) := h5

private lemma exp_ten_log {d : ℕ} (hd : 1 ≤ d) :
    Real.exp (((10:ℕ):ℝ) * Real.log (d:ℝ)) = (d:ℝ)^(10:ℕ) := by
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hd))]

private lemma bw_boundary_left (C : ℝ) (hC : 0 < C) (d : ℕ) (hd : 1 ≤ d) {z : ℂ}
    (hz : z.re = 1) : C * (d:ℝ)^10 * (1 + |z.im|)^10 ≤ ‖bw C d z‖ := by
  rw [bw_norm C (le_of_lt hC) d z, hz]
  have hexp : Real.exp (20 * Real.log (d:ℝ) * (3/2 - 1)) = (d:ℝ)^(10:ℕ) := by
    rw [show 20 * Real.log (d:ℝ) * (3/2 - 1) = ((10:ℕ):ℝ) * Real.log (d:ℝ) by ring, exp_ten_log hd]
  rw [hexp]
  have h2 : ‖z - 2‖ ^ (20:ℕ) = (1 + z.im^2)^(10:ℕ) := by
    rw [pow20_eq_sq10, norm_sub_two_sq, hz]; norm_num
  rw [h2]
  have h4 : (1 + |z.im|)^(10:ℕ) ≤ 2^(20:ℕ) * (1 + z.im^2)^(10:ℕ) := by
    have h5 : (2:ℝ)^(10:ℕ) ≤ 2^(20:ℕ) := by norm_num
    have h6 : (0:ℝ) ≤ (1 + z.im^2)^(10:ℕ) := by positivity
    nlinarith [t_sq_le z.im, h5, h6]
  have hC' : (0:ℝ) ≤ C * (d:ℝ)^10 := by positivity
  calc C * (d:ℝ)^10 * (1 + |z.im|)^10
      ≤ C * (d:ℝ)^10 * (2^(20:ℕ) * (1 + z.im^2)^(10:ℕ)) :=
        mul_le_mul_of_nonneg_left h4 hC'
    _ = C * 2 ^ (20:ℕ) * (d:ℝ)^10 * (1 + z.im^2)^(10:ℕ) := by ring

private lemma bw_boundary_right (C : ℝ) (hC : 0 < C) {d : ℕ} {z : ℂ} (hz : z.re = 3/2) :
    C ≤ ‖bw C d z‖ := by
  rw [bw_norm C (le_of_lt hC) d z, hz]
  have hexp : Real.exp (20 * Real.log (d:ℝ) * (3/2 - 3/2)) = 1 := by
    rw [show (3:ℝ)/2 - 3/2 = 0 by ring, mul_zero, Real.exp_zero]
  rw [hexp, mul_one]
  have h2 : ‖z - 2‖ ^ (20:ℕ) = ((1/4 : ℝ) + z.im^2)^(10:ℕ) := by
    rw [pow20_eq_sq10, norm_sub_two_sq, hz]; norm_num
  rw [h2]
  have h3 : (1/4 : ℝ) ≤ (1/4 : ℝ) + z.im^2 := by nlinarith [sq_nonneg z.im]
  have h4 : ((1/4 : ℝ) + z.im^2)^(10:ℕ) ≥ ((1/4 : ℝ))^(10:ℕ) :=
    pow_le_pow_left₀ (by norm_num) h3 10
  have hone : C * 2^(20:ℕ) * ((1/4:ℝ))^(10:ℕ) = C := by ring_nf
  calc C = C * 2^(20:ℕ) * ((1/4:ℝ))^(10:ℕ) := hone.symm
    _ ≤ C * 2^(20:ℕ) * ((1/4:ℝ) + z.im^2)^(10:ℕ) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

private lemma bw_ge_strip (C : ℝ) (hC : 0 < C) {d : ℕ} (hd : 1 ≤ d) {z : ℂ}
    (h1 : (1:ℝ) ≤ z.re) (h2 : z.re ≤ 3/2) : C ≤ ‖bw C d z‖ := by
  rw [bw_norm C (le_of_lt hC) d z, pow20_eq_sq10, norm_sub_two_sq]
  have hlogd : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hexp : (1:ℝ) ≤ Real.exp (20 * Real.log (d:ℝ) * (3/2 - z.re)) :=
    Real.one_le_exp (by nlinarith)
  have hz4 : (1/4 : ℝ) ≤ (z.re - 2)^2 + z.im^2 := by nlinarith [sq_nonneg z.im]
  have hone : C * 2^(20:ℕ) * ((1/4:ℝ))^(10:ℕ) = C := by ring_nf
  calc C = C * 2^(20:ℕ) * ((1/4:ℝ))^(10:ℕ) := hone.symm
    _ ≤ C * 2^(20:ℕ) * Real.exp (20 * Real.log (d:ℝ) * (3/2 - z.re)) * ((1/4:ℝ))^(10:ℕ) := by
        have h6 : (0:ℝ) ≤ C * 2^(20:ℕ) * ((1/4:ℝ))^(10:ℕ) := by positivity
        nlinarith [hexp, h6]
    _ ≤ C * 2^(20:ℕ) * Real.exp (20 * Real.log (d:ℝ) * (3/2 - z.re))
          * ((z.re - 2)^2 + z.im^2)^(10:ℕ) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hz4 10) (by positivity)

private lemma bw_le_ball (C : ℝ) (hC : 0 < C) (d : ℕ) (hd : 1 ≤ d) {z : ℂ}
    (hz : z ∈ closedBall (2:ℂ) (3/2)) (hz1 : (1:ℝ) ≤ z.re) :
    ‖bw C d z‖ ≤ C * 2^(20:ℕ) * (d:ℝ)^(10:ℕ) * ((3:ℝ)/2)^(20:ℕ) := by
  rw [bw_norm C (le_of_lt hC) d z]
  have hlogd : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast hd)
  have hexp : Real.exp (20 * Real.log (d:ℝ) * (3/2 - z.re)) ≤ (d:ℝ)^(10:ℕ) := by
    rw [← exp_ten_log hd]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hnorm : ‖z - 2‖ ≤ 3/2 := by
    have h := mem_closedBall.mp hz
    rwa [dist_eq_norm] at h
  have h4 : ‖z - 2‖ ^ (20:ℕ) ≤ ((3:ℝ)/2)^(20:ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 20
  calc C * 2^(20:ℕ) * Real.exp (20 * Real.log (d:ℝ) * (3/2 - z.re)) * ‖z - 2‖ ^ (20:ℕ)
      ≤ C * 2^(20:ℕ) * (d:ℝ)^(10:ℕ) * ((3:ℝ)/2)^(20:ℕ) := by
        have h5 : C * 2^(20:ℕ) * Real.exp (20 * Real.log (d:ℝ) * (3/2 - z.re))
            ≤ C * 2^(20:ℕ) * (d:ℝ)^(10:ℕ) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        exact mul_le_mul h5 h4 (pow_nonneg (norm_nonneg _) 20) (by positivity)

/-- **The core interpolation.** -/
private theorem ball_core (K : ℝ) (hKpos : 0 < K)
    (hLamBound : ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
          Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
      ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → ‖Lam s‖ ≤ K * (d : ℝ) ^ (10 : ℕ)) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
        ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ (C : ℝ), 1 ≤ C →
        (∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 →
          ‖Work.FIArea6Hecke.Lval d 0 Lam s‖
            ≤ C * (d : ℝ) ^ (10 : ℕ) * (1 + |s.im|) ^ (10 : ℕ)) →
        (∀ s : ℂ, 3 / 2 ≤ s.re → ‖Work.FIArea6Hecke.Lval d 0 Lam s‖ ≤ C) →
        (∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
          ‖Work.FIArea6Hecke.Lval d 0 Lam s‖ ≤ C' * C * (d : ℝ) ^ (10 : ℕ)) ∧
        (∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (5 / 4) →
          ‖deriv (fun z : ℂ => Work.FIArea6Hecke.Lval d 0 Lam z) s‖
            ≤ C' * C * (d : ℝ) ^ (10 : ℕ)) := by

  refine ⟨4 * ((3:ℝ)^(20:ℕ) + 1), by positivity, ?_⟩
  intro d hd chi hchi hb Lam hAn hagr C hC hstrip hline3
  obtain ⟨c₁, C₁, hc₁, hC₁, harch⟩ := heckeArch_inv_exp_growth d hd
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  set f : ℂ → ℂ := fun z => Work.FIArea6Hecke.Lval d 0 Lam z with hf
  set W : ℂ → ℂ := bw C d with hW
  have hLb : ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 2 → ‖Lam s‖ ≤ K * (d:ℝ)^10 :=
    hLamBound d hd chi hchi hb Lam hAn hagr
  have hfgrow : ∀ s : ℂ, 1/2 ≤ s.re → s.re ≤ 3/2 →
      ‖f s‖ ≤ (K * (d:ℝ)^10) * (c₁ * Real.exp (C₁ * (1 + |s.im|))) := by
    intro s hs1 hs2
    have hfs : f s = Lam s / Work.FITop4.Bridge.heckeArch d 0 s := by
      simp [hf, Work.FIArea6Hecke.Lval]
    rw [hfs, div_eq_mul_inv, norm_mul]
    refine mul_le_mul (hLb s hs1 (by linarith)) (harch s (by linarith) hs2)
      (norm_nonneg _) (by positivity)
  have hf_an : AnalyticOn ℂ f {z : ℂ | 0 < z.re} := by
    have hfe : f = fun z => Lam z / Work.FITop4.Bridge.heckeArch d 0 z := by
      funext z; simp [hf, Work.FIArea6Hecke.Lval]
    rw [hfe]
    refine AnalyticOn.div (hAn.mono (Set.subset_univ _)) ?_ ?_
    · refine DifferentiableOn.analyticOn ?_ (isOpen_Ioi.preimage Complex.continuous_re)
      intro z hz
      have hz' : (0:ℝ) < z.re := hz
      exact (heckeArch_differentiableAt_of_pos hd 0 hz').differentiableWithinAt
    · intro z hz
      have hz' : (0:ℝ) < z.re := hz
      exact heckeArch_ne_zero_of_pos_re hd 0 hz'
  have hW_an : AnalyticOn ℂ W Set.univ := by
    rw [hW]
    exact (bw_differentiable C d).differentiableOn.analyticOn isOpen_univ
  have hF_an : AnalyticOn ℂ (fun z => f z / W z)
      (Complex.re ⁻¹' Set.Ioo (0:ℝ) 2) := by
    refine AnalyticOn.div (hf_an.mono ?_) (hW_an.mono (Set.subset_univ _)) ?_
    · intro z hz
      exact hz.1
    · intro z hz
      have hz2 : z.re < 2 := hz.2
      rw [hW]
      exact bw_ne_zero C hC0 hz2
  have hle_a : ∀ z : ℂ, z.re = 1 → ‖f z / W z‖ ≤ 1 := by
    intro z hz
    rw [norm_div]
    refine div_le_one_of_le₀ ?_ (norm_nonneg _)
    have h1 : ‖f z‖ ≤ C * (d:ℝ)^10 * (1 + |z.im|)^10 := by
      have := hstrip z (by rw [hz]; norm_num) (by rw [hz])
      simpa [hf] using this
    have h2 : C * (d:ℝ)^10 * (1 + |z.im|)^10 ≤ ‖W z‖ := by
      rw [hW]; exact bw_boundary_left C hC0 d hd hz
    linarith
  have hle_b : ∀ z : ℂ, z.re = 3/2 → ‖f z / W z‖ ≤ 1 := by
    intro z hz
    rw [norm_div]
    refine div_le_one_of_le₀ ?_ (norm_nonneg _)
    have h1 : ‖f z‖ ≤ C := by
      have := hline3 z (by rw [hz])
      simpa [hf] using this
    have h2 : C ≤ ‖W z‖ := by
      rw [hW]; exact bw_boundary_right C hC0 hz
    linarith

  have hgrow : ∃ B : ℝ, ∀ z : ℂ, 1 < z.re → z.re < 3/2 →
      ‖f z / W z‖ ≤ Real.exp (B * Real.exp (1 * |z.im|)) := by
    set A : ℝ := (K * (d:ℝ)^10) * c₁ / C with hA
    have hApos : 0 < A := by
      rw [hA]
      have h1 : 0 < K * (d:ℝ)^10 := by
        have h2 : (0:ℝ) < (d:ℝ)^10 := by positivity
        positivity
      positivity
    refine ⟨max (Real.log A) 0 + (C₁ + 1), ?_⟩
    intro z hz1 hz2
    have hWge : C ≤ ‖W z‖ := by
      rw [hW]; exact bw_ge_strip C hC0 hd (le_of_lt hz1) (le_of_lt hz2)
    have hWpos : 0 < ‖W z‖ := lt_of_lt_of_le hC0 hWge
    have hfge := hfgrow z (by linarith : (1:ℝ)/2 ≤ z.re) (le_of_lt hz2)
    have hmain : ‖f z‖ / ‖W z‖ ≤ A * Real.exp (C₁ * (1 + |z.im|)) := by
      rw [hA, div_le_iff₀ hWpos]
      calc ‖f z‖ ≤ (K * (d:ℝ)^10) * (c₁ * Real.exp (C₁ * (1 + |z.im|))) := hfge
        _ = ((K * (d:ℝ)^10) * c₁ / C) * Real.exp (C₁ * (1 + |z.im|)) * C := by
            field_simp
        _ ≤ ((K * (d:ℝ)^10) * c₁ / C) * Real.exp (C₁ * (1 + |z.im|)) * ‖W z‖ := by
            apply mul_le_mul_of_nonneg_left hWge
            positivity
    rw [norm_div, one_mul]
    refine hmain.trans ?_
    set B : ℝ := max (Real.log A) 0 + (C₁ + 1) with hB
    have hBge : C₁ ≤ B := by
      rw [hB]; have := le_max_right (Real.log A) 0; linarith
    have hlogA : Real.log A ≤ B - C₁ := by
      rw [hB]
      have h2 : (0:ℝ) ≤ max (Real.log A) 0 := le_max_right _ _
      have h3 : Real.log A ≤ max (Real.log A) 0 := le_max_left _ _
      linarith
    have hBpos : 0 ≤ B := le_trans hC₁.le hBge
    have he : (1:ℝ) + |z.im| ≤ Real.exp |z.im| := by
      linarith [Real.add_one_le_exp |z.im|]
    have hnn : (0:ℝ) ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
    calc A * Real.exp (C₁ * (1 + |z.im|))
        ≤ Real.exp (B - C₁) * Real.exp (C₁ * (1 + |z.im|)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          calc A = Real.exp (Real.log A) := (Real.exp_log hApos).symm
            _ ≤ Real.exp (B - C₁) := Real.exp_le_exp.mpr hlogA
      _ = Real.exp ((B - C₁) + C₁ * (1 + |z.im|)) := by rw [Real.exp_add]
      _ ≤ Real.exp (B * Real.exp |z.im|) := by
          apply Real.exp_le_exp.mpr
          have h4 : (B - C₁) + C₁ * (1 + |z.im|) ≤ B * (1 + |z.im|) := by
            nlinarith [hBge, abs_nonneg z.im]
          have h5 : B * (1 + |z.im|) ≤ B * Real.exp |z.im| :=
            mul_le_mul_of_nonneg_left he hBpos
          linarith
  have hPL : ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 3/2 → ‖f z / W z‖ ≤ 1 := by
    intro z hz1 hz2
    have hdcoc : DiffContOnCl ℂ (fun z => f z / W z)
        (Complex.re ⁻¹' Set.Ioo (1:ℝ) (3/2)) := by
      refine ⟨hF_an.differentiableOn.mono ?_, hF_an.continuousOn.mono ?_⟩
      · intro w hw; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
      · have h1 : closure (Complex.re ⁻¹' Set.Ioo (1:ℝ) (3/2))
            ⊆ Complex.re ⁻¹' Set.Icc (1:ℝ) (3/2) :=
          closure_minimal (fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩)
            (isClosed_Icc.preimage Complex.continuous_re)
        have h2 : Complex.re ⁻¹' Set.Icc (1:ℝ) (3/2)
            ⊆ Complex.re ⁻¹' Set.Ioo (0:ℝ) 2 :=
          fun w hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩
        exact h1.trans h2
    obtain ⟨B, hB⟩ := hgrow
    refine PhragmenLindelof.vertical_strip (a := (1:ℝ)) (b := (3:ℝ)/2) (C := 1)
      (f := fun z => f z / W z) (z := z) hdcoc ?_ hle_a hle_b hz1 hz2
    refine ⟨1, ?_, B, ?_⟩
    · have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
      rw [show (3:ℝ)/2 - 1 = 1/2 by ring, div_eq_mul_inv]
      have h2 : ((1:ℝ)/2)⁻¹ = 2 := by norm_num
      rw [h2]
      nlinarith
    · refine Asymptotics.IsBigO.of_bound 1 ?_
      refine Filter.Eventually.filter_mono inf_le_right ?_
      rw [Filter.eventually_principal]
      intro w hw
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
      exact hB w hw.1 hw.2

  have hval : ∀ s : ℂ, s ∈ closedBall (2:ℂ) (3/2) →
      ‖f s‖ ≤ ((3:ℝ)^(20:ℕ) + 1) * C * (d:ℝ)^(10:ℕ) := by
    intro s hs
    have hsre : s.re ≤ 7/2 := by
      have h := mem_closedBall.mp hs
      rw [dist_eq_norm] at h
      have h2 := Complex.abs_re_le_norm (s - 2)
      have h3 : (s-2).re = s.re - 2 := by simp
      rw [h3, abs_le] at h2
      linarith [h2.2]
    have hsre' : (1:ℝ)/2 ≤ s.re := by
      have h := mem_closedBall.mp hs
      rw [dist_eq_norm] at h
      have h2 := Complex.abs_re_le_norm (s - 2)
      have h3 : (s-2).re = s.re - 2 := by simp
      rw [h3, abs_le] at h2
      linarith [h2.1]
    have hsim : |s.im| ≤ 3/2 := by
      have h := mem_closedBall.mp hs
      rw [dist_eq_norm] at h
      have h2 : |s.im| ≤ ‖s - 2‖ := by
        have h3 := Complex.abs_im_le_norm (s - 2)
        simpa using h3
      linarith
    by_cases h1 : s.re ≤ 1
    · have h1' : ‖f s‖ ≤ C * (d:ℝ)^10 * (1 + |s.im|)^10 := by
        have := hstrip s hsre' h1
        simpa [hf] using this
      have h2 : (1 + |s.im|)^10 ≤ (1 + (3:ℝ)/2)^10 :=
        pow_le_pow_left₀ (by linarith [abs_nonneg s.im]) (by linarith) 10
      have h3 : ‖f s‖ ≤ C * (d:ℝ)^10 * (1 + (3:ℝ)/2)^10 := by
        calc ‖f s‖ ≤ C * (d:ℝ)^10 * (1 + |s.im|)^10 := h1'
          _ ≤ C * (d:ℝ)^10 * (1 + (3:ℝ)/2)^10 :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : ((5:ℝ)/2)^10 ≤ (3:ℝ)^(20:ℕ) + 1 := by norm_num
      have h5 : (1 + (3:ℝ)/2)^10 = ((5:ℝ)/2)^10 := by norm_num
      have hCnn : (0:ℝ) ≤ C * (d:ℝ)^10 := by positivity
      calc ‖f s‖ ≤ C * (d:ℝ)^10 * (1 + (3:ℝ)/2)^10 := h3
        _ = C * (d:ℝ)^10 * ((5:ℝ)/2)^10 := by rw [h5]
        _ ≤ C * (d:ℝ)^10 * ((3:ℝ)^(20:ℕ) + 1) :=
            mul_le_mul_of_nonneg_left h4 hCnn
        _ = ((3:ℝ)^(20:ℕ) + 1) * C * (d:ℝ)^10 := by ring
    · by_cases h2 : s.re ≤ 3/2
      · have hPLs : ‖f s‖ ≤ ‖W s‖ := by
          have hs1 : (1:ℝ) ≤ s.re := by linarith [h1]
          have hs2 : s.re ≤ 3/2 := by linarith [h2]
          have := hPL s hs1 hs2
          rw [norm_div] at this
          have hWpos : 0 < ‖W s‖ := by
            rw [hW]
            exact lt_of_lt_of_le hC0 (bw_ge_strip C hC0 hd hs1 hs2)
          simpa using (div_le_iff₀ hWpos).mp this
        have hWb := bw_le_ball C hC0 d hd hs (by linarith [h1])
        have h4 : 2^(20:ℕ) * ((3:ℝ)/2)^(20:ℕ) = (3:ℝ)^(20:ℕ) := by
          rw [← mul_pow]; norm_num
        have h5 : (3:ℝ)^(20:ℕ) ≤ (3:ℝ)^(20:ℕ) + 1 := by linarith
        have h6 : (0:ℝ) ≤ C * (d:ℝ)^(10:ℕ) := by positivity
        calc ‖f s‖ ≤ ‖bw C d s‖ := by rw [← hW]; exact hPLs
          _ ≤ C * 2^(20:ℕ) * (d:ℝ)^(10:ℕ) * ((3:ℝ)/2)^(20:ℕ) := hWb
          _ = C * (d:ℝ)^(10:ℕ) * (2^(20:ℕ) * ((3:ℝ)/2)^(20:ℕ)) := by ring
          _ = C * (d:ℝ)^(10:ℕ) * (3:ℝ)^(20:ℕ) := by rw [h4]
          _ ≤ C * (d:ℝ)^(10:ℕ) * ((3:ℝ)^(20:ℕ) + 1) :=
              mul_le_mul_of_nonneg_left h5 h6
          _ = ((3:ℝ)^(20:ℕ) + 1) * C * (d:ℝ)^(10:ℕ) := by ring
      · have h1' : ‖f s‖ ≤ C := by
          have := hline3 s (by linarith [h2])
          simpa [hf] using this
        have h6 : (0:ℝ) ≤ (d:ℝ)^(10:ℕ) := by positivity
        have h7 : (1:ℝ) ≤ (3:ℝ)^(20:ℕ) + 1 := by norm_num
        calc ‖f s‖ ≤ C := h1'
          _ ≤ ((3:ℝ)^(20:ℕ) + 1) * C * (d:ℝ)^(10:ℕ) := by
              have h8 : (1:ℝ) ≤ ((3:ℝ)^(20:ℕ) + 1) * (d:ℝ)^(10:ℕ) := by
                have h9 : (1:ℝ) ≤ (d:ℝ)^(10:ℕ) := one_le_pow₀ hd1
                nlinarith [h7, h9]
              nlinarith [h8, hC0]
  constructor
  · intro s hs
    have h := hval s hs
    have h4 : ((3:ℝ)^(20:ℕ) + 1) ≤ 4 * ((3:ℝ)^(20:ℕ) + 1) := by linarith
    have hCnn : (0:ℝ) ≤ C * (d:ℝ)^(10:ℕ) := by positivity
    calc ‖f s‖ ≤ ((3:ℝ)^(20:ℕ) + 1) * C * (d:ℝ)^(10:ℕ) := h
      _ ≤ (4 * ((3:ℝ)^(20:ℕ) + 1)) * C * (d:ℝ)^(10:ℕ) := by
          nlinarith [h4, hCnn]
  · intro s hs
    have hsre : (3:ℝ)/4 ≤ s.re := by
      have h := mem_closedBall.mp hs
      rw [dist_eq_norm] at h
      have h2 := Complex.abs_re_le_norm (s - 2)
      have h3 : (s-2).re = s.re - 2 := by simp
      rw [h3, abs_le] at h2
      linarith [h2.1]
    have hder : ‖deriv f s‖ ≤
        (((3:ℝ)^(20:ℕ) + 1) * C * (d:ℝ)^(10:ℕ)) / (1/4) := by
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (R := (1:ℝ)/4)
        (C := ((3:ℝ)^(20:ℕ) + 1) * C * (d:ℝ)^(10:ℕ)) (by norm_num) ?_ ?_
      · refine ⟨hf_an.differentiableOn.mono ?_, hf_an.continuousOn.mono ?_⟩
        · intro z hz
          have h := mem_ball.mp hz
          rw [dist_eq_norm] at h
          have h2 := Complex.abs_re_le_norm (z - s)
          have h3 : (z-s).re = z.re - s.re := by simp
          rw [h3, abs_le] at h2
          have : (0:ℝ) < z.re := by linarith [h2.1, h, hsre]
          exact this
        · refine Metric.closure_ball_subset_closedBall.trans ?_
          intro z hz
          have h := mem_closedBall.mp hz
          rw [dist_eq_norm] at h
          have h2 := Complex.abs_re_le_norm (z - s)
          have h3 : (z-s).re = z.re - s.re := by simp
          rw [h3, abs_le] at h2
          have : (0:ℝ) < z.re := by linarith [h2.1, h, hsre]
          exact this
      · intro z hz
        have hzball : z ∈ closedBall (2:ℂ) (3/2) := by
          have h1 : dist z s = (1:ℝ)/4 := mem_sphere.mp hz
          rw [dist_eq_norm] at h1
          have h := mem_closedBall.mp hs
          rw [dist_eq_norm] at h
          rw [mem_closedBall, dist_eq_norm]
          calc ‖z - 2‖ = ‖(z - s) + (s - 2)‖ := by ring_nf
            _ ≤ ‖z - s‖ + ‖s - 2‖ := norm_add_le _ _
            _ = 1/4 + ‖s - 2‖ := by rw [h1]
            _ ≤ 1/4 + 5/4 := by linarith
            _ = 3/2 := by norm_num
        exact hval z hzball
    have h4 : (((3:ℝ)^(20:ℕ) + 1) * C * (d:ℝ)^(10:ℕ)) / (1/4)
        = (4 * ((3:ℝ)^(20:ℕ) + 1)) * C * (d:ℝ)^(10:ℕ) := by
      rw [div_eq_mul_inv]
      have hq : ((1:ℝ)/4)⁻¹ = 4 := by norm_num
      rw [hq]
      ring
    rw [h4] at hder
    exact hder

/-- **The values and the derivative of `Lval` on the ball `|s-2| ≤ 3/2`, with an absolute
constant, uniform in the modulus.**  `Lval d 0 Lam` is entire (the denominator `heckeArch d 0` is
zero-free), and it agrees with the Hecke `L`-series on `re s > 1` by `hagr`, so the two supplied
line bounds produce a bound on the whole ball `|s-2| ≤ 3/2` (i.e. `re s ∈ [1/2,7/2]`,
`|im s| ≤ 3/2`): the cap `re s ∈ [1/2,1]` is `hstrip` (with `|im s| ≤ 3/2`), the line `re s = 3/2`
is `hline3`, and the remaining slice `re s ∈ [1,3/2]` follows from them by Hadamard's three-lines
argument on the rectangle `[1,3/2] × [-3/2,3/2]` (no growth hypothesis is needed because `|im|` is
bounded).  The derivative bound on the smaller ball `|s-2| ≤ 5/4` then follows from Cauchy's
estimate on the circle of radius `1/4`, which stays inside `|s-2| ≤ 3/2`.  Since `5/4 > 21/20`,
this covers every real point of `[19/20,1]`. -/
theorem Lval_ball_bound_uniform :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
        ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ (C : ℝ), 1 ≤ C →
        (∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 →
          ‖Work.FIArea6Hecke.Lval d 0 Lam s‖
            ≤ C * (d : ℝ) ^ (10 : ℕ) * (1 + |s.im|) ^ (10 : ℕ)) →
        (∀ s : ℂ, 3 / 2 ≤ s.re → ‖Work.FIArea6Hecke.Lval d 0 Lam s‖ ≤ C) →
        (∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
          ‖Work.FIArea6Hecke.Lval d 0 Lam s‖ ≤ C' * C * (d : ℝ) ^ (10 : ℕ)) ∧
        (∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (5 / 4) →
          ‖deriv (fun z : ℂ => Work.FIArea6Hecke.Lval d 0 Lam z) s‖
            ≤ C' * C * (d : ℝ) ^ (10 : ℕ)) := by
  obtain ⟨K, hKpos, hK⟩ := completion_strip_bound_strict
  exact ball_core K hKpos hK

end

end Work.FIArea6Hecke.R
