import Mathlib
import Submission.Work.BMF.V4prelim
import Submission.Work.BMF.N4chain.LFunction_norm_lower_of_re
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
import Submission.Work.BMF.VKPrimeSums.VKD67Defs
import Submission.Work.BMF.VKPrimeSums.VKD67_arith
import Submission.Work.BMF.VKPrimeSums.LFunction_norm_le_ball

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BMF.VKPrimeSums

open Complex Metric
open scoped Topology

private lemma N_cast_one_le {N : ℕ} [NeZero N] : (1 : ℝ) ≤ (N : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)

private lemma one_le_log_abs_add_three {t : ℝ} (ht : 4 ≤ |t|) :
    (1 : ℝ) ≤ Real.log (|t| + 3) := by
  have h : (3 : ℝ) ≤ |t| + 3 := by linarith [abs_nonneg t]
  exact le_trans Work.BMF.log_three_ge_one (Real.log_le_log (by norm_num) h)

private lemma one_le_log_N_mul {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    (1 : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 3)) := by
  have h3 : (0 : ℝ) < |t| + 3 := by linarith [abs_nonneg t]
  have hle : |t| + 3 ≤ (N : ℝ) * (|t| + 3) := by
    nlinarith [N_cast_one_le (N := N), h3]
  exact le_trans (one_le_log_abs_add_three ht) (Real.log_le_log h3 hle)

private lemma log_N_le_L {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    Real.log (N : ℝ) ≤ Real.log ((N : ℝ) * (|t| + 3)) := by
  have h3 : (0 : ℝ) < |t| + 3 := by linarith [abs_nonneg t]
  have hN : (1 : ℝ) ≤ (N : ℝ) := N_cast_one_le (N := N)
  exact Real.log_le_log (by linarith) (by nlinarith)

private lemma log_abs_add_three_le_L {N : ℕ} [NeZero N] {t : ℝ} (ht : 4 ≤ |t|) :
    Real.log (|t| + 3) ≤ Real.log ((N : ℝ) * (|t| + 3)) := by
  have h3 : (0 : ℝ) < |t| + 3 := by linarith [abs_nonneg t]
  have hle : |t| + 3 ≤ (N : ℝ) * (|t| + 3) := by
    nlinarith [N_cast_one_le (N := N), h3]
  exact Real.log_le_log h3 hle

/-- **The logarithmic-derivative bound in the Vinogradov–Korobov region, from the zero-free
region** (the remaining step of node V4, `Work.BMF.logDeriv_LFunction_VK`).

Route: given the zero-free region (hypothesis `hreg`), fix `δ = c₀/(16 D)` with
`D = (log(|t|+3))^{6/7}(log(N+2) + log log(|t|+3))` and split on `σ`.

* `1 + δ ≤ σ ≤ 2`: `logDeriv L = -LSeries (Λ·χ)`, so `‖L′/L‖ ≤ Σ Λ(n)n^{-σ} = -ζ′/ζ(σ) ≤ 1/(σ-1) + C`
  (`Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound` together with
  `Commons.NumberTheory.Zeta.logDeriv_riemannZeta_eq`).
* `σ ≤ 1 + δ`: the Cauchy–Borel–Carathéodory ball estimate
  `Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic` around the centre `1+δ+it` with
  radius `3δ` (which stays inside the region because the denominator is at most `4` times its value
  at `t` on the ball), the upper bound `‖L(w,χ)‖ ≤ 2N‖w‖/Re w`
  (`Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane`) and the Euler-product lower
  bound `δ/4 ≤ ‖L(1+δ+it,χ)‖` (`Work.BMF.N4chain.LFunction_norm_lower_of_re`).

Shrink `c` to `min c₀ 1 / 32` so that the ball stays inside `hreg`'s region. -/
theorem logDeriv_LVK_of_zeroFree
    (hreg : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      χ ≠ 1 → ∀ σ t : ℝ, 3 ≤ |t| →
        1 - c / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ σ t : ℝ, 4 ≤ |t| →
        1 - c / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ → σ ≤ 2 →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * Real.log ((N : ℝ) * (|t| + 3)) ^ 4 := by
  obtain ⟨c₀, hc₀pos, h₀⟩ := hreg
  set c : ℝ := min 1 c₀ / 16 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hc1 : c ≤ 1 / 16 := by
    rw [hcdef]
    have h : min 1 c₀ ≤ 1 := min_le_left _ _
    linarith
  have hcc₀ : 8 * c ≤ c₀ := by
    have h : min 1 c₀ ≤ c₀ := min_le_right _ _
    rw [hcdef]; linarith
  have hcc₀' : c ≤ c₀ := by
    have h : min 1 c₀ ≤ c₀ := min_le_right _ _
    rw [hcdef]; linarith
  set K₂ : ℝ := Real.log (1 / c) + 6 with hK₂def
  have hK₂pos : 0 < K₂ := by
    rw [hK₂def]
    have h : 0 ≤ Real.log (1 / c) := Real.log_nonneg (by rw [le_div_iff₀ hcpos]; linarith)
    linarith
  have hCpos : 0 < 200 * (64 + K₂) / c + 1 := by
    have h1 : 0 ≤ 200 * (64 + K₂) / c := by positivity
    linarith
  refine ⟨200 * (64 + K₂) / c + 1, c, hCpos, hcpos, ?_⟩
  intro N _ χ hχprim hχne σ t ht4 hσlo hσhi
  have ht3 : 3 ≤ |t| := by linarith
  set L : ℝ := Real.log ((N : ℝ) * (|t| + 3)) with hLdef
  set D : ℝ := VKD67 N t with hDdef
  set δ : ℝ := c / D with hδdef
  set m : ℝ := δ / 2 with hmdef
  set R : ℝ := 3 * δ with hRdef
  set M : ℝ := 4 * (N : ℝ) * (|t| + 4) with hMdef
  set s₀ : ℝ := max σ (1 + δ) with hs₀def
  set cc : ℂ := (s₀ : ℂ) + (t : ℂ) * I with hccdef
  set z₀ : ℂ := (σ : ℂ) + (t : ℂ) * I with hz₀def
  obtain ⟨hD67pos, hD67one, hD67shift, hD67Lsq, hlogD67⟩ := VKD67_arith (N := N)
  have hL1 : 1 ≤ L := one_le_log_N_mul ht4
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hD1 : 1 ≤ D := by rw [hDdef]; exact hD67one t ht3
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hD4 : D ≤ 4 * L ^ 2 := by rw [hDdef, hLdef]; exact hD67Lsq t ht4
  have hlogD : Real.log D ≤ 5 * L := by rw [hDdef, hLdef]; exact hlogD67 t ht4
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hcpos hDpos
  have hδnn : 0 ≤ δ := le_of_lt hδpos
  have hδone : δ ≤ 1 := by
    rw [hδdef, div_le_one hDpos]
    linarith [hc1, hD1]
  have hδsmall : 3 * δ ≤ 1 := by
    rw [hδdef, show 3 * (c / D) = 3 * c / D by ring, div_le_one hDpos]
    nlinarith [hc1, hD1]
  have hδ16 : δ ≤ 1 / 16 := by
    rw [hδdef, div_le_iff₀ hDpos]
    nlinarith [hc1, hD1]
  have hM2 : 2 ≤ M := by
    rw [hMdef]
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := N_cast_one_le (N := N)
    nlinarith [abs_nonneg t]
  have hMpos : 0 < M := by linarith
  have hmpos : 0 < m := by rw [hmdef]; linarith
  have hmone : m ≤ 1 := by rw [hmdef]; linarith
  have hmM : m ≤ M := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := N_cast_one_le (N := N)
    have h4 : (4 : ℝ) ≤ |t| := ht4
    rw [hmdef, hMdef]
    nlinarith [abs_nonneg t]
  have hRpos : 0 < R := by rw [hRdef]; linarith
  -- the target region condition, with the denominator identified as `D`
  have hσge : 1 - δ ≤ σ := by
    rw [hδdef]
    calc 1 - c / D = 1 - c / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
            (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) := by
          rw [hDdef, VKD67_eq]
      _ ≤ σ := hσlo
  -- ## geometry of the disc
  have hball : ∀ w : ℂ, w ∈ Metric.ball cc R →
      (1 - 2 * δ < w.re ∧ |w.im| ≤ |t| + 1 ∧ 3 ≤ |w.im|) := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hdist' : ‖w - cc‖ < 3 * δ := by rw [← hRdef]; exact hw
    have hre_le : w.re - s₀ ≤ ‖w - cc‖ := by
      have h := Complex.abs_re_le_norm (w - cc)
      have h2 : (w - cc).re = w.re - s₀ := by simp [hccdef]
      rw [h2] at h
      exact le_trans (le_abs_self _) h
    have hre_ge : s₀ - w.re ≤ ‖w - cc‖ := by
      have h := Complex.abs_re_le_norm (w - cc)
      have h2 : (w - cc).re = w.re - s₀ := by simp [hccdef]
      rw [h2] at h
      have h3 : -(w.re - s₀) ≤ ‖w - cc‖ := le_trans (neg_le_abs _) h
      linarith
    have him : |w.im - t| ≤ ‖w - cc‖ := by
      have h := Complex.abs_im_le_norm (w - cc)
      have h2 : (w - cc).im = w.im - t := by simp [hccdef]
      rwa [h2] at h
    have hs₀1 : 1 + δ ≤ s₀ := by rw [hs₀def]; exact le_max_right _ _
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · have h1 : |w.im| ≤ |w.im - t| + |t| := by
        calc |w.im| = |(w.im - t) + t| := by ring_nf
          _ ≤ |w.im - t| + |t| := abs_add_le _ _
      linarith
    · have h1 : |t| - |w.im| ≤ |t - w.im| := abs_sub_abs_le_abs_sub t w.im
      have h2 : |t - w.im| = |w.im - t| := abs_sub_comm _ _
      linarith
  have hshift : ∀ w : ℂ, w ∈ Metric.ball cc R → |w.im - t| ≤ 1 := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have him : |w.im - t| ≤ ‖w - cc‖ := by
      have h := Complex.abs_im_le_norm (w - cc)
      have h2 : (w - cc).im = w.im - t := by simp [hccdef]
      rwa [h2] at h
    linarith [hδsmall]
  -- ## zero-freeness of the disc
  have hzf : ∀ w ∈ Metric.ball cc R, DirichletCharacter.LFunction χ w ≠ 0 := by
    intro w hw
    obtain ⟨hwre, _, hwim_ge⟩ := hball w hw
    have hs := hshift w hw
    have hVKD : VKD67 N w.im ≤ 4 * D := by
      rw [hDdef]
      exact hD67shift t w.im ht4 hs
    have hpos1 : 0 < VKD67 N w.im := hD67pos w.im hwim_ge
    have hle : c₀ / (4 * D) ≤ c₀ / VKD67 N w.im :=
      div_le_div_of_nonneg_left hc₀pos.le hpos1 hVKD
    have hbig : 2 * δ ≤ c₀ / (4 * D) := by
      rw [hδdef, show 2 * (c / D) = 2 * c / D by ring, div_le_div_iff₀ hDpos (by positivity)]
      nlinarith [hcc₀, hDpos]
    have hstep : 1 - c₀ / VKD67 N w.im ≤ w.re := by linarith
    have happ := h₀ N χ hχprim hχne w.re w.im hwim_ge (by
      rw [← VKD67_eq]
      exact hstep)
    rwa [Complex.re_add_im w] at happ
  -- ## upper bound on the disc
  have hMbound : ∀ w ∈ Metric.ball cc R, ‖DirichletCharacter.LFunction χ w‖ ≤ M := by
    intro w hw
    obtain ⟨hwre, _, _⟩ := hball w hw
    have hrew : 1 / 2 ≤ w.re := by linarith [hδ16]
    have hdist : ‖w - cc‖ < 3 * δ := by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      linarith [hRdef]
    have hccnorm : ‖cc‖ ≤ |t| + 2 := by
      have hs₀2 : s₀ ≤ 2 := by
        rw [hs₀def]
        exact max_le hσhi (by linarith)
      have hs₀0 : 0 ≤ s₀ := by
        rw [hs₀def]
        exact le_trans (by linarith [hδpos] : (0 : ℝ) ≤ 1 + δ) (le_max_right _ _)
      have h1 : ‖(s₀ : ℂ) + (t : ℂ) * I‖ ≤ s₀ + |t| := by
        calc ‖(s₀ : ℂ) + (t : ℂ) * I‖ ≤ ‖(s₀ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
          _ = |s₀| + |t| := by simp
          _ = s₀ + |t| := by rw [abs_of_nonneg hs₀0]
      rw [hccdef]
      linarith
    have hnorm : ‖w‖ ≤ |t| + 4 := by
      have h1 : ‖w‖ ≤ ‖cc‖ + ‖w - cc‖ := by
        calc ‖w‖ = ‖cc + (w - cc)‖ := by ring_nf
          _ ≤ ‖cc‖ + ‖w - cc‖ := norm_add_le _ _
      linarith
    have hb := LFunction_norm_le_ball χ hχne ht4 hrew hnorm
    rw [hMdef]
    exact hb
  -- ## analyticity on the disc
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.ball cc R) := by
    have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.ball cc R) := by
      intro w hw
      have hwne : w ≠ 1 := by
        intro h1
        have h3 := (hball w hw).2.2
        rw [h1] at h3
        simp at h3
        linarith
      exact (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hwne)).differentiableWithinAt
    intro w hw
    exact hdiff.analyticAt (Metric.isOpen_ball.mem_nhds hw)
  -- ## the evaluation point
  have hdist : ‖z₀ - cc‖ ≤ 2 * δ := by
    have h1 : z₀ - cc = (((σ - s₀ : ℝ)) : ℂ) := by
      apply Complex.ext <;> simp [hz₀def, hccdef]
    have hσs₀ : σ - s₀ ≤ 0 := by
      have hσle : σ ≤ s₀ := by rw [hs₀def]; exact le_max_left _ _
      linarith
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hσs₀]
    rcases lt_or_ge σ (1 + δ) with h | h
    · have hs : s₀ = 1 + δ := by rw [hs₀def]; exact max_eq_right h.le
      rw [hs]; linarith
    · have hs : s₀ = σ := by rw [hs₀def]; exact max_eq_left h
      rw [hs]; linarith [hδpos]
  have hz0mem : z₀ ∈ Metric.ball cc R := by
    rw [Metric.mem_ball, dist_eq_norm, hRdef]
    linarith
  have hdist_lt : m < R - ‖z₀ - cc‖ := by
    rw [hRdef, hmdef]
    linarith
  -- ## the lower bound at the centre
  have hmlow : m ≤ ‖DirichletCharacter.LFunction χ cc‖ := by
    have hccre : cc.re = s₀ := by simp [hccdef]
    have h1 : 1 + δ ≤ cc.re := by rw [hccre]; exact le_max_right _ _
    have h := Work.BMF.N4chain.LFunction_norm_lower_of_re χ (s := cc) (y := δ) hδpos hδone h1
    rw [hmdef]
    exact h
  refine ⟨?_, ?_⟩
  · -- non-vanishing at the point itself
    refine h₀ N χ hχprim hχne σ t ht3 ?_
    have hden : 0 < Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3))) := by
      rw [← VKD67_eq]
      exact hDpos
    have hle : c / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤
        c₀ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) := by
      rw [div_le_div_iff_of_pos_right hden]
      linarith [hcc₀']
    linarith
  · -- the logarithmic-derivative bound
    have hlog2M : Real.log (2 * M) ≤ 64 * L := by
      have hA : (7 : ℝ) ≤ (N : ℝ) * (|t| + 3) := by
        have hN1 : (1 : ℝ) ≤ (N : ℝ) := N_cast_one_le (N := N)
        nlinarith [abs_nonneg t]
      have h2Mle : 2 * M ≤ ((N : ℝ) * (|t| + 3)) ^ 4 := by
        rw [hMdef]
        have hA3 : (343 : ℝ) ≤ ((N : ℝ) * (|t| + 3)) ^ 3 := by
          nlinarith [sq_nonneg ((N : ℝ) * (|t| + 3) - 7), hA]
        have h1 : 343 * ((N : ℝ) * (|t| + 3)) ≤ ((N : ℝ) * (|t| + 3)) ^ 3 * ((N : ℝ) * (|t| + 3)) :=
          mul_le_mul_of_nonneg_right hA3 (by linarith)
        have h2 : ((N : ℝ) * (|t| + 3)) ^ 3 * ((N : ℝ) * (|t| + 3)) = ((N : ℝ) * (|t| + 3)) ^ 4 := by
          ring
        have h3 : 8 * (N : ℝ) * (|t| + 4) ≤ 343 * ((N : ℝ) * (|t| + 3)) := by
          have hN1 : (1 : ℝ) ≤ (N : ℝ) := N_cast_one_le (N := N)
          nlinarith [abs_nonneg t]
        linarith [h1, h2, h3]
      have hpos2M : 0 < 2 * M := by linarith [hM2]
      have hlogpow : Real.log (((N : ℝ) * (|t| + 3)) ^ 4) =
          4 * Real.log ((N : ℝ) * (|t| + 3)) := by
        have hpos : (0 : ℝ) < (N : ℝ) * (|t| + 3) := by
          have hN1 : (1 : ℝ) ≤ (N : ℝ) := N_cast_one_le (N := N)
          nlinarith [abs_nonneg t]
        rw [Real.log_pow]
        norm_num
      calc Real.log (2 * M) ≤ Real.log (((N : ℝ) * (|t| + 3)) ^ 4) :=
            Real.log_le_log hpos2M h2Mle
        _ = 4 * Real.log ((N : ℝ) * (|t| + 3)) := hlogpow
        _ = 4 * L := by rw [hLdef]
        _ ≤ 64 * L := by linarith [hL1]
    have hlog1m : Real.log (1 / m) ≤ K₂ * L := by
      have hm2 : (1 : ℝ) / m = 2 * D / c := by
        rw [hmdef, hδdef]; field_simp
      have hlog : Real.log (2 * D / c) = Real.log 2 + Real.log D + Real.log (1 / c) := by
        rw [show 2 * D / c = 2 * D * (1 / c) by ring]
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) (by positivity)]
      have hlogc : 0 ≤ Real.log (1 / c) := Real.log_nonneg (by rw [le_div_iff₀ hcpos]; linarith)
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      rw [hm2, hlog, hK₂def]
      nlinarith [hlogD, hlogc, hlog2, hL1]
    have hsum_log : 2 * (Real.log (2 * M) - Real.log m) ≤ 2 * ((64 + K₂) * L) := by
      have hinv : Real.log m = -Real.log (1 / m) := by
        rw [one_div, Real.log_inv, neg_neg]
      rw [hinv]
      linarith
    have hB : (‖z₀ - cc‖ + m) / ((R - ‖z₀ - cc‖ - m) * m) ≤ 10 / δ := by
      have hnum : ‖z₀ - cc‖ + m ≤ 2.5 * δ := by rw [hmdef]; linarith
      have hden : δ ^ 2 / 4 ≤ (R - ‖z₀ - cc‖ - m) * m := by
        rw [hRdef, hmdef] at *
        nlinarith [hdist, hδpos]
      have hc_nn : (0 : ℝ) ≤ 2.5 * δ := by linarith
      have hdpos : 0 < δ ^ 2 / 4 := by positivity
      calc (‖z₀ - cc‖ + m) / ((R - ‖z₀ - cc‖ - m) * m)
          ≤ (2.5 * δ) / (δ ^ 2 / 4) := div_le_div₀ hc_nn hnum hdpos hden
        _ = 10 / δ := by
              field_simp
              ring
    have hAnn : 0 ≤ 2 * (Real.log (2 * M) - Real.log m) := by
      have h1 : (1 : ℝ) ≤ 2 * M := by linarith [hM2]
      have h2 : (1 : ℝ) ≤ 1 / m := by
        rw [le_div_iff₀ hmpos]; linarith [hmone]
      have h3 : 0 ≤ Real.log (2 * M) := Real.log_nonneg h1
      have h4 : Real.log m = -Real.log (1 / m) := by rw [one_div, Real.log_inv, neg_neg]
      rw [h4]
      have h5 : 0 ≤ Real.log (1 / m) := Real.log_nonneg h2
      linarith
    have hBnn : 0 ≤ (‖z₀ - cc‖ + m) / ((R - ‖z₀ - cc‖ - m) * m) := by
      apply div_nonneg
      · linarith [norm_nonneg (z₀ - cc), hmpos]
      · have h1 : 0 < R - ‖z₀ - cc‖ - m := by linarith [hdist_lt]
        positivity
    have hdisk := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic
        (g := DirichletCharacter.LFunction χ) (c := cc) (R := R) (m := m) (M := M)
        hRpos hmpos hmM han hzf hMbound hmlow (z₀ := z₀) hz0mem m hmpos hdist_lt
    have htarget : ‖logDeriv (DirichletCharacter.LFunction χ) z₀‖ ≤
        (200 * (64 + K₂) / c + 1) * L ^ 4 := by
      calc ‖logDeriv (DirichletCharacter.LFunction χ) z₀‖
          = ‖deriv (DirichletCharacter.LFunction χ) z₀ / DirichletCharacter.LFunction χ z₀‖ := by
            rw [logDeriv_apply]
        _ ≤ 2 * (Real.log (2 * M) - Real.log m) * (‖z₀ - cc‖ + m) /
              ((R - ‖z₀ - cc‖ - m) * m) := hdisk
        _ = 2 * (Real.log (2 * M) - Real.log m) *
              ((‖z₀ - cc‖ + m) / ((R - ‖z₀ - cc‖ - m) * m)) := by rw [mul_div_assoc]
        _ ≤ 2 * ((64 + K₂) * L) * (10 / δ) :=
              mul_le_mul hsum_log hB hBnn (by
                have hKL : 0 ≤ (64 + K₂) * L := by linarith [hK₂pos.le, hL1]
                linarith)
        _ = 20 * (64 + K₂) * L / δ := by ring
        _ ≤ (200 * (64 + K₂) / c + 1) * L ^ 4 := by
              have h1δ : (1 : ℝ) / δ = D / c := by rw [hδdef]; field_simp
              rw [show 20 * (64 + K₂) * L / δ = 20 * (64 + K₂) * L * (1 / δ) by ring, h1δ]
              have h2 : 20 * (64 + K₂) * L * (D / c) ≤ 20 * (64 + K₂) * L * (4 * L ^ 2 / c) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact div_le_div_of_nonneg_right hD4 hcpos.le
              have h3 : 20 * (64 + K₂) * L * (4 * L ^ 2 / c) = 80 * (64 + K₂) * L ^ 3 / c := by ring
              rw [h3] at h2
              have hL3 : L ^ 3 ≤ L ^ 4 := by
                have h := mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ L ^ 3)
                simpa [pow_succ] using h
              have hKL : 0 ≤ (64 + K₂) := by linarith
              have hcoef : 0 ≤ 80 * (64 + K₂) / c := div_nonneg (by linarith) hcpos.le
              have h5 : 80 * (64 + K₂) * L ^ 3 / c = (80 * (64 + K₂) / c) * L ^ 3 := by ring
              rw [h5] at h2
              have h6 : (80 * (64 + K₂) / c) * L ^ 3 ≤ (80 * (64 + K₂) / c) * L ^ 4 :=
                mul_le_mul_of_nonneg_left hL3 hcoef
              have h7 : (80 * (64 + K₂) / c) * L ^ 4 ≤
                  (200 * (64 + K₂) / c + 1) * L ^ 4 := by
                have h8 : 0 ≤ L ^ 4 := by positivity
                have h9 : 80 * (64 + K₂) / c ≤ 200 * (64 + K₂) / c := by
                  have hXc : 0 ≤ (64 + K₂) / c := div_nonneg hKL hcpos.le
                  have ha : 80 * (64 + K₂) / c = 80 * ((64 + K₂) / c) := by ring
                  have hb : 200 * (64 + K₂) / c = 200 * ((64 + K₂) / c) := by ring
                  linarith
                have h10 : 80 * (64 + K₂) / c ≤ 200 * (64 + K₂) / c + 1 := by linarith
                exact mul_le_mul_of_nonneg_right h10 h8
              linarith [h2, h6, h7]
    rw [hz₀def] at htarget
    exact htarget

end Work.BMF.VKPrimeSums
