import Mathlib
import Submission.Work.EQ.Ladf.wsec_defs
import Submission.Work.EQ.Ladf.wsec_geo
import Submission.Work.EQ.H0_tail_bounded
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.HeteroAlgebra

/-!
# The descent steps of `wsec_tails`

`wsec_step_bwd` / `wsec_step_fwd`: one level of the "principal descent" that turns the depth-`M`
tail of the *witness* into the depth-`M` tail of the whole local section, using
`Work.EQ.Ladf.wsec_germ_step` for the principal branch and the quantitative separation facts
`fwdAlt_far_A2` / `invBranch_false_far_A1` to exclude the other one.
-/

namespace Work.EQ.Ladf

open Work.EQ Complex Filter _root_.Topology
open scoped Topology

/-- `ugermC a h 0 = A₂ = (1/2, 0)`. -/
theorem ugermC_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) : ugermC a h 0 = ((1 / 2 : ℂ), (0 : ℂ)) := by
  have h0 : germC a h 0 = ((-1 / 2 : ℂ), (0 : ℂ)) := germC_value (a := a) (h := h) (r := r) ha0 ha1 hh
  simp only [ugermC, h0, eqMirror]
  norm_num

/-- `ugermC a h` is continuous at `0`. -/
theorem continuousAt_ugermC_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) : ContinuousAt (ugermC a h) 0 := by
  obtain ⟨ρ, hρ, hAn⟩ := germC_analytic ha0 ha1 hh
  have hc : ContinuousAt (germC a h) 0 := (hAn 0 (Metric.mem_ball_self hρ)).continuousAt
  have hm : ContinuousAt (fun z : ℂ × ℂ => eqMirror z) (germC a h 0) :=
    (continuous_fst.neg.prodMk continuous_snd).continuousAt
  have hfun : ugermC a h = fun u => eqMirror (germC a h u) := rfl
  rw [hfun]
  exact hm.comp hc

/-- **Backward descent step.**  If the level `-(n+1)` point of a chain is the unstable germ point at
parameter `λ^{n+1} w` with small parameter, and its level `-n` point is close to `A₂`, then the
level `-n` point is the germ point at parameter `λ^n w`. -/
theorem wsec_step_bwd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ {q : ChainData}, IsChain a h q → ∀ {n : ℕ} {w : ℂ},
      q.1 (-((n : ℤ) + 1)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * w) →
      ‖(((eqLam a : ℝ) : ℂ) ^ (n + 1) * w)‖ < δ₂ →
      ‖q.1 (-(n : ℤ)) - ((1 / 2 : ℂ), (0 : ℂ))‖ < 1 / 2 →
      q.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * w) := by
  obtain ⟨δstep, hδstep, -, -, hstep3, -⟩ := wsec_germ_step ha0 ha1 hh
  obtain ⟨ρfar, hρfar, hfar⟩ := fwdAlt_far_A2 ha0 ha1
  have hcont := continuousAt_ugermC_zero (a := a) (h := h) (r := r) ha0 ha1 hh
  have hu0 := ugermC_zero (a := a) (h := h) (r := r) ha0 ha1 hh
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ), dist (ugermC a h u) ((1 / 2 : ℂ), (0 : ℂ))
      < min ρfar (1 / 2) := by
    have h1 : ∀ᶠ u in 𝓝 (0 : ℂ), ugermC a h u ∈
        Metric.ball (ugermC a h 0) (min ρfar (1 / 2)) :=
      hcont.eventually (Metric.ball_mem_nhds _ (by positivity))
    filter_upwards [h1] with u hu
    show dist (ugermC a h u) ((1 / 2 : ℂ), (0 : ℂ)) < min ρfar (1 / 2)
    have h2 : dist (ugermC a h u) (ugermC a h 0) < min ρfar (1 / 2) := Metric.mem_ball.mp hu
    rwa [hu0] at h2
  obtain ⟨δc, hδc, hδcball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨min δstep (min δc (1 / 2)), by positivity, ?_⟩
  intro q hq n w hP hsmall hnearQ
  have hlt : ‖(((eqLam a : ℝ) : ℂ) ^ (n + 1) * w)‖ < min δstep (min δc (1 / 2)) := hsmall
  have h1 : ‖(((eqLam a : ℝ) : ℂ) ^ (n + 1) * w)‖ < δstep :=
    lt_of_lt_of_le hlt (min_le_left _ _)
  have h2 : ‖(((eqLam a : ℝ) : ℂ) ^ (n + 1) * w)‖ < δc :=
    lt_of_lt_of_le hlt (le_trans (min_le_right _ _) (min_le_left _ _))
  -- the germ point at level `-(n+1)` is within `ρfar` of `A₂`
  have hPnear : ‖ugermC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * w) - ((1 / 2 : ℂ), (0 : ℂ))‖
      < ρfar := by
    have h3 : dist (ugermC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * w)) ((1 / 2 : ℂ), (0 : ℂ))
        < min ρfar (1 / 2) :=
      hδcball (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact h2)
    rw [dist_eq_norm] at h3
    linarith [h3, min_le_left ρfar (1 / 2)]
  -- the pair is regular
  have hpair : RegPair a (q.1 (-((n : ℤ) + 1))) (q.1 (-(n : ℤ))) := by
    have h := hq.1 (-((n : ℤ) + 1))
    simpa [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring] using h
  rcases fwd_pair_dichotomy hpair.1 hpair.2.1 with hcase | hcase
  · rw [hcase, hP, hstep3 _ (by rw [Metric.mem_ball, dist_zero_right]; exact h1)]
    congr 1
    rw [div_eq_iff (Complex.ofReal_ne_zero.mpr (ne_of_gt (eqLam_pos' ha0 ha1)))]
    rw [pow_succ]
    ring
  · exfalso
    have hfar' : 1 ≤ ‖q.1 (-(n : ℤ)) - ((1 / 2 : ℂ), (0 : ℂ))‖ := by
      rw [hcase, hP]
      exact hfar _ hPnear
    linarith

/-- `germC a h` is continuous at `0`. -/
theorem continuousAt_germC_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) : ContinuousAt (germC a h) 0 := by
  obtain ⟨ρ, hρ, hAn⟩ := germC_analytic ha0 ha1 hh
  exact (hAn 0 (Metric.mem_ball_self hρ)).continuousAt

/-- **Forward descent step.**  If the level `n+1` point of a chain is the stable germ point at
parameter `λ^{n+1} v` with small parameter, and its level `n` point is close to `A₁`, then the
level `n` point is the germ point at parameter `λ^n v`. -/
theorem wsec_step_fwd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ {q : ChainData}, IsChain a h q → ∀ {n : ℕ} {v : ℂ},
      q.1 ((n : ℤ) + 1) = germC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * v) →
      ‖(((eqLam a : ℝ) : ℂ) ^ (n + 1) * v)‖ < δ₁ →
      ‖q.1 (n : ℤ) - ((-1 / 2 : ℂ), (0 : ℂ))‖ < 1 / 2 →
      q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * v) := by
  obtain ⟨δstep, hδstep, hstep1, -, -, -⟩ := wsec_germ_step ha0 ha1 hh
  obtain ⟨ρfar, hρfar, hfar⟩ := invBranch_false_far_A1 ha1
  have hlam : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hcont := continuousAt_germC_zero (a := a) (h := h) (r := r) ha0 ha1 hh
  have hu0 := germC_value (a := a) (h := h) (r := r) ha0 ha1 hh
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ),
      dist (germC a h u) ((-1 / 2 : ℂ), (0 : ℂ)) < min ρfar (1 / 2) := by
    have h1 : ∀ᶠ u in 𝓝 (0 : ℂ),
        germC a h u ∈ Metric.ball (germC a h 0) (min ρfar (1 / 2)) :=
      hcont.eventually (Metric.ball_mem_nhds _ (by positivity))
    filter_upwards [h1] with u hu
    show dist (germC a h u) ((-1 / 2 : ℂ), (0 : ℂ)) < min ρfar (1 / 2)
    have h2 : dist (germC a h u) (germC a h 0) < min ρfar (1 / 2) := Metric.mem_ball.mp hu
    rwa [hu0] at h2
  obtain ⟨δc, hδc, hδcball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨min (eqLam a * δstep) (min δc (1 / 2)), lt_min (mul_pos hlam hδstep) (by positivity), ?_⟩
  intro q hq n v hP hsmall hnearQ
  have h1 : ‖(((eqLam a : ℝ) : ℂ) ^ (n + 1) * v)‖ < eqLam a * δstep :=
    lt_of_lt_of_le hsmall (min_le_left _ _)
  have h2 : ‖(((eqLam a : ℝ) : ℂ) ^ (n + 1) * v)‖ < δc :=
    lt_of_lt_of_le hsmall (le_trans (min_le_right _ _) (min_le_left _ _))
  have hQnear : ‖germC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * v) - ((-1 / 2 : ℂ), (0 : ℂ))‖
      < ρfar := by
    have h3 : dist (germC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * v)) ((-1 / 2 : ℂ), (0 : ℂ))
        < min ρfar (1 / 2) :=
      hδcball (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact h2)
    rw [dist_eq_norm] at h3
    linarith [h3, min_le_left ρfar (1 / 2)]
  have hpair : RegPair a (q.1 (n : ℤ)) (q.1 ((n : ℤ) + 1)) := hq.1 (n : ℤ)
  rcases eqRelC_solutions hpair.1 hpair.2.2 with hcase | hcase
  · rw [hcase, hP]
    have hnorm : ‖(((eqLam a : ℝ) : ℂ) ^ n * v)‖ < δstep := by
      have hfin : eqLam a * ‖(((eqLam a : ℝ) : ℂ) ^ n * v)‖ < eqLam a * δstep := by
        have hpow : (eqLam a : ℂ) * (((eqLam a : ℝ) : ℂ) ^ n * v)
            = ((eqLam a : ℝ) : ℂ) ^ (n + 1) * v := by rw [pow_succ]; ring
        have : ‖(((eqLam a : ℝ) : ℂ) ^ (n + 1) * v)‖
            = eqLam a * ‖(((eqLam a : ℝ) : ℂ) ^ n * v)‖ := by
          rw [← hpow, norm_mul, Complex.norm_of_nonneg (le_of_lt hlam)]
        rwa [this] at h1
      exact lt_of_mul_lt_mul_left hfin (le_of_lt hlam)
    have hkey := hstep1 (((eqLam a : ℝ) : ℂ) ^ n * v)
      (by rw [Metric.mem_ball, dist_zero_right]; exact hnorm)
    have hpow : (eqLam a : ℂ) * (((eqLam a : ℝ) : ℂ) ^ n * v)
        = ((eqLam a : ℝ) : ℂ) ^ (n + 1) * v := by rw [pow_succ]; ring
    rwa [hpow] at hkey
  · exfalso
    have hfar' : 1 ≤ ‖q.1 (n : ℤ) - ((-1 / 2 : ℂ), (0 : ℂ))‖ := by
      rw [hcase, hP]
      exact hfar _ hQnear
    linarith

end Work.EQ.Ladf
