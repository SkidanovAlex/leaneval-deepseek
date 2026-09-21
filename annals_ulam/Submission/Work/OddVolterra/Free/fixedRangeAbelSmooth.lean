import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib
import Submission.Work.OddCurve.LowSlope.gapKernel_derivs

/-!
# Smoothness of the fixed-range Abel integral in the exterior variable

For `a > 0`, a weight `w` continuous on `[0,a]` and `n : ℕ`, the *weighted Abel integral of order*
`n + 1/2`

  `abelPsi a n w v = ∫ c in 0..a, w c * (v²-c²)^{-(n+1/2)}`

is `C^∞` on the exterior interval `Ioi a`.  The range of integration is fixed and strictly below
every point of `Ioi a`, so the only `v`-dependence sits in a kernel which is smooth on a
neighbourhood of `Ioi a ×ˢ Icc 0 a`; the weight does not depend on `v` at all.  Hence
differentiating under the integral sign raises `n` by one:

  `d/dv abelPsi a n w v = -(2n+1) · v · abelPsi a (n+1) w v`   (`a < v`).

Since `abelPsi` with index `n+1` is again an integral of the same shape, this gives `C^∞` by
induction on the number of derivatives, the induction hypothesis being run for *all* indices `n`
simultaneously (`abelPsi_contDiffOn`).

The target `fixedRangeAbelSmooth` is the case `n = 0` and `w c = c * Θ c`.

## Main results

* `Work.OddVolterra.Free.abelPsi` — the weighted Abel integral;
* `Work.OddVolterra.Free.abelPsi_continuousOn` — continuity on `Ioi a`;
* `Work.OddVolterra.Free.abelPsi_hasDerivAt` — the differentiation formula;
* `Work.OddVolterra.Free.abelPsi_contDiffOn` — `C^k` for every `k`;
* `Work.OddVolterra.Free.fixedRangeAbelSmooth` — the requested statement.
-/

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Interval Topology ContDiff

noncomputable section

/-- The weighted Abel integral of order `n + 1/2` over the fixed range `[0,a]`:
`v ↦ ∫ c in 0..a, w c * (v² - c²) ^ (-(n + 1/2))`. -/
def abelPsi (a : ℝ) (n : ℕ) (w : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ c in (0 : ℝ)..a, w c * (v ^ 2 - c ^ 2) ^ (-((n : ℝ) + 1 / 2))

section Kernel

/-- `x² - t² > 0` for `0 ≤ t < x`. -/
lemma abelKernel_sq_sub_sq_pos {t x : ℝ} (ht : 0 ≤ t) (h : t < x) : 0 < x ^ 2 - t ^ 2 := by
  have h1 : 0 < x - t := sub_pos.mpr h
  have h2 : 0 < x + t := by linarith
  nlinarith [mul_pos h1 h2]

/-- The kernel `t ↦ (x² - t²)^e` is continuous on any set where `0 ≤ t < x`. -/
lemma abelKernel_continuousOn_rpow {x e : ℝ} {s : Set ℝ}
    (hxs : ∀ t ∈ s, t < x) (ht0 : ∀ t ∈ s, 0 ≤ t) :
    ContinuousOn (fun t : ℝ => (x ^ 2 - t ^ 2) ^ e) s := by
  refine ContinuousOn.rpow_const ?_ ?_
  · exact continuousOn_const.sub (continuousOn_id.pow 2)
  · intro t ht
    exact Or.inl (ne_of_gt (abelKernel_sq_sub_sq_pos (ht0 t ht) (hxs t ht)))

end Kernel

/-- **Continuity** of the weighted Abel integral on the exterior interval. -/
lemma abelPsi_continuousOn {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Set.Icc 0 a)) (n : ℕ) :
    ContinuousOn (abelPsi a n w) (Set.Ioi a) := by
  intro v hv
  have hv' : a < v := hv
  set δ : ℝ := (v - a) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (w a)) (hB a ⟨ha.le, le_rfl⟩)
  set β : ℝ := ((v + a) / 2) ^ 2 - a ^ 2 with hβdef
  have hβ : 0 < β := by
    have h1 : 0 < (v + a) / 2 - a := by linarith
    have h2 : 0 < (v + a) / 2 + a := by linarith
    have h3 : 0 < ((v + a) / 2 - a) * ((v + a) / 2 + a) := mul_pos h1 h2
    have h4 : ((v + a) / 2 - a) * ((v + a) / 2 + a) = β := by
      rw [hβdef]; ring
    rwa [h4] at h3
  have hsub : (Ι (0 : ℝ) a) ⊆ Set.Icc 0 a := by
    rw [Set.uIoc_of_le ha.le]
    intro t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hball : Metric.ball v δ ∈ 𝓝[Set.Ioi a] v :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds v hδ)
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (F := fun x c => w c * (x ^ 2 - c ^ 2) ^ (-((n : ℝ) + 1 / 2)))
    (x₀ := v) (bound := fun _ : ℝ => B * β ^ (-((n : ℝ) + 1 / 2)))
    (a := 0) (b := a) (s := Set.Ioi a) (μ := volume) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxa : a < x := hx
    have hcont : ContinuousOn (fun c : ℝ => (x ^ 2 - c ^ 2) ^ (-((n : ℝ) + 1 / 2)))
        (Ι (0 : ℝ) a) :=
      abelKernel_continuousOn_rpow (x := x) (e := -((n : ℝ) + 1 / 2))
        (fun t ht => lt_of_le_of_lt (hsub ht).2 hxa) (fun t ht => (hsub ht).1)
    exact ((hw.mono hsub).mul hcont).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin, hball] with x hx hxv
    filter_upwards with c hc
    rw [Set.uIoc_of_le ha.le] at hc
    obtain ⟨hc0, hca⟩ := hc
    have hxlb : (v + a) / 2 < x := by
      rw [Metric.mem_ball, Real.dist_eq] at hxv
      rcases abs_lt.mp hxv with ⟨h1, _⟩
      rw [hδdef] at h1; linarith
    have hxc : 0 < x ^ 2 - c ^ 2 :=
      abelKernel_sq_sub_sq_pos (le_of_lt hc0) (lt_of_le_of_lt hca (show a < x from hx))
    have hle : β ≤ x ^ 2 - c ^ 2 := by
      rw [hβdef]
      nlinarith [hxlb, hca, hc0, sq_nonneg ((v + a) / 2), sq_nonneg c, sq_nonneg x]
    have hp : -((n : ℝ) + 1 / 2) ≤ 0 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h1 : |w c| ≤ B := by
      have := hB c ⟨le_of_lt hc0, hca⟩
      rwa [Real.norm_eq_abs] at this
    have h3 : 0 ≤ (x ^ 2 - c ^ 2) ^ (-((n : ℝ) + 1 / 2)) := Real.rpow_nonneg hxc.le _
    have h4 : (x ^ 2 - c ^ 2) ^ (-((n : ℝ) + 1 / 2)) ≤ β ^ (-((n : ℝ) + 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos hβ hle hp
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h3]
    exact mul_le_mul h1 h4 h3 hB0
  · exact intervalIntegrable_const
  · filter_upwards with c hc
    rw [Set.uIoc_of_le ha.le] at hc
    obtain ⟨hc0, hca⟩ := hc
    have hp : 0 < v ^ 2 - c ^ 2 :=
      abelKernel_sq_sub_sq_pos (le_of_lt hc0) (lt_of_le_of_lt hca hv')
    have h1 : ContinuousAt (fun x : ℝ => x ^ 2 - c ^ 2) v :=
      (continuousAt_id.pow 2).sub continuousAt_const
    have h2 : ContinuousAt (fun x : ℝ => (x ^ 2 - c ^ 2) ^ (-((n : ℝ) + 1 / 2))) v :=
      h1.rpow_const (Or.inl (ne_of_gt hp))
    exact (h2.const_mul (w c)).continuousWithinAt

/-- **Differentiation formula.**  On `Ioi a` the derivative of the weighted Abel integral of order
`n + 1/2` is `-(2n+1) · v` times the integral of order `n + 3/2`. -/
lemma abelPsi_hasDerivAt {a : ℝ} (ha : 0 < a) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Set.Icc 0 a)) (n : ℕ) {v : ℝ} (hv : a < v) :
    HasDerivAt (abelPsi a n w) (-(2 * (n : ℝ) + 1) * v * abelPsi a (n + 1) w v) v := by
  set δ : ℝ := (v - a) / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδa : a < v - δ := by rw [hδdef]; linarith
  set F' : ℝ → ℝ → ℝ := fun x t =>
    w t * ((-(2 * (n : ℝ) + 1) * x) * (x ^ 2 - t ^ 2) ^ (-(((n + 1 : ℕ) : ℝ) + 1 / 2)))
    with hF'def
  have hx_of_mem : ∀ x ∈ Metric.ball v δ, a < x := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, hδdef] at hx
    rcases abs_lt.mp hx with ⟨h1, _⟩
    linarith
  have hF_cont : ∀ x ∈ Metric.ball v δ,
      ContinuousOn (fun t : ℝ => w t * (x ^ 2 - t ^ 2) ^ (-((n : ℝ) + 1 / 2)))
        (Set.Icc 0 a) := by
    intro x hx
    refine hw.mul ?_
    refine abelKernel_continuousOn_rpow ?_ ?_
    · intro t ht; exact lt_of_le_of_lt ht.2 (hx_of_mem x hx)
    · intro t ht; exact ht.1
  have hF'_cont : ContinuousOn (F' v) (Set.Icc 0 a) := by
    rw [hF'def]
    refine hw.mul ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine abelKernel_continuousOn_rpow ?_ ?_
    · intro t ht; exact lt_of_le_of_lt ht.2 hv
    · intro t ht; exact ht.1
  have hK_cont : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2)
      (Set.Icc (v - δ) (v + δ) ×ˢ Set.Icc 0 a) := by
    rw [hF'def]
    have hxt : ∀ p ∈ Set.Icc (v - δ) (v + δ) ×ˢ Set.Icc 0 a, p.2 < p.1 := by
      intro p hp
      exact lt_of_lt_of_le (lt_of_le_of_lt hp.2.2 hδa) hp.1.1
    have hw2 : ContinuousOn (fun p : ℝ × ℝ => w p.2)
        (Set.Icc (v - δ) (v + δ) ×ˢ Set.Icc 0 a) :=
      hw.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have hbase : ContinuousOn
        (fun p : ℝ × ℝ => (p.1 ^ 2 - p.2 ^ 2) ^ (-(((n + 1 : ℕ) : ℝ) + 1 / 2)))
        (Set.Icc (v - δ) (v + δ) ×ˢ Set.Icc 0 a) := by
      refine ContinuousOn.rpow_const
        ((continuous_fst.pow 2).sub (continuous_snd.pow 2)).continuousOn ?_
      intro p hp
      exact Or.inl (ne_of_gt (abelKernel_sq_sub_sq_pos hp.2.1 (hxt p hp)))
    exact hw2.mul ((continuous_const.mul continuous_fst).continuousOn.mul hbase)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hK_cont
  have hbound : ∀ x ∈ Metric.ball v δ, ∀ t ∈ Set.Icc 0 a, |F' x t| ≤ C := by
    intro x hx t ht
    have hx' : x ∈ Set.Icc (v - δ) (v + δ) := by
      rw [Metric.mem_ball, Real.dist_eq] at hx
      rcases abs_lt.mp hx with ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    have := hC (x, t) ⟨hx', ht⟩
    rwa [Real.norm_eq_abs] at this
  have hdiff : ∀ x ∈ Metric.ball v δ, ∀ t ∈ Set.Icc 0 a,
      HasDerivAt (fun y : ℝ => w t * (y ^ 2 - t ^ 2) ^ (-((n : ℝ) + 1 / 2))) (F' x t) x := by
    intro x hx t ht
    have hxc : 0 < x ^ 2 - t ^ 2 :=
      abelKernel_sq_sub_sq_pos ht.1 (lt_of_le_of_lt ht.2 (hx_of_mem x hx))
    have hd := Work.OddCurve.LowSlope.gapKernel_hasDerivAt_sq_sub_rpow
      (t := t) (p := -((n : ℝ) + 1 / 2)) (x := x) (ne_of_gt hxc)
    have hmul := hd.const_mul (w t)
    have hexp : (-((n : ℝ) + 1 / 2)) - 1 = -(((n + 1 : ℕ) : ℝ) + 1 / 2) := by push_cast; ring
    have hvaleq : w t * ((-((n : ℝ) + 1 / 2)) * (x ^ 2 - t ^ 2) ^ ((-((n : ℝ) + 1 / 2)) - 1)
        * (2 * x)) = F' x t := by
      rw [hF'def, hexp]
      ring
    exact hmul.congr_deriv hvaleq
  have hmain := Work.OddCurve.LowSlope.gapKernel_integral_hasDerivAt (m := 0) (M' := a) (u := v)
    (δ := δ) (C := C) ha.le hδ hF_cont hF'_cont hbound hdiff
  have hval : (∫ t in (0 : ℝ)..a, F' v t) = (-(2 * (n : ℝ) + 1) * v) * abelPsi a (n + 1) w v := by
    rw [hF'def]
    rw [show (∫ t in (0 : ℝ)..a,
        w t * ((-(2 * (n : ℝ) + 1) * v) * (v ^ 2 - t ^ 2) ^ (-(((n + 1 : ℕ) : ℝ) + 1 / 2))))
        = ∫ t in (0 : ℝ)..a,
          (-(2 * (n : ℝ) + 1) * v) * (w t * (v ^ 2 - t ^ 2) ^ (-(((n + 1 : ℕ) : ℝ) + 1 / 2)))
        from intervalIntegral.integral_congr (fun t _ => by ring)]
    rw [intervalIntegral.integral_const_mul, abelPsi]
  rw [hval] at hmain
  exact hmain

/-- **Smoothness.**  The weighted Abel integral of order `n + 1/2` is `C^k` on `Ioi a` for every
`k`, hence smooth. -/
lemma abelPsi_contDiffOn {a : ℝ} (ha : 0 < a) (n k : ℕ) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Set.Icc 0 a)) :
    ContDiffOn ℝ (k : ℕ∞ω) (abelPsi a n w) (Set.Ioi a) := by
  induction k generalizing n w with
  | zero => exact contDiffOn_zero.2 (abelPsi_continuousOn ha hw n)
  | succ k ih =>
    have hdiff : DifferentiableOn ℝ (abelPsi a n w) (Set.Ioi a) := fun v hv =>
      (abelPsi_hasDerivAt ha hw n hv).differentiableAt.differentiableWithinAt
    have han : ((k : ℕ∞ω) = ω → AnalyticOn ℝ (abelPsi a n w) (Set.Ioi a)) := by
      intro h; exact absurd h (by simp)
    have hderiv : ContDiffOn ℝ (k : ℕ∞ω) (deriv (abelPsi a n w)) (Set.Ioi a) := by
      have hlin : ContDiffOn ℝ (k : ℕ∞ω) (fun v : ℝ => -(2 * (n : ℝ) + 1) * v)
          (Set.Ioi a) :=
        contDiffOn_const.mul contDiffOn_id
      have hmain : ContDiffOn ℝ (k : ℕ∞ω)
          (fun v : ℝ => -(2 * (n : ℝ) + 1) * v * abelPsi a (n + 1) w v) (Set.Ioi a) :=
        hlin.mul (ih (n + 1) hw)
      exact hmain.congr (fun v hv => (abelPsi_hasDerivAt ha hw n hv).deriv)
    rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp]
    exact (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).2 ⟨hdiff, han, hderiv⟩

/-- The fixed-range Abel integral `v ↦ ∫ c in 0..a, c Θ c (v²-c²)^{-1/2}` is smooth on the
exterior of the integration range, for `Θ` continuous on `[0,a]`. -/
theorem fixedRangeAbelSmooth {a : ℝ} (ha : 0 < a) {Θ : ℝ → ℝ}
    (hΘ : ContinuousOn Θ (Set.Icc 0 a)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : ℝ => ∫ c in (0 : ℝ)..a, c * Θ c * (v ^ 2 - c ^ 2) ^ (-(1 / 2 : ℝ))) (Set.Ioi a) := by
  have hw : ContinuousOn (fun c : ℝ => c * Θ c) (Set.Icc 0 a) := continuousOn_id.mul hΘ
  refine (contDiffOn_infty.2 fun k => abelPsi_contDiffOn ha 0 k hw).congr ?_
  intro v _
  rw [abelPsi]
  refine intervalIntegral.integral_congr fun c _ => ?_
  rw [show (-(((0 : ℕ) : ℝ) + 1 / 2)) = -(1 / 2 : ℝ) by norm_num]

end

end Work.OddVolterra.Free
