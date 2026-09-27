import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.germCHelpers
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.germC_W_coord
import Submission.Work.EQ.ugermC_snd_eq_neg_mul
import Submission.Work.EQ.germC_graph
import Submission.Work.EQ.branchPt_meromorphic
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.germC_snd_analyticOnNhd_ball
import Submission.Work.EQ.meromorphicAt_value_of_seq_germC_snd
import Submission.Work.EQ.eventuallyEq_zero_of_meromorphicAt_of_seq_zero
import Submission.Work.EQ.eventually_ne_zero_of_meromorphicAt_of_seq_ne_zero

namespace Work.EQ

open Complex Metric Filter Set
open scoped Topology

noncomputable section


/-! ## 0. The denominator of `germC` on `ball 0 ρY` -/

/-- The third `dslope` of `germC a h` at `0` is `1 - λ ≠ 0` (`a ≠ 0`). -/
lemma germC_dslope_den_zero_ne {a : ℝ} (ha0 : 0 < a) {h : ℂ → ℂ} (hAn : AnalyticAt ℂ h 0)
    (hd : deriv h 0 = -1) :
    dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 0 ≠ 0 := by
  rw [dslope_same]
  have hfd : DifferentiableAt ℂ (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 := by
    have h1 : AnalyticAt ℂ (fun v : ℂ => (eqLam a : ℂ) * v) 0 :=
      analyticAt_const.mul analyticAt_id
    have hAn' : AnalyticAt ℂ h ((fun v : ℂ => (eqLam a : ℂ) * v) 0) := by simpa using hAn
    exact (hAn'.comp h1).differentiableAt
  have hgd : DifferentiableAt ℂ h 0 := hAn.differentiableAt
  change deriv ((fun v : ℂ => h ((eqLam a : ℂ) * v)) - h) 0 ≠ 0
  rw [deriv_sub hfd hgd, deriv_eqLam_mul hd, hd]
  intro hcon
  have h1 : -((eqLam a : ℂ)) - -1 = 1 - (eqLam a : ℂ) := by ring
  rw [h1] at hcon
  have h2 : eqLam a = 1 := by
    have h3 : (1 : ℝ) = eqLam a := by
      have h4 : (1 : ℂ) = (eqLam a : ℂ) := sub_eq_zero.mp hcon
      exact_mod_cast h4
    exact h3.symm
  rw [eqLam] at h2
  have hpos : (0 : ℝ) < 1 + a := by linarith
  field_simp at h2
  linarith

/-- The third `dslope` of `germC a h` does not vanish on `ball 0 ρY`. -/
lemma germC_dslope_den_ne {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {ρY : ℝ} (hρY : 0 < ρY) {Yinv : ℂ → ℂ}
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) ρY) :
    dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u ≠ 0 := by
  intro hC
  have hYu : (germC a h u).2 = 0 := by
    simp only [germC, hC, div_zero]
  have hY0 : (germC a h (0 : ℂ)).2 = 0 := by
    simp only [germC]; ring
  have hzero : Yinv 0 = 0 := by
    have := hY3 0 (by simp [Metric.mem_ball, hρY])
    rwa [hY0] at this
  have hu0 : u = 0 := by
    have h := hY3 u hu
    rw [hYu, hzero] at h
    exact h.symm
  subst hu0
  obtain ⟨hr, hAn, h0, hderiv, -, -⟩ := hh
  exact germC_dslope_den_zero_ne ha0 (hAn 0 (by simpa using hr)) hderiv hC

/-! ## 1. Two elementary consequences on `ball 0 ρY` -/

/-- On `ball 0 ρY` the germ `h` vanishes only at `0`. -/
lemma h_eq_zero_iff_of_mem_ball {a : ℝ} {h : ℂ → ℂ} {ρY : ℝ} (hρY : 0 < ρY) {Yinv : ℂ → ℂ}
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w) (h0 : h 0 = 0)
    {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) ρY) : h u = 0 ↔ u = 0 := by
  refine ⟨fun hhu => ?_, fun h => by rw [h]; exact h0⟩
  have hY0 : (germC a h (0 : ℂ)).2 = 0 := by
    simp only [germC]; ring
  have hzero : Yinv 0 = 0 := by
    have := hY3 0 (by simp [Metric.mem_ball, hρY])
    rwa [hY0] at this
  have hI := germC_snd_eq_h_mul_add (a := a) h0 u
  rw [hhu, zero_mul] at hI
  have h := hY3 u hu
  rw [hI, hzero] at h
  exact h.symm

/-- On `ball 0 ρY`, the first coordinate of `germC` is never `a/2`. -/
lemma germC_fst_ne_half {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {ρY : ℝ} (hρY : 0 < ρY) {Yinv : ℂ → ℂ}
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) ρY) :
    (germC a h u).1 ≠ ((a / 2 : ℝ) : ℂ) := by
  intro hXu
  have hC := germC_dslope_den_ne ha0 ha1 hh hρY hY3 hu
  have hI := germC_snd_eq_h_mul (a := a) (u := u) (by obtain ⟨-, -, h0, -, -, -⟩ := hh; exact h0) hC
  rw [hXu, sub_self, mul_zero] at hI
  have hY0 : (germC a h (0 : ℂ)).2 = 0 := by
    simp only [germC]; ring
  have hzero : Yinv 0 = 0 := by
    have := hY3 0 (by simp [Metric.mem_ball, hρY])
    rwa [hY0] at this
  have hu0 : u = 0 := by
    have h := hY3 u hu
    rw [hI, hzero] at h
    exact h.symm
  subst hu0
  obtain ⟨ρ, hρ, hAnC, hgerm0, -⟩ := germC_facts ha0 ha1 hh
  rw [hgerm0] at hXu
  have hXu' : ((-1 / 2 : ℝ) : ℂ) = ((a / 2 : ℝ) : ℂ) := by simpa using hXu
  have hreal : (-1 / 2 : ℝ) = a / 2 := Complex.ofReal_inj.mp hXu'
  linarith

/-- On `ball 0 ρY`, the first coordinate of `germC` is never `-a/2`. -/
lemma germC_fst_ne_neg_half {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {ρY : ℝ} (hρY : 0 < ρY) {Yinv : ℂ → ℂ}
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) ρY) :
    (germC a h u).1 ≠ -((a / 2 : ℝ) : ℂ) := by
  intro hXu
  have h0 := (by obtain ⟨-, -, h0, -, -, -⟩ := hh; exact h0 : h 0 = 0)
  have hI := germC_snd_eq_h_mul_add (a := a) h0 u
  have hsum : (germC a h u).1 + ((a / 2 : ℝ) : ℂ) = 0 := by
    rw [hXu]; ring
  rw [hsum, mul_zero] at hI
  have hY0 : (germC a h (0 : ℂ)).2 = 0 := by
    simp only [germC]; ring
  have hzero : Yinv 0 = 0 := by
    have := hY3 0 (by simp [Metric.mem_ball, hρY])
    rwa [hY0] at this
  have hu0 : u = 0 := by
    have h := hY3 u hu
    rw [hI, hzero] at h
    exact h.symm
  subst hu0
  obtain ⟨ρ, hρ, hAnC, hgerm0, -⟩ := germC_facts ha0 ha1 hh
  rw [hgerm0] at hXu
  have hXu'' : ((-1 / 2 : ℝ) : ℂ) = -((a / 2 : ℝ) : ℂ) := by simpa using hXu
  have hXu' : ((-1 / 2 : ℝ) : ℂ) = ((-(a / 2) : ℝ) : ℂ) := by
    rw [hXu'']; push_cast; ring
  have hreal : (-1 / 2 : ℝ) = -(a / 2) := Complex.ofReal_inj.mp hXu'
  linarith

/-! ## 2. The propagation step

The identities `germC_snd_eq_h_mul_add` (`Y = h u · (X + a/2)`) and `germC_snd_eq_h_mul`
(`Y = h (λu) · (X - a/2)`) of `Work.EQ.germC_W_coord` hold at every point of `ball 0 ρY`
(§0).  Eliminating `Y` from them, and using that `X` is never `±a/2` and `h` never vanishes on
`ball 0 ρY` (§1), gives

  `h u = h (λ u) · (X u - a/2) · (X u + a/2)⁻¹`,   `X u = Y u / h (λ u) + a/2`.

Hence `h` analytic at `λ v` forces `X` (and then `h`) analytic at `v`: this is the propagation of
analyticity that lets us walk from a small parameter back to any parameter in `ball 0 ρY`. -/

/-- **Propagation step.**  If `h` is analytic at `λ v` for `v ∈ ball 0 ρY`, then `germC a h` and
`h` are analytic at `v`. -/
lemma analyticAt_germC_and_h_of_analyticAt_lam {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {h : ℂ → ℂ} {r : ℝ} (hh : IsStableGerm a h r) {ρY : ℝ} (hρY : 0 < ρY) {Yinv : ℂ → ℂ}
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hY1 : ∀ y ∈ Metric.ball (0 : ℂ) ρY, (germC a h (Yinv y)).2 = y)
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hstrict : ∀ w : ℂ, ‖w‖ ≤ ρY → ‖(germC a h w).2‖ < ρY)
    {v : ℂ} (hv : v ∈ Metric.ball (0 : ℂ) ρY)
    (hv' : AnalyticAt ℂ h ((eqLam a : ℂ) * v)) :
    AnalyticAt ℂ (germC a h) v ∧ AnalyticAt ℂ h v := by
  have hr : 0 < r := hh.1
  have hAn : AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) r) := hh.2.1
  have h0 : h 0 = 0 := hh.2.2.1
  have hderiv : deriv h 0 = -1 := hh.2.2.2.1
  have hlam0 : 0 < eqLam a := by rw [eqLam]; positivity
  have hlam1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  have hvball : ‖v‖ < ρY := by simpa [Metric.mem_ball, dist_zero_right] using hv
  rcases eq_or_ne v 0 with hv0 | hv0ne
  · subst hv0
    obtain ⟨ρ, hρ, hAnC, -, -, -, -⟩ := germC_facts ha0 ha1 hh
    exact ⟨hAnC 0 (by simpa using hρ), hAn 0 (by simpa using hr)⟩
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0ne
  have hYanC := germC_snd_analyticOnNhd_ball hρY hYan hY1 hY3 hstrict
  have hYv : AnalyticAt ℂ (fun u : ℂ => (germC a h u).2) v := hYanC v hv
  -- analyticity of `u ↦ h (λ u)` at `v`, and its non-vanishing there
  have hcv : AnalyticAt ℂ (fun u : ℂ => h ((eqLam a : ℂ) * u)) v := by
    have hm : AnalyticAt ℂ (fun u : ℂ => (eqLam a : ℂ) * u) v :=
      analyticAt_const.mul analyticAt_id
    have hv'' : AnalyticAt ℂ h ((fun u : ℂ => (eqLam a : ℂ) * u) v) := hv'
    exact hv''.comp hm
  have hlamv_mem : (eqLam a : ℂ) * v ∈ Metric.ball (0 : ℂ) ρY := by
    rw [Metric.mem_ball, dist_zero_right, norm_mul]
    have hnorm : ‖((eqLam a : ℂ))‖ = eqLam a := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
    rw [hnorm]
    calc eqLam a * ‖v‖ ≤ 1 * ‖v‖ :=
          mul_le_mul_of_nonneg_right (le_of_lt hlam1) (norm_nonneg v)
      _ = ‖v‖ := one_mul _
      _ < ρY := hvball
  have hlamv_ne : h ((eqLam a : ℂ) * v) ≠ 0 := by
    intro hz
    have h1 := (h_eq_zero_iff_of_mem_ball hρY hY3 h0 hlamv_mem).mp hz
    have h2 : ((eqLam a : ℝ) : ℂ) * v = 0 := by simpa using h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (Complex.ofReal_ne_zero.mpr (by rw [eqLam]; positivity))
    · exact hv0ne h3
  -- the first coordinate is the quotient `Y / h (λ ·) + a/2`
  have hXev : (fun u : ℂ => (germC a h u).1) =ᶠ[𝓝 v]
      ((fun u : ℂ => (germC a h u).2) / (fun u : ℂ => h ((eqLam a : ℂ) * u)) +
        fun _ => ((a / 2 : ℝ) : ℂ)) := by
    have hmem : Metric.ball v (‖v‖ / 2) ∈ 𝓝 v := Metric.ball_mem_nhds v (by linarith)
    have hmem0 : Metric.ball (0 : ℂ) ρY ∈ 𝓝 v := Metric.isOpen_ball.mem_nhds hv
    filter_upwards [hmem, hmem0] with u hu hu0
    have hu_ne : u ≠ 0 := by
      intro huz
      subst huz
      rw [Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg] at hu
      have hnn := norm_nonneg v
      linarith
    have huB : u ∈ Metric.ball (0 : ℂ) ρY := hu0
    have hC := germC_dslope_den_ne ha0 ha1 hh hρY hY3 huB
    have hI := germC_snd_eq_h_mul (a := a) h0 hC
    have hlamu_mem : (eqLam a : ℂ) * u ∈ Metric.ball (0 : ℂ) ρY := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul]
      have hnorm : ‖((eqLam a : ℂ))‖ = eqLam a := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
      rw [hnorm]
      have hu'_lt : ‖u‖ < ρY := by simpa [Metric.mem_ball, dist_zero_right] using huB
      calc eqLam a * ‖u‖ ≤ 1 * ‖u‖ :=
            mul_le_mul_of_nonneg_right (le_of_lt hlam1) (norm_nonneg u)
        _ = ‖u‖ := one_mul _
        _ < ρY := hu'_lt
    have hlamu_ne : h ((eqLam a : ℂ) * u) ≠ 0 := by
      intro hz
      have h1 := (h_eq_zero_iff_of_mem_ball hρY hY3 h0 hlamu_mem).mp hz
      have h2 : ((eqLam a : ℝ) : ℂ) * u = 0 := by simpa using h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (Complex.ofReal_ne_zero.mpr (by rw [eqLam]; positivity))
      · exact hu_ne h3
    rw [Pi.add_apply, Pi.div_apply, hI]
    field_simp
    ring
  have hXan : AnalyticAt ℂ (fun u : ℂ => (germC a h u).1) v :=
    ((hYv.div hcv hlamv_ne).add analyticAt_const).congr hXev.symm
  have hgan : AnalyticAt ℂ (germC a h) v := hXan.prod hYv
  -- and now `h` itself
  have hhev : h =ᶠ[𝓝 v]
      (fun u : ℂ => h ((eqLam a : ℂ) * u) * ((germC a h u).1 - ((a / 2 : ℝ) : ℂ)) *
        ((germC a h u).1 + ((a / 2 : ℝ) : ℂ))⁻¹) := by
    have hmem0 : Metric.ball (0 : ℂ) ρY ∈ 𝓝 v := Metric.isOpen_ball.mem_nhds hv
    filter_upwards [hmem0] with u hu
    have hC := germC_dslope_den_ne ha0 ha1 hh hρY hY3 hu
    have h1 := germC_snd_eq_h_mul_add (a := a) h0 u
    have h2 := germC_snd_eq_h_mul (a := a) h0 hC
    have hEq : h u * ((germC a h u).1 + ((a / 2 : ℝ) : ℂ)) =
        h ((eqLam a : ℂ) * u) * ((germC a h u).1 - ((a / 2 : ℝ) : ℂ)) := by
      rw [← h1, h2]
    have hne : (germC a h u).1 + ((a / 2 : ℝ) : ℂ) ≠ 0 := by
      intro hz
      have hz' : (germC a h u).1 = -((a / 2 : ℝ) : ℂ) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hz
      exact germC_fst_ne_neg_half ha0 ha1 hh hρY hY3 hu hz'
    calc h u = h u * ((germC a h u).1 + ((a / 2 : ℝ) : ℂ)) *
            ((germC a h u).1 + ((a / 2 : ℝ) : ℂ))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
      _ = h ((eqLam a : ℂ) * u) * ((germC a h u).1 - ((a / 2 : ℝ) : ℂ)) *
            ((germC a h u).1 + ((a / 2 : ℝ) : ℂ))⁻¹ := by rw [hEq]
  have hhan : AnalyticAt ℂ h v := by
    have hR : AnalyticAt ℂ (fun u : ℂ => h ((eqLam a : ℂ) * u) *
        ((germC a h u).1 - ((a / 2 : ℝ) : ℂ)) *
        ((germC a h u).1 + ((a / 2 : ℝ) : ℂ))⁻¹) v := by
      refine (hcv.mul (hXan.sub analyticAt_const)).mul ?_
      refine (hXan.add analyticAt_const).inv ?_
      have hne := germC_fst_ne_neg_half ha0 ha1 hh hρY hY3 hv
      intro hz
      rw [Pi.add_apply] at hz
      exact hne (by rw [eq_neg_iff_add_eq_zero]; exact hz)
    exact hR.congr hhev.symm
  exact ⟨hgan, hhan⟩

/-! ## 3. `h` and `germC a h` are analytic on the whole ball `ball 0 ρY` -/

/-- **The germ data is analytic on `ball 0 ρY`.**  Iterating the propagation step from a parameter
`λ^K u` close enough to `0` (where `h` is analytic by `IsStableGerm` and `germC a h` by
`germC_facts`) back to `u` shows that `h` and `germC a h` are analytic on `ball 0 ρY`. -/
theorem analyticOnNhd_h_and_germC_ball {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {ρY : ℝ} (hρY : 0 < ρY) {Yinv : ℂ → ℂ}
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hY1 : ∀ y ∈ Metric.ball (0 : ℂ) ρY, (germC a h (Yinv y)).2 = y)
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((germC a h w).2) = w)
    (hstrict : ∀ w : ℂ, ‖w‖ ≤ ρY → ‖(germC a h w).2‖ < ρY) :
    AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) ρY) ∧
      AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρY) := by
  obtain ⟨ρ0, hρ0pos, hAnC, hgerm0, hregC, hinjC, hderivC⟩ := germC_facts ha0 ha1 hh
  have hr : 0 < r := hh.1
  have hAn : AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) r) := hh.2.1
  have h0 : h 0 = 0 := hh.2.2.1
  have hderiv : deriv h 0 = -1 := hh.2.2.2.1
  have hlam0 : 0 < eqLam a := by rw [eqLam]; positivity
  have hlam1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  have hnorm : ‖((eqLam a : ℂ))‖ = eqLam a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
  have hnorm_lt : ‖((eqLam a : ℂ))‖ < 1 := by rw [hnorm]; exact hlam1
  have key : ∀ u ∈ Metric.ball (0 : ℂ) ρY, AnalyticAt ℂ h u ∧ AnalyticAt ℂ (germC a h) u := by
    intro u hu
    have hu' : ‖u‖ < ρY := by simpa [Metric.mem_ball, dist_zero_right] using hu
    have hδ : 0 < min r ρ0 := lt_min hr hρ0pos
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ‖((eqLam a : ℂ)) ^ K * u‖ < min r ρ0 := by
      have htend : Filter.Tendsto (fun k : ℕ => ((eqLam a : ℂ)) ^ k * u) Filter.atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm_lt).mul_const u
      have hev : ∀ᶠ k : ℕ in Filter.atTop, ‖((eqLam a : ℂ)) ^ k * u‖ < min r ρ0 := by
        filter_upwards [htend (Metric.ball_mem_nhds (0 : ℂ) hδ)] with k hk
        simpa [Metric.mem_ball, dist_zero_right] using hk
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
      exact ⟨K, hK K le_rfl⟩
    have hmain : ∀ k, k ≤ K → AnalyticAt ℂ h (((eqLam a : ℂ)) ^ (K - k) * u) ∧
        AnalyticAt ℂ (germC a h) (((eqLam a : ℂ)) ^ (K - k) * u) := by
      intro k hk
      induction k with
      | zero =>
        have h1 : AnalyticAt ℂ h (((eqLam a : ℂ)) ^ K * u) :=
          hAn _ (by
            rw [Metric.mem_ball, dist_zero_right]
            exact lt_of_lt_of_le hK (min_le_left _ _))
        have h2 : AnalyticAt ℂ (germC a h) (((eqLam a : ℂ)) ^ K * u) :=
          hAnC _ (by
            rw [Metric.mem_ball, dist_zero_right]
            exact lt_of_lt_of_le hK (min_le_right _ _))
        simpa using ⟨h1, h2⟩
      | succ j ih =>
        have hj : j ≤ K := by omega
        have hprev := ih hj
        have hsub : K - (j + 1) = K - j - 1 := by omega
        have hmul : (eqLam a : ℂ) * (((eqLam a : ℂ)) ^ (K - (j + 1)) * u) =
            ((eqLam a : ℂ)) ^ (K - j) * u := by
          rw [hsub]
          conv_rhs => rw [show K - j = (K - j - 1) + 1 by omega, pow_succ']
          ring
        have hv : ((eqLam a : ℂ)) ^ (K - (j + 1)) * u ∈ Metric.ball (0 : ℂ) ρY := by
          rw [Metric.mem_ball, dist_zero_right, norm_mul]
          calc ‖((eqLam a : ℂ)) ^ (K - (j + 1))‖ * ‖u‖
              = eqLam a ^ (K - (j + 1)) * ‖u‖ := by rw [norm_pow, hnorm]
            _ ≤ 1 * ‖u‖ := by
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)
                exact pow_le_one₀ (le_of_lt hlam0) (le_of_lt hlam1)
            _ = ‖u‖ := one_mul _
            _ < ρY := hu'
        have hv' : AnalyticAt ℂ h ((eqLam a : ℂ) * (((eqLam a : ℂ)) ^ (K - (j + 1)) * u)) := by
          rw [hmul]
          exact hprev.1
        obtain ⟨h1, h2⟩ := analyticAt_germC_and_h_of_analyticAt_lam ha0 ha1 hh hρY hYan hY1 hY3
          hstrict hv hv'
        exact ⟨h2, h1⟩
    have hfin := hmain K le_rfl
    simpa using hfin
  exact ⟨fun u hu => (key u hu).1, fun u hu => (key u hu).2⟩

/-! ## 4. Small helpers for the assembly -/

/-- An eventual equality in `𝓝[≠] 0` holds on an honest punctured ball. -/
lemma exists_ball_punctured_of_eventuallyEq {α : Type*} {p q : ℂ → α}
    (h : p =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ] q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → p z = q z := by
  have h' : ∀ᶠ z in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, p z = q z := h
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h'
  obtain ⟨ε, hε, hε'⟩ := h'
  refine ⟨ε, hε, fun z hz hzz => ?_⟩
  exact hε' (by simpa [Metric.mem_ball, dist_eq_norm] using hzz) (by simpa using hz)

/-- A function analytic at `0` whose value at `0` has norm `< C` is bounded by `C` near `0`. -/
lemma exists_ball_norm_lt {f : ℂ → ℂ} {C : ℝ} (hf : AnalyticAt ℂ f 0) (h : ‖f 0‖ < C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ < δ → ‖f z‖ < C := by
  have hε : 0 < C - ‖f 0‖ := by linarith
  have hcont := hf.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont (C - ‖f 0‖) hε
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have h1 : dist (f z) (f 0) < C - ‖f 0‖ := hδ' (by simpa [dist_eq_norm] using hz)
  rw [dist_eq_norm] at h1
  have h2 : ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := by
    have := norm_add_le (f z - f 0) (f 0)
    simpa using this
  linarith

/-! ## 5. The window entry of a branch on the unstable germ curve -/

/-- **The first window entry of a backward-Puiseux branch lies on the unstable germ curve.** -/
theorem H0_path_limit_germ_curve {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {n₁ m₁ : ℕ} {u : ℂ} {R : ℝ} (hR : 0 < R)
    {c : ℂ → ℂ × ℂ} (hc : AnalyticOnNhd ℂ c (Metric.ball u R))
    {σ : Fin (n₁ + m₁) → Bool} (hσ : Work.EQ.Adm a c u R σ)
    {ρY : ℝ} (hρY : 0 < ρY) {φ Yinv : ℂ → ℂ}
    (hYan : AnalyticOnNhd ℂ Yinv (Metric.ball (0 : ℂ) ρY))
    (hY1 : ∀ y ∈ Metric.ball (0 : ℂ) ρY, (Work.EQ.germC a h (Yinv y)).2 = y)
    (hY2 : ∀ y ∈ Metric.ball (0 : ℂ) ρY, (Work.EQ.germC a h (Yinv y)).1 = φ y)
    (hY3 : ∀ w, w ∈ Metric.ball (0 : ℂ) ρY → Yinv ((Work.EQ.germC a h w).2) = w)
    (hstrict : ∀ w : ℂ, ‖w‖ ≤ ρY → ‖(Work.EQ.germC a h w).2‖ < ρY)
    {t : ℕ → ℂ} (ht0 : ∀ n, t n ≠ 0)
    (htlt : ∀ n, ‖t n‖ < Work.EQ.rhoFin' a c u R (n₁ + m₁))
    (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    {w : ℕ → ℂ} (hwne : ∀ n, w n ≠ 0) (hwball : ∀ n, ‖w n‖ ≤ ρY / 2)
    (hw : ∀ n, Work.EQ.ugermC a h (w n) = Work.EQ.branchPt a c u R σ (t n) 0) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ Work.EQ.rhoFin' a c u R (n₁ + m₁) ∧
      ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ' →
        ∃ w : ℂ, w ∈ Metric.ball (0 : ℂ) ρY ∧ w ≠ 0 ∧
          Work.EQ.ugermC a h w = Work.EQ.branchPt a c u R σ t 0 := by
  -- 0. the germ data is analytic where we need it
  have hYanC : AnalyticOnNhd ℂ (fun v : ℂ => (germC a h v).2) (Metric.ball (0 : ℂ) ρY) :=
    germC_snd_analyticOnNhd_ball hρY hYan hY1 hY3 hstrict
  have hAna := analyticOnNhd_h_and_germC_ball ha0 ha1 hh hρY hYan hY1 hY3 hstrict
  -- 1. meromorphy of the two coordinates of the branch family
  have hM1 : MeromorphicAt (fun s : ℂ => (branchPt a c u R σ s 0).1) 0 :=
    (branchPt_meromorphic hR hc hσ (0 : Fin (n₁ + m₁ + 1))).1
  have hM2 : MeromorphicAt (fun s : ℂ => (branchPt a c u R σ s 0).2) 0 :=
    (branchPt_meromorphic hR hc hσ (0 : Fin (n₁ + m₁ + 1))).2
  -- 2. the sequence lies on the `y`-coordinate of the germ
  have hfw : ∀ n : ℕ, (branchPt a c u R σ (t n) 0).2 = (germC a h (w n)).2 := by
    intro n
    have h := congrArg Prod.snd (hw n)
    simpa [ugermC, eqMirror] using h.symm
  -- 3. the `y`-coordinate extends analytically at `0`, with value of norm `< ρY`
  obtain ⟨c₂, g, hc₂lt, hgan, hg0, hgeq⟩ :=
    meromorphicAt_value_of_seq_germC_snd (a := a) (h := h) hρY hYanC hstrict hM2 ht0 ht
      hwball hfw
  -- 4. the analytic witness family `G = Yinv ∘ g`
  let G : ℂ → ℂ := fun s => Yinv (g s)
  have hc₂mem : c₂ ∈ Metric.ball (0 : ℂ) ρY := by
    rw [Metric.mem_ball, dist_zero_right]; exact hc₂lt
  have hwmem : ∀ n : ℕ, w n ∈ Metric.ball (0 : ℂ) ρY := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    have := hwball n
    linarith
  have hGan : AnalyticAt ℂ G 0 := by
    have h1 : AnalyticAt ℂ g 0 := hgan
    have h2 : AnalyticAt ℂ Yinv (g 0) := by
      rw [hg0]
      exact hYan c₂ hc₂mem
    have h3 : AnalyticAt ℂ (Yinv ∘ g) 0 := h2.comp h1
    rw [show G = Yinv ∘ g from rfl]
    exact h3
  -- 5. the limit of `G` along the sequence, giving the bound on `G 0`
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (fun s : ℂ => (branchPt a c u R σ s 0).2) (t n) = g (t n) := by
    have htne : Filter.Tendsto t Filter.atTop (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨ht, Filter.Eventually.of_forall (fun n => by simpa using ht0 n)⟩
    exact htne.eventually hgeq
  have hG0 : ‖G 0‖ ≤ ρY / 2 := by
    have htend : Filter.Tendsto (fun n : ℕ => G (t n)) Filter.atTop (𝓝 (G 0)) :=
      hGan.continuousAt.tendsto.comp ht
    have hb : ∀ᶠ n : ℕ in Filter.atTop, ‖G (t n)‖ ≤ ρY / 2 := by
      filter_upwards [hev] with n hn
      have h1 : G (t n) = w n := by
        show Yinv (g (t n)) = w n
        rw [← hn, hfw n]
        exact hY3 (w n) (hwmem n)
      rw [h1]
      exact hwball n
    exact le_of_tendsto htend.norm hb
  -- 6. `G` does not vanish on a punctured disc
  have hev' : ∀ᶠ n : ℕ in Filter.atTop, g (t n) = (branchPt a c u R σ (t n) 0).2 :=
    hev.mono (fun n hn => hn.symm)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev'
  -- main assembly
  -- thresholds
  obtain ⟨ε_g, hεg_pos, hεg⟩ := exists_ball_punctured_of_eventuallyEq hgeq
  have hg0lt : ‖g 0‖ < ρY := by rw [hg0]; exact hc₂lt
  obtain ⟨ε_b, hεb_pos, hεb⟩ := exists_ball_norm_lt hgan hg0lt
  have hG0lt : ‖G 0‖ < ρY := by linarith [hG0, hρY]
  obtain ⟨ε_Gb, hεGb_pos, hεGb⟩ := exists_ball_norm_lt hGan hG0lt
  -- `G ≠ 0` on a punctured disc
  have hGne : ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → G z ≠ 0 := by
    refine eventually_ne_zero_of_meromorphicAt_of_seq_ne_zero (f := G)
      (AnalyticAt.meromorphicAt hGan) (fun n => ht0 (n + N₀)) ?_ (fun n => ?_)
    · exact ht.comp (tendsto_add_atTop_nat N₀)
    · show Yinv (g (t (n + N₀))) ≠ 0
      rw [hN₀ (n + N₀) (by omega), hfw (n + N₀)]
      intro hz
      exact hwne (n + N₀) (by
        rw [← hY3 (w (n + N₀)) (hwmem (n + N₀))]
        exact hz)
  obtain ⟨ε_Gne, hεGne_pos, hεGne⟩ := hGne
  -- `Ξ` is meromorphic at `0` and vanishes along the sequence
  let Ξ : ℂ → ℂ := fun s => (branchPt a c u R σ s 0).1 + (germC a h (G s)).1
  have hΞm : MeromorphicAt Ξ 0 := by
    have h1 : MeromorphicAt (fun s : ℂ => (branchPt a c u R σ s 0).1) 0 := hM1
    have hGmem : G 0 ∈ Metric.ball (0 : ℂ) ρY := by
      rw [Metric.mem_ball, dist_zero_right]; exact hG0lt
    have h2 : AnalyticAt ℂ (germC a h) (G 0) := hAna.2 (G 0) hGmem
    have h3 : AnalyticAt ℂ (fun s : ℂ => germC a h (G s)) 0 := by
      have := h2.comp hGan
      rw [show (fun s : ℂ => germC a h (G s)) = (germC a h) ∘ G from rfl]
      exact this
    have h4 : AnalyticAt ℂ (fun s : ℂ => (germC a h (G s)).1) 0 := by
      have hfst : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (germC a h (G 0)) :=
        (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (germC a h (G 0))
      have h5 : AnalyticAt ℂ (fun s : ℂ => (germC a h (G s)).1) 0 :=
        AnalyticAt.comp (f := fun s : ℂ => germC a h (G s)) (x := (0 : ℂ)) hfst h3
      exact h5
    rw [show Ξ = fun s : ℂ =>
      (branchPt a c u R σ s 0).1 + (germC a h (G s)).1 from rfl]
    exact h1.add h4.meromorphicAt
  have hΞ0 : ∀ n ≥ N₀, Ξ (t n) = 0 := by
    intro n hn
    have h1 : (branchPt a c u R σ (t n) 0).1 = -(germC a h (w n)).1 := by
      have h := congrArg Prod.fst (hw n)
      simp only [ugermC, eqMirror] at h
      exact h.symm
    have h2 : (germC a h (G (t n))).1 = (germC a h (w n)).1 := by
      have hG : G (t n) = w n := by
        show Yinv (g (t n)) = w n
        rw [hN₀ n hn, hfw n]
        exact hY3 (w n) (hwmem n)
      rw [hG]
    show (branchPt a c u R σ (t n) 0).1 + (germC a h (G (t n))).1 = 0
    rw [h1, h2]
    ring
  have hΞev : Ξ =ᶠ[nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ] 0 :=
    eventuallyEq_zero_of_meromorphicAt_of_seq_zero hΞm (fun n => ht0 (n + N₀))
      (ht.comp (tendsto_add_atTop_nat N₀)) (fun n => hΞ0 (n + N₀) (by omega))
  obtain ⟨ε_Ξ, hεΞ_pos, hεΞ⟩ := exists_ball_punctured_of_eventuallyEq hΞev
  -- the answer
  refine ⟨min (min 1 (Work.EQ.rhoFin' a c u R (n₁ + m₁)))
    (min (min ε_g ε_Ξ) (min (min ε_b ε_Gb) ε_Gne)), ?_, ?_, ?_⟩
  · refine lt_min (lt_min one_pos (rhoFin'_pos hR hc))
      (lt_min (lt_min hεg_pos hεΞ_pos) (lt_min (lt_min hεb_pos hεGb_pos) hεGne_pos))
  · exact le_trans (min_le_left _ _) (min_le_right _ _)
  · intro s hs0 hslt
    have h1 : ‖s‖ < ε_g := lt_of_lt_of_le hslt (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
    have h2 : ‖s‖ < ε_Ξ := lt_of_lt_of_le hslt (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
    have h3 : ‖s‖ < ε_b := lt_of_lt_of_le hslt
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))))
    have h4 : ‖s‖ < ε_Gb := lt_of_lt_of_le hslt
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))))
    have h5 : ‖s‖ < ε_Gne := lt_of_lt_of_le hslt
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hgs : g s = (branchPt a c u R σ s 0).2 := (hεg s (by simpa using hs0) h1).symm
    have hΞs : Ξ s = 0 := hεΞ s (by simpa using hs0) h2
    have hGball : G s ∈ Metric.ball (0 : ℂ) ρY := by
      rw [Metric.mem_ball, dist_zero_right]; exact hεGb s h4
    have hGne' : G s ≠ 0 := hεGne s (by simpa using hs0) h5
    refine ⟨G s, hGball, hGne', ?_⟩
    have hY2s : (germC a h (G s)).1 = φ (g s) := by
      show (germC a h (Yinv (g s))).1 = φ (g s)
      exact hY2 (g s) (by rw [Metric.mem_ball, dist_zero_right]; exact hεb s h3)
    have hY1s : (germC a h (G s)).2 = g s := by
      show (germC a h (Yinv (g s))).2 = g s
      exact hY1 (g s) (by rw [Metric.mem_ball, dist_zero_right]; exact hεb s h3)
    have hZ1 : (branchPt a c u R σ s 0).1 = -(germC a h (G s)).1 := by
      have hsum : (branchPt a c u R σ s 0).1 + (germC a h (G s)).1 = 0 := hΞs
      exact (eq_neg_iff_add_eq_zero).mpr hsum
    have hZ2 : (branchPt a c u R σ s 0).2 = (germC a h (G s)).2 := by
      rw [← hgs, ← hY1s]
    refine Prod.ext ?_ ?_
    · show -(germC a h (G s)).1 = (branchPt a c u R σ s 0).1
      rw [hZ1]
    · show (germC a h (G s)).2 = (branchPt a c u R σ s 0).2
      rw [hZ2]

end
end Work.EQ
