import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.B.mellin_psiTail
import Submission.Work.RHContract.B.Phi_analyticOn

namespace Work.RHContract.B

open MeasureTheory Filter
open scoped Topology

noncomputable section

/-!
# `B.G_analytic_zero`

Given a function `Ψ` which is analytic on a ball `ball 0 r` and which agrees with the Landau
integral `Φ(s) = ∫_2^∞ (ψ t − t) k(t) t^{−s} dt` on the right half plane, build a function
`G`, analytic on a smaller ball around `0`, which on the right half plane equals

`(2^{−s} · J(2) − Ψ(s))/s + K · 2^{−(s+β)}/(s+β)`.

The only real input is the value of `Ψ` at `0`: since `(ψ t − t) k(t)` is integrable on
`(2, ∞)` (`Identity.TailInt.integrableOn_psi_sub_id_mul_kW`), the defining integral of `Φ`
is continuous at `s = 0` by dominated convergence, so `Φ 0 = J(2) = ∫_2^∞ (ψ t − t) k(t) dt`.
Hence `Ψ 0 = J(2)`, the numerator `2^{−s} J(2) − Ψ(s)` vanishes at `0`, and the apparent
pole of the first term is removable.  The second term has its only pole at `s = −β`, which
lies outside the ball of radius `r' < β`.
-/

/-- The real kernel `(ψ t − t) k(t)`. -/
private def realKer (t : ℝ) : ℝ := (Chebyshev.psi t - t) * Work.RHContract.kW t

private lemma measurable_realKer : Measurable realKer := by
  have hψ : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
  have hk : Measurable (fun t : ℝ => Work.RHContract.kW t) := by
    unfold Work.RHContract.kW; fun_prop
  exact (hψ.sub measurable_id).mul hk

/-- The complex kernel, exactly as it appears in the integrand of `Φ`. -/
private def psiKerC (t : ℝ) : ℂ := ((Chebyshev.psi t - t) * Work.RHContract.kW t : ℂ)

private lemma psiKerC_eq (t : ℝ) : psiKerC t = (realKer t : ℂ) := by
  rw [psiKerC, realKer]; push_cast; ring

private lemma measurable_psiKerC : Measurable psiKerC := by
  rw [show psiKerC = fun t => (realKer t : ℂ) from funext psiKerC_eq]
  exact Complex.measurable_ofReal.comp measurable_realKer

/-- `x ↦ (x : ℂ) ^ z` is measurable. -/
private lemma measurable_cpow_ofReal (z : ℂ) : Measurable (fun x : ℝ => (x : ℂ) ^ z) := by
  have h : Measurable (fun w : ℂ => w ^ z) := by
    simp only [Complex.cpow_def]
    refine Measurable.ite (measurableSet_singleton 0) ?_ ?_
    · exact measurable_const
    · exact Complex.measurable_exp.comp (Complex.measurable_log.mul_const z)
  exact h.comp Complex.measurable_ofReal

/-- `Φ` as a set integral against the complex kernel. -/
private lemma Phi_eq_int (s : ℂ) :
    Work.RHContract.Landau.Phi s
      = ∫ t in Set.Ioi 2, psiKerC t * (t : ℂ) ^ (-s) := rfl

/-- The defining integral of `Φ` is continuous at `0` from the right, with value `Φ 0`.
Dominated convergence with dominating function `‖(ψ t − t)k(t)‖`, integrable on `(2, ∞)`. -/
private lemma Phi_continuousAt_zero :
    Tendsto (fun x : ℝ => Work.RHContract.Landau.Phi (x : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (Work.RHContract.Landau.Phi 0)) := by
  have hint : Integrable (fun t : ℝ => ‖realKer t‖) (volume.restrict (Set.Ioi 2)) :=
    (Work.RHContract.Identity.TailInt.integrableOn_psi_sub_id_mul_kW le_rfl).norm
  have hmain : Tendsto
      (fun x : ℝ => ∫ t in Set.Ioi 2, psiKerC t * (t : ℂ) ^ (-(x : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in Set.Ioi 2, psiKerC t)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[>] (0 : ℝ)) (μ := volume.restrict (Set.Ioi 2))
      (F := fun x : ℝ => fun t : ℝ => psiKerC t * (t : ℂ) ^ (-(x : ℂ)))
      (f := fun t : ℝ => psiKerC t)
      (fun t : ℝ => ‖realKer t‖) ?_ ?_ hint ?_
    · filter_upwards with x
      exact (measurable_psiKerC.mul (measurable_cpow_ofReal (-(x : ℂ)))).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := by linarith [Set.mem_Ioi.mp ht]
      have ht1 : (1 : ℝ) ≤ t := by linarith [Set.mem_Ioi.mp ht]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
        show ‖psiKerC t‖ = ‖realKer t‖ by rw [psiKerC_eq t]; simp]
      have hre : (-(x : ℂ)).re = -x := by simp
      rw [hre]
      have hle : t ^ (-x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith [hx.1])
      calc ‖realKer t‖ * t ^ (-x) ≤ ‖realKer t‖ * 1 :=
            mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ = ‖realKer t‖ := mul_one _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := by linarith [Set.mem_Ioi.mp ht]
      have hb : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have hcont : ContinuousAt (fun x : ℝ => (t : ℂ) ^ (-(x : ℂ))) 0 :=
        ContinuousAt.const_cpow ((Complex.continuous_ofReal.neg).continuousAt) (Or.inl hb)
      have hlim := hcont.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
      simpa using hlim.const_mul (psiKerC t)
  have htarget : Work.RHContract.Landau.Phi 0 = ∫ t in Set.Ioi 2, psiKerC t := by
    rw [Phi_eq_int 0]
    simp only [neg_zero, Complex.cpow_zero, mul_one]
  rw [htarget]
  exact hmain.congr (fun x => (Phi_eq_int (x : ℂ)).symm)

/-- `Φ 0 = J(2)`. -/
private lemma Phi_zero : Work.RHContract.Landau.Phi 0 = (Work.RHContract.psiTail 2 : ℂ) := by
  rw [Phi_eq_int 0]
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  have h_int : (∫ t in Set.Ioi 2, psiKerC t) = ∫ t in Set.Ioi 2, (realKer t : ℂ) :=
    MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
      (Filter.Eventually.of_forall (fun t _ => psiKerC_eq t))
  have h2 : (∫ t in Set.Ioi 2, (realKer t : ℂ))
      = ((∫ t in Set.Ioi 2, realKer t : ℝ) : ℂ) := integral_ofReal
  rw [h_int, h2]
  rfl

/-- The value at `0` of an analytic continuation `Ψ` of `Φ` to a ball is `J(2)`. -/
private lemma Psi_zero_eq {r : ℝ} (hr : 0 < r) {Ψ : ℂ → ℂ}
    (hΨ : AnalyticOn ℂ Ψ (Metric.ball 0 r))
    (hΨΦ : ∀ s : ℂ, s ∈ Metric.ball 0 r → 0 < s.re → Ψ s = Work.RHContract.Landau.Phi s) :
    Ψ 0 = (Work.RHContract.psiTail 2 : ℂ) := by
  have hcontΨ : ContinuousAt Ψ 0 :=
    (hΨ.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).continuousAt
  have h1 : Tendsto (fun x : ℝ => Ψ (x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (Ψ 0)) :=
    hcontΨ.tendsto.comp
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have h2 : Tendsto (fun x : ℝ => Ψ (x : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (Work.RHContract.Landau.Phi 0)) :=
    Phi_continuousAt_zero.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hr] with x hx
      have hmem : (x : ℂ) ∈ Metric.ball 0 r := by
        rw [Metric.mem_ball, dist_zero_right,
          show ‖(x : ℂ)‖ = |x| by simp, abs_of_pos hx.1]
        exact hx.2
      exact (hΨΦ (x : ℂ) hmem (by rw [Complex.ofReal_re]; exact hx.1)).symm)
  rw [tendsto_nhds_unique h1 h2, Phi_zero]

/-- The numerator `2^{−s} J(2) − Ψ(s)`. -/
private def cN (Ψ : ℂ → ℂ) (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (-s) * (Work.RHContract.psiTail 2 : ℂ) - Ψ s

/-- The second summand `K · 2^{−(s+β)}/(s+β)`. -/
private def cT (K β : ℝ) (s : ℂ) : ℂ :=
  K * (2 : ℂ) ^ (-(s + β)) / (s + β)

/-- `cT K β` is analytic away from its pole `s = −β`. -/
private lemma cT_analyticAt (K β : ℝ) {z : ℂ} (hz : z ≠ -(β : ℂ)) :
    AnalyticAt ℂ (cT K β) z := by
  have hnum : AnalyticAt ℂ (fun s : ℂ => (K : ℂ) * (2 : ℂ) ^ (-(s + (β : ℂ)))) z :=
    (analyticAt_const (v := (K : ℂ)) (x := z)).mul
      (AnalyticAt.cpow (analyticAt_const (v := (2 : ℂ)) (x := z))
        ((analyticAt_id (z := z)).add (analyticAt_const (v := (β : ℂ)) (x := z))).neg
        (by norm_num [Complex.mem_slitPlane_iff]))
  have hden : AnalyticAt ℂ (fun s : ℂ => s + (β : ℂ)) z :=
    (analyticAt_id (z := z)).add (analyticAt_const (v := (β : ℂ)) (x := z))
  have hne : z + (β : ℂ) ≠ 0 := by
    intro h
    exact hz ((add_eq_zero_iff_eq_neg).mp h)
  exact hnum.div hden hne

/-- A removable-singularity statement: if `N` is analytic at `0` and `N 0 = 0`, then `N s / s`
agrees off `0` with the analytic function `dslope N 0`. -/
private lemma div_removable (N : ℂ → ℂ) (hN : AnalyticAt ℂ N 0) (hN0 : N 0 = 0) :
    AnalyticAt ℂ (dslope N 0) 0 ∧ ∀ s : ℂ, s ≠ 0 → dslope N 0 s = N s / s := by
  obtain ⟨p, hp⟩ := hN
  refine ⟨(hp.has_fpower_series_dslope_fslope).analyticAt, fun s hs => ?_⟩
  rw [dslope_of_ne _ hs, slope_def_field, hN0, sub_zero]
  ring

theorem G_analytic_zero
    (β K : ℝ) (hβ : 0 < β) (r : ℝ) (hr : 0 < r) (Ψ : ℂ → ℂ)
    (hΨ : AnalyticOn ℂ Ψ (Metric.ball 0 r))
    (hΨΦ : ∀ s : ℂ, s ∈ Metric.ball 0 r → 0 < s.re → Ψ s = Work.RHContract.Landau.Phi s) :
    ∃ r' : ℝ, 0 < r' ∧ r' < β ∧ ∃ G : ℂ → ℂ,
      AnalyticOn ℂ G (Metric.ball 0 r') ∧
      (∀ s : ℂ, 0 < s.re → G s = (2 ^ (-s) * (Work.RHContract.psiTail 2 : ℂ) - Ψ s) / s
          + K * (2 : ℂ) ^ (-(s + β)) / (s + β)) := by
  classical
  have hΨ0 : Ψ 0 = (Work.RHContract.psiTail 2 : ℂ) := Psi_zero_eq hr hΨ hΨΦ
  -- `cN Ψ` is analytic on the ball and vanishes at `0`.
  have hN_an : AnalyticOn ℂ (cN Ψ) (Metric.ball 0 r) := by
    intro s hs
    have h1 : AnalyticAt ℂ
        (fun t : ℂ => (2 : ℂ) ^ (-t) * (Work.RHContract.psiTail 2 : ℂ) - Ψ t) s :=
      (((AnalyticAt.cpow (analyticAt_const (v := (2 : ℂ)) (x := s))
          (analyticAt_id (z := s)).neg (by norm_num [Complex.mem_slitPlane_iff])).mul
        (analyticAt_const (v := (Work.RHContract.psiTail 2 : ℂ)) (x := s))).sub
        (hΨ.analyticAt (Metric.isOpen_ball.mem_nhds hs)))
    exact h1.analyticWithinAt
  have hN0 : cN Ψ 0 = 0 := by
    simp only [cN, neg_zero, Complex.cpow_zero, one_mul]
    rw [hΨ0, sub_self]
  have hN_an0 : AnalyticAt ℂ (cN Ψ) 0 :=
    hN_an.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  obtain ⟨hÄ_an, hÄ_eq⟩ := div_removable (cN Ψ) hN_an0 hN0
  -- a ball on which `dslope (cN Ψ) 0` is analytic
  obtain ⟨R₁, hR₁pos, hR₁an⟩ : ∃ R : ℝ, 0 < R ∧
      ∀ z : ℂ, z ∈ Metric.ball 0 R → AnalyticAt ℂ (dslope (cN Ψ) 0) z := by
    have h : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ (dslope (cN Ψ) 0) z := hÄ_an.eventually_analyticAt
    rcases Metric.mem_nhds_iff.mp h with ⟨R, hR, hsub⟩
    exact ⟨R, hR, fun z hz => hsub hz⟩
  set r' : ℝ := min R₁ β / 2 with hr'def
  have hminpos : 0 < min R₁ β := lt_min hR₁pos hβ
  have hr'pos : 0 < r' := by rw [hr'def]; positivity
  have hr'lt : r' < β := by
    rw [hr'def]
    have hle : min R₁ β ≤ β := min_le_right _ _
    linarith
  -- the analytic extension on the small ball
  have hB_an : AnalyticOn ℂ (fun s : ℂ => dslope (cN Ψ) 0 s + cT K β s)
      (Metric.ball 0 r') := by
    intro z hz
    have hz1 : z ∈ Metric.ball 0 R₁ := by
      rw [Metric.mem_ball] at hz ⊢
      have h2 : r' ≤ R₁ := by
        rw [hr'def]
        calc min R₁ β / 2 ≤ R₁ / 2 :=
              div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
          _ ≤ R₁ := by linarith [hR₁pos]
      linarith
    have hz_ne : z ≠ -(β : ℂ) := by
      intro h
      rw [h, Metric.mem_ball, dist_zero_right] at hz
      have hnorm : ‖(-(β : ℂ))‖ = β := by
        rw [norm_neg, show ‖(β : ℂ)‖ = |β| by simp, abs_of_pos hβ]
      rw [hnorm] at hz
      linarith [hr'lt]
    exact ((hR₁an z hz1).add (cT_analyticAt K β hz_ne)).analyticWithinAt
  refine ⟨r', hr'pos, hr'lt,
    fun s : ℂ => if s ∈ Metric.ball 0 r' then (dslope (cN Ψ) 0 s + cT K β s)
      else cN Ψ s / s + cT K β s, ?_, ?_⟩
  · refine hB_an.congr (fun z hz => ?_)
    rw [if_pos hz]
  · intro s hs
    have hsne : s ≠ 0 := by
      intro h; rw [h] at hs; simp at hs
    by_cases hmem : s ∈ Metric.ball 0 r'
    · dsimp only
      rw [if_pos hmem, hÄ_eq s hsne]
      rfl
    · dsimp only
      rw [if_neg hmem]
      rfl

end

end Work.RHContract.B
