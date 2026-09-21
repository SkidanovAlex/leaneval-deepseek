import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.xi_close_of_small
import Submission.Work.OddVolterra.Existence.abel_deriv_bound
import Submission.Work.OddVolterra.Existence.aw_xi_smooth
import Submission.Work.OddVolterra.Smooth.Q_regularity
import Submission.Work.OddVolterra.Existence.E1_E2_contDiff
import Submission.Work.OddVolterra.Existence.E1_E2_diff_bounds
import Submission.Work.OddVolterra.Existence.exists_bound_comp_pair_sub_param
import Submission.Work.OddVolterra.Abel.abelF_deriv2_bound
import Submission.Work.OddVolterra.Existence.E1_E2_deriv2_bounds
import Submission.Work.OddVolterra.Existence.deriv_Qtilde_sub_abelF

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.WinData
noncomputable section

/-! ## Generic helpers -/

lemma deriv_neg_fun (F : ℝ → ℝ) : deriv (fun u : ℝ => - F u) = fun u => - deriv F u := by
  have h : (fun u : ℝ => - F u) = -F := rfl
  rw [h]
  funext u
  simp only [deriv, fderiv_neg, neg_apply]

lemma abelF_neg_fun (g : ℝ → ℝ) :
    Work.OddVolterra.Existence.abelF (fun v : ℝ => - g v)
      = fun u : ℝ => - Work.OddVolterra.Existence.abelF g u := by
  funext u
  simp only [Work.OddVolterra.Existence.abelF]
  rw [show (fun v : ℝ => -g v / Real.sqrt (v - u))
      = (fun v : ℝ => -(g v / Real.sqrt (v - u))) from by funext v; ring]
  rw [intervalIntegral.integral_neg]

lemma deriv_eventuallyEq_zero {φ : ℝ → ℝ} {x : ℝ} (h : φ =ᶠ[𝓝 x] 0) :
    deriv φ =ᶠ[𝓝 x] 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (show {y : ℝ | φ y = 0} ∈ 𝓝 x from h)
  filter_upwards [Metric.ball_mem_nhds x (half_pos hε)] with u hu
  have hloc : φ =ᶠ[𝓝 u] 0 := by
    filter_upwards [Metric.ball_mem_nhds u (half_pos hε)] with v hv
    exact hball (by
      rw [Metric.mem_ball] at hu hv ⊢
      calc dist v x ≤ dist v u + dist u x := dist_triangle v u x
        _ < ε / 2 + ε / 2 := add_lt_add hv hu
        _ = ε := by ring)
  rw [Filter.EventuallyEq.deriv_eq hloc]
  exact deriv_const u 0

lemma deriv_deriv_abelF_neg (f : ℝ → ℝ) (s : ℝ) :
    deriv (deriv (Work.OddVolterra.Existence.abelF (fun v => - f v))) s
      = - deriv (deriv (Work.OddVolterra.Existence.abelF f)) s := by
  simp only [abelF_neg_fun, deriv_neg_fun]

lemma phi_abel_data {φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hcd : ContDiffOn ℝ (⊤ : ℕ∞) φ (Set.Ioo (0:ℝ) 1))
    (hev : φ =ᶠ[𝓝 1] 0) :
    φ 1 = 0 ∧ deriv φ 1 = 0 ∧
      (∀ u ∈ Set.Icc c 1, DifferentiableAt ℝ φ u) ∧
      (∀ u ∈ Set.Icc c 1, DifferentiableAt ℝ (deriv φ) u) ∧
      ContinuousOn (deriv φ) (Set.Icc c 1) ∧
      ContinuousOn (deriv (deriv φ)) (Set.Icc c 1) := by
  have hcd1 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv φ) (Set.Ioo (0:ℝ) 1) :=
    hcd.deriv_of_isOpen isOpen_Ioo (by simp)
  have hcd2 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv (deriv φ)) (Set.Ioo (0:ℝ) 1) :=
    hcd1.deriv_of_isOpen isOpen_Ioo (by simp)
  have hev1 : deriv φ =ᶠ[𝓝 1] 0 := deriv_eventuallyEq_zero hev
  have hev2 : deriv (deriv φ) =ᶠ[𝓝 1] 0 := deriv_eventuallyEq_zero hev1
  have hzer : deriv φ 1 = 0 := by
    rw [hev.deriv_eq]; exact deriv_const 1 0
  have hmem : ∀ u ∈ Set.Icc c 1, u < 1 → u ∈ Set.Ioo (0:ℝ) 1 := by
    intro u hu hlt
    exact ⟨by linarith [hc, hu.1], hlt⟩
  refine ⟨hev.eq_of_nhds, hzer, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · exact (hcd.differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds (hmem u hu hlt))
    · subst heq
      exact (differentiableAt_const (c := (0:ℝ))).congr_of_eventuallyEq hev
  · intro u hu
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · exact (hcd1.differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds (hmem u hu hlt))
    · subst heq
      exact (differentiableAt_const (c := (0:ℝ))).congr_of_eventuallyEq hev1
  · intro u hu
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · exact (hcd1.continuousOn.continuousAt
        (isOpen_Ioo.mem_nhds (hmem u hu hlt))).continuousWithinAt
    · subst heq
      exact (continuousWithinAt_const (b := (0:ℝ))).congr_of_eventuallyEq
        (hev1.filter_mono inf_le_left) hzer
  · intro u hu
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · exact (hcd2.continuousOn.continuousAt
        (isOpen_Ioo.mem_nhds (hmem u hu hlt))).continuousWithinAt
    · subst heq
      exact (continuousWithinAt_const (b := (0:ℝ))).congr_of_eventuallyEq
        (hev2.filter_mono inf_le_left)
        (by rw [hev1.deriv_eq]; exact deriv_const 1 0)

lemma deriv_deriv_abelF_Q0 (n : ℕ) (h : ℝ → ℝ) (s : ℝ) :
    deriv (deriv (Work.OddVolterra.Existence.abelF
        (fun v : ℝ => (Q n h v) 0 - (Q n 0 v) 0))) s
      = -deriv (deriv (Work.OddVolterra.Existence.abelF
          (fun v : ℝ => E1 n h v - E1 n 0 v))) s := by
  have h1 : (fun v : ℝ => (Q n h v) 0 - (Q n 0 v) 0)
      = fun v : ℝ => -(E1 n h v - E1 n 0 v) := by
    funext v; exact Work.OddVolterra.Existence.xiC_Q_sub_zero n h v
  rw [h1, deriv_deriv_abelF_neg]

lemma deriv_deriv_abelF_Q1 (n : ℕ) (h : ℝ → ℝ) (s : ℝ) :
    deriv (deriv (Work.OddVolterra.Existence.abelF
        (fun v : ℝ => (Q n h v) 1 - (Q n 0 v) 1))) s
      = -deriv (deriv (Work.OddVolterra.Existence.abelF
          (fun v : ℝ => E2 n h v - E2 n 0 v))) s := by
  have h1 : (fun v : ℝ => (Q n h v) 1 - (Q n 0 v) 1)
      = fun v : ℝ => -(E2 n h v - E2 n 0 v) := by
    funext v; exact Work.OddVolterra.Existence.xiC_Q_sub_one n h v
  rw [h1, deriv_deriv_abelF_neg]

lemma contDiffOn_deriv_Q (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) (i : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => deriv (fun x : ℝ => ∫ v in x..(1:ℝ),
        (Q n h v) i / Real.sqrt (v - x)) u)
      (Set.Ioo (1/8 : ℝ) 1) := by
  refine Work.OddVolterra.Existence.aw_abel_deriv_contDiffOn
    (Q := fun v : ℝ => (Q n h v) i) (a := 1/8) (by norm_num) (by norm_num) ?_ ?_
  · exact (contDiffOn_pi.mp (Work.OddVolterra.Existence.aw_Q_contDiffOn n hn hh hsupp hsmall)) i
  · exact (continuousOn_pi.mp (Work.OddVolterra.Existence.aw_Q_continuousOn_Icc n hn hh hsupp hsmall
      (a := 1/8) (by norm_num))) i

lemma differentiableAt_Xi_component (n : ℕ) (hn : 1 ≤ n) {h' : ℝ → ℝ}
    (hh' : ContDiff ℝ (⊤ : ℕ∞) h')
    (hsupp' : Function.support h' ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall' : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h' s| ≤ 1 / 100)
    {s : ℝ} (hs : (1/8 : ℝ) < s) (hs1 : s < 1) (i : Fin 4) :
    DifferentiableAt ℝ (fun u : ℝ => Xi n h' u i) s := by
  have hmem : s ∈ Set.Ioo (1/8 : ℝ) 1 := ⟨hs, hs1⟩
  have h0 : (fun u : ℝ => Xi n h' u (0 : Fin 4)) = fun _ => Commons.Geometry.Ulam.profileX 1 := by
    funext u; simp [Xi]
  have h1 : (fun u : ℝ => Xi n h' u (1 : Fin 4)) = fun _ => Commons.Geometry.Ulam.profileX 1 := by
    funext u; simp [Xi]
  have h2 : (fun u : ℝ => Xi n h' u (2 : Fin 4))
      = fun u : ℝ => deriv (fun x : ℝ => ∫ v in x..(1:ℝ),
          (Q n h' v) 0 / Real.sqrt (v - x)) u := by
    funext u; simp [Xi, Qtilde]
  have h3 : (fun u : ℝ => Xi n h' u (3 : Fin 4))
      = fun u : ℝ => deriv (fun x : ℝ => ∫ v in x..(1:ℝ),
          (Q n h' v) 1 / Real.sqrt (v - x)) u := by
    funext u; simp [Xi, Qtilde]
  fin_cases i
  · change DifferentiableAt ℝ (fun u : ℝ => Xi n h' u (0 : Fin 4)) s
    rw [h0]; exact differentiableAt_const _
  · change DifferentiableAt ℝ (fun u : ℝ => Xi n h' u (1 : Fin 4)) s
    rw [h1]; exact differentiableAt_const _
  · change DifferentiableAt ℝ (fun u : ℝ => Xi n h' u (2 : Fin 4)) s
    rw [h2]
    exact ((contDiffOn_deriv_Q n hn hh' hsupp' hsmall' 0).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hmem)
  · change DifferentiableAt ℝ (fun u : ℝ => Xi n h' u (3 : Fin 4)) s
    rw [h3]
    exact ((contDiffOn_deriv_Q n hn hh' hsupp' hsmall' 1).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hmem)

/-! ## The main theorem -/

theorem xi_deriv_close (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
        ‖deriv (fun u : ℝ => Work.OddVolterra.Xi n h u) s -
          deriv (fun u : ℝ => Work.OddVolterra.Xi n 0 u) s‖ ≤ C * δ := by
  have ht : (1 : ℝ) - tau = 9 / 10 := Work.OddVolterra.Smooth.one_sub_tau_eq
  obtain ⟨Ca, hCa0, hCa⟩ :=
    Work.OddVolterra.Abel.abelF_deriv2_bound (c := 1/8) (d := 1)
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Ce, hCe0, hCe⟩ :=
    Work.OddVolterra.Existence.E1_E2_deriv2_bounds n hn (c := 1/16) (by norm_num) (by rw [ht]; norm_num)
  refine ⟨Ca * Ce + 1, by positivity, ?_⟩
  intro h δ hh hδpos hδ100 hjet hsupp s hs
  have hδnn : 0 ≤ δ := hδpos.le
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ 1/100 := by
    intro k hk t
    have := hjet k (by omega) t
    linarith
  have hsmall : ∀ t : ℝ, |h t| ≤ 1/100 := by
    intro t
    have h1 : |iteratedDeriv 0 h t| ≤ δ := hjet 0 (by omega) t
    rw [iteratedDeriv_zero] at h1
    linarith
  have hsmall0_1 : ∀ k : ℕ, k ≤ 1 → ∀ t : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) t| ≤ 1/100 := by
    intro k hk t
    have hz : iteratedDeriv k (0 : ℝ → ℝ) t = 0 := by
      rw [show (0 : ℝ → ℝ) = fun _ => (0:ℝ) from rfl, iteratedDeriv_const]
      split_ifs <;> rfl
    rw [hz, abs_zero]; norm_num
  have hsmall0 : ∀ t : ℝ, |(0 : ℝ → ℝ) t| ≤ 1/100 := by intro t; simp
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆ Set.Icc (1 - 2 * tau) (1 - tau) := by
    intro x hx; rw [Function.mem_support] at hx; exact absurd rfl hx
  have hmid := Work.OddVolterra.Existence.xiC_mem_hmid hsupp hsmall
  have hmid0 := Work.OddVolterra.Existence.xiC_mem_hmid_zero
  obtain ⟨hE1a, hE2a⟩ := Work.OddVolterra.Existence.E1_E2_contDiff n hn hh hmid
  obtain ⟨hE1b, hE2b⟩ := Work.OddVolterra.Existence.E1_E2_contDiff n hn contDiff_const hmid0
  have hφE1cd : ContDiffOn ℝ (⊤:ℕ∞) (fun v : ℝ => E1 n h v - E1 n 0 v) (Set.Ioo (0:ℝ) 1) :=
    hE1a.sub hE1b
  have hφE2cd : ContDiffOn ℝ (⊤:ℕ∞) (fun v : ℝ => E2 n h v - E2 n 0 v) (Set.Ioo (0:ℝ) 1) :=
    hE2a.sub hE2b
  have hone : (1 - tau : ℝ) < 1 := by
    rw [Work.OddVolterra.Smooth.one_sub_tau_eq]; norm_num
  have hφE1ev : (fun v : ℝ => E1 n h v - E1 n 0 v) =ᶠ[𝓝 1] 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds hone] with v hv
    simp only [Pi.zero_apply]
    exact sub_eq_zero.mpr (Work.OddVolterra.Existence.xiC_E1_eq_of_gt n hsupp hv)
  have hφE2ev : (fun v : ℝ => E2 n h v - E2 n 0 v) =ᶠ[𝓝 1] 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds hone] with v hv
    simp only [Pi.zero_apply]
    exact sub_eq_zero.mpr (Work.OddVolterra.Existence.xiC_E2_eq_of_gt n hsupp hv)
  obtain ⟨hφ1a, hφ1b, h1c, h1d, h1e, h1f⟩ :=
    phi_abel_data (c := 1/8) (by norm_num) hφE1cd hφE1ev
  obtain ⟨hφ2a, hφ2b, h2c, h2d, h2e, h2f⟩ :=
    phi_abel_data (c := 1/8) (by norm_num) hφE2cd hφE2ev
  have hKE1 : ∀ v ∈ Set.Ioo (1/8 : ℝ) 1,
      |deriv (deriv (fun v : ℝ => E1 n h v - E1 n 0 v)) v| ≤ Ce * δ := by
    intro v hv
    by_cases hle : v ≤ 1 - tau
    · exact (hCe h δ hh hδpos hδ100 hjet).1 v ⟨by linarith [hv.1], hle⟩
    · have hgt : 1 - tau < v := lt_of_not_ge hle
      have hev0 : (fun w : ℝ => E1 n h w - E1 n 0 w) =ᶠ[𝓝 v] 0 := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        simp only [Pi.zero_apply]
        exact sub_eq_zero.mpr (Work.OddVolterra.Existence.xiC_E1_eq_of_gt n hsupp hw)
      have hd1 : deriv (fun w : ℝ => E1 n h w - E1 n 0 w) =ᶠ[𝓝 v] 0 :=
        deriv_eventuallyEq_zero hev0
      have hd2 : deriv (deriv (fun w : ℝ => E1 n h w - E1 n 0 w)) v = 0 := by
        rw [Filter.EventuallyEq.deriv_eq hd1]; exact deriv_const v 0
      rw [hd2, abs_zero]; positivity
  have hKE2 : ∀ v ∈ Set.Ioo (1/8 : ℝ) 1,
      |deriv (deriv (fun v : ℝ => E2 n h v - E2 n 0 v)) v| ≤ Ce * δ := by
    intro v hv
    by_cases hle : v ≤ 1 - tau
    · exact (hCe h δ hh hδpos hδ100 hjet).2 v ⟨by linarith [hv.1], hle⟩
    · have hgt : 1 - tau < v := lt_of_not_ge hle
      have hev0 : (fun w : ℝ => E2 n h w - E2 n 0 w) =ᶠ[𝓝 v] 0 := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
        simp only [Pi.zero_apply]
        exact sub_eq_zero.mpr (Work.OddVolterra.Existence.xiC_E2_eq_of_gt n hsupp hw)
      have hd1 : deriv (fun w : ℝ => E2 n h w - E2 n 0 w) =ᶠ[𝓝 v] 0 :=
        deriv_eventuallyEq_zero hev0
      have hd2 : deriv (deriv (fun w : ℝ => E2 n h w - E2 n 0 w)) v = 0 := by
        rw [Filter.EventuallyEq.deriv_eq hd1]; exact deriv_const v 0
      rw [hd2, abs_zero]; positivity
  have hab1 : |deriv (deriv (Work.OddVolterra.Existence.abelF
      (fun v : ℝ => E1 n h v - E1 n 0 v))) s| ≤ Ca * (Ce * δ) :=
    hCa (K := Ce * δ) (mul_nonneg hCe0 hδnn) hφ1a hφ1b h1c h1d h1e h1f hKE1 s
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hab2 : |deriv (deriv (Work.OddVolterra.Existence.abelF
      (fun v : ℝ => E2 n h v - E2 n 0 v))) s| ≤ Ca * (Ce * δ) :=
    hCa (K := Ce * δ) (mul_nonneg hCe0 hδnn) hφ2a hφ2b h2c h2d h2e h2f hKE2 s
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hs' : (1/4 : ℝ) ≤ s := hs.1
  have hs1' : s < 1 := by linarith [hs.2]
  have hXsub0 : |deriv (fun u : ℝ => (Qtilde n h u) 0) s
      - deriv (fun u : ℝ => (Qtilde n 0 u) 0) s| ≤ Ca * (Ce * δ) := by
    rw [Work.OddVolterra.Existence.deriv_Qtilde_sub_abelF n hn hh hsupp hsmall 0 hs' hs1', deriv_deriv_abelF_Q0,
      abs_neg]
    exact hab1
  have hXsub1 : |deriv (fun u : ℝ => (Qtilde n h u) 1) s
      - deriv (fun u : ℝ => (Qtilde n 0 u) 1) s| ≤ Ca * (Ce * δ) := by
    rw [Work.OddVolterra.Existence.deriv_Qtilde_sub_abelF n hn hh hsupp hsmall 1 hs' hs1', deriv_deriv_abelF_Q1,
      abs_neg]
    exact hab2
  have hd1 : ∀ i : Fin 4, DifferentiableAt ℝ (fun u : ℝ => Xi n h u i) s :=
    fun i => differentiableAt_Xi_component n hn hh hsupp hsmall1
      (by linarith [hs.1]) (by linarith [hs.2]) i
  have hd0 : ∀ i : Fin 4, DifferentiableAt ℝ (fun u : ℝ => Xi n 0 u i) s :=
    fun i => differentiableAt_Xi_component n hn contDiff_const hsupp0 hsmall0_1
      (by linarith [hs.1]) (by linarith [hs.2]) i
  have hZ0 : (fun u : ℝ => Xi n h u (0 : Fin 4)) = fun _ => Commons.Geometry.Ulam.profileX 1 := by
    funext u; simp [Xi]
  have hZ0' : (fun u : ℝ => Xi n 0 u (0 : Fin 4)) = fun _ => Commons.Geometry.Ulam.profileX 1 := by
    funext u; simp [Xi]
  have hZ1 : (fun u : ℝ => Xi n h u (1 : Fin 4)) = fun _ => Commons.Geometry.Ulam.profileX 1 := by
    funext u; simp [Xi]
  have hZ1' : (fun u : ℝ => Xi n 0 u (1 : Fin 4)) = fun _ => Commons.Geometry.Ulam.profileX 1 := by
    funext u; simp [Xi]
  have hZ2 : (fun u : ℝ => Xi n h u (2 : Fin 4)) = fun u : ℝ => (Qtilde n h u) 0 := by
    funext u; simp [Xi]
  have hZ2' : (fun u : ℝ => Xi n 0 u (2 : Fin 4)) = fun u : ℝ => (Qtilde n 0 u) 0 := by
    funext u; simp [Xi]
  have hZ3 : (fun u : ℝ => Xi n h u (3 : Fin 4)) = fun u : ℝ => (Qtilde n h u) 1 := by
    funext u; simp [Xi]
  have hZ3' : (fun u : ℝ => Xi n 0 u (3 : Fin 4)) = fun u : ℝ => (Qtilde n 0 u) 1 := by
    funext u; simp [Xi]
  have hle : Ca * (Ce * δ) ≤ (Ca * Ce + 1) * δ := by nlinarith [hCa0, hCe0, hδnn]
  rw [deriv_pi hd1, deriv_pi hd0]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
  rw [Real.norm_eq_abs]
  fin_cases i
  · change |deriv (fun u : ℝ => Xi n h u (0 : Fin 4)) s
        - deriv (fun u : ℝ => Xi n 0 u (0 : Fin 4)) s| ≤ (Ca * Ce + 1) * δ
    simp only [hZ0, hZ0', deriv_const, sub_self, abs_zero]
    positivity
  · change |deriv (fun u : ℝ => Xi n h u (1 : Fin 4)) s
        - deriv (fun u : ℝ => Xi n 0 u (1 : Fin 4)) s| ≤ (Ca * Ce + 1) * δ
    simp only [hZ1, hZ1', deriv_const, sub_self, abs_zero]
    positivity
  · change |deriv (fun u : ℝ => Xi n h u (2 : Fin 4)) s
        - deriv (fun u : ℝ => Xi n 0 u (2 : Fin 4)) s| ≤ (Ca * Ce + 1) * δ
    rw [hZ2, hZ2']
    exact le_trans hXsub0 hle
  · change |deriv (fun u : ℝ => Xi n h u (3 : Fin 4)) s
        - deriv (fun u : ℝ => Xi n 0 u (3 : Fin 4)) s| ≤ (Ca * Ce + 1) * δ
    rw [hZ3, hZ3']
    exact le_trans hXsub1 hle

end
end Work.OddVolterra.WinData
