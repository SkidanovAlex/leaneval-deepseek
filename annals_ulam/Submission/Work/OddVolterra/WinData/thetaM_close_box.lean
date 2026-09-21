import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.WinData.Specs
import Submission.Work.OddVolterra.WinData.Basic
import Submission.Work.OddVolterra.WinData.Kden
import Submission.Work.OddVolterra.WinData.J12M
import Submission.Work.OddVolterra.KernelExt.Rnu_contDiff
import Submission.Work.OddVolterra.Existence.krad_pos_state_region
import Submission.Work.OddExistence.Manifest.aw_toolkit
import Submission.Work.OddExistence.Manifest.hasDerivAt_G2M_apply
import Submission.Work.OddVolterra.WinData.Kden_jets_ext
import Submission.Work.OddVolterra.WinData.J12M_est_ext
import Submission.Work.OddVolterra.WinData.state_ball_bounds

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## Positivity of the Abel radicand for arbitrary positive slopes

`krad_pos_state_region` proves `0 < krad h σ t a` for `b ≤ a ≤ σ ≤ 1`; its proof never uses
`σ ≤ 1`, so the same computation gives positivity for *any* `0 < a ≤ σ`.  Combining with
`krad_comm` covers both orderings. -/

lemma krad_pos_any {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b a σ t : ℝ} (hb : 0 < b) (ha : b ≤ a) (haσ : a ≤ σ) (ht : 1 / 5 ≤ |t|) :
    0 < Work.OddVolterra.krad h σ t a := by
  have hh0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => hsmall 0 (by norm_num) x
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := by
    intro x
    simpa using hsmall 1 (by norm_num) x
  have htau1 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by
    rw [Work.OddVolterra.tau]; norm_num
  have htau2 : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by
    rw [Work.OddVolterra.tau]; norm_num
  have hzero : ∀ x : ℝ, x < 4 / 5 → h x = 0 := by
    intro x hx
    by_contra hne
    have hmem := hsupp (Function.mem_support.mpr hne)
    rw [htau1, htau2] at hmem
    linarith [hmem.1]
  have hapos : 0 < a := lt_of_lt_of_le hb ha
  have hσpos : 0 < σ := lt_of_lt_of_le hapos haσ
  have hS : 0 < σ + a := by linarith
  have hquotbd : |Work.OddVolterra.hquot h a σ| ≤ 1 / 100 :=
    Work.OddExistence.Manifest.AW.abs_hquot_le_state hh1
  have hbnd := abs_le.mp hquotbd
  have hhl : |h σ + h a| ≤ 1 / 50 := by
    have h1 := abs_le.mp (hh0 σ)
    have h2 := abs_le.mp (hh0 a)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hsumlt : |h σ + h a| < (σ + a) * (1 / 5) := by
    rcases lt_or_ge σ (4 / 5 : ℝ) with hlt | hge
    · rw [hzero σ hlt, hzero a (lt_of_le_of_lt haσ hlt), add_zero, abs_zero]
      exact mul_pos hS (by norm_num)
    · have h1 : (4 : ℝ) / 5 * (1 / 5) ≤ (σ + a) * (1 / 5) :=
        mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
      have h25 : (4 : ℝ) / 5 * (1 / 5) = 4 / 25 := by norm_num
      have h50 : (1 : ℝ) / 50 < 4 / 25 := by norm_num
      linarith
  have hhline : Work.OddVolterra.line h σ t + Work.OddVolterra.line h a t
      = (σ + a) * t + (h σ + h a) := by
    unfold Work.OddVolterra.line; ring
  rw [Work.OddVolterra.krad_apply, hhline]
  rcases lt_trichotomy t 0 with htn | htz | htp
  · have htle : t ≤ -(1 / 5) := by
      have h := ht; rw [abs_of_neg htn] at h; linarith
    have h1 : t + Work.OddVolterra.hquot h a σ < 0 := by linarith [hbnd.2]
    have hlt' : h σ + h a < (σ + a) * (1 / 5) := lt_of_le_of_lt (le_abs_self _) hsumlt
    have hmul : (σ + a) * t ≤ -((σ + a) * (1 / 5)) := by
      have h := mul_le_mul_of_nonneg_left htle (le_of_lt hS)
      rwa [show (σ + a) * (-(1 / 5)) = -((σ + a) * (1 / 5)) by ring] at h
    have h2 : (σ + a) * t + (h σ + h a) < 0 := by linarith
    exact mul_pos_of_neg_of_neg h1 h2
  · rw [htz] at ht; norm_num at ht
  · have htge : 1 / 5 ≤ t := by have h := ht; rwa [abs_of_pos htp] at h
    have h1 : 0 < t + Work.OddVolterra.hquot h a σ := by linarith [hbnd.1]
    have hnegabs : -((σ + a) * (1 / 5)) < -|h σ + h a| := by linarith
    have hgt' : -((σ + a) * (1 / 5)) < h σ + h a :=
      lt_of_lt_of_le hnegabs (neg_abs_le _)
    have hmul : (σ + a) * (1 / 5) ≤ (σ + a) * t :=
      mul_le_mul_of_nonneg_left htge (le_of_lt hS)
    have h2 : 0 < (σ + a) * t + (h σ + h a) := by linarith
    exact mul_pos h1 h2

lemma krad_pos_of_pos {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {A u σ t : ℝ} (hA : 0 < A) (hu : A ≤ u) (hσ : A ≤ σ) (ht : 1 / 5 ≤ |t|) :
    0 < Work.OddVolterra.krad h σ t u := by
  rcases le_total u σ with h | h
  · exact krad_pos_any hsupp hsmall hA hu h ht
  · rw [krad_comm]
    exact krad_pos_any hsupp hsmall hA hσ h ht

/-! ## An upper bound for the Abel denominator -/

lemma Kden_le_four {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a σ t : ℝ}
    (hq : |Work.OddVolterra.hquot h a σ| ≤ 1 / 100) (hhσ : |h σ| ≤ 1 / 100)
    (hha : |h a| ≤ 1 / 100) (ht2 : |t| ≤ 2) (hS2 : σ + a ≤ 5 / 2) (hS0 : 0 < σ + a) :
    Work.OddVolterra.Kden h a σ t ≤ 4 := by
  have hline : ∀ s : ℝ, Work.OddVolterra.line h s t = s * t + h s := fun s => rfl
  have hkr : Work.OddVolterra.krad h σ t a
      = (t + Work.OddVolterra.hquot h a σ)
        * ((σ + a) * t + (h σ + h a)) := by
    rw [Work.OddVolterra.krad_apply]
    congr 1
    rw [hline σ, hline a]; ring
  have h1 : |t + Work.OddVolterra.hquot h a σ| ≤ 21 / 10 := by
    have h := abs_le.mp hq
    have ht := abs_le.mp ht2
    rw [abs_le]; constructor <;> linarith
  have h2 : |(σ + a) * t + (h σ + h a)| ≤ 51 / 10 := by
    have h3 : |(σ + a) * t| ≤ 5 := by
      rw [abs_mul, abs_of_pos hS0]
      calc (σ + a) * |t| ≤ (5 / 2) * 2 := mul_le_mul hS2 ht2 (abs_nonneg t) (by norm_num)
        _ = 5 := by norm_num
    have h4 : |h σ + h a| ≤ 1 / 50 := by
      have h5 := abs_le.mp hhσ
      have h6 := abs_le.mp hha
      rw [abs_le]; constructor <;> linarith
    linarith [abs_add_le ((σ + a) * t) (h σ + h a)]
  have h3 : Work.OddVolterra.krad h σ t a ≤ 11 := by
    rw [hkr]
    have h4 : |(t + Work.OddVolterra.hquot h a σ) * ((σ + a) * t + (h σ + h a))|
        ≤ (21 / 10) * (51 / 10) := by
      rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    linarith [le_abs_self ((t + Work.OddVolterra.hquot h a σ) * ((σ + a) * t + (h σ + h a)))]
  rw [Work.OddVolterra.Kden_eq_sqrt_krad]
  calc Real.sqrt (Work.OddVolterra.krad h σ t a) ≤ Real.sqrt 11 := Real.sqrt_le_sqrt h3
    _ ≤ 4 := by
        have h16 : Real.sqrt (16 : ℝ) = 4 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        calc Real.sqrt 11 ≤ Real.sqrt 16 := Real.sqrt_le_sqrt (by norm_num)
          _ = 4 := h16

/-! ## Differentiability of the manifest kernel in the first slot -/

lemma differentiableAt_Kden {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a σ t : ℝ}
    (hpos : 0 < Work.OddVolterra.krad h σ t a) :
    DifferentiableAt ℝ (fun a' : ℝ => Work.OddVolterra.Kden h a' σ t) a := by
  have hcont : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Work.OddVolterra.hquot h p.1 p.2) :=
    Work.OddExistence.Manifest.AW.hquot_contDiff_local hh
  have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => (a', σ)) := by fun_prop
  have hq : DifferentiableAt ℝ (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a :=
    ((hcont.comp hpair).differentiable (by simp)).differentiableAt
  have hl : DifferentiableAt ℝ (fun a' : ℝ => Work.OddVolterra.line h a' t) a := by
    unfold Work.OddVolterra.line
    exact ((differentiableAt_id (x := a)).mul_const t).add
      ((hh.differentiable (by simp)).differentiableAt)
  have hkd : DifferentiableAt ℝ (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a := by
    have hfun : (fun a' : ℝ => Work.OddVolterra.krad h σ t a')
        = fun a' : ℝ => (t + Work.OddVolterra.hquot h a' σ)
            * (Work.OddVolterra.line h σ t + Work.OddVolterra.line h a' t) := by
      funext a'; rw [Work.OddVolterra.krad_apply]
    rw [hfun]
    exact ((hq.const_add t).mul
      ((differentiableAt_const (c := Work.OddVolterra.line h σ t)).add hl))
  have hder := hkd.hasDerivAt.sqrt (ne_of_gt hpos)
  have heq : (fun a' : ℝ => Real.sqrt (Work.OddVolterra.krad h σ t a'))
      = fun a' => Work.OddVolterra.Kden h a' σ t :=
    funext fun a' => (Work.OddVolterra.Kden_eq_sqrt_krad h a' σ t).symm
  rw [heq] at hder
  exact hder.differentiableAt

lemma differentiableAt_J1M (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t a : ℝ) :
    DifferentiableAt ℝ (fun a' : ℝ => KernelExt.J1M n h a' σ t) a := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => KernelExt.J1M n h a' σ t) := by
    simpa only [KernelExt.J1M] using
      Work.OddExistence.Manifest.AW.contDiff_Rnu_section ((n : ℝ) + 1 / 2) hh contDiff_const
        (n + 1) σ t
  exact (hcd.differentiable (by simp)).differentiableAt

lemma differentiableAt_J2M (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t a : ℝ) :
    DifferentiableAt ℝ (fun a' : ℝ => KernelExt.J2M n h a' σ t) a := by
  have hinit : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × ℝ => Work.OddVolterra.lineSlope h p.1 p.2.2) := by
    unfold Work.OddVolterra.lineSlope; fun_prop
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => KernelExt.J2M n h a' σ t) := by
    simpa only [KernelExt.J2M] using
      Work.OddExistence.Manifest.AW.contDiff_Rnu_section ((n : ℝ) - 1 / 2) hh hinit n σ t
  exact (hcd.differentiable (by simp)).differentiableAt

/-! ## Estimates for the manifest Abel kernels `K₁`, `K₂` on the extended box -/

theorem K12M_est_ext (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      ∀ u : ℝ, 3 * a / 4 ≤ u → u ≤ 3 / 2 → ∀ σ : ℝ, a ≤ σ → σ ≤ 1 →
      ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 2 →
      (|Work.OddVolterra.KernelExt.K1M n h u σ t| ≤ C ∧
       |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ t) u| ≤ C ∧
       |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ t) u -
        deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ t) u| ≤ C * δ ∧
       |Work.OddVolterra.KernelExt.K2M n h u σ t| ≤ C ∧
       |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ t) u| ≤ C ∧
       |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ t) u -
        deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ t) u| ≤ C * δ) := by
  obtain ⟨CJ, hCJ0, hJ⟩ := J12M_est_ext n hn (a := a) ha
  have hA : 0 < a / 2 := by linarith
  set κ : ℝ := kdenKap (a / 2) with hκdef
  have hκ0 : 0 < κ := by rw [hκdef]; exact kdenKap_pos hA
  set Kd : ℝ := kdenC (a / 2) with hKddef
  have hKd0 : 0 < Kd := by rw [hKddef]; exact kdenC_pos hA
  set Cf : ℝ := 2 * CJ with hCfdef
  have hCf0 : 0 < Cf := by rw [hCfdef]; linarith
  set A0 : ℝ := 1 / κ + Cf / κ ^ 2 with hA0def
  set A1 : ℝ := 2 * (Cf * 4 + Cf * Kd) * 4 / κ ^ 4 + (4 + 2 * Cf + Kd) / κ ^ 2 with hA1def
  have hA0nn : 0 ≤ A0 := by rw [hA0def]; positivity
  have hA1nn : 0 ≤ A1 := by rw [hA1def]; positivity
  have hA0pos : 0 < A0 := by rw [hA0def]; positivity
  have hA1pos : 0 < A1 := by rw [hA1def]; positivity
  set C12 : ℝ := A0 * (CJ + Kd) + A1 * (CJ + Kd) + Cf / κ + (Cf * 4 + Cf * Kd) / κ ^ 2 +
      (Cf * 4 + Cf * Kd) + 1 with hC12def
  refine ⟨C12, ?_, ?_⟩
  · rw [hC12def]
    have h1 : 0 < A0 * (CJ + Kd) := mul_pos hA0pos (by linarith)
    have h2 : 0 < A1 * (CJ + Kd) := mul_pos hA1pos (by linarith)
    have h3 : 0 < Cf / κ := by positivity
    have h4 : 0 ≤ (Cf * 4 + Cf * Kd) / κ ^ 2 := by positivity
    have h5 : 0 ≤ (Cf * 4 + Cf * Kd) := by positivity
    linarith
  intro h δ hh hδ0 hδ1 hjet hsupp u hu1 hu2 σ hσa hσ1 t ht1 ht2
  have hδ0' : 0 ≤ δ := hδ0.le
  obtain ⟨⟨hJ1v, hJ1d, hJ10v, hJ10d⟩, ⟨hJ2v, hJ2d, hJ20v, hJ20d⟩⟩ :=
    hJ h δ hh hδ0 hδ1 hjet hsupp u hu1 hu2 σ hσa hσ1 t ht1 ht2
  obtain ⟨hKl, hKl0, hKcl, hKd1, hKd2, hKdcl⟩ :=
    Kden_jets_ext hh hsupp hδ0 hδ1 (fun k hk => hjet k (by omega))
      hA (by linarith) (by linarith) hσ1 hu2 ht1 ht2
  have hKl' : κ ≤ Work.OddVolterra.Kden h u σ t := by rw [hκdef]; exact hKl
  have hKl0' : κ ≤ Work.OddVolterra.Kden 0 u σ t := by rw [hκdef]; exact hKl0
  have hKcl' : |Work.OddVolterra.Kden h u σ t - Work.OddVolterra.Kden 0 u σ t| ≤ Kd * δ := by
    rw [hKddef]; exact hKcl
  have hKd1' : |deriv (fun a' : ℝ => Work.OddVolterra.Kden h a' σ t) u| ≤ Kd := by
    rw [hKddef]; exact hKd1
  have hKd2' : |deriv (fun a' : ℝ => Work.OddVolterra.Kden 0 a' σ t) u| ≤ Kd := by
    rw [hKddef]; exact hKd2
  have hKdcl' : |deriv (fun a' : ℝ => Work.OddVolterra.Kden h a' σ t) u -
      deriv (fun a' : ℝ => Work.OddVolterra.Kden 0 a' σ t) u| ≤ Kd * δ := by
    rw [hKddef]; exact hKdcl
  -- smallness of the jets
  have hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hjet k (by omega) s) hδ1
  have hd1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := by
    intro x; simpa [iteratedDeriv_one] using hsmall 1 (by norm_num) x
  have hsmall0 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ 1 / 100 := by
    intro k hk s
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split_ifs <;> norm_num
  have hd10 : ∀ x : ℝ, |deriv (0 : ℝ → ℝ) x| ≤ 1 / 100 := by
    intro x
    have h0 : deriv (0 : ℝ → ℝ) x = 0 := by
      simpa using deriv_const (𝕜 := ℝ) (x := x) (c := (0 : ℝ))
    rw [h0]; norm_num
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) := by
    intro x hx; simp at hx
  have hpos : 0 < Work.OddVolterra.krad h σ t u :=
    krad_pos_of_pos hsupp hsmall hA (by linarith) (by linarith) ht1
  have hpos0 : 0 < Work.OddVolterra.krad 0 σ t u :=
    krad_pos_of_pos hsupp0 hsmall0 hA (by linarith) (by linarith) ht1
  -- upper bounds for `Kden`
  have hq : |Work.OddVolterra.hquot h u σ| ≤ 1 / 100 :=
    Work.OddExistence.Manifest.AW.abs_hquot_le_state hd1
  have hσsm : |h σ| ≤ 1 / 100 := le_trans (hjet 0 (by omega) σ) hδ1
  have husm : |h u| ≤ 1 / 100 := le_trans (hjet 0 (by omega) u) hδ1
  have hKle : Work.OddVolterra.Kden h u σ t ≤ 4 :=
    Kden_le_four hh hq hσsm husm ht2 (by linarith) (by linarith)
  have hq0 : |Work.OddVolterra.hquot (0 : ℝ → ℝ) u σ| ≤ 1 / 100 := by
    rw [Work.OddExistence.Manifest.AW.hquot_zero]; norm_num
  have hKle0 : Work.OddVolterra.Kden 0 u σ t ≤ 4 :=
    Kden_le_four (h := (0 : ℝ → ℝ)) contDiff_const hq0 (by simp) (by simp) ht2
      (by linarith) (by linarith)
  have hKne : Work.OddVolterra.Kden h u σ t ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hκ0 hKl')
  have hKne0 : Work.OddVolterra.Kden 0 u σ t ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hκ0 hKl0')
  have hKabs : κ ≤ |Work.OddVolterra.Kden h u σ t| := by
    rw [abs_of_pos (lt_of_lt_of_le hκ0 hKl')]; exact hKl'
  have hKabs0 : κ ≤ |Work.OddVolterra.Kden 0 u σ t| := by
    rw [abs_of_pos (lt_of_lt_of_le hκ0 hKl0')]; exact hKl0'
  have hKg1 : |Work.OddVolterra.Kden h u σ t| ≤ 4 := by
    rw [abs_of_pos (lt_of_lt_of_le hκ0 hKl')]; exact hKle
  have hKg0 : |Work.OddVolterra.Kden 0 u σ t| ≤ 4 := by
    rw [abs_of_pos (lt_of_lt_of_le hκ0 hKl0')]; exact hKle0
  have hKpos : 0 ≤ Work.OddVolterra.Kden h u σ t := le_of_lt (lt_of_lt_of_le hκ0 hKl')
  -- numerator bounds
  have hJδ : CJ * δ ≤ CJ := by
    calc CJ * δ ≤ CJ * 1 := mul_le_mul_of_nonneg_left (by linarith [hδ1]) hCJ0.le
      _ = CJ := mul_one CJ
  have hnum1 : |Work.OddVolterra.KernelExt.J1M n h u σ t| ≤ Cf := by
    rw [hCfdef]
    calc |Work.OddVolterra.KernelExt.J1M n h u σ t|
        = |(Work.OddVolterra.KernelExt.J1M n h u σ t - Work.OddVolterra.KernelExt.J1M n 0 u σ t) + Work.OddVolterra.KernelExt.J1M n 0 u σ t| := by
          congr 1
          ring
      _ ≤ |Work.OddVolterra.KernelExt.J1M n h u σ t -
            Work.OddVolterra.KernelExt.J1M n 0 u σ t| + |Work.OddVolterra.KernelExt.J1M n 0 u σ t| := abs_add_le _ _
      _ ≤ CJ * δ + CJ := add_le_add hJ1v hJ10v
      _ ≤ CJ + CJ := by linarith [hJδ]
      _ = 2 * CJ := by ring
  have hnum1d : |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n h y σ t) u| ≤ Cf := by
    rw [hCfdef]
    calc |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n h y σ t) u|
        = |(deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n h y σ t) u - deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n 0 y σ t) u) + deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n 0 y σ t) u| := by
          congr 1
          ring
      _ ≤ |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n h y σ t) u -
            deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n 0 y σ t) u| + |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n 0 y σ t) u| := abs_add_le _ _
      _ ≤ CJ * δ + CJ := add_le_add hJ1d hJ10d
      _ ≤ CJ + CJ := by linarith [hJδ]
      _ = 2 * CJ := by ring
  have hnum10 : |Work.OddVolterra.KernelExt.J1M n 0 u σ t| ≤ Cf := by
    rw [hCfdef]; linarith [hJ10v, hCJ0]
  have hnum10d : |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n 0 y σ t) u| ≤ Cf := by
    rw [hCfdef]; linarith [hJ10d, hCJ0]
  have hnum2 : |Work.OddVolterra.KernelExt.J2M n h u σ t| ≤ Cf := by
    rw [hCfdef]
    calc |Work.OddVolterra.KernelExt.J2M n h u σ t|
        = |(Work.OddVolterra.KernelExt.J2M n h u σ t - Work.OddVolterra.KernelExt.J2M n 0 u σ t) + Work.OddVolterra.KernelExt.J2M n 0 u σ t| := by
          congr 1
          ring
      _ ≤ |Work.OddVolterra.KernelExt.J2M n h u σ t -
            Work.OddVolterra.KernelExt.J2M n 0 u σ t| + |Work.OddVolterra.KernelExt.J2M n 0 u σ t| := abs_add_le _ _
      _ ≤ CJ * δ + CJ := add_le_add hJ2v hJ20v
      _ ≤ CJ + CJ := by linarith [hJδ]
      _ = 2 * CJ := by ring
  have hnum2d : |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n h y σ t) u| ≤ Cf := by
    rw [hCfdef]
    calc |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n h y σ t) u|
        = |(deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n h y σ t) u - deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n 0 y σ t) u) + deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n 0 y σ t) u| := by
          congr 1
          ring
      _ ≤ |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n h y σ t) u -
            deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n 0 y σ t) u| + |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n 0 y σ t) u| := abs_add_le _ _
      _ ≤ CJ * δ + CJ := add_le_add hJ2d hJ20d
      _ ≤ CJ + CJ := by linarith [hJδ]
      _ = 2 * CJ := by ring
  have hnum20 : |Work.OddVolterra.KernelExt.J2M n 0 u σ t| ≤ Cf := by
    rw [hCfdef]; linarith [hJ20v, hCJ0]
  have hnum20d : |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n 0 y σ t) u| ≤ Cf := by
    rw [hCfdef]; linarith [hJ20d, hCJ0]
  -- differentiability
  have hdJ1 : DifferentiableAt ℝ (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n h y σ t) u :=
    differentiableAt_J1M n hh σ t u
  have hdJ10 : DifferentiableAt ℝ (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n 0 y σ t) u :=
    differentiableAt_J1M n contDiff_const σ t u
  have hdJ2 : DifferentiableAt ℝ (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n h y σ t) u :=
    differentiableAt_J2M n hh σ t u
  have hdJ20 : DifferentiableAt ℝ (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n 0 y σ t) u :=
    differentiableAt_J2M n contDiff_const σ t u
  have hdK : DifferentiableAt ℝ (fun y : ℝ => Work.OddVolterra.Kden h y σ t) u :=
    differentiableAt_Kden hh hpos
  have hdK0 : DifferentiableAt ℝ (fun y : ℝ => Work.OddVolterra.Kden 0 y σ t) u :=
    differentiableAt_Kden contDiff_const hpos0
  -- the closeness bounds, all against the single bound `e = (CJ + Kd) * δ`
  have heJ1 : |Work.OddVolterra.KernelExt.J1M n h u σ t -
      Work.OddVolterra.KernelExt.J1M n 0 u σ t| ≤ (CJ + Kd) * δ :=
    le_trans hJ1v (mul_le_mul_of_nonneg_right (by linarith [hKd0]) hδ0')
  have heJ1d : |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n h y σ t) u -
      deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n 0 y σ t) u| ≤ (CJ + Kd) * δ :=
    le_trans hJ1d (mul_le_mul_of_nonneg_right (by linarith [hKd0]) hδ0')
  have heJ2 : |Work.OddVolterra.KernelExt.J2M n h u σ t -
      Work.OddVolterra.KernelExt.J2M n 0 u σ t| ≤ (CJ + Kd) * δ :=
    le_trans hJ2v (mul_le_mul_of_nonneg_right (by linarith [hKd0]) hδ0')
  have heJ2d : |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n h y σ t) u -
      deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n 0 y σ t) u| ≤ (CJ + Kd) * δ :=
    le_trans hJ2d (mul_le_mul_of_nonneg_right (by linarith [hKd0]) hδ0')
  have heK : |Work.OddVolterra.Kden h u σ t - Work.OddVolterra.Kden 0 u σ t| ≤
      (CJ + Kd) * δ :=
    le_trans hKcl' (mul_le_mul_of_nonneg_right (by linarith [hCJ0]) hδ0')
  have heKd : |deriv (fun y : ℝ => Work.OddVolterra.Kden h y σ t) u -
      deriv (fun y : ℝ => Work.OddVolterra.Kden 0 y σ t) u| ≤ (CJ + Kd) * δ :=
    le_trans hKdcl' (mul_le_mul_of_nonneg_right (by linarith [hCJ0]) hδ0')
  have he0 : 0 ≤ (CJ + Kd) * δ := by positivity
  have hT1 : 0 ≤ A0 * (CJ + Kd) := mul_nonneg hA0nn (by linarith)
  have hT2 : 0 ≤ A1 * (CJ + Kd) := mul_nonneg hA1nn (by linarith)
  have hT3 : 0 ≤ Cf / κ := by positivity
  have hT4 : 0 ≤ (Cf * 4 + Cf * Kd) / κ ^ 2 := by positivity
  have hT5 : 0 ≤ (Cf * 4 + Cf * Kd) := by positivity
  have hcl : Cf * 4 + Cf * Kd ≤ C12 := by rw [hC12def]; linarith [hT1, hT2, hT3, hT4, hT5]
  have hclk : (Cf * 4 + Cf * Kd) / κ ^ 2 ≤ C12 := by
    rw [hC12def]; linarith [hT1, hT2, hT3, hT4, hT5]
  have hA1le : A1 * (CJ + Kd) ≤ C12 := by rw [hC12def]; linarith [hT1, hT2, hT3, hT4, hT5]
  have hCfle : Cf / κ ≤ C12 := by rw [hC12def]; linarith [hT1, hT2, hT3, hT4, hT5]
  have hτ : ∀ y : ℝ, y ≤ A1 * (CJ + Kd) → y * δ ≤ C12 * δ := fun y hy =>
    mul_le_mul_of_nonneg_right (le_trans hy hA1le) hδ0'
  have hkey1 : (2 * (Cf * 4 + Cf * Kd) * 4 / κ ^ 4 + (4 + 2 * Cf + Kd) / κ ^ 2) = A1 :=
    hA1def.symm
  have hgoal : ∀ e : ℝ, e = (CJ + Kd) * δ →
      (2 * (Cf * 4 + Cf * Kd) * 4 / κ ^ 4 + (4 + 2 * Cf + Kd) / κ ^ 2) * e ≤ C12 * δ := by
    intro e he
    rw [he, hkey1]
    calc A1 * ((CJ + Kd) * δ) = (A1 * (CJ + Kd)) * δ := by ring
      _ ≤ C12 * δ := mul_le_mul_of_nonneg_right hA1le hδ0'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the value of `K₁M`
    have h1 : |Work.OddVolterra.KernelExt.K1M n h u σ t| ≤ Cf / κ := by
      rw [Work.OddVolterra.KernelExt.K1M, abs_div]
      exact div_le_div₀ hCf0.le hnum1 hκ0 hKabs
    exact le_trans h1 hCfle
  · -- the derivative of `K₁M`
    have hder : deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ t) u
        = (deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n h y σ t) u *
              Work.OddVolterra.Kden h u σ t -
            Work.OddVolterra.KernelExt.J1M n h u σ t *
              deriv (fun y : ℝ => Work.OddVolterra.Kden h y σ t) u)
          / Work.OddVolterra.Kden h u σ t ^ 2 := by
      rw [show (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ t)
          = fun u' : ℝ => Work.OddVolterra.KernelExt.J1M n h u' σ t /
              Work.OddVolterra.Kden h u' σ t from rfl]
      exact deriv_div hdJ1 hdK hKne
    have hb1 : |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n h y σ t) u *
          Work.OddVolterra.Kden h u σ t| ≤ Cf * 4 := by
      rw [abs_mul]
      exact mul_le_mul hnum1d hKg1 (abs_nonneg _) hCf0.le
    have hb2 : |Work.OddVolterra.KernelExt.J1M n h u σ t *
          deriv (fun y : ℝ => Work.OddVolterra.Kden h y σ t) u| ≤ Cf * Kd := by
      rw [abs_mul]
      exact mul_le_mul hnum1 hKd1' (abs_nonneg _) hCf0.le
    have hnum : |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J1M n h y σ t) u *
            Work.OddVolterra.Kden h u σ t -
            Work.OddVolterra.KernelExt.J1M n h u σ t *
            deriv (fun y : ℝ => Work.OddVolterra.Kden h y σ t) u|
        ≤ Cf * 4 + Cf * Kd :=
      le_trans (Work.OddExistence.Manifest.AW.abs_sub_le_add _ _) (add_le_add hb1 hb2)
    have hden : κ ^ 2 ≤ Work.OddVolterra.Kden h u σ t ^ 2 :=
      pow_le_pow_left₀ hκ0.le hKl' 2
    rw [hder, abs_div, abs_of_pos (pow_pos (lt_of_lt_of_le hκ0 hKl') 2)]
    exact le_trans (div_le_div₀ (by positivity) hnum (pow_pos hκ0 2) hden) hclk
  · -- closeness of the derivatives of `K₁M`
    have hdd := Work.OddExistence.Manifest.AW.deriv_div_close
      (f1 := fun y : ℝ => Work.OddVolterra.KernelExt.J1M n h y σ t)
      (f0 := fun y : ℝ => Work.OddVolterra.KernelExt.J1M n 0 y σ t)
      (g1 := fun y : ℝ => Work.OddVolterra.Kden h y σ t)
      (g0 := fun y : ℝ => Work.OddVolterra.Kden 0 y σ t)
      (x := u) (Cf := Cf) (Cg := 4) (Cg' := Kd) (c := κ) (e := (CJ + Kd) * δ)
      hκ0 he0 hCf0.le (by norm_num) hKd0.le hdJ1 hdJ10 hdK hdK0 hKne hKne0
      heJ1 heJ1d heK heKd hnum1 hnum10 hnum1d hnum10d hKg1 hKg0 hKd1' hKd2' hKabs hKabs0
    refine le_trans ?_ (hgoal ((CJ + Kd) * δ) rfl)
    rw [show (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ t)
        = fun u' : ℝ => Work.OddVolterra.KernelExt.J1M n h u' σ t /
            Work.OddVolterra.Kden h u' σ t from rfl,
      show (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ t)
        = fun u' : ℝ => Work.OddVolterra.KernelExt.J1M n 0 u' σ t /
            Work.OddVolterra.Kden 0 u' σ t from rfl]
    exact hdd
  · -- the value of `K₂M`
    have h1 : |Work.OddVolterra.KernelExt.K2M n h u σ t| ≤ Cf / κ := by
      rw [Work.OddVolterra.KernelExt.K2M, abs_div]
      exact div_le_div₀ hCf0.le hnum2 hκ0 hKabs
    exact le_trans h1 hCfle
  · -- the derivative of `K₂M`
    have hder : deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ t) u
        = (deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n h y σ t) u *
              Work.OddVolterra.Kden h u σ t -
            Work.OddVolterra.KernelExt.J2M n h u σ t *
              deriv (fun y : ℝ => Work.OddVolterra.Kden h y σ t) u)
          / Work.OddVolterra.Kden h u σ t ^ 2 := by
      rw [show (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ t)
          = fun u' : ℝ => Work.OddVolterra.KernelExt.J2M n h u' σ t /
              Work.OddVolterra.Kden h u' σ t from rfl]
      exact deriv_div hdJ2 hdK hKne
    have hb1 : |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n h y σ t) u *
          Work.OddVolterra.Kden h u σ t| ≤ Cf * 4 := by
      rw [abs_mul]
      exact mul_le_mul hnum2d hKg1 (abs_nonneg _) hCf0.le
    have hb2 : |Work.OddVolterra.KernelExt.J2M n h u σ t *
          deriv (fun y : ℝ => Work.OddVolterra.Kden h y σ t) u| ≤ Cf * Kd := by
      rw [abs_mul]
      exact mul_le_mul hnum2 hKd1' (abs_nonneg _) hCf0.le
    have hnum : |deriv (fun y : ℝ => Work.OddVolterra.KernelExt.J2M n h y σ t) u *
            Work.OddVolterra.Kden h u σ t -
            Work.OddVolterra.KernelExt.J2M n h u σ t *
            deriv (fun y : ℝ => Work.OddVolterra.Kden h y σ t) u|
        ≤ Cf * 4 + Cf * Kd :=
      le_trans (Work.OddExistence.Manifest.AW.abs_sub_le_add _ _) (add_le_add hb1 hb2)
    have hden : κ ^ 2 ≤ Work.OddVolterra.Kden h u σ t ^ 2 :=
      pow_le_pow_left₀ hκ0.le hKl' 2
    rw [hder, abs_div, abs_of_pos (pow_pos (lt_of_lt_of_le hκ0 hKl') 2)]
    exact le_trans (div_le_div₀ (by positivity) hnum (pow_pos hκ0 2) hden) hclk
  · -- closeness of the derivatives of `K₂M`
    have hdd := Work.OddExistence.Manifest.AW.deriv_div_close
      (f1 := fun y : ℝ => Work.OddVolterra.KernelExt.J2M n h y σ t)
      (f0 := fun y : ℝ => Work.OddVolterra.KernelExt.J2M n 0 y σ t)
      (g1 := fun y : ℝ => Work.OddVolterra.Kden h y σ t)
      (g0 := fun y : ℝ => Work.OddVolterra.Kden 0 y σ t)
      (x := u) (Cf := Cf) (Cg := 4) (Cg' := Kd) (c := κ) (e := (CJ + Kd) * δ)
      hκ0 he0 hCf0.le (by norm_num) hKd0.le hdJ2 hdJ20 hdK hdK0 hKne hKne0
      heJ2 heJ2d heK heKd hnum2 hnum20 hnum2d hnum20d hKg1 hKg0 hKd1' hKd2' hKabs hKabs0
    refine le_trans ?_ (hgoal ((CJ + Kd) * δ) rfl)
    rw [show (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ t)
        = fun u' : ℝ => Work.OddVolterra.KernelExt.J2M n h u' σ t /
            Work.OddVolterra.Kden h u' σ t from rfl,
      show (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ t)
        = fun u' : ℝ => Work.OddVolterra.KernelExt.J2M n 0 u' σ t /
            Work.OddVolterra.Kden 0 u' σ t from rfl]
    exact hdd

lemma Kden_ne_of_pos {h : ℝ → ℝ} {a σ t : ℝ} (hpos : 0 < Work.OddVolterra.krad h σ t a) :
    Work.OddVolterra.Kden h a σ t ≠ 0 := by
  rw [Work.OddVolterra.Kden_eq_sqrt_krad]
  exact ne_of_gt (Real.sqrt_pos.mpr hpos)

lemma differentiableAt_K1M (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {u σ t : ℝ}
    (hpos : 0 < Work.OddVolterra.krad h σ t u) :
    DifferentiableAt ℝ (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ t) u :=
  (differentiableAt_J1M n hh σ t u).div (differentiableAt_Kden hh hpos) (Kden_ne_of_pos hpos)

lemma differentiableAt_K2M (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {u σ t : ℝ}
    (hpos : 0 < Work.OddVolterra.krad h σ t u) :
    DifferentiableAt ℝ (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ t) u :=
  (differentiableAt_J2M n hh σ t u).div (differentiableAt_Kden hh hpos) (Kden_ne_of_pos hpos)

/-! ## Componentwise estimates for the manifest kernel vector on the extended box -/

theorem KvecM_est_ext (n : ℕ) (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      ∀ u : ℝ, 3 * a / 4 ≤ u → u ≤ 3 / 2 → ∀ σ : ℝ, a ≤ σ → σ ≤ 1 →
      ∀ z : Work.OddVolterra.St, (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 →
      (∀ i : Fin 4, |z i| ≤ 2) → ∀ j : Fin 2,
      (‖(Work.OddVolterra.KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j‖ ≤ C ∧
       ‖deriv (fun u' : ℝ =>
            (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) j) u‖ ≤ C ∧
       ‖deriv (fun u' : ℝ =>
              (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) j) u -
            deriv (fun u' : ℝ =>
              (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) j) u‖
          ≤ C * δ) := by
  obtain ⟨C12, hC120, hK12⟩ := K12M_est_ext n hn (a := a) ha
  have hC12nn : 0 ≤ C12 := hC120.le
  refine ⟨4 * C12 + 1, by linarith, ?_⟩
  intro h δ hh hδ0 hδ1 hjet hsupp u hu1 hu2 σ hσa hσ1 z hz0 hz1 hzb j
  have hδ0' : 0 ≤ δ := hδ0.le
  have hz0pos : (0 : ℝ) ≤ z 0 := by linarith [hz0]
  have hz1pos : (0 : ℝ) ≤ z 1 := by linarith [hz1]
  have hz0a : (1 / 5 : ℝ) ≤ |-(z 0)| := by rw [abs_neg, abs_of_nonneg hz0pos]; exact hz0
  have hz1a : (1 / 5 : ℝ) ≤ |z 1| := by rw [abs_of_nonneg hz1pos]; exact hz1
  have hz0b : |-(z 0)| ≤ 2 := by rw [abs_neg]; exact hzb 0
  have hz1b : |z 1| ≤ 2 := hzb 1
  obtain ⟨h1v, h1d, h1c, h2v, h2d, h2c⟩ :=
    hK12 h δ hh hδ0 hδ1 hjet hsupp u hu1 hu2 σ hσa hσ1 (-(z 0)) hz0a hz0b
  obtain ⟨h1v', h1d', h1c', h2v', h2d', h2c'⟩ :=
    hK12 h δ hh hδ0 hδ1 hjet hsupp u hu1 hu2 σ hσa hσ1 (z 1) hz1a hz1b
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) := by
    intro x hx; simp at hx
  have hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hjet k (by omega) s) hδ1
  have hsmall0 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ 1 / 100 := by
    intro k hk s
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split_ifs <;> norm_num
  have hA : 0 < a / 2 := by linarith
  have hposx : 0 < Work.OddVolterra.krad h σ (-(z 0)) u :=
    krad_pos_of_pos hsupp hsmall hA (by linarith) (by linarith) hz0a
  have hposy : 0 < Work.OddVolterra.krad h σ (z 1) u :=
    krad_pos_of_pos hsupp hsmall hA (by linarith) (by linarith) hz1a
  have hposx0 : 0 < Work.OddVolterra.krad 0 σ (-(z 0)) u :=
    krad_pos_of_pos hsupp0 hsmall0 hA (by linarith) (by linarith) hz0a
  have hposy0 : 0 < Work.OddVolterra.krad 0 σ (z 1) u :=
    krad_pos_of_pos hsupp0 hsmall0 hA (by linarith) (by linarith) hz1a
  have hCn : ∀ y : ℝ, y ≤ 4 * C12 → y ≤ 4 * C12 + 1 := fun y hy => by linarith
  have hfour : (4 : ℝ) * C12 ≤ 4 * C12 + 1 := by linarith
  have hnorm : ∀ y : ℝ, ‖y‖ = |y| := fun y => Real.norm_eq_abs y
  have hcz2 : |z 2| ≤ 2 := hzb 2
  have hcz3 : |z 3| ≤ 2 := hzb 3
  have hca : |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (-(z 0))) u -
      deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (-(z 0))) u| ≤ C12 * δ := by
    rw [abs_sub_comm]; exact h1c
  have hcb : |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (z 1)) u -
      deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (z 1)) u| ≤ C12 * δ := by
    rw [abs_sub_comm]; exact h1c'
  have hca2 : |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (-(z 0))) u -
      deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (-(z 0))) u| ≤ C12 * δ := by
    rw [abs_sub_comm]; exact h2c
  have hcb2 : |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (z 1)) u -
      deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (z 1)) u| ≤ C12 * δ := by
    rw [abs_sub_comm]; exact h2c'
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · -- the first component
    have hfe : (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) 0)
        = fun u' : ℝ => -(Work.OddVolterra.KernelExt.K1M n h u' σ (-(z 0)) * (z 2) +
            Work.OddVolterra.KernelExt.K1M n h u' σ (z 1) * (z 3)) := by
      funext u'; simp [Work.OddVolterra.KernelExt.KvecM]
    have hfe0 : (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) 0)
        = fun u' : ℝ => -(Work.OddVolterra.KernelExt.K1M n 0 u' σ (-(z 0)) * (z 2) +
            Work.OddVolterra.KernelExt.K1M n 0 u' σ (z 1) * (z 3)) := by
      funext u'; simp [Work.OddVolterra.KernelExt.KvecM]
    have hval : (Work.OddVolterra.KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) 0
        = -(Work.OddVolterra.KernelExt.K1M n h u σ (-(z 0)) * (z 2) +
            Work.OddVolterra.KernelExt.K1M n h u σ (z 1) * (z 3)) := by
      simp [Work.OddVolterra.KernelExt.KvecM]
    have hder : deriv (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) 0) u
        = -(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (-(z 0))) u * (z 2) +
            deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (z 1)) u * (z 3)) := by
      rw [hfe]
      exact ((((differentiableAt_K1M n hh hposx).hasDerivAt).mul_const (z 2)).add
        (((differentiableAt_K1M n hh hposy).hasDerivAt).mul_const (z 3))).neg.deriv
    have hder0 : deriv (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) 0) u
        = -(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (-(z 0))) u * (z 2) +
            deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (z 1)) u * (z 3)) := by
      rw [hfe0]
      exact ((((differentiableAt_K1M n contDiff_const hposx0).hasDerivAt).mul_const (z 2)).add
        (((differentiableAt_K1M n contDiff_const hposy0).hasDerivAt).mul_const (z 3))).neg.deriv
    refine ⟨?_, ?_, ?_⟩
    · rw [hval, Real.norm_eq_abs, abs_neg]
      calc |Work.OddVolterra.KernelExt.K1M n h u σ (-(z 0)) * (z 2) +
            Work.OddVolterra.KernelExt.K1M n h u σ (z 1) * (z 3)|
          ≤ |Work.OddVolterra.KernelExt.K1M n h u σ (-(z 0)) * (z 2)| +
            |Work.OddVolterra.KernelExt.K1M n h u σ (z 1) * (z 3)| := abs_add_le _ _
        _ ≤ C12 * 2 + C12 * 2 := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul h1v hcz2 (abs_nonneg _) hC12nn)
              (mul_le_mul h1v' hcz3 (abs_nonneg _) hC12nn)
        _ ≤ 4 * C12 + 1 := by linarith
    · rw [hder, Real.norm_eq_abs, abs_neg]
      calc |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (-(z 0))) u * (z 2) +
            deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (z 1)) u * (z 3)|
          ≤ |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (-(z 0))) u * (z 2)| +
            |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (z 1)) u * (z 3)| :=
            abs_add_le _ _
        _ ≤ C12 * 2 + C12 * 2 := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul h1d hcz2 (abs_nonneg _) hC12nn)
              (mul_le_mul h1d' hcz3 (abs_nonneg _) hC12nn)
        _ ≤ 4 * C12 + 1 := by linarith
    · rw [hder, hder0, Real.norm_eq_abs]
      have hkey : -(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (-(z 0))) u *
            (z 2) + deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (z 1)) u * (z 3)) -
          -(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (-(z 0))) u *
            (z 2) + deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (z 1)) u * (z 3))
          = (deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (-(z 0))) u -
              deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (-(z 0))) u) * (z 2) +
            (deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (z 1)) u -
              deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (z 1)) u) * (z 3) := by
        ring
      rw [hkey]
      calc |(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (-(z 0))) u -
              deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (-(z 0))) u) * (z 2) +
            (deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (z 1)) u -
              deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (z 1)) u) * (z 3)|
          ≤ |(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (-(z 0))) u -
                deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (-(z 0))) u) *
              (z 2)| +
            |(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n 0 u' σ (z 1)) u -
                deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K1M n h u' σ (z 1)) u) * (z 3)| :=
            abs_add_le _ _
        _ ≤ C12 * δ * 2 + C12 * δ * 2 := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul hca hcz2 (abs_nonneg _) (mul_nonneg hC12nn hδ0'))
              (mul_le_mul hcb hcz3 (abs_nonneg _) (mul_nonneg hC12nn hδ0'))
        _ ≤ (4 * C12 + 1) * δ := by
            have h : C12 * δ * 2 + C12 * δ * 2 = (4 * C12) * δ := by ring
            rw [h]
            exact mul_le_mul_of_nonneg_right (by linarith) hδ0'
  · -- the second component
    have hfe : (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) 1)
        = fun u' : ℝ => -(Work.OddVolterra.KernelExt.K2M n h u' σ (-(z 0)) * (z 2) +
            Work.OddVolterra.KernelExt.K2M n h u' σ (z 1) * (z 3)) := by
      funext u'; simp [Work.OddVolterra.KernelExt.KvecM]
    have hfe0 : (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) 1)
        = fun u' : ℝ => -(Work.OddVolterra.KernelExt.K2M n 0 u' σ (-(z 0)) * (z 2) +
            Work.OddVolterra.KernelExt.K2M n 0 u' σ (z 1) * (z 3)) := by
      funext u'; simp [Work.OddVolterra.KernelExt.KvecM]
    have hval : (Work.OddVolterra.KernelExt.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) 1
        = -(Work.OddVolterra.KernelExt.K2M n h u σ (-(z 0)) * (z 2) +
            Work.OddVolterra.KernelExt.K2M n h u σ (z 1) * (z 3)) := by
      simp [Work.OddVolterra.KernelExt.KvecM]
    have hder : deriv (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) 1) u
        = -(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (-(z 0))) u * (z 2) +
            deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (z 1)) u * (z 3)) := by
      rw [hfe]
      exact ((((differentiableAt_K2M n hh hposx).hasDerivAt).mul_const (z 2)).add
        (((differentiableAt_K2M n hh hposy).hasDerivAt).mul_const (z 3))).neg.deriv
    have hder0 : deriv (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) 1) u
        = -(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (-(z 0))) u * (z 2) +
            deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (z 1)) u * (z 3)) := by
      rw [hfe0]
      exact ((((differentiableAt_K2M n contDiff_const hposx0).hasDerivAt).mul_const (z 2)).add
        (((differentiableAt_K2M n contDiff_const hposy0).hasDerivAt).mul_const (z 3))).neg.deriv
    refine ⟨?_, ?_, ?_⟩
    · rw [hval, Real.norm_eq_abs, abs_neg]
      calc |Work.OddVolterra.KernelExt.K2M n h u σ (-(z 0)) * (z 2) +
            Work.OddVolterra.KernelExt.K2M n h u σ (z 1) * (z 3)|
          ≤ |Work.OddVolterra.KernelExt.K2M n h u σ (-(z 0)) * (z 2)| +
            |Work.OddVolterra.KernelExt.K2M n h u σ (z 1) * (z 3)| := abs_add_le _ _
        _ ≤ C12 * 2 + C12 * 2 := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul h2v hcz2 (abs_nonneg _) hC12nn)
              (mul_le_mul h2v' hcz3 (abs_nonneg _) hC12nn)
        _ ≤ 4 * C12 + 1 := by linarith
    · rw [hder, Real.norm_eq_abs, abs_neg]
      calc |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (-(z 0))) u * (z 2) +
            deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (z 1)) u * (z 3)|
          ≤ |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (-(z 0))) u * (z 2)| +
            |deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (z 1)) u * (z 3)| :=
            abs_add_le _ _
        _ ≤ C12 * 2 + C12 * 2 := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul h2d hcz2 (abs_nonneg _) hC12nn)
              (mul_le_mul h2d' hcz3 (abs_nonneg _) hC12nn)
        _ ≤ 4 * C12 + 1 := by linarith
    · rw [hder, hder0, Real.norm_eq_abs]
      have hkey : -(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (-(z 0))) u *
            (z 2) + deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (z 1)) u * (z 3)) -
          -(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (-(z 0))) u *
            (z 2) + deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (z 1)) u * (z 3))
          = (deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (-(z 0))) u -
              deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (-(z 0))) u) * (z 2) +
            (deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (z 1)) u -
              deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (z 1)) u) * (z 3) := by
        ring
      rw [hkey]
      calc |(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (-(z 0))) u -
              deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (-(z 0))) u) * (z 2) +
            (deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (z 1)) u -
              deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (z 1)) u) * (z 3)|
          ≤ |(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (-(z 0))) u -
                deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (-(z 0))) u) *
              (z 2)| +
            |(deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n 0 u' σ (z 1)) u -
                deriv (fun u' : ℝ => Work.OddVolterra.KernelExt.K2M n h u' σ (z 1)) u) * (z 3)| :=
            abs_add_le _ _
        _ ≤ C12 * δ * 2 + C12 * δ * 2 := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul hca2 hcz2 (abs_nonneg _) (mul_nonneg hC12nn hδ0'))
              (mul_le_mul hcb2 hcz3 (abs_nonneg _) (mul_nonneg hC12nn hδ0'))
        _ ≤ (4 * C12 + 1) * δ := by
            have h : C12 * δ * 2 + C12 * δ * 2 = (4 * C12) * δ := by ring
            rw [h]
            exact mul_le_mul_of_nonneg_right (by linarith) hδ0'

/-! ## Closeness of the manifest kernel `ΘM` on a general slope box -/

theorem thetaM_close_box (n : ℕ) (hn : 1 ≤ n) {a b ρ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    Work.OddVolterra.WinData.ThetaMCloseBox n a b ρ := by
  obtain ⟨Cv, hCv0, hKv⟩ := KvecM_est_ext n hn (a := a) ha
  have hCvnn : 0 ≤ Cv := hCv0.le
  set eps : ℝ := min (a / 4) (1 / 2) with heps
  have heps0 : 0 < eps := by rw [heps]; exact lt_min (by linarith) (by norm_num)
  have heps1 : eps ≤ a / 4 := by rw [heps]; exact min_le_left _ _
  have heps2 : eps ≤ 1 / 2 := by rw [heps]; exact min_le_right _ _
  refine ⟨Real.pi * Cv + 1, by positivity, ?_⟩
  intro h hh hsupp δ hδ0 hδ1 hjet s hs σ hσ z hz
  obtain ⟨hz0, hz1, hzb⟩ := state_ball_bounds ha hab hb hρ0 hρ1 hσ hz
  have hδ0' : 0 ≤ δ := hδ0.le
  have hσa : a ≤ σ := hσ.1
  have hσb : σ ≤ 1 := le_trans hσ.2 hb
  have hsa : a ≤ s := hs.1
  have hsb : s ≤ b := hs.2
  have hz0pos : (0 : ℝ) ≤ z 0 := by linarith [hz0]
  have hz1pos : (0 : ℝ) ≤ z 1 := by linarith [hz1]
  have hz0a : (1 / 5 : ℝ) ≤ |-(z 0)| := by rw [abs_neg, abs_of_nonneg hz0pos]; exact hz0
  have hz1a : (1 / 5 : ℝ) ≤ |z 1| := by rw [abs_of_nonneg hz1pos]; exact hz1
  have hz0b : |-(z 0)| ≤ 2 := by rw [abs_neg]; exact hzb 0
  have hz1b : |z 1| ≤ 2 := hzb 1
  have hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hjet k (by omega) s) hδ1
  have hsmall0 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ 1 / 100 := by
    intro k hk s
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split_ifs <;> norm_num
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) := by
    intro x hx; simp at hx
  have hjet0 : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ δ := by
    intro k hk s
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split_ifs <;> simpa using hδ0'
  -- the moving point stays in the box
  have hpt : ∀ x ∈ Set.Ioo (s - eps) (s + eps), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      x + τ * (σ - x) ∈ Set.Icc (3 * a / 4) (3 / 2) := by
    intro x hx τ hτ
    have hτ0 : (0 : ℝ) ≤ τ := hτ.1
    have hlo : 3 * a / 4 ≤ s - eps := by linarith [hsa, heps1]
    have hhi : s + eps ≤ 3 / 2 := by linarith [hsb, hb, heps2]
    have hxε1 : 3 * a / 4 ≤ x := by linarith [hx.1, hlo]
    have hxε2 : x ≤ 3 / 2 := by linarith [hx.2, hhi]
    rcases le_total σ x with h | h
    · have h1 : σ ≤ x + τ * (σ - x) := by
        have h2 : (0 : ℝ) ≤ (x - σ) * (1 - τ) :=
          mul_nonneg (by linarith) (by linarith [hτ.2])
        have he : x + τ * (σ - x) - σ = (x - σ) * (1 - τ) := by ring
        linarith
      have h3 : x + τ * (σ - x) ≤ x := by
        have h2 : τ * (σ - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ0 (by linarith)
        linarith
      exact ⟨by linarith [hσa, ha, h1], by linarith [hxε2, h3]⟩
    · have h1 : x ≤ x + τ * (σ - x) := by
        have h2 : 0 ≤ τ * (σ - x) := mul_nonneg hτ0 (by linarith)
        linarith
      have h3 : x + τ * (σ - x) ≤ σ := by
        have h2 : 0 ≤ (σ - x) * (1 - τ) :=
          mul_nonneg (by linarith) (by linarith [hτ.2])
        have he : σ - (x + τ * (σ - x)) = (σ - x) * (1 - τ) := by ring
        linarith
      exact ⟨by linarith [hxε1, h1], by linarith [hσb, h3]⟩
  -- the moving point with base point `s`, for `τ ∈ [0,1]`
  have hmovI : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      s + τ * (σ - s) ∈ Set.Icc (3 * a / 4) (3 / 2) := by
    intro τ hτ
    rcases le_total σ s with h | h
    · have h1 : σ ≤ s + τ * (σ - s) := by
        have h2 : (0 : ℝ) ≤ (s - σ) * (1 - τ) :=
          mul_nonneg (by linarith) (by linarith [hτ.2])
        have he : s + τ * (σ - s) - σ = (s - σ) * (1 - τ) := by ring
        linarith
      have h3 : s + τ * (σ - s) ≤ s := by
        have h2 : τ * (σ - s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ.1 (by linarith)
        linarith
      exact ⟨by linarith [hσa, ha, h1], by linarith [hsb, hb, h3]⟩
    · have h1 : s ≤ s + τ * (σ - s) := by
        have h2 : 0 ≤ τ * (σ - s) := mul_nonneg hτ.1 (by linarith)
        linarith
      have h3 : s + τ * (σ - s) ≤ σ := by
        have h2 : 0 ≤ (σ - s) * (1 - τ) :=
          mul_nonneg (by linarith) (by linarith [hτ.2])
        have he : σ - (s + τ * (σ - s)) = (σ - s) * (1 - τ) := by ring
        linarith
      exact ⟨by linarith [hsa, ha, h1], by linarith [hσb, h3]⟩
  have hmov : ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      s + τ * (σ - s) ∈ Set.Icc (3 * a / 4) (3 / 2) :=
    fun τ hτ => hmovI τ ⟨hτ.1, le_of_lt hτ.2⟩
  -- differentiability of the components of `KvecM` in the first slot
  have hdiffc : ∀ (h' : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) h' →
      Function.support h' ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h' s| ≤ 1 / 100) →
      ∀ x : ℝ, 3 * a / 4 ≤ x → x ≤ 3 / 2 → ∀ i : Fin 2,
      DifferentiableAt ℝ (fun u' : ℝ =>
        (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i) x := by
    intro h' hh' hsupp' hsmall' x hx1 hx2 i
    have hA : 0 < a / 2 := by linarith
    have hxu : a / 2 ≤ x := by linarith
    have hxσ : a / 2 ≤ σ := by linarith
    have hposx : 0 < Work.OddVolterra.krad h' σ (-(z 0)) x :=
      krad_pos_of_pos hsupp' hsmall' hA hxu hxσ hz0a
    have hposy : 0 < Work.OddVolterra.krad h' σ (z 1) x :=
      krad_pos_of_pos hsupp' hsmall' hA hxu hxσ hz1a
    have hj : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hj with rfl | rfl
    · have hfe : (fun u' : ℝ =>
            (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) 0)
          = fun u' : ℝ => -(Work.OddVolterra.KernelExt.K1M n h' u' σ (-(z 0)) * (z 2) +
              Work.OddVolterra.KernelExt.K1M n h' u' σ (z 1) * (z 3)) := by
        funext u'; simp [Work.OddVolterra.KernelExt.KvecM]
      rw [hfe]
      exact ((((differentiableAt_K1M n hh' hposx).mul_const (z 2)).add
        ((differentiableAt_K1M n hh' hposy).mul_const (z 3))).neg)
    · have hfe : (fun u' : ℝ =>
            (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) 1)
          = fun u' : ℝ => -(Work.OddVolterra.KernelExt.K2M n h' u' σ (-(z 0)) * (z 2) +
              Work.OddVolterra.KernelExt.K2M n h' u' σ (z 1) * (z 3)) := by
        funext u'; simp [Work.OddVolterra.KernelExt.KvecM]
      rw [hfe]
      exact ((((differentiableAt_K2M n hh' hposx).mul_const (z 2)).add
        ((differentiableAt_K2M n hh' hposy).mul_const (z 3))).neg)
  -- the first-slot derivative of each component of `G2M`, in integral form
  have hform : ∀ (h' : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) h' →
      Function.support h' ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h' s| ≤ 1 / 100) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h' s| ≤ δ) →
      ∀ i : Fin 2,
      deriv (fun u : ℝ => (Work.OddVolterra.KernelExt.G2M n h' u σ (z 0) (z 1) (z 2) (z 3)) i) s
        = ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
            ((1 - τ) * deriv (fun u' : ℝ =>
              (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
                (s + τ * (σ - s))) := by
    intro h' hh' hsupp' hsmall' hj' i
    have hmeas : Measurable (fun u' : ℝ =>
        (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i) :=
      (measurable_pi_apply i).comp
        (Work.OddExistence.Manifest.AW.measurable_KvecM n hh' σ z)
    have hbdx : ∀ x ∈ Set.Ioo (s - eps) (s + eps), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
        ‖(Work.OddVolterra.KernelExt.KvecM n h' (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)) i‖
          ≤ Cv := by
      intro x hx τ hτ
      have hmem := hpt x hx τ hτ
      have hb := (hKv h' δ hh' hδ0 hδ1 hj' hsupp' _ hmem.1 hmem.2 σ hσa hσb z hz0 hz1 hzb i).1
      rwa [Real.norm_eq_abs]
    have hdifx : ∀ x ∈ Set.Ioo (s - eps) (s + eps), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
        DifferentiableAt ℝ (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
            (x + τ * (σ - x)) := by
      intro x hx τ hτ
      exact hdiffc h' hh' hsupp' hsmall' _ (hpt x hx τ hτ).1 (hpt x hx τ hτ).2 i
    have hbndx : ∀ x ∈ Set.Ioo (s - eps) (s + eps), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ‖(1 - τ) * deriv (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
            (x + τ * (σ - x))‖ ≤ Cv := by
      intro x hx τ hτ
      rcases eq_or_lt_of_le hτ.2 with h1 | h1
      · rw [← h1, sub_self, zero_mul, norm_zero]
        exact hCvnn
      · have hmem := hpt x hx τ ⟨hτ.1, h1⟩
        have hd := (hKv h' δ hh' hδ0 hδ1 hj' hsupp' _ hmem.1 hmem.2 σ hσa hσb z hz0 hz1
          hzb i).2.1
        have hnn : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.1, h1]
        have hτnn : (0 : ℝ) ≤ τ := hτ.1
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
        calc (1 - τ) * |deriv (fun u' : ℝ =>
                (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
                  (x + τ * (σ - x))|
            ≤ 1 * |deriv (fun u' : ℝ =>
                (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
                  (x + τ * (σ - x))| :=
              mul_le_mul_of_nonneg_right (by linarith [hτnn]) (abs_nonneg _)
          _ = |deriv (fun u' : ℝ =>
                (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
                  (x + τ * (σ - x))| := one_mul _
          _ ≤ Cv := by rw [← Real.norm_eq_abs]; exact hd
    have hmain := Work.OddExistence.Manifest.hasDerivAt_abelAvg_scalar
      (K := fun u' : ℝ =>
        (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
      hmeas (δ := eps) (C := Cv) heps0 hbdx hdifx hbndx
    have hfun : (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n h' u σ (z 0) (z 1) (z 2) (z 3)) i)
        = fun u : ℝ => ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
            (Work.OddVolterra.KernelExt.KvecM n h' (u + τ * (σ - u)) σ
              (z 0) (z 1) (z 2) (z 3)) i := by
      funext u
      simp only [Work.OddVolterra.KernelExt.G2M]
      exact intervalIntegral.integral_congr (fun τ _ => by rw [div_eq_mul_inv, mul_comm])
    rw [hfun, hmain.deriv]
  -- the Abel weight
  have hw : ∀ τ : ℝ, 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ :=
    fun τ => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hmeasw : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
    ((Work.OddVolterra.measurable_sqrt_real.comp
      (measurable_id.mul (measurable_const.sub measurable_id)))).inv
  -- the weighted derivative bound along the moving point
  have hderbd : ∀ (h' : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) h' →
      Function.support h' ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h' s| ≤ δ) → ∀ i : Fin 2,
      ∀ τ ∈ Set.uIoc (0 : ℝ) 1,
      ‖(Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
            (s + τ * (σ - s)))‖ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * Cv := by
    intro h' hh' hsupp' hj' i τ hτ
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
    rcases eq_or_lt_of_le hτ.2 with h1 | h1
    · rw [h1]
      simp [Real.sqrt_zero]
    · have hτIco : τ ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt hτ.1, h1⟩
      have hmem := hmov τ hτIco
      have hd := (hKv h' δ hh' hδ0 hδ1 hj' hsupp' _ hmem.1 hmem.2 σ hσa hσb z hz0 hz1
        hzb i).2.1
      have hnn : (0 : ℝ) ≤ 1 - τ := by linarith [le_of_lt hτ.1, h1]
      have hτnn : (0 : ℝ) ≤ τ := le_of_lt hτ.1
      have hb : ‖(1 - τ) * deriv (fun u' : ℝ =>
            (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
              (s + τ * (σ - s))‖ ≤ Cv := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
        calc (1 - τ) * |deriv (fun u' : ℝ =>
                (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
                  (s + τ * (σ - s))|
            ≤ 1 * |deriv (fun u' : ℝ =>
                (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
                  (s + τ * (σ - s))| :=
              mul_le_mul_of_nonneg_right (by linarith [hτnn]) (abs_nonneg _)
          _ = |deriv (fun u' : ℝ =>
                (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
                  (s + τ * (σ - s))| := one_mul _
          _ ≤ Cv := by rw [← Real.norm_eq_abs]; exact hd
      calc ‖(Real.sqrt (τ * (1 - τ)))⁻¹ *
            ((1 - τ) * deriv (fun u' : ℝ =>
              (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
                (s + τ * (σ - s)))‖
          = (Real.sqrt (τ * (1 - τ)))⁻¹ * ‖(1 - τ) * deriv (fun u' : ℝ =>
              (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
                (s + τ * (σ - s))‖ := by
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw τ)]
        _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * Cv := mul_le_mul_of_nonneg_left hb (hw τ)
  -- integrability of the two Abel integrands
  have hint : ∀ (h' : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) h' →
      Function.support h' ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h' s| ≤ δ) → ∀ i : Fin 2,
      IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)
            (s + τ * (σ - s)))) volume 0 1 := by
    intro h' hh' hsupp' hj' i
    refine (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cv).mono_fun' ?_ ?_
    · refine (hmeasw.mul ?_).aestronglyMeasurable
      exact ((measurable_const.sub measurable_id).mul
        ((measurable_deriv (𝕜 := ℝ) (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n h' u' σ (z 0) (z 1) (z 2) (z 3)) i)).comp
            (by fun_prop)))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      exact hderbd h' hh' hsupp' hj' i τ hτ
  -- the comparison of the two derivatives of `G2M`
  have hclose : ∀ i : Fin 2,
      |deriv (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) i) s -
       deriv (fun u : ℝ =>
          (Work.OddVolterra.KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) i) s|
        ≤ Real.pi * (Cv * δ) := by
    intro i
    rw [hform h hh hsupp hsmall hjet i, hform 0 contDiff_const hsupp0 hsmall0 hjet0 i]
    set F1 : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) i)
            (s + τ * (σ - s))) with hF1
    set F0 : ℝ → ℝ := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (fun u' : ℝ =>
          (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) i)
            (s + τ * (σ - s))) with hF0
    have hIF1 : IntervalIntegrable F1 volume 0 1 := hint h hh hsupp hjet i
    have hIF0 : IntervalIntegrable F0 volume 0 1 := hint 0 contDiff_const hsupp0 hjet0 i
    rw [← intervalIntegral.integral_sub hIF1 hIF0]
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs (by norm_num)) ?_
    have hba : IntervalIntegrable
        (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * (Cv * δ)) volume 0 1 :=
      Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const (Cv * δ)
    have hmono : (∫ τ in (0 : ℝ)..1, |F1 τ - F0 τ|)
        ≤ ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * (Cv * δ) := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ hba ?_
      · exact (hIF1.sub hIF0).abs
      · intro τ hτ
        rcases eq_or_lt_of_le hτ.2 with h1 | h1
        · rw [h1, hF1, hF0]
          simp [Real.sqrt_zero]
        · have hτIco : τ ∈ Set.Ico (0 : ℝ) 1 := ⟨hτ.1, h1⟩
          have hmem := hmov τ hτIco
          have hnn : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.1, h1]
          have hτnn : (0 : ℝ) ≤ τ := hτ.1
          have hcl := (hKv h δ hh hδ0 hδ1 hjet hsupp _ hmem.1 hmem.2 σ hσa hσb z hz0 hz1
            hzb i).2.2
          have hcl' : |deriv (fun u' : ℝ =>
                (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) i)
                  (s + τ * (σ - s)) -
              deriv (fun u' : ℝ =>
                (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) i)
                  (s + τ * (σ - s))| ≤ Cv * δ := by
            rwa [Real.norm_eq_abs] at hcl
          rw [hF1, hF0]
          have he : (Real.sqrt (τ * (1 - τ)))⁻¹ *
                ((1 - τ) * deriv (fun u' : ℝ =>
                  (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) i)
                    (s + τ * (σ - s))) -
              (Real.sqrt (τ * (1 - τ)))⁻¹ *
                ((1 - τ) * deriv (fun u' : ℝ =>
                  (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) i)
                    (s + τ * (σ - s)))
              = (Real.sqrt (τ * (1 - τ)))⁻¹ *
                ((1 - τ) * (deriv (fun u' : ℝ =>
                    (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) i)
                      (s + τ * (σ - s)) -
                  deriv (fun u' : ℝ =>
                    (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) i)
                      (s + τ * (σ - s)))) := by ring
          rw [he, abs_mul, abs_of_nonneg (hw τ), abs_mul, abs_of_nonneg hnn]
          refine mul_le_mul_of_nonneg_left ?_ (hw τ)
          calc (1 - τ) * |deriv (fun u' : ℝ =>
                  (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) i)
                    (s + τ * (σ - s)) -
                deriv (fun u' : ℝ =>
                  (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) i)
                    (s + τ * (σ - s))|
              ≤ 1 * |deriv (fun u' : ℝ =>
                  (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) i)
                    (s + τ * (σ - s)) -
                deriv (fun u' : ℝ =>
                  (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) i)
                    (s + τ * (σ - s))| :=
                mul_le_mul_of_nonneg_right (by linarith [hτnn]) (abs_nonneg _)
            _ = |deriv (fun u' : ℝ =>
                  (Work.OddVolterra.KernelExt.KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) i)
                    (s + τ * (σ - s)) -
                deriv (fun u' : ℝ =>
                  (Work.OddVolterra.KernelExt.KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) i)
                    (s + τ * (σ - s))| := one_mul _
            _ ≤ Cv * δ := hcl'
    calc (∫ τ in (0 : ℝ)..1, |F1 τ - F0 τ|)
        ≤ ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * (Cv * δ) := hmono
      _ = (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹) * (Cv * δ) :=
          intervalIntegral.integral_mul_const (Cv * δ) _
      _ = Real.pi * (Cv * δ) := by
          rw [Work.OddVolterra.Existence.abel_weight_integral]
  -- assemble: `ThetaM` differs only in its last two rows
  refine (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.pi * Cv + 1) * δ)).mpr ?_
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp
  rcases hi with hi0 | hi1 | hi2 | hi3
  · rw [hi0]
    have hz0' : (Work.OddVolterra.KernelExt.ThetaM n h s σ z -
        Work.OddVolterra.KernelExt.ThetaM n 0 s σ z) 0 = 0 := by
      simp [Work.OddVolterra.KernelExt.ThetaM, Pi.sub_apply]
    rw [hz0', norm_zero]
    positivity
  · rw [hi1]
    have hz1' : (Work.OddVolterra.KernelExt.ThetaM n h s σ z -
        Work.OddVolterra.KernelExt.ThetaM n 0 s σ z) 1 = 0 := by
      simp [Work.OddVolterra.KernelExt.ThetaM, Pi.sub_apply]
    rw [hz1', norm_zero]
    positivity
  · rw [hi2]
    have hz2' : (Work.OddVolterra.KernelExt.ThetaM n h s σ z -
        Work.OddVolterra.KernelExt.ThetaM n 0 s σ z) 2 =
        -(deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s) +
          deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s := by
      simp [Work.OddVolterra.KernelExt.ThetaM, Pi.sub_apply]
    rw [hz2', Real.norm_eq_abs]
    have he : -(deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s) +
          deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s
        = -(deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s -
          deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s) := by ring
    rw [he, abs_neg]
    calc |deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s -
          deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s|
        ≤ Real.pi * (Cv * δ) := hclose 0
      _ ≤ (Real.pi * Cv + 1) * δ := by
          rw [show Real.pi * (Cv * δ) = (Real.pi * Cv) * δ by ring]
          exact mul_le_mul_of_nonneg_right (by linarith) hδ0'
  · rw [hi3]
    have hz3' : (Work.OddVolterra.KernelExt.ThetaM n h s σ z -
        Work.OddVolterra.KernelExt.ThetaM n 0 s σ z) 3 =
        -(deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s) +
          deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s := by
      simp [Work.OddVolterra.KernelExt.ThetaM, Pi.sub_apply]
    rw [hz3', Real.norm_eq_abs]
    have he : -(deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s) +
          deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s
        = -(deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s -
          deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s) := by ring
    rw [he, abs_neg]
    calc |deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s -
          deriv (fun u : ℝ =>
            (Work.OddVolterra.KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s|
        ≤ Real.pi * (Cv * δ) := hclose 1
      _ ≤ (Real.pi * Cv + 1) * δ := by
          rw [show Real.pi * (Cv * δ) = (Real.pi * Cv) * δ by ring]
          exact mul_le_mul_of_nonneg_right (by linarith) hδ0'

end

end Work.OddVolterra.WinData
