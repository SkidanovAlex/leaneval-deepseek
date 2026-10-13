import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.Trunc.chiDeriv2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false


/-- `tk` is locally `1` near the points of the open interval `(-1,1)`. -/
theorem tk_eventuallyEq_one {s : ℝ} (h : |s| < 1) : Trunc.tk =ᶠ[𝓝 s] (fun _ => (1 : ℝ)) := by
  have hopen : IsOpen {u : ℝ | |u| < 1} := isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.mem_nhds h] with u hu
  exact Trunc.tk_eq_one (le_of_lt hu)

/-- `tk` is locally `0` near the points with `u ^ 2 > 2` (in particular for `2 ≤ |s|`). -/
theorem tk_eventuallyEq_zero {s : ℝ} (h : (2 : ℝ) < s ^ 2) :
    Trunc.tk =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
  have hopen : IsOpen {u : ℝ | (2 : ℝ) < u ^ 2} :=
    isOpen_lt continuous_const (continuous_id.pow 2)
  filter_upwards [hopen.mem_nhds h] with u hu
  unfold Trunc.tk
  exact Real.smoothTransition.zero_of_nonpos (by linarith [hu])

theorem two_lt_sq_of_two_le_abs {s : ℝ} (h : 2 ≤ |s|) : (2 : ℝ) < s ^ 2 := by
  have h2 := sq_abs s
  nlinarith [abs_nonneg s, h]

theorem deriv_tk_eq_zero_of_abs_lt_one {s : ℝ} (h : |s| < 1) : deriv Trunc.tk s = 0 := by
  rw [(tk_eventuallyEq_one h).deriv_eq, deriv_const]

theorem deriv_tk_eq_zero_of_two_lt_sq {s : ℝ} (h : (2 : ℝ) < s ^ 2) : deriv Trunc.tk s = 0 := by
  rw [(tk_eventuallyEq_zero h).deriv_eq, deriv_const]

theorem deriv_deriv_tk_eq_zero_of_abs_lt_one {s : ℝ} (h : |s| < 1) :
    deriv (deriv Trunc.tk) s = 0 := by
  have hd : deriv Trunc.tk =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_lt continuous_abs continuous_const |>.mem_nhds h] with u hu
    exact deriv_tk_eq_zero_of_abs_lt_one hu
  rw [hd.deriv_eq, deriv_const]

theorem deriv_deriv_tk_eq_zero_of_two_lt_sq {s : ℝ} (h : (2 : ℝ) < s ^ 2) :
    deriv (deriv Trunc.tk) s = 0 := by
  have hd : deriv Trunc.tk =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_lt continuous_const (continuous_id.pow 2) |>.mem_nhds h] with u hu
    exact deriv_tk_eq_zero_of_two_lt_sq hu
  rw [hd.deriv_eq, deriv_const]

theorem deriv_phiTr_eq (N t : ℝ) :
    deriv (phiTr N) t = deriv Trunc.tk (t / (4096 * N)) / (4096 * N) :=
  Trunc.deriv_chi_eq (4096 * N) t

theorem deriv2_phiTr_eq (N t : ℝ) :
    deriv (deriv (phiTr N)) t = deriv (deriv Trunc.tk) (t / (4096 * N)) / (4096 * N) ^ 2 :=
  Trunc.deriv2_chi_eq (4096 * N) t

theorem abs_deriv_phiTr_le (N : ℝ) {Kd : ℝ} (hKd : ∀ t : ℝ, |deriv Trunc.tk t| ≤ Kd)
    {t : ℝ} (hN : 0 < N) : |deriv (phiTr N) t| ≤ Kd / (4096 * N) :=
  Trunc.abs_deriv_chi_le hKd (by linarith) t

theorem abs_deriv2_phiTr_le (N : ℝ) {M : ℝ} (hM : ∀ t : ℝ, |deriv (deriv Trunc.tk) t| ≤ M)
    {t : ℝ} (hN : 0 < N) : |deriv (deriv (phiTr N)) t| ≤ M / (4096 * N) ^ 2 := by
  rw [deriv2_phiTr_eq, abs_div, abs_of_nonneg (sq_nonneg (4096 * N))]
  exact div_le_div_of_nonneg_right (hM _) (sq_nonneg _)

theorem deriv2_phiTr_eq_zero_of_abs_lt {N : ℝ} (hN : 0 < N) {t : ℝ}
    (h : |t| < 4096 * N) : deriv (deriv (phiTr N)) t = 0 := by
  have hpos : 0 < 4096 * N := by linarith
  rw [deriv2_phiTr_eq]
  have hlt : |t / (4096 * N)| < 1 := by
    rw [abs_div, abs_of_pos hpos, div_lt_one hpos]
    exact h
  rw [deriv_deriv_tk_eq_zero_of_abs_lt_one hlt, zero_div]

theorem deriv2_phiTr_eq_zero_of_abs_ge {N : ℝ} (hN : 0 < N) {t : ℝ}
    (h : 8192 * N ≤ |t|) : deriv (deriv (phiTr N)) t = 0 := by
  have hpos : 0 < 4096 * N := by linarith
  rw [deriv2_phiTr_eq]
  have h2 : 2 ≤ |t / (4096 * N)| := by
    rw [abs_div, abs_of_pos hpos, le_div_iff₀ hpos]
    linarith
  rw [deriv_deriv_tk_eq_zero_of_two_lt_sq (two_lt_sq_of_two_le_abs h2), zero_div]

/-- The mass bound on the second derivative of `phiTr`: its support has length `16384*N` and
the function is bounded by `M/(4096*N)^2` there. -/
theorem integral_deriv2_phiTr_sq_le (N : ℝ) {M : ℝ}
    (hM : ∀ t : ℝ, |deriv (deriv Trunc.tk) t| ≤ M) (hN : 0 < N) :
    (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2) ≤
      16384 * N * (M / (4096 * N) ^ 2) ^ 2 := by
  set A : ℝ := 8192 * N with hAdef
  have hA0 : 0 < A := by rw [hAdef]; linarith
  have hsupp : ∀ t : ℝ, t ∉ Set.Icc (-A) A → (deriv (deriv (phiTr N)) t) ^ 2 = 0 := by
    intro t ht
    have hge : A ≤ |t| := by
      by_contra hcon
      push Not at hcon
      exact ht ⟨by linarith [neg_abs_le t, hcon], by linarith [le_abs_self t, hcon]⟩
    rw [deriv2_phiTr_eq_zero_of_abs_ge hN (by rw [hAdef] at hge; exact hge)]
    ring
  have hfin : volume (Set.Icc (-A) A) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hbnd : ∀ t ∈ Set.Icc (-A) A, ‖(deriv (deriv (phiTr N)) t) ^ 2‖
      ≤ (M / (4096 * N) ^ 2) ^ 2 := by
    intro t _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := abs_deriv2_phiTr_le N hM (t := t) hN
    have hle : deriv (deriv (phiTr N)) t ≤ M / (4096 * N) ^ 2 := le_trans (le_abs_self _) h
    have hle' : -(M / (4096 * N) ^ 2) ≤ deriv (deriv (phiTr N)) t :=
      le_trans (neg_le_neg h) (neg_abs_le _)
    nlinarith [sq_nonneg (deriv (deriv (phiTr N)) t)]
  have hmain : (∫ t in Set.Icc (-A) A, (deriv (deriv (phiTr N)) t) ^ 2)
      ≤ (M / (4096 * N) ^ 2) ^ 2 * volume.real (Set.Icc (-A) A) := by
    have h1 := MeasureTheory.norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hfin) hbnd
    rwa [Real.norm_of_nonneg
      (MeasureTheory.integral_nonneg (fun t => sq_nonneg _))] at h1
  calc (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
      = ∫ t in Set.Icc (-A) A, (deriv (deriv (phiTr N)) t) ^ 2 := by
        rw [MeasureTheory.setIntegral_univ]
        exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
    _ ≤ (M / (4096 * N) ^ 2) ^ 2 * volume.real (Set.Icc (-A) A) := hmain
    _ = 16384 * N * (M / (4096 * N) ^ 2) ^ 2 := by
        rw [Real.volume_real_Icc_of_le (by rw [hAdef]; linarith), hAdef]; ring

/-! ## The a.e. description of the strip `ℝ × Iθ` -/

theorem ae_mem_Ioo_of_Iθ :
    ∀ᵐ p ∂(volume.restrict ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)),
      p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  have hprod : ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume] ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.set_prod_ae_eq EventuallyEq.rfl hθ
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  rw [MeasureTheory.ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioo)]
  filter_upwards with p hp
  exact hp.2

theorem measurableSet_stripIθ : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ) :=
  MeasurableSet.univ.prod measurableSet_Icc

/-! ## The pointwise description of the shifted second slot of `uTr N b u` -/

end

end Work.FTS.EllSol.ShiftFT
