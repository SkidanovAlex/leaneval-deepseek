import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.SepDefs
import Submission.Work.FIArea4.Vflip.sep_defs
import Submission.Work.FIArea4.Vflip.deriv_chirp
import Submission.Work.FIArea4.Vflip.deriv_deriv_chirp
import Submission.Work.FIArea4.Vflip.Vfd.contDiff_fcut
import Submission.Commons.Analysis.ContDiff.exists_smooth_cutoff_infty

namespace Work.FIArea4.Vflip.Vfd

open MeasureTheory
open scoped Topology

noncomputable section

/-! ## 1. Vanishing of the cutoff derivatives outside their transition zones -/

lemma cutPhi_eq_one_of_half_lt_sq {x : ℝ} (h : (1 : ℝ) / 2 < x ^ 2) : cutPhi x = 1 := by
  unfold cutPhi
  exact Real.smoothTransition.one_of_one_le (by nlinarith)

lemma iteratedDeriv_cutPhi_eq_zero_of_one_lt_abs {x : ℝ} (h : 1 < |x|) {j : ℕ} (hj : j ≠ 0) :
    iteratedDeriv j cutPhi x = 0 := by
  have hx2 : (1 : ℝ) / 2 < x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hopen : IsOpen {y : ℝ | (1 : ℝ) / 2 < y ^ 2} := isOpen_lt continuous_const (by fun_prop)
  have hev : cutPhi =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hx2] with y hy
    exact cutPhi_eq_one_of_half_lt_sq hy
  rw [Filter.EventuallyEq.iteratedDeriv_eq j hev, iteratedDeriv_const]
  simp [hj]

lemma iteratedDeriv_cutPsi_eq_zero_of_two_lt_abs {x : ℝ} (h : 2 < |x|) {j : ℕ} (hj : j ≠ 0) :
    iteratedDeriv j cutPsi x = 0 := by
  have hx2 : (4 : ℝ) < x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hopen : IsOpen {y : ℝ | (4 : ℝ) < y ^ 2} := isOpen_lt continuous_const (by fun_prop)
  have hev : cutPsi =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hx2] with y hy
    exact cutPsi_eq_zero_of_sq_ge (le_of_lt hy)
  rw [Filter.EventuallyEq.iteratedDeriv_eq j hev, iteratedDeriv_const]
  simp [hj]

theorem exists_bound_iteratedDeriv_cutPhi (j : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ t, |iteratedDeriv j cutPhi t| ≤ A := by
  refine Commons.Analysis.ContDiff.exists_bound_iteratedDeriv_of_const_outside cutPhi
    contDiff_cutPhi (a := -1) (b := 1) (by norm_num) ?_ ?_ j
  · intro t ht
    have h1 : cutPhi (-1) = 1 := cutPhi_eq_one_of_one_le (by norm_num)
    rw [h1]
    apply cutPhi_eq_one_of_one_le
    rw [abs_of_nonpos (by linarith : t ≤ 0)]
    linarith
  · intro t ht
    have h1 : cutPhi 1 = 1 := cutPhi_eq_one_of_one_le (by norm_num)
    rw [h1]
    apply cutPhi_eq_one_of_one_le
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)]
    linarith

theorem exists_bound_iteratedDeriv_cutPsi (j : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ t, |iteratedDeriv j cutPsi t| ≤ A := by
  refine Commons.Analysis.ContDiff.exists_bound_iteratedDeriv_of_const_outside cutPsi
    contDiff_cutPsi (a := -2) (b := 2) (by norm_num) ?_ ?_ j
  · intro t ht
    have h1 : cutPsi (-2) = 0 := cutPsi_eq_zero_of_sq_ge (by norm_num)
    rw [h1]
    apply cutPsi_eq_zero_of_sq_ge
    nlinarith [ht]
  · intro t ht
    have h1 : cutPsi 2 = 0 := cutPsi_eq_zero_of_sq_ge (by norm_num)
    rw [h1]
    apply cutPsi_eq_zero_of_sq_ge
    nlinarith [ht]

/-! ## 2. The dyadic bump `gAbs t = dyadEta |t|` (as a complex function) -/

private def gAbs : ℝ → ℂ := fun t => (dyadEta |t| : ℂ)

private lemma dyadEta_le_one' (t : ℝ) : dyadEta t ≤ 1 := by
  unfold dyadEta dyadStep
  linarith [Real.smoothTransition.le_one (2 * t - 1), Real.smoothTransition.nonneg (t - 1)]

private lemma dyadEta_abs_le_one (t : ℝ) : |dyadEta t| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [dyadEta_nonneg t], dyadEta_le_one' t⟩

private lemma contDiff_gAbs : ContDiff ℝ (⊤ : ℕ∞) gAbs := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => dyadEta |t|) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases h : (1 : ℝ) / 2 ≤ t
    · refine ContDiffAt.congr_of_eventuallyEq (f := dyadEta) contDiff_dyadEta.contDiffAt ?_
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi (by linarith : (0 : ℝ) < t)] with x hx
      rw [abs_of_pos hx]
    · rw [not_le] at h
      by_cases h2 : t ≤ -(1 : ℝ) / 2
      · have hneg : t < 0 := by linarith
        refine ContDiffAt.congr_of_eventuallyEq (f := fun x : ℝ => dyadEta (-x)) ?_ ?_
        · exact contDiff_dyadEta.comp_contDiffAt t (by fun_prop)
        · filter_upwards [IsOpen.mem_nhds isOpen_Iio hneg] with x hx
          rw [abs_of_neg hx]
      · rw [not_le] at h2
        refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : ℝ => (0 : ℝ))
          (contDiffAt_const (c := (0 : ℝ))) ?_
        filter_upwards [IsOpen.mem_nhds isOpen_Ioo ⟨h2, h⟩] with x hx
        rw [Set.mem_Ioo] at hx
        have hx' : |x| < (1 : ℝ) / 2 := by
          rw [abs_lt]; exact ⟨by linarith [hx.1], hx.2⟩
        exact dyadEta_eq_zero_of_le (le_of_lt hx')
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ((dyadEta |t| : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h1
  exact h2

private lemma hasCompactSupport_gAbs : HasCompactSupport gAbs := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(2 : ℝ)) 2) isCompact_Icc ?_
  rw [Function.support_subset_iff]
  intro x hx
  rw [Set.mem_Icc, ← abs_le]
  by_contra hc
  rw [not_le] at hc
  exact hx (by simp [gAbs, dyadEta_eq_zero_of_ge (le_of_lt hc)])

private lemma norm_gAbs_le (t : ℝ) : ‖gAbs t‖ ≤ 1 := by
  rw [gAbs, Complex.norm_real, Real.norm_eq_abs]
  exact dyadEta_abs_le_one |t|

theorem exists_bound_iteratedDeriv_gAbs (j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t, ‖iteratedDeriv j gAbs t‖ ≤ D := by
  have hcont : Continuous (iteratedDeriv j gAbs) :=
    contDiff_gAbs.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤))
  have hcs : HasCompactSupport (iteratedDeriv j gAbs) := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact (hasCompactSupport_gAbs.iteratedFDeriv (𝕜 := ℝ) j).comp_left (map_zero _)
  obtain ⟨D, hD⟩ := hcs.exists_bound_of_continuous hcont
  exact ⟨max D 0, le_max_right _ _, fun t => le_trans (hD t) (le_max_left _ _)⟩

/-! ## 3. Smoothness of the chirp at non-zero points -/

private lemma contDiffAt_chirp (α : ℝ) {u : ℝ} (hu : u ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (chirp α) u := by
  have hlog : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.log |x|) u :=
    Work.FIArea4.Vflip.contDiffAt_log_abs hu
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => ((α * Real.log |x| : ℝ) : ℂ) * Complex.I) u := by
    have ha : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => α * Real.log |x|) u :=
      contDiffAt_const.mul hlog
    exact (Complex.ofRealCLM.contDiff.comp_contDiffAt u ha).mul contDiffAt_const
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ => Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I)) u := h1.cexp
  exact h2

/-! ## 4. Scaling lemmas for iterated derivatives -/

private lemma iteratedDeriv_ofReal_cplx (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    iteratedDeriv n (fun y => (f y : ℂ)) = fun y => ((iteratedDeriv n f y : ℝ) : ℂ) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hdiff : Differentiable ℝ (iteratedDeriv n f) :=
      hf.differentiable_iteratedDeriv n (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
    have hd : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x := by
      rw [iteratedDeriv_succ]
      exact (hdiff x).hasDerivAt
    simpa using (HasDerivAt.ofReal_comp hd).deriv

private lemma iteratedDeriv_comp_const_mul_cplx (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x => f (c * x)) = fun x => (c : ℂ) ^ n * iteratedDeriv n f (c * x) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hdiff : Differentiable ℝ (iteratedDeriv n f) :=
      hf.differentiable_iteratedDeriv n (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))
    rw [deriv_const_mul]
    · rw [deriv_comp_mul_left]
      rw [iteratedDeriv_succ]
      simp only [Complex.real_smul]
      ring
    · exact hdiff.differentiableAt.comp x (by fun_prop)

private lemma norm_iteratedDeriv_gAbs_div_le (R : ℝ) (hR : 0 < R) (n : ℕ) {D : ℝ}
    (hD : ∀ t, ‖iteratedDeriv n gAbs t‖ ≤ D) (u : ℝ) :
    ‖iteratedDeriv n (fun x : ℝ => gAbs (x / R)) u‖ ≤ D / R ^ n := by
  have hfun : (fun x : ℝ => gAbs (x / R)) = fun x => gAbs ((R⁻¹) * x) := by
    funext x; rw [inv_mul_eq_div]
  rw [hfun, congrFun (iteratedDeriv_comp_const_mul_cplx gAbs contDiff_gAbs (R⁻¹) n) u]
  rw [norm_mul, norm_pow]
  have hinv : ‖((R⁻¹ : ℝ) : ℂ)‖ = R⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  rw [hinv]
  calc (R⁻¹) ^ n * ‖iteratedDeriv n gAbs (R⁻¹ * u)‖ ≤ (R⁻¹) ^ n * D :=
        mul_le_mul_of_nonneg_left (hD _) (by positivity)
    _ = D / R ^ n := by rw [inv_pow]; ring

/-! ## 5. Norm bounds for the individual factors of `fcut` -/

private lemma norm_factorA_le (u : ℝ) : ‖(cutPhi u : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [cutPhi_nonneg u], cutPhi_le_one u⟩

private lemma norm_factorB_le (ε u : ℝ) : ‖(cutPsi (ε * u) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [cutPsi_nonneg (ε * u)], cutPsi_le_one (ε * u)⟩

private lemma norm_factorA1_le {a1 R u : ℝ} (ha1 : ∀ t, |iteratedDeriv 1 cutPhi t| ≤ a1)
    (ha1nn : 0 ≤ a1) (hR : 0 < R) (hu : R / 2 ≤ |u|) :
    ‖iteratedDeriv 1 (fun x : ℝ => (cutPhi x : ℂ)) u‖ ≤ 2 * a1 / R := by
  have hA : iteratedDeriv 1 (fun x : ℝ => (cutPhi x : ℂ)) u
      = ((iteratedDeriv 1 cutPhi u : ℝ) : ℂ) :=
    congrFun (iteratedDeriv_ofReal_cplx cutPhi contDiff_cutPhi 1) u
  rw [hA, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt R 2 with hR2 | hR2
  · have hle : a1 ≤ 2 * a1 / R := by rw [le_div_iff₀ hR]; nlinarith [ha1nn, hR2, hR]
    linarith [ha1 u]
  · have hu1 : 1 < |u| := by linarith
    rw [iteratedDeriv_cutPhi_eq_zero_of_one_lt_abs hu1 (by norm_num : (1 : ℕ) ≠ 0), abs_zero]
    positivity

private lemma norm_factorA2_le {a2 R u : ℝ} (ha2 : ∀ t, |iteratedDeriv 2 cutPhi t| ≤ a2)
    (ha2nn : 0 ≤ a2) (hR : 0 < R) (hu : R / 2 ≤ |u|) :
    ‖iteratedDeriv 2 (fun x : ℝ => (cutPhi x : ℂ)) u‖ ≤ 4 * a2 / R ^ 2 := by
  have hA : iteratedDeriv 2 (fun x : ℝ => (cutPhi x : ℂ)) u
      = ((iteratedDeriv 2 cutPhi u : ℝ) : ℂ) :=
    congrFun (iteratedDeriv_ofReal_cplx cutPhi contDiff_cutPhi 2) u
  rw [hA, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt R 2 with hR2 | hR2
  · have hRR : R ^ 2 ≤ 4 := by nlinarith [hR, hR2]
    have hle : a2 ≤ 4 * a2 / R ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [ha2nn, hRR]
    linarith [ha2 u]
  · have hu1 : 1 < |u| := by linarith
    rw [iteratedDeriv_cutPhi_eq_zero_of_one_lt_abs hu1 (by norm_num : (2 : ℕ) ≠ 0), abs_zero]
    positivity

private lemma norm_factorB1_le {b1 : ℝ} (hb1 : ∀ s, |iteratedDeriv 1 cutPsi s| ≤ b1)
    (hb1nn : 0 ≤ b1) {ε R u : ℝ} (hε : 0 < ε) (hR : 0 < R) (hu : R / 2 ≤ |u|) :
    ‖iteratedDeriv 1 (fun x : ℝ => (cutPsi (ε * x) : ℂ)) u‖ ≤ 4 * b1 / R := by
  have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
  have hcomp : iteratedDeriv 1 (fun x : ℝ => (cutPsi (ε * x) : ℂ)) u
      = (ε : ℂ) * ((iteratedDeriv 1 cutPsi (ε * u) : ℝ) : ℂ) := by
    have h1 := congrFun (iteratedDeriv_comp_const_mul_cplx (fun s : ℝ => (cutPsi s : ℂ))
        (Complex.ofRealCLM.contDiff.comp contDiff_cutPsi) ε 1) u
    have h2 := congrFun (iteratedDeriv_ofReal_cplx cutPsi contDiff_cutPsi 1) (ε * u)
    rw [h1, h2, pow_one]
  rw [hcomp, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hε]
  have hstep : ε * |iteratedDeriv 1 cutPsi (ε * u)| ≤ (2 / |u|) * b1 := by
    by_cases hz : iteratedDeriv 1 cutPsi (ε * u) = 0
    · rw [hz, abs_zero, mul_zero]; positivity
    · have hle : ε ≤ 2 / |u| := by
        have h2 : |ε * u| ≤ 2 := by
          by_contra hc
          rw [not_le] at hc
          exact hz (iteratedDeriv_cutPsi_eq_zero_of_two_lt_abs hc (by norm_num : (1 : ℕ) ≠ 0))
        rw [abs_mul, abs_of_pos hε] at h2
        rw [le_div_iff₀ (abs_pos.mpr hu0)]; linarith
      calc ε * |iteratedDeriv 1 cutPsi (ε * u)| ≤ ε * b1 :=
            mul_le_mul_of_nonneg_left (hb1 _) hε.le
        _ ≤ (2 / |u|) * b1 := mul_le_mul_of_nonneg_right hle hb1nn
  calc ε * |iteratedDeriv 1 cutPsi (ε * u)| ≤ (2 / |u|) * b1 := hstep
    _ = 2 * b1 / |u| := by rw [div_mul_eq_mul_div]
    _ ≤ 4 * b1 / R := by
        rw [div_le_div_iff₀ (abs_pos.mpr hu0) hR]
        nlinarith [hb1nn, hR, hu]

private lemma norm_factorB2_le {b2 : ℝ} (hb2 : ∀ s, |iteratedDeriv 2 cutPsi s| ≤ b2)
    (hb2nn : 0 ≤ b2) {ε R u : ℝ} (hε : 0 < ε) (hR : 0 < R) (hu : R / 2 ≤ |u|) :
    ‖iteratedDeriv 2 (fun x : ℝ => (cutPsi (ε * x) : ℂ)) u‖ ≤ 16 * b2 / R ^ 2 := by
  have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
  have hcomp : iteratedDeriv 2 (fun x : ℝ => (cutPsi (ε * x) : ℂ)) u
      = (ε : ℂ) ^ 2 * ((iteratedDeriv 2 cutPsi (ε * u) : ℝ) : ℂ) := by
    have h1 := congrFun (iteratedDeriv_comp_const_mul_cplx (fun s : ℝ => (cutPsi s : ℂ))
        (Complex.ofRealCLM.contDiff.comp contDiff_cutPsi) ε 2) u
    have h2 := congrFun (iteratedDeriv_ofReal_cplx cutPsi contDiff_cutPsi 2) (ε * u)
    rw [h1, h2]
  rw [hcomp, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hε]
  have hstep : ε ^ 2 * |iteratedDeriv 2 cutPsi (ε * u)| ≤ (2 / |u|) ^ 2 * b2 := by
    by_cases hz : iteratedDeriv 2 cutPsi (ε * u) = 0
    · rw [hz, abs_zero, mul_zero]; positivity
    · have hle : ε ≤ 2 / |u| := by
        have h2 : |ε * u| ≤ 2 := by
          by_contra hc
          rw [not_le] at hc
          exact hz (iteratedDeriv_cutPsi_eq_zero_of_two_lt_abs hc (by norm_num : (2 : ℕ) ≠ 0))
        rw [abs_mul, abs_of_pos hε] at h2
        rw [le_div_iff₀ (abs_pos.mpr hu0)]; linarith
      have hle2 : ε ^ 2 ≤ (2 / |u|) ^ 2 := by
        calc ε ^ 2 = ε * ε := by ring
          _ ≤ (2 / |u|) * (2 / |u|) := mul_le_mul hle hle hε.le (by positivity)
          _ = (2 / |u|) ^ 2 := by ring
      calc ε ^ 2 * |iteratedDeriv 2 cutPsi (ε * u)| ≤ ε ^ 2 * b2 :=
            mul_le_mul_of_nonneg_left (hb2 _) (by positivity)
        _ ≤ (2 / |u|) ^ 2 * b2 := mul_le_mul_of_nonneg_right hle2 hb2nn
  calc ε ^ 2 * |iteratedDeriv 2 cutPsi (ε * u)| ≤ (2 / |u|) ^ 2 * b2 := hstep
    _ = 4 * b2 / |u| ^ 2 := by rw [div_pow]; ring
    _ ≤ 16 * b2 / R ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hR2u : R ≤ 2 * |u| := by linarith
        have hsq : R * R ≤ (2 * |u|) * (2 * |u|) := mul_self_le_mul_self hR.le hR2u
        nlinarith [hb2nn, hsq]

private lemma norm_factorC_le (α u : ℝ) : ‖chirp α u‖ = 1 := norm_chirp α u

private lemma norm_factorC1_le {α R u : ℝ} (hR : 0 < R) (hu : R / 2 ≤ |u|) :
    ‖iteratedDeriv 1 (chirp α) u‖ ≤ 2 * |α| / R := by
  have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
  have hC : iteratedDeriv 1 (chirp α) u
      = ((α : ℂ) * (u : ℂ)⁻¹) * Complex.I * chirp α u := by
    rw [iteratedDeriv_one]
    exact Work.FIArea4.Vflip.deriv_chirp α hu0
  have hnorm : ‖((α : ℂ) * (u : ℂ)⁻¹) * Complex.I * chirp α u‖ = |α| / |u| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, norm_chirp, mul_one]
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_inv, div_eq_mul_inv]
  rw [hC, hnorm]
  calc |α| / |u| ≤ |α| / (R / 2) := by
        apply div_le_div_of_nonneg_left (abs_nonneg α) (by positivity) hu
    _ = 2 * |α| / R := by ring

private lemma norm_factorC2_le {α R u : ℝ} (hR : 0 < R) (hu : R / 2 ≤ |u|) :
    ‖iteratedDeriv 2 (chirp α) u‖ ≤ 4 * (1 + |α|) ^ 2 / R ^ 2 := by
  have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
  have hC : iteratedDeriv 2 (chirp α) u
      = -(((α : ℂ) ^ 2 + Complex.I * (α : ℂ)) / (u : ℂ) ^ 2) * chirp α u := by
    rw [Work.FIArea4.Vflip.iteratedDeriv_two_eq]
    exact Work.FIArea4.Vflip.deriv_deriv_chirp α hu0
  have hnorm : ‖-(((α : ℂ) ^ 2 + Complex.I * (α : ℂ)) / (u : ℂ) ^ 2) * chirp α u‖
      = ‖(α : ℂ) ^ 2 + Complex.I * (α : ℂ)‖ / |u| ^ 2 := by
    rw [norm_mul, norm_neg, norm_div, norm_pow, norm_chirp, mul_one]
    simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [hC, hnorm]
  have hnum : ‖(α : ℂ) ^ 2 + Complex.I * (α : ℂ)‖ ≤ (1 + |α|) ^ 2 := by
    calc ‖(α : ℂ) ^ 2 + Complex.I * (α : ℂ)‖ ≤ ‖(α : ℂ) ^ 2‖ + ‖Complex.I * (α : ℂ)‖ :=
          norm_add_le _ _
      _ = |α| ^ 2 + |α| := by
          rw [norm_pow, norm_mul, Complex.norm_I, one_mul]
          simp only [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (1 + |α|) ^ 2 := by nlinarith [abs_nonneg α]
  calc ‖(α : ℂ) ^ 2 + Complex.I * (α : ℂ)‖ / |u| ^ 2 ≤ (1 + |α|) ^ 2 / |u| ^ 2 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (1 + |α|) ^ 2 / (R / 2) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [hu, hR, abs_nonneg u]
    _ = 4 * (1 + |α|) ^ 2 / R ^ 2 := by ring

private lemma norm_fcut_le_one (ε α u : ℝ) : ‖fcut ε α u‖ ≤ 1 := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [fcut]
    have hz : cutPhi 0 = 0 := cutPhi_eq_zero_of_abs_le (by norm_num)
    rw [hz]; simp
  · rw [fcut, cpow_eq_chirp hu, norm_mul, norm_mul, norm_chirp, mul_one, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
    have ha : |cutPhi u| ≤ 1 := abs_le.mpr ⟨by linarith [cutPhi_nonneg u], cutPhi_le_one u⟩
    have hb : |cutPsi (ε * u)| ≤ 1 :=
      abs_le.mpr ⟨by linarith [cutPsi_nonneg (ε * u)], cutPsi_le_one (ε * u)⟩
    nlinarith [abs_nonneg (cutPhi u), abs_nonneg (cutPsi (ε * u))]

/-! ## 6. Leibniz inequalities via the exact product formulas -/

private lemma iteratedDeriv_one_mul_cplx (f g : ℝ → ℂ) {x : ℝ}
    (hf : ContDiffAt ℝ (1 : WithTop ℕ∞) f x) (hg : ContDiffAt ℝ (1 : WithTop ℕ∞) g x) :
    iteratedDeriv 1 (f * g) x = f x * iteratedDeriv 1 g x + iteratedDeriv 1 f x * g x := by
  rw [iteratedDeriv_mul (n := 1) hf hg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_self]
  norm_num [iteratedDeriv_zero]

private lemma iteratedDeriv_two_mul_cplx (f g : ℝ → ℂ) {x : ℝ}
    (hf : ContDiffAt ℝ (2 : WithTop ℕ∞) f x) (hg : ContDiffAt ℝ (2 : WithTop ℕ∞) g x) :
    iteratedDeriv 2 (f * g) x = iteratedDeriv 2 f x * g x + 2 * iteratedDeriv 1 f x * iteratedDeriv 1 g x + f x * iteratedDeriv 2 g x := by
  rw [iteratedDeriv_mul (n := 2) hf hg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_self]
  norm_num [iteratedDeriv_zero]
  ring

private lemma norm_iteratedDeriv_one_mul_le (f g : ℝ → ℂ) {x : ℝ}
    (hf : ContDiffAt ℝ (1 : WithTop ℕ∞) f x) (hg : ContDiffAt ℝ (1 : WithTop ℕ∞) g x) :
    ‖iteratedDeriv 1 (f * g) x‖
      ≤ ‖f x‖ * ‖iteratedDeriv 1 g x‖ + ‖iteratedDeriv 1 f x‖ * ‖g x‖ := by
  calc ‖iteratedDeriv 1 (f * g) x‖ ≤ ‖f x * iteratedDeriv 1 g x‖ + ‖iteratedDeriv 1 f x * g x‖ := by
        rw [iteratedDeriv_one_mul_cplx f g hf hg]; exact norm_add_le _ _
    _ = ‖f x‖ * ‖iteratedDeriv 1 g x‖ + ‖iteratedDeriv 1 f x‖ * ‖g x‖ := by
        rw [norm_mul, norm_mul]

private lemma norm_iteratedDeriv_two_mul_le (f g : ℝ → ℂ) {x : ℝ}
    (hf : ContDiffAt ℝ (2 : WithTop ℕ∞) f x) (hg : ContDiffAt ℝ (2 : WithTop ℕ∞) g x) :
    ‖iteratedDeriv 2 (f * g) x‖
      ≤ ‖iteratedDeriv 2 f x‖ * ‖g x‖ + 2 * ‖iteratedDeriv 1 f x‖ * ‖iteratedDeriv 1 g x‖
        + ‖f x‖ * ‖iteratedDeriv 2 g x‖ := by
  rw [iteratedDeriv_two_mul_cplx f g hf hg]
  calc ‖iteratedDeriv 2 f x * g x + 2 * iteratedDeriv 1 f x * iteratedDeriv 1 g x
          + f x * iteratedDeriv 2 g x‖
      ≤ ‖iteratedDeriv 2 f x * g x + 2 * iteratedDeriv 1 f x * iteratedDeriv 1 g x‖
          + ‖f x * iteratedDeriv 2 g x‖ := norm_add_le _ _
    _ ≤ (‖iteratedDeriv 2 f x * g x‖ + ‖2 * iteratedDeriv 1 f x * iteratedDeriv 1 g x‖)
          + ‖f x * iteratedDeriv 2 g x‖ := by
        have h := norm_add_le (iteratedDeriv 2 f x * g x)
          (2 * iteratedDeriv 1 f x * iteratedDeriv 1 g x)
        linarith
    _ = ‖iteratedDeriv 2 f x‖ * ‖g x‖ + 2 * ‖iteratedDeriv 1 f x‖ * ‖iteratedDeriv 1 g x‖
          + ‖f x‖ * ‖iteratedDeriv 2 g x‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        norm_num



private lemma coe_order_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

/-! ## 7. First-derivative bound for `fcut` on the annulus `|u| ≥ R/2` -/

theorem fcut_deriv1_bound :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ (ε α R : ℝ), 0 < ε → 0 < R → ∀ u : ℝ,
      R / 2 ≤ |u| → ‖iteratedDeriv 1 (fcut ε α) u‖ ≤ C1 * (1 + |α|) / R := by
  obtain ⟨a1, ha1pos, ha1⟩ := exists_bound_iteratedDeriv_cutPhi 1
  obtain ⟨b1, hb1pos, hb1⟩ := exists_bound_iteratedDeriv_cutPsi 1
  refine ⟨2 * a1 + 4 * b1 + 2, by positivity, ?_⟩
  intro ε α R hε hR u hu
  have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
  have hnhds : {x : ℝ | x ≠ 0} ∈ 𝓝 u := by
    rw [show {x : ℝ | x ≠ 0} = {0}ᶜ by ext x; simp]
    exact isOpen_compl_singleton.mem_nhds (by simpa using hu0)
  have hfc : fcut ε α =ᶠ[𝓝 u]
      (fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ) * chirp α x) := by
    filter_upwards [hnhds] with x hx
    simp only [fcut]
    rw [cpow_eq_chirp hx]
  rw [Filter.EventuallyEq.iteratedDeriv_eq 1 hfc]
  have hA2 : ContDiffAt ℝ (1 : WithTop ℕ∞) (fun x : ℝ => (cutPhi x : ℂ)) u :=
    ((Complex.ofRealCLM.contDiff.comp contDiff_cutPhi).contDiffAt).of_le (coe_order_le_top _)
  have hB2 : ContDiffAt ℝ (1 : WithTop ℕ∞) (fun x : ℝ => (cutPsi (ε * x) : ℂ)) u := by
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => cutPsi (ε * x)) :=
      contDiff_cutPsi.comp (contDiff_const.mul contDiff_id)
    exact ((Complex.ofRealCLM.contDiff.comp h2).contDiffAt).of_le (coe_order_le_top _)
  have hC2 : ContDiffAt ℝ (1 : WithTop ℕ∞) (chirp α) u :=
    (contDiffAt_chirp α hu0).of_le (coe_order_le_top _)
  have hF0 : ‖(fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) u‖ ≤ 1 := by
    simp only
    rw [norm_mul]
    nlinarith [norm_factorA_le u, norm_factorB_le ε u,
      norm_nonneg (cutPhi u : ℂ), norm_nonneg (cutPsi (ε * u) : ℂ)]
  have hF1 : ‖iteratedDeriv 1 (fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) u‖
      ≤ 2 * a1 / R + 4 * b1 / R := by
    have h := norm_iteratedDeriv_one_mul_le (fun x : ℝ => (cutPhi x : ℂ))
      (fun x : ℝ => (cutPsi (ε * x) : ℂ)) hA2 hB2
    refine le_trans h ?_
    have h1 := norm_factorA1_le ha1 ha1pos.le hR hu
    have h2 := norm_factorB1_le hb1 hb1pos.le hε hR hu
    have ha := norm_factorA_le u
    have hb := norm_factorB_le ε u
    have e1 : ‖(cutPhi u : ℂ)‖ * ‖iteratedDeriv 1 (fun x : ℝ => (cutPsi (ε * x) : ℂ)) u‖
        ≤ 1 * (4 * b1 / R) := mul_le_mul ha h2 (norm_nonneg _) (by norm_num)
    have e2 : ‖iteratedDeriv 1 (fun x : ℝ => (cutPhi x : ℂ)) u‖ * ‖(cutPsi (ε * u) : ℂ)‖
        ≤ (2 * a1 / R) * 1 := mul_le_mul h1 hb (norm_nonneg _) (by positivity)
    nlinarith [e1, e2]
  have hmain := norm_iteratedDeriv_one_mul_le
    (fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) (chirp α) (hA2.mul hB2) hC2
  refine le_trans hmain ?_
  have hCc1 := norm_factorC1_le (α := α) hR hu
  have hCc0 := norm_factorC_le α u
  have e1 : ‖(fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) u‖
      * ‖iteratedDeriv 1 (chirp α) u‖ ≤ 1 * (2 * |α| / R) :=
    mul_le_mul hF0 hCc1 (norm_nonneg _) (by norm_num)
  have e2 : ‖iteratedDeriv 1 (fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) u‖
      * ‖chirp α u‖ ≤ (2 * a1 / R + 4 * b1 / R) * 1 :=
    mul_le_mul hF1 (le_of_eq hCc0) (norm_nonneg _) (by positivity)
  have hfin : 1 * (2 * |α| / R) + (2 * a1 / R + 4 * b1 / R) * 1
      ≤ (2 * a1 + 4 * b1 + 2) * (1 + |α|) / R := by
    have e : 1 * (2 * |α| / R) + (2 * a1 / R + 4 * b1 / R) * 1
        = (2 * |α| + 2 * a1 + 4 * b1) / R := by ring
    rw [e]
    apply div_le_div_of_nonneg_right _ hR.le
    nlinarith [abs_nonneg α, ha1pos.le, hb1pos.le]
  linarith [e1, e2, hfin]

/-! ## 8. Second-derivative bound for `fcut` on the annulus `|u| ≥ R/2` -/

theorem fcut_deriv2_bound :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ (ε α R : ℝ), 0 < ε → 0 < R → ∀ u : ℝ,
      R / 2 ≤ |u| → ‖iteratedDeriv 2 (fcut ε α) u‖ ≤ C2 * (1 + |α|) ^ 2 / R ^ 2 := by
  obtain ⟨a1, ha1pos, ha1⟩ := exists_bound_iteratedDeriv_cutPhi 1
  obtain ⟨a2, ha2pos, ha2⟩ := exists_bound_iteratedDeriv_cutPhi 2
  obtain ⟨b1, hb1pos, hb1⟩ := exists_bound_iteratedDeriv_cutPsi 1
  obtain ⟨b2, hb2pos, hb2⟩ := exists_bound_iteratedDeriv_cutPsi 2
  refine ⟨4 * a2 + 16 * a1 * b1 + 16 * b2 + 8 * a1 + 16 * b1 + 4, by positivity, ?_⟩
  intro ε α R hε hR u hu
  have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
  have hnhds : {x : ℝ | x ≠ 0} ∈ 𝓝 u := by
    rw [show {x : ℝ | x ≠ 0} = {0}ᶜ by ext x; simp]
    exact isOpen_compl_singleton.mem_nhds (by simpa using hu0)
  have hfc : fcut ε α =ᶠ[𝓝 u]
      (fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ) * chirp α x) := by
    filter_upwards [hnhds] with x hx
    simp only [fcut]
    rw [cpow_eq_chirp hx]
  rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hfc]
  have hA2 : ContDiffAt ℝ (2 : WithTop ℕ∞) (fun x : ℝ => (cutPhi x : ℂ)) u :=
    ((Complex.ofRealCLM.contDiff.comp contDiff_cutPhi).contDiffAt).of_le (coe_order_le_top _)
  have hB2 : ContDiffAt ℝ (2 : WithTop ℕ∞) (fun x : ℝ => (cutPsi (ε * x) : ℂ)) u := by
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => cutPsi (ε * x)) :=
      contDiff_cutPsi.comp (contDiff_const.mul contDiff_id)
    exact ((Complex.ofRealCLM.contDiff.comp h2).contDiffAt).of_le (coe_order_le_top _)
  have hC2 : ContDiffAt ℝ (2 : WithTop ℕ∞) (chirp α) u :=
    (contDiffAt_chirp α hu0).of_le (coe_order_le_top _)
  have hF0 : ‖(fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) u‖ ≤ 1 := by
    simp only
    rw [norm_mul]
    nlinarith [norm_factorA_le u, norm_factorB_le ε u,
      norm_nonneg (cutPhi u : ℂ), norm_nonneg (cutPsi (ε * u) : ℂ)]
  have hF1 : ‖iteratedDeriv 1 (fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) u‖
      ≤ 2 * a1 / R + 4 * b1 / R := by
    have h := norm_iteratedDeriv_one_mul_le (fun x : ℝ => (cutPhi x : ℂ))
      (fun x : ℝ => (cutPsi (ε * x) : ℂ))
      (hA2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
      (hB2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
    refine le_trans h ?_
    have h1 := norm_factorA1_le ha1 ha1pos.le hR hu
    have h2 := norm_factorB1_le hb1 hb1pos.le hε hR hu
    have ha := norm_factorA_le u
    have hb := norm_factorB_le ε u
    have e1 : ‖(cutPhi u : ℂ)‖ * ‖iteratedDeriv 1 (fun x : ℝ => (cutPsi (ε * x) : ℂ)) u‖
        ≤ 1 * (4 * b1 / R) := mul_le_mul ha h2 (norm_nonneg _) (by norm_num)
    have e2 : ‖iteratedDeriv 1 (fun x : ℝ => (cutPhi x : ℂ)) u‖ * ‖(cutPsi (ε * u) : ℂ)‖
        ≤ (2 * a1 / R) * 1 := mul_le_mul h1 hb (norm_nonneg _) (by positivity)
    nlinarith [e1, e2]
  have hF2 : ‖iteratedDeriv 2 (fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) u‖
      ≤ 4 * a2 / R ^ 2 + 16 * a1 * b1 / R ^ 2 + 16 * b2 / R ^ 2 := by
    have h := norm_iteratedDeriv_two_mul_le (fun x : ℝ => (cutPhi x : ℂ))
      (fun x : ℝ => (cutPsi (ε * x) : ℂ)) hA2 hB2
    refine le_trans h ?_
    have h1 := norm_factorA1_le ha1 ha1pos.le hR hu
    have h2 := norm_factorB1_le hb1 hb1pos.le hε hR hu
    have h1' := norm_factorA2_le ha2 ha2pos.le hR hu
    have h2' := norm_factorB2_le hb2 hb2pos.le hε hR hu
    have ha := norm_factorA_le u
    have hb := norm_factorB_le ε u
    have e1 : ‖iteratedDeriv 2 (fun x : ℝ => (cutPhi x : ℂ)) u‖ * ‖(cutPsi (ε * u) : ℂ)‖
        ≤ (4 * a2 / R ^ 2) * 1 := mul_le_mul h1' hb (norm_nonneg _) (by positivity)
    have e2 : 2 * ‖iteratedDeriv 1 (fun x : ℝ => (cutPhi x : ℂ)) u‖
        * ‖iteratedDeriv 1 (fun x : ℝ => (cutPsi (ε * x) : ℂ)) u‖
        ≤ 16 * a1 * b1 / R ^ 2 := by
      have hh := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      have hh2 := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)
      have heq : 2 * ((2 * a1 / R) * (4 * b1 / R)) = 16 * a1 * b1 / R ^ 2 := by ring
      nlinarith [hh2, heq]
    have e3 : ‖(cutPhi u : ℂ)‖ * ‖iteratedDeriv 2 (fun x : ℝ => (cutPsi (ε * x) : ℂ)) u‖
        ≤ 1 * (16 * b2 / R ^ 2) := mul_le_mul ha h2' (norm_nonneg _) (by norm_num)
    nlinarith [e1, e2, e3]
  have hmain := norm_iteratedDeriv_two_mul_le
    (fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) (chirp α) (hA2.mul hB2) hC2
  refine le_trans hmain ?_
  have hCc1 := norm_factorC1_le (α := α) hR hu
  have hCc2 := norm_factorC2_le (α := α) hR hu
  have hCc0 := norm_factorC_le α u
  have e1 : ‖iteratedDeriv 2 (fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) u‖
      * ‖chirp α u‖ ≤ (4 * a2 / R ^ 2 + 16 * a1 * b1 / R ^ 2 + 16 * b2 / R ^ 2) * 1 :=
    mul_le_mul hF2 (le_of_eq hCc0) (norm_nonneg _) (by positivity)
  have e2 : 2 * ‖iteratedDeriv 1 (fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) u‖
      * ‖iteratedDeriv 1 (chirp α) u‖
      ≤ 2 * (2 * a1 / R + 4 * b1 / R) * (2 * |α| / R) := by
    have hh := mul_le_mul hF1 hCc1 (norm_nonneg _) (by positivity)
    nlinarith [hh]
  have e3 : ‖(fun x : ℝ => (cutPhi x : ℂ) * (cutPsi (ε * x) : ℂ)) u‖
      * ‖iteratedDeriv 2 (chirp α) u‖ ≤ 1 * (4 * (1 + |α|) ^ 2 / R ^ 2) :=
    mul_le_mul hF0 hCc2 (norm_nonneg _) (by norm_num)
  have hfin : (4 * a2 / R ^ 2 + 16 * a1 * b1 / R ^ 2 + 16 * b2 / R ^ 2) * 1
      + 2 * (2 * a1 / R + 4 * b1 / R) * (2 * |α| / R)
      + 1 * (4 * (1 + |α|) ^ 2 / R ^ 2)
      ≤ (4 * a2 + 16 * a1 * b1 + 16 * b2 + 8 * a1 + 16 * b1 + 4) * (1 + |α|) ^ 2 / R ^ 2 := by
    have hkey :
        (4 * a2 / R ^ 2 + 16 * a1 * b1 / R ^ 2 + 16 * b2 / R ^ 2) * 1
          + 2 * (2 * a1 / R + 4 * b1 / R) * (2 * |α| / R)
          + 1 * (4 * (1 + |α|) ^ 2 / R ^ 2)
        = (4 * a2 + 16 * a1 * b1 + 16 * b2 + 8 * a1 * |α| + 16 * b1 * |α| + 4 * (1 + |α|) ^ 2) / R ^ 2 := by
      ring_nf
    rw [hkey]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hbig : 1 ≤ (1 + |α|) ^ 2 := by nlinarith [abs_nonneg α]
    have habs : |α| ≤ (1 + |α|) ^ 2 := by nlinarith [abs_nonneg α]
    have c1 : 0 ≤ (4 * a2 + 16 * a1 * b1 + 16 * b2) * ((1 + |α|) ^ 2 - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hbig)
    have c2 : 0 ≤ (8 * a1 + 16 * b1) * ((1 + |α|) ^ 2 - |α|) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr habs)
    nlinarith [c1, c2]
  linarith [e1, e2, e3, hfin]

/-! ## 9. The main bound -/

theorem fcut_piece_deriv2 :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (R ε α : ℝ) (u : ℝ), 0 < R → 0 < ε →
      ‖iteratedDeriv 2 (fun x : ℝ => (dyadEta (|x| / R) : ℂ) * fcut ε α x) u‖
        ≤ K * (1 + |α|) ^ 2 / R ^ 2 := by
  obtain ⟨C1, hC1nn, hC1⟩ := fcut_deriv1_bound
  obtain ⟨C2, hC2nn, hC2⟩ := fcut_deriv2_bound
  obtain ⟨D1, hD1nn, hD1⟩ := exists_bound_iteratedDeriv_gAbs 1
  obtain ⟨D2, hD2nn, hD2⟩ := exists_bound_iteratedDeriv_gAbs 2
  refine ⟨D2 + 2 * D1 * C1 + C2, by positivity, ?_⟩
  intro R ε α u hR hε
  have heta : (fun x : ℝ => (dyadEta (|x| / R) : ℂ)) = fun x => gAbs (x / R) := by
    funext x; rw [gAbs, abs_div, abs_of_pos hR]
  by_cases hu : |u| < R / 2
  · have hnhds : {x : ℝ | |x| < R / 2} ∈ 𝓝 u := by
      have hopen : IsOpen {x : ℝ | |x| < R / 2} := by
        rw [show {x : ℝ | |x| < R / 2} = Set.Ioo (-(R / 2)) (R / 2) by
          ext x; rw [Set.mem_ofPred_eq, Set.mem_Ioo, abs_lt]]
        exact isOpen_Ioo
      exact hopen.mem_nhds hu
    have hev : (fun x : ℝ => (dyadEta (|x| / R) : ℂ) * fcut ε α x) =ᶠ[𝓝 u] 0 := by
      filter_upwards [hnhds] with x hx
      have hx' : |x| / R < 1 / 2 := by rw [div_lt_iff₀ hR]; linarith [hx]
      simp [dyadEta_eq_zero_of_le (le_of_lt hx')]
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hev]
    change ‖iteratedDeriv 2 (fun _ : ℝ => (0 : ℂ)) u‖
        ≤ (D2 + 2 * D1 * C1 + C2) * (1 + |α|) ^ 2 / R ^ 2
    rw [iteratedDeriv_const]
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte, norm_zero]
    positivity
  · rw [not_lt] at hu
    have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
    have hηc : ContDiffAt ℝ (2 : WithTop ℕ∞) (fun x : ℝ => (dyadEta (|x| / R) : ℂ)) u := by
      rw [heta]
      exact ((contDiff_gAbs.comp (contDiff_id.div_const R)).contDiffAt).of_le (coe_order_le_top _)
    have hfc2 : ContDiffAt ℝ (2 : WithTop ℕ∞) (fcut ε α) u :=
      (contDiff_fcut ε α hε).1.contDiffAt.of_le (coe_order_le_top _)
    have hη0 : ‖(fun x : ℝ => (dyadEta (|x| / R) : ℂ)) u‖ ≤ 1 := by
      rw [heta]; exact norm_gAbs_le (u / R)
    have hη1 : ‖iteratedDeriv 1 (fun x : ℝ => (dyadEta (|x| / R) : ℂ)) u‖ ≤ D1 / R := by
      rw [heta]; simpa using norm_iteratedDeriv_gAbs_div_le R hR 1 hD1 u
    have hη2 : ‖iteratedDeriv 2 (fun x : ℝ => (dyadEta (|x| / R) : ℂ)) u‖ ≤ D2 / R ^ 2 := by
      rw [heta]; exact norm_iteratedDeriv_gAbs_div_le R hR 2 hD2 u
    have hf0 := norm_fcut_le_one ε α u
    have hf1 := hC1 ε α R hε hR u hu
    have hf2 := hC2 ε α R hε hR u hu
    have hmain := norm_iteratedDeriv_two_mul_le
      (fun x : ℝ => (dyadEta (|x| / R) : ℂ)) (fcut ε α) hηc hfc2
    rw [show (fun x : ℝ => (dyadEta (|x| / R) : ℂ) * fcut ε α x)
        = (fun x : ℝ => (dyadEta (|x| / R) : ℂ)) * (fcut ε α) from rfl]
    refine le_trans hmain ?_
    have e1 : ‖iteratedDeriv 2 (fun x : ℝ => (dyadEta (|x| / R) : ℂ)) u‖ * ‖fcut ε α u‖
        ≤ (D2 / R ^ 2) * 1 := mul_le_mul hη2 hf0 (norm_nonneg _) (by positivity)
    have e2 : 2 * ‖iteratedDeriv 1 (fun x : ℝ => (dyadEta (|x| / R) : ℂ)) u‖
        * ‖iteratedDeriv 1 (fcut ε α) u‖ ≤ 2 * (D1 / R) * (C1 * (1 + |α|) / R) := by
      have hh := mul_le_mul hη1 hf1 (norm_nonneg _) (by positivity)
      nlinarith [hh]
    have e3 : ‖(fun x : ℝ => (dyadEta (|x| / R) : ℂ)) u‖ * ‖iteratedDeriv 2 (fcut ε α) u‖
        ≤ 1 * (C2 * (1 + |α|) ^ 2 / R ^ 2) := mul_le_mul hη0 hf2 (norm_nonneg _) (by norm_num)
    have hfin : (D2 / R ^ 2) * 1 + 2 * (D1 / R) * (C1 * (1 + |α|) / R)
        + 1 * (C2 * (1 + |α|) ^ 2 / R ^ 2)
        ≤ (D2 + 2 * D1 * C1 + C2) * (1 + |α|) ^ 2 / R ^ 2 := by
      have hkey :
          (D2 / R ^ 2) * 1 + 2 * (D1 / R) * (C1 * (1 + |α|) / R)
            + 1 * (C2 * (1 + |α|) ^ 2 / R ^ 2)
          = (D2 + 2 * D1 * C1 * (1 + |α|) + C2 * (1 + |α|) ^ 2) / R ^ 2 := by
        ring_nf
      rw [hkey]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hbig : 1 ≤ (1 + |α|) ^ 2 := by nlinarith [abs_nonneg α]
      have hbig2 : (1 + |α|) ≤ (1 + |α|) ^ 2 := by nlinarith [abs_nonneg α]
      have c1 : 0 ≤ D2 * ((1 + |α|) ^ 2 - 1) := mul_nonneg hD2nn (sub_nonneg.mpr hbig)
      have c2 : 0 ≤ (2 * D1 * C1) * ((1 + |α|) ^ 2 - (1 + |α|)) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr hbig2)
      nlinarith [c1, c2]
    linarith [e1, e2, e3, hfin]

end

end Work.FIArea4.Vflip.Vfd
