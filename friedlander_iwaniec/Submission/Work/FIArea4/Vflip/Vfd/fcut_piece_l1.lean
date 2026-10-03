import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.SepDefs
import Submission.Work.FIArea4.Vflip.Vfd.fourier_l1_sqrt
import Submission.Work.FIArea4.Vflip.Vfd.dilation_fourier_l1
import Submission.Work.FIArea4.Vflip.Vfd.contDiff_fcut
import Submission.Work.FIArea4.Vflip.Vfd.fcut_piece_deriv2
import Submission.Work.FIArea4.Vflip.sep_defs

namespace Work.FIArea4.Vflip.Vfd

open MeasureTheory
open Filter
open scoped Topology FourierTransform

noncomputable section

set_option linter.unusedVariables false

/-! ## The dyadic bump `u ↦ dyadEta (|u| / R)` -/

lemma contDiff_dyadEta_abs : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => dyadEta |u|) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases eq_or_ne u 0 with rfl | hu
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
    exact dyadEta_eq_zero_of_le (le_of_lt hx)
  · have hOn : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => dyadEta |x|) {x : ℝ | x ≠ 0} :=
      contDiff_dyadEta.comp_contDiffOn (contDiffOn_abs (n := ⊤) (by simp))
    exact hOn.contDiffAt (isOpen_ne.mem_nhds hu)

lemma contDiff_dyadEta_abs_div (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => dyadEta (|u| / R)) := by
  have hfun : (fun u : ℝ => dyadEta (|u| / R)) =
      (fun x : ℝ => dyadEta |x|) ∘ (fun u : ℝ => u / R) := by
    funext u
    simp only [Function.comp_apply, abs_div, abs_of_pos hR]
  rw [hfun]
  exact contDiff_dyadEta_abs.comp (by fun_prop)

lemma contDiff_g (R ε α : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (dyadEta (|u| / R) : ℂ) * fcut ε α u) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_dyadEta_abs_div R hR)).mul (contDiff_fcut ε α hε).1

lemma hasCompactSupport_g (R ε α : ℝ) (hR : 0 < R) :
    HasCompactSupport (fun u : ℝ => (dyadEta (|u| / R) : ℂ) * fcut ε α u) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(2 * R)) (2 * R))
    isCompact_Icc ?_
  intro u hu
  rw [Function.mem_support] at hu
  rw [Set.mem_Icc]
  have h2 : |u| ≤ 2 * R := by
    by_contra hc
    rw [not_le] at hc
    have h3 : 2 ≤ |u| / R := by rw [le_div_iff₀ hR]; linarith
    exact hu (by rw [dyadEta_eq_zero_of_ge h3, Complex.ofReal_zero, zero_mul])
  exact abs_le.mp h2

lemma dyadEta_le_one (t : ℝ) : dyadEta t ≤ 1 := by
  unfold dyadEta dyadStep
  have h1 : Real.smoothTransition (2 * t - 1) ≤ 1 := Real.smoothTransition.le_one _
  have h2 : 0 ≤ Real.smoothTransition (t - 1) := Real.smoothTransition.nonneg _
  linarith

/-- The norm of a dyadic piece is at most `1`. -/
lemma norm_g_le_one (R ε α u : ℝ) :
    ‖(dyadEta (|u| / R) : ℂ) * fcut ε α u‖ ≤ 1 := by
  rw [norm_mul]
  have h1 : ‖(dyadEta (|u| / R) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [dyadEta_nonneg (|u| / R)], dyadEta_le_one (|u| / R)⟩
  have h2 : ‖fcut ε α u‖ ≤ 1 := by
    rcases eq_or_ne u 0 with rfl | hu
    · have hz : cutPhi 0 = 0 := by
        rw [cutPhi]
        have h4 : (4 * (0 : ℝ) ^ 2 - 1) = -1 := by norm_num
        rw [h4, Real.smoothTransition.zero_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)]
      rw [fcut, hz]
      simp
    · rw [fcut, cpow_eq_chirp hu, norm_mul, norm_mul, norm_chirp, mul_one, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
      have ha : |cutPhi u| ≤ 1 :=
        abs_le.mpr ⟨by linarith [cutPhi_nonneg u], cutPhi_le_one u⟩
      have hb : |cutPsi (ε * u)| ≤ 1 :=
        abs_le.mpr ⟨by linarith [cutPsi_nonneg (ε * u)], cutPsi_le_one (ε * u)⟩
      nlinarith [abs_nonneg (cutPhi u), abs_nonneg (cutPsi (ε * u))]
  calc ‖(dyadEta (|u| / R) : ℂ)‖ * ‖fcut ε α u‖ ≤ 1 * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-! ## The pointwise second-derivative bound is the imported lemma
`Work.FIArea4.Vflip.Vfd.fcut_piece_deriv2` (module
`Submission.Work.FIArea4.Vflip.Vfd.fcut_piece_deriv2`). -/

private lemma integrable_iteratedDeriv_top (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) (n : ℕ) : Integrable (iteratedDeriv n f) := by
  have hsupp : HasCompactSupport (iteratedDeriv n f) := by
    rw [iteratedDeriv_eq_iterate]
    induction n with
    | zero => simpa using hs
    | succ k ih => rw [Function.iterate_succ']; exact ih.deriv
  have hcont : Continuous (iteratedDeriv n f) :=
    hf.continuous_iteratedDeriv n (WithTop.coe_le_coe.mpr le_top)
  exact hcont.integrable_of_hasCompactSupport hsupp

private lemma norm_two_pi_I_mul (u : ℝ) :
    ‖(2 * ↑Real.pi * Complex.I * (u : ℂ))‖ = 2 * Real.pi * |u| := by
  have h1 : (2 * ↑Real.pi * Complex.I * (u : ℂ)) = ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos]

private lemma norm_two_pi_I_mul_sq (u : ℝ) :
    ‖(2 * ↑Real.pi * Complex.I * (u : ℂ)) ^ 2‖ = (2 * Real.pi * |u|) ^ 2 := by
  rw [norm_pow, norm_two_pi_I_mul]

theorem fcut_piece_l1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε α : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (j : ℤ),
      ∫ ξ : ℝ, ‖FourierTransform.fourier
          (fun u : ℝ => (dyadEta (|u| / (2 : ℝ) ^ j) : ℂ) * fcut ε α u) ξ‖
        ≤ C * (1 + |α|) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := fcut_piece_deriv2
  refine ⟨max 1 (8 * Real.sqrt K / Real.pi),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro ε α hε hε1 j
  set R : ℝ := (2 : ℝ) ^ j with hRdef
  have hRpos : 0 < R := by rw [hRdef]; exact zpow_pos (by norm_num) j
  set g : ℝ → ℂ := fun u => (dyadEta (|u| / R) : ℂ) * fcut ε α u with hgdef
  have hcd : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_g R ε α hRpos hε
  have hcs : HasCompactSupport g := hasCompactSupport_g R ε α hRpos
  have hcd2 : ContDiff ℝ (↑(2 : ℕ∞)) g := hcd.of_le (WithTop.coe_le_coe.mpr le_top)
  have hint : ∀ n : ℕ, ↑n ≤ (2 : ℕ∞) → Integrable (iteratedDeriv n g) :=
    fun n _ => integrable_iteratedDeriv_top g hcd hcs n
  have hfour := Real.fourier_iteratedDeriv (f := g) (N := (2 : ℕ∞)) hcd2 hint (n := 2) le_rfl
  set A : ℝ := ∫ u, ‖g u‖ with hAdef
  set B : ℝ := (∫ u, ‖iteratedDeriv 2 g u‖) / (4 * Real.pi ^ 2) with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact integral_nonneg (fun u => norm_nonneg _)
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact div_nonneg (integral_nonneg (fun u => norm_nonneg _)) (by positivity)
  -- the two bounds used in `fourier_l1_sqrt`
  have h1 : ∀ u : ℝ, ‖𝓕 g u‖ ≤ A := by
    intro u
    rw [hAdef]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  have h2 : ∀ u : ℝ, u ≠ 0 → ‖𝓕 g u‖ ≤ B / u ^ 2 := by
    intro u hu
    have hkey : ‖𝓕 (iteratedDeriv 2 g) u‖ = (2 * Real.pi * |u|) ^ 2 * ‖𝓕 g u‖ := by
      rw [congrFun hfour u, norm_smul, norm_two_pi_I_mul_sq]
    have hbound : ‖𝓕 (iteratedDeriv 2 g) u‖ ≤ ∫ x : ℝ, ‖iteratedDeriv 2 g x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hu2 : (0 : ℝ) < (2 * Real.pi * |u|) ^ 2 := by
      have : 0 < |u| := abs_pos.mpr hu
      positivity
    have h3 : ‖𝓕 g u‖ ≤ (∫ x : ℝ, ‖iteratedDeriv 2 g x‖) / (2 * Real.pi * |u|) ^ 2 := by
      rw [le_div_iff₀ hu2, mul_comm, ← hkey]
      exact hbound
    have heq : 4 * Real.pi ^ 2 * u ^ 2 = (2 * Real.pi * |u|) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    rw [hBdef, div_div, heq]
    exact h3
  have hmain := fourier_l1_sqrt g hA0 hB0 h1 h2
  -- support facts
  have hg_norm_le : ∀ u : ℝ, ‖g u‖ ≤ 1 := fun u => by
    rw [hgdef]; exact norm_g_le_one R ε α u
  have hgint : Integrable g := hcd.continuous.integrable_of_hasCompactSupport hcs
  have hzero_compl : ∀ u : ℝ, ¬ (u ∈ Set.Icc (-(2 * R)) (2 * R)) → ‖g u‖ = 0 := by
    intro u hu
    have h2 : 2 * R < |u| := by
      rw [Set.mem_Icc] at hu
      simp only [not_and_or, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    rw [hgdef]
    have hz : dyadEta (|u| / R) = 0 :=
      dyadEta_eq_zero_of_ge (by rw [le_div_iff₀ hRpos]; linarith)
    simp [hz]
  have hA1 : A ≤ 4 * R := by
    rw [hAdef]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc (-(2 * R)) (2 * R)) hzero_compl]
    have hf : IntegrableOn (fun u : ℝ => ‖g u‖) (Set.Icc (-(2 * R)) (2 * R)) :=
      hgint.norm.integrableOn
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (-(2 * R)) (2 * R)) := by
      refine integrableOn_const (hs := ?_) (hC := ?_)
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      · simp
    calc ∫ u in Set.Icc (-(2 * R)) (2 * R), ‖g u‖
        ≤ ∫ u in Set.Icc (-(2 * R)) (2 * R), (1 : ℝ) :=
          setIntegral_mono_on hf hc measurableSet_Icc (fun u _ => hg_norm_le u)
      _ = 4 * R := by
          rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]
          ring
  have hzero_compl_e : ∀ u : ℝ, ¬ (u ∈ Set.Icc (-(2 / ε)) (2 / ε)) → ‖g u‖ = 0 := by
    intro u hu
    rw [Set.mem_Icc] at hu
    simp only [not_and_or, not_le] at hu
    have h2e : (0 : ℝ) < 2 / ε := div_pos (by norm_num) hε
    have hu' : 2 / ε < |u| := by
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    have h4 : 4 ≤ (ε * u) ^ 2 := by
      rw [mul_pow]
      have h1 : 2 < ε * |u| := by
        have := mul_lt_mul_of_pos_left hu' hε
        rwa [mul_div_cancel₀ 2 (ne_of_gt hε)] at this
      have h2 : 4 ≤ (ε * |u|) ^ 2 := by nlinarith
      rw [mul_pow, sq_abs] at h2
      linarith
    simp only [hgdef]
    have hcut : fcut ε α u = ((cutPhi u : ℝ) : ℂ) * ((cutPsi (ε * u) : ℝ) : ℂ)
        * (((|u| : ℝ) : ℂ) ^ (Complex.I * (α : ℂ))) := rfl
    rw [hcut, cutPsi_eq_zero_of_sq_ge h4]
    simp
  have hA2 : A ≤ 4 / ε := by
    rw [hAdef]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc (-(2 / ε)) (2 / ε)) hzero_compl_e]
    have hf : IntegrableOn (fun u : ℝ => ‖g u‖) (Set.Icc (-(2 / ε)) (2 / ε)) :=
      hgint.norm.integrableOn
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (-(2 / ε)) (2 / ε)) := by
      refine integrableOn_const (hs := ?_) (hC := ?_)
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      · simp
    calc ∫ u in Set.Icc (-(2 / ε)) (2 / ε), ‖g u‖
        ≤ ∫ u in Set.Icc (-(2 / ε)) (2 / ε), (1 : ℝ) :=
          setIntegral_mono_on hf hc measurableSet_Icc (fun u _ => hg_norm_le u)
      _ = 4 / ε := by
          have h2e : (0 : ℝ) < 2 / ε := div_pos (by norm_num) hε
          rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]
          ring
  -- the second derivative integral
  have hzero_compl2 : ∀ u : ℝ, ¬ (u ∈ Set.Icc (-(2 * R)) (2 * R)) →
      ‖iteratedDeriv 2 g u‖ = 0 := by
    intro u hu
    have h2 : 2 * R < |u| := by
      rw [Set.mem_Icc] at hu
      simp only [not_and_or, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    have hev : g =ᶠ[𝓝 u] (fun _ => 0) := by
      rw [hgdef]
      have hopen : {x : ℝ | 2 * R < |x|} ∈ 𝓝 u :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds h2
      filter_upwards [hopen] with x hx
      have hz : dyadEta (|x| / R) = 0 :=
        dyadEta_eq_zero_of_ge (by rw [le_div_iff₀ hRpos]; linarith)
      rw [hz, Complex.ofReal_zero, zero_mul]
    have hd : deriv g =ᶠ[𝓝 u] (fun _ => 0) := by simpa using hev.deriv
    have hdd : deriv (deriv g) =ᶠ[𝓝 u] (fun _ => 0) := by simpa using hd.deriv
    rw [iteratedDeriv_two_eq]
    have h0 : deriv (deriv g) u = 0 := hdd.eq_of_nhds
    rw [h0, norm_zero]
  have hInt2 : ∫ u : ℝ, ‖iteratedDeriv 2 g u‖ ≤ 4 * K * (1 + |α|) ^ 2 / R := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Icc (-(2 * R)) (2 * R)) hzero_compl2]
    have hf : IntegrableOn (fun u : ℝ => ‖iteratedDeriv 2 g u‖) (Set.Icc (-(2 * R)) (2 * R)) :=
      (integrable_iteratedDeriv_top g hcd hcs 2).norm.integrableOn
    have hc : IntegrableOn (fun _ : ℝ => K * (1 + |α|) ^ 2 / R ^ 2)
        (Set.Icc (-(2 * R)) (2 * R)) := by
      refine integrableOn_const (hs := ?_) (hC := ?_)
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      · simp
    calc ∫ u in Set.Icc (-(2 * R)) (2 * R), ‖iteratedDeriv 2 g u‖
        ≤ ∫ u in Set.Icc (-(2 * R)) (2 * R), K * (1 + |α|) ^ 2 / R ^ 2 :=
          setIntegral_mono_on hf hc measurableSet_Icc (fun u _ => hK R ε α u hRpos hε)
      _ = 4 * K * (1 + |α|) ^ 2 / R := by
          rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
          field_simp
          try ring
  have hBbound : B ≤ K * (1 + |α|) ^ 2 / (Real.pi ^ 2 * R) := by
    rw [hBdef]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi ^ 2)]
    have heq : (K * (1 + |α|) ^ 2 / (Real.pi ^ 2 * R)) * (4 * Real.pi ^ 2)
        = 4 * K * (1 + |α|) ^ 2 / R := by
      field_simp
      try ring
    rw [heq]
    exact hInt2
  -- combining
  have hAB : A * B ≤ 4 * K * (1 + |α|) ^ 2 / Real.pi ^ 2 := by
    have hAmin : A ≤ min (4 * R) (4 / ε) := le_min hA1 hA2
    have hBnn : 0 ≤ B := hB0
    have hminnn : 0 ≤ min (4 * R) (4 / ε) := le_trans hA0 hAmin
    calc A * B ≤ min (4 * R) (4 / ε) * (K * (1 + |α|) ^ 2 / (Real.pi ^ 2 * R)) :=
          mul_le_mul hAmin hBbound hBnn hminnn
      _ = (K * (1 + |α|) ^ 2 / Real.pi ^ 2) * (min (4 * R) (4 / ε) / R) := by
          field_simp
          try ring
      _ ≤ (K * (1 + |α|) ^ 2 / Real.pi ^ 2) * 4 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_iff₀ hRpos]
          exact min_le_left _ _
      _ = 4 * K * (1 + |α|) ^ 2 / Real.pi ^ 2 := by ring
  have hgoal : ∫ ξ : ℝ, ‖𝓕 g ξ‖ ≤ max 1 (8 * Real.sqrt K / Real.pi) * (1 + |α|) ^ 2 := by
    calc ∫ ξ : ℝ, ‖𝓕 g ξ‖ ≤ 4 * Real.sqrt (A * B) := hmain
      _ ≤ 4 * Real.sqrt (4 * K * (1 + |α|) ^ 2 / Real.pi ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hAB) (by norm_num)
      _ = (8 * Real.sqrt K / Real.pi) * (1 + |α|) := by
          have hsq : (2 * Real.sqrt K * (1 + |α|) / Real.pi) ^ 2
              = 4 * K * (1 + |α|) ^ 2 / Real.pi ^ 2 := by
            rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hK0]
            ring
          rw [← hsq, Real.sqrt_sq (by positivity)]
          ring
      _ ≤ max 1 (8 * Real.sqrt K / Real.pi) * (1 + |α|) ^ 2 := by
          have hone : (1 : ℝ) + |α| ≤ (1 + |α|) ^ 2 := by nlinarith [abs_nonneg α]
          have hmax : 0 ≤ max 1 (8 * Real.sqrt K / Real.pi) :=
            le_trans zero_le_one (le_max_left _ _)
          calc (8 * Real.sqrt K / Real.pi) * (1 + |α|)
              ≤ max 1 (8 * Real.sqrt K / Real.pi) * (1 + |α|) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
            _ ≤ max 1 (8 * Real.sqrt K / Real.pi) * (1 + |α|) ^ 2 :=
                mul_le_mul_of_nonneg_left hone hmax
  simpa [hgdef, hRdef] using hgoal

end

end Work.FIArea4.Vflip.Vfd
