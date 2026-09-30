import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.casdiv.plancherel_Kf
import Submission.Work.BMF.mrlas.casdiv_far_window
import Submission.Work.BMF.window_weighted_integral_bound
import Submission.Work.BMF.Psi1_L2_bound
import Submission.Work.BMF.Psi2_L2_bound
import Submission.Work.BMF.LSeries_norm_le_exp_Wsup
import Submission.Work.BMF.mrlas.Wsup_le_Zrcp
import Submission.Work.BMF.mrlas.Kser_eq_neg_LSeries_mul_Psi
import Submission.Work.BMF.halasz_plancherel
import Submission.Work.BMF.casdiv.Kser_line_aemeasurable
import Submission.Work.BMF.casdiv.Kf_integrableOn
import Submission.Work.BMF.casdiv.psi_weighted_lbounds
import Submission.Work.BMF.Psi_continuous
import Submission.Work.BMF.mrlas.Psi_norm_sq_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `L²` bound for `Kf` (own copy, unconditional dependency closure)

This is a copy of `Work.BMF.casdiv.L2_Kf_bound` (same proof, same statement, renamed) with the
import list pruned to modules whose transitive closure is sorries-free: in particular it uses the
proved `Work.BMF.Psi2_L2_bound` rather than the still-unproved `Work.BMF.mrlas.Psi2_L2_bound`.
-/

set_option maxHeartbeats 1000000

namespace Work.BMF.casdiv

open MeasureTheory

/-! ## The pointwise comparison `‖Kser‖²/‖s‖² ≤ b² ‖Ψ‖²/‖s‖²` -/

private lemma Kser_div_le (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) (hb : ∀ n, ‖f n‖ ≤ 1)
    {a b τ : ℝ} (ha : 1 < a)
    (hLb : ‖LSeries f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ b) :
    ‖Kser f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
        ‖((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 ≤
      b ^ 2 * (‖Work.BMF.Psi f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
        ‖((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
  have hker : Kser f ((a : ℂ) + (τ : ℂ) * Complex.I)
      = -(LSeries f ((a : ℂ) + (τ : ℂ) * Complex.I)) *
        Work.BMF.Psi f ((a : ℂ) + (τ : ℂ) * Complex.I) :=
    Work.BMF.mrlas.Kser_eq_neg_LSeries_mul_Psi f hf1 hmul hb
      (s := (a : ℂ) + (τ : ℂ) * Complex.I) (by simp; linarith)
  calc ‖Kser f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
        ‖((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
      = ‖LSeries f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 *
          (‖Work.BMF.Psi f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
            ‖((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
        rw [hker, norm_mul, norm_neg]
        ring
    _ ≤ b ^ 2 * (‖Work.BMF.Psi f ((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
          ‖((a : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) hLb 2

/-- Real form of the exponential square identity used twice below. -/
private lemma exp_sq (y : ℝ) : Real.exp y ^ 2 = Real.exp (2 * y) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

theorem yr_L2_Kf_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x α T : ℝ, 2 ≤ x → 0 < α → α ≤ 1 → 1 ≤ T → Real.exp (1 / α) ≤ x →
        (∫ t in (1 : ℝ)..x, ‖Work.BMF.Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) ≤
          C * ((1 / α) * Real.exp (2 * Work.BMF.Wsup f x α (T + 1)) +
               Real.exp (2 * Work.BMF.Zrcp x) / (α * T)) := by
  obtain ⟨CL, hCLpos, hCL⟩ := LSeries_norm_le_exp_Wsup
  obtain ⟨CP, hCPpos, hCP⟩ := psi_weighted_lbounds
  refine ⟨CL ^ 2 * CP / (2 * Real.pi) + 1, by positivity, ?_⟩
  intro f hf1 hmul hb x α T hx2 hα hα1 hT hexp
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  set X : ℝ := Real.exp (2 * Wsup f x α (T + 1)) with hX
  set Z : ℝ := Real.exp (2 * Zrcp x) with hZ
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  set Kmid : ℝ := CL ^ 2 * X with hKmid
  set Ktail : ℝ := CL ^ 2 * Z with hKtail
  have hKmid0 : 0 < Kmid := by rw [hKmid]; positivity
  have hKtail0 : 0 < Ktail := by rw [hKtail]; positivity
  -- the two integrands on the critical line
  set hfun : ℝ → ℝ := fun τ => ‖Kser f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
      ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 with hhfun
  set Gfun : ℝ → ℝ := fun τ => ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
      ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 with hGfun
  -- bounds for `LSeries`
  have hLsup : ∀ {s : ℂ}, s.re = 1 + α → ‖LSeries f s‖ ≤ CL * Real.exp (Zrcp x) := by
    intro s hs
    have h1 : ‖LSeries f s‖ ≤ CL * Real.exp (Wsup f x α (|s.im| + 1)) :=
      hCL f hf1 hmul hb x α |s.im| hx2 hα hexp hs (by linarith [abs_nonneg s.im])
    have h2 : Wsup f x α (|s.im| + 1) ≤ Zrcp x :=
      Work.BMF.mrlas.Wsup_le_Zrcp f hb x (|s.im| + 1) α hα.le
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hCLpos.le)
  have hLmid : ∀ τ : ℝ, |τ| ≤ T →
      ‖LSeries f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        CL * Real.exp (Wsup f x α (T + 1)) := by
    intro τ hτ
    have hre : (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I).re = 1 + α := by simp
    have him : |(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I).im| ≤ T + 1 := by
      have h2 : (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I).im = τ := by simp
      rw [h2]; linarith
    exact hCL f hf1 hmul hb x α T hx2 hα hexp hre him
  have hLtail : ∀ τ : ℝ, T < |τ| →
      ‖LSeries f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ CL * Real.exp (Zrcp x) := by
    intro τ _
    exact hLsup (by simp)
  -- pointwise comparisons
  have hptmid : ∀ τ : ℝ, |τ| ≤ T → hfun τ ≤ Kmid * Gfun τ := by
    intro τ hτ
    have h1 : hfun τ ≤ (CL * Real.exp (Wsup f x α (T + 1))) ^ 2 * Gfun τ := by
      simp only [hhfun, hGfun]
      exact Kser_div_le f hf1 hmul hb (a := 1 + α) (b := CL * Real.exp (Wsup f x α (T + 1)))
        (by linarith) (hLmid τ hτ)
    have h2 : (CL * Real.exp (Wsup f x α (T + 1))) ^ 2 = Kmid := by
      rw [hKmid, hX, mul_pow, exp_sq]
    rwa [h2] at h1
  have hpttail : ∀ τ : ℝ, T < |τ| → hfun τ ≤ Ktail * Gfun τ := by
    intro τ hτ
    have h1 : hfun τ ≤ (CL * Real.exp (Zrcp x)) ^ 2 * Gfun τ := by
      simp only [hhfun, hGfun]
      exact Kser_div_le f hf1 hmul hb (a := 1 + α) (b := CL * Real.exp (Zrcp x))
        (by linarith) (hLtail τ hτ)
    have h2 : (CL * Real.exp (Zrcp x)) ^ 2 = Ktail := by
      rw [hKtail, hZ, mul_pow, exp_sq]
    rwa [h2] at h1
  -- continuity/measurability of `Gfun`
  have hGcont : Continuous Gfun := by
    rw [hGfun]
    have h1 : Continuous (fun τ : ℝ =>
        ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) :=
      Work.BMF.Psi_continuous f hf1 hb (1 + α) (by linarith)
    have h2 : Continuous (fun τ : ℝ => ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
      fun_prop
    exact h1.div h2 (fun τ => by
      have hne : (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      exact ne_of_gt (pow_pos (norm_pos_iff.mpr hne) 2))
  have hGmeas : Measurable (fun τ : ℝ => ENNReal.ofReal (Gfun τ)) :=
    ENNReal.measurable_ofReal.comp hGcont.measurable
  -- measurability of `hfun`
  have hA : AEStronglyMeasurable hfun volume := by
    have h1 : AEMeasurable (fun τ : ℝ => Kser f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)) volume :=
      Kser_line_aemeasurable f (1 + α) (by linarith)
    have h2 : AEMeasurable (fun τ : ℝ => ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) volume := by
      have hc : Continuous (fun τ : ℝ => ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
        fun_prop
      exact hc.aemeasurable
    rw [hhfun]
    exact ((h1.norm.pow_const 2).div h2).aestronglyMeasurable
  -- Step 1: enlarge the interval of integration
  have hstep1 : (∫ t in (1 : ℝ)..x, ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) ≤
      ∫ t in Set.Ioi (0 : ℝ), ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α) := by
    rw [intervalIntegral.integral_of_le hx1]
    refine setIntegral_mono_set (Kf_integrableOn f hb α hα) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.le _)
    · have hsub : Set.Ioc (1 : ℝ) x ⊆ Set.Ioi (0 : ℝ) :=
        fun y hy => Set.mem_Ioi.mpr (lt_trans zero_lt_one hy.1)
      exact LE.le.eventuallySubset hsub
  -- Step 2: Plancherel
  have hstep2 : (∫ t in Set.Ioi (0 : ℝ), ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) =
      (1 / (2 * Real.pi)) * ∫ τ : ℝ, hfun τ := by
    rw [hhfun]
    exact halasz_plancherel f hb α hα
  -- Step 3: rewrite the real integral as a `toReal` of a lintegral
  have hstep3 : (∫ τ : ℝ, hfun τ) =
      (∫⁻ τ : ℝ, ENNReal.ofReal (hfun τ)).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun τ => div_nonneg (sq_nonneg _) (sq_nonneg _))) hA
  have hsplit : (∫⁻ τ : ℝ, ENNReal.ofReal (hfun τ)) =
      (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)) +
      (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ)) :=
    (lintegral_add_compl _ measurableSet_Icc).symm
  -- Step 4: the middle piece
  have hmidpt : ∀ᵐ τ ∂(volume.restrict (Set.Icc (-T) T)),
      ENNReal.ofReal (hfun τ) ≤ ENNReal.ofReal Kmid * ENNReal.ofReal (Gfun τ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    rw [← ENNReal.ofReal_mul hKmid0.le]
    exact ENNReal.ofReal_le_ofReal (hptmid τ (abs_le.mpr ⟨hτ.1, hτ.2⟩))
  have hIntMid : (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)).toReal ≤ Kmid * (CP / α) := by
    have hchild : (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (Gfun τ)) ≤ ENNReal.ofReal (CP / α) :=
      (hCP f hf1 hb α hα hα1 T hT).1
    have hle : (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)) ≤
        (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal Kmid * ENNReal.ofReal (Gfun τ)) :=
      lintegral_mono_ae hmidpt
    have heq : (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal Kmid * ENNReal.ofReal (Gfun τ)) =
        ENNReal.ofReal Kmid * (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (Gfun τ)) :=
      lintegral_const_mul _ hGmeas
    have hbne : (∫⁻ τ in Set.Icc (-T) T,
        ENNReal.ofReal Kmid * ENNReal.ofReal (Gfun τ)) ≠ ⊤ := by
      rw [heq]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hchild)
    calc (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)).toReal
        ≤ (∫⁻ τ in Set.Icc (-T) T,
            ENNReal.ofReal Kmid * ENNReal.ofReal (Gfun τ)).toReal :=
          ENNReal.toReal_mono hbne hle
      _ = (ENNReal.ofReal Kmid *
            (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (Gfun τ))).toReal := by rw [heq]
      _ = Kmid * (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (Gfun τ)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hKmid0.le]
      _ ≤ Kmid * (CP / α) := by
          apply mul_le_mul_of_nonneg_left _ hKmid0.le
          calc (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (Gfun τ)).toReal
              ≤ (ENNReal.ofReal (CP / α)).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hchild
            _ = CP / α := ENNReal.toReal_ofReal (by positivity)
  -- Step 5: the two tails
  have hcset : (Set.Icc (-T) T)ᶜ = Set.Iio (-T) ∪ Set.Ioi T := by
    ext τ
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro h
      rcases lt_or_ge τ (-T) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (lt_of_not_ge (fun h2 => h ⟨h1, h2⟩))
    · rintro (h1 | h1) ⟨h2, h3⟩
      · exact absurd h2 (not_le.mpr h1)
      · exact absurd h3 (not_le.mpr h1)
  have hdisj : Disjoint (Set.Iio (-T)) (Set.Ioi T) := by
    rw [Set.disjoint_left]
    intro τ h1 h2
    simp only [Set.mem_Iio] at h1
    simp only [Set.mem_Ioi] at h2
    linarith
  have hunion : (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ)) =
      (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (hfun τ)) +
      (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (hfun τ)) := by
    rw [hcset]
    rw [lintegral_union measurableSet_Ioi hdisj]
  have htailNeg : (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (hfun τ)) ≤
      ENNReal.ofReal Ktail * (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) := by
    have hpt : ∀ᵐ τ ∂(volume.restrict (Set.Iio (-T))),
        ENNReal.ofReal (hfun τ) ≤ ENNReal.ofReal Ktail * ENNReal.ofReal (Gfun τ) := by
      filter_upwards [ae_restrict_mem measurableSet_Iio] with τ hτ
      rw [← ENNReal.ofReal_mul hKtail0.le]
      exact ENNReal.ofReal_le_ofReal (hpttail τ (by
        simp only [Set.mem_Iio] at hτ
        rw [abs_of_neg (by linarith : τ < 0)]
        linarith))
    exact (lintegral_mono_ae hpt).trans_eq (lintegral_const_mul _ hGmeas)
  have htailPos : (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (hfun τ)) ≤
      ENNReal.ofReal Ktail * (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ)) := by
    have hpt : ∀ᵐ τ ∂(volume.restrict (Set.Ioi T)),
        ENNReal.ofReal (hfun τ) ≤ ENNReal.ofReal Ktail * ENNReal.ofReal (Gfun τ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      rw [← ENNReal.ofReal_mul hKtail0.le]
      exact ENNReal.ofReal_le_ofReal (hpttail τ (by
        simp only [Set.mem_Ioi] at hτ
        rw [abs_of_pos (by linarith : 0 < τ)]
        linarith))
    exact (lintegral_mono_ae hpt).trans_eq (lintegral_const_mul _ hGmeas)
  have hIntTail : (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ)).toReal ≤
      Ktail * (CP / (α * T)) := by
    have hchild' : (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) +
        (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ)) ≤ ENNReal.ofReal (CP / (α * T)) := by
      rw [add_comm]
      exact (hCP f hf1 hb α hα hα1 T hT).2
    have hsum := add_le_add htailNeg htailPos
    rw [← mul_add] at hsum
    have hbne : ENNReal.ofReal Ktail *
        ((∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) +
         (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ))) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hchild')
    calc (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ)).toReal
        = ((∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (hfun τ)) +
            (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (hfun τ))).toReal := by rw [hunion]
      _ ≤ (ENNReal.ofReal Ktail *
            ((∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) +
             (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ)))).toReal :=
          ENNReal.toReal_mono hbne hsum
      _ = Ktail * ((∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) +
            (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ))).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hKtail0.le]
      _ ≤ Ktail * (CP / (α * T)) := by
          apply mul_le_mul_of_nonneg_left _ hKtail0.le
          calc ((∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (Gfun τ)) +
                (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (Gfun τ))).toReal
              ≤ (ENNReal.ofReal (CP / (α * T))).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hchild'
            _ = CP / (α * T) := ENNReal.toReal_ofReal (by positivity)
  -- Step 6: assemble
  have hfin : (∫ τ : ℝ, hfun τ) ≤ Kmid * (CP / α) + Ktail * (CP / (α * T)) := by
    rw [hstep3, hsplit]
    calc ((∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)) +
          (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ))).toReal
        ≤ (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (hfun τ)).toReal +
          (∫⁻ τ in (Set.Icc (-T) T)ᶜ, ENNReal.ofReal (hfun τ)).toReal := ENNReal.toReal_add_le
      _ ≤ Kmid * (CP / α) + Ktail * (CP / (α * T)) := add_le_add hIntMid hIntTail
  have hchain : (∫ t in (1 : ℝ)..x, ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) ≤
      (1 / (2 * Real.pi)) * (Kmid * (CP / α) + Ktail * (CP / (α * T))) := by
    calc (∫ t in (1 : ℝ)..x, ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α))
        ≤ (∫ t in Set.Ioi (0 : ℝ), ‖Kf f t‖ ^ 2 / t ^ (3 + 2 * α)) := hstep1
      _ = (1 / (2 * Real.pi)) * ∫ τ : ℝ, hfun τ := hstep2
      _ ≤ (1 / (2 * Real.pi)) * (Kmid * (CP / α) + Ktail * (CP / (α * T))) :=
          mul_le_mul_of_nonneg_left hfin (by positivity)
  refine hchain.trans ?_
  have hkey : (1 / (2 * Real.pi)) * (Kmid * (CP / α) + Ktail * (CP / (α * T))) =
      (CL ^ 2 * CP / (2 * Real.pi)) * (X / α + Z / (α * T)) := by
    rw [hKmid, hKtail, hX, hZ]
    field_simp
  rw [hkey]
  have hsum0 : 0 ≤ X / α + Z / (α * T) :=
    add_nonneg (div_nonneg hX0 hα.le) (div_nonneg hZ0 (by positivity))
  calc (CL ^ 2 * CP / (2 * Real.pi)) * (X / α + Z / (α * T))
      ≤ (CL ^ 2 * CP / (2 * Real.pi) + 1) * (X / α + Z / (α * T)) := by
        apply mul_le_mul_of_nonneg_right _ hsum0
        linarith
    _ = (CL ^ 2 * CP / (2 * Real.pi) + 1) *
          ((1 / α) * Real.exp (2 * Wsup f x α (T + 1)) + Real.exp (2 * Zrcp x) / (α * T)) := by
        rw [hX, hZ]
        ring

end Work.BMF.casdiv
