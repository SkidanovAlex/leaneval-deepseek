import Mathlib
import Submission.Work.IonescuWainger.exists_flat_bump

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped BigOperators ENNReal

local notation "CircT" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-- The Fourier transform of a horizontal dilation on the line: for `η > 0`,
`𝓕 (x ↦ f (x/η)) (m) = η · (𝓕 f) (η m)`.  (Change of variables `x = η t`; the statement holds
for arbitrary `f` thanks to the convention that the integral of a non-integrable function is
`0`.) -/
lemma fourier_fun_div_eq (f : ℝ → ℂ) {η : ℝ} (hη : 0 < η) (m : ℝ) :
    FourierTransform.fourier (fun x : ℝ => f (x / η)) m
      = η * FourierTransform.fourier f (η * m) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  set G : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * m) * Complex.I) • f (x / η)
    with hG
  set H : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * (η * m)) * Complex.I) • f x
    with hH
  have hGH : ∀ x : ℝ, G (η * x) = H x := by
    intro x
    simp only [hG, hH, smul_eq_mul]
    rw [mul_div_cancel_left₀ _ (ne_of_gt hη)]
    congr 1
    congr 1
    push_cast
    ring
  have hcomp : (∫ x : ℝ, G (η * x)) = |η⁻¹| • ∫ y : ℝ, G y :=
    MeasureTheory.Measure.integral_comp_mul_left G η
  rw [abs_of_pos (inv_pos.mpr hη)] at hcomp
  have key : (∫ y : ℝ, G y) = η • ∫ x : ℝ, G (η * x) := by
    rw [hcomp, smul_smul, mul_inv_cancel₀ (ne_of_gt hη), one_smul]
  have hGHint : (∫ x : ℝ, G (η * x)) = ∫ x : ℝ, H x :=
    integral_congr_ae (ae_of_all _ hGH)
  calc (∫ x : ℝ, G x) = η • ∫ x : ℝ, G (η * x) := key
    _ = η • ∫ x : ℝ, H x := by rw [hGHint]
    _ = η * ∫ x : ℝ, H x := by rw [Complex.real_smul]

/-- A flat-top bump on the circle with a **uniform** coefficient-decay constant: for every `0 < ε ≤ η/2`, `η ≤ 1/2` there is a circle function `φ` that is `1` on the ball of radius `ε`, supported in the ball of radius `η`, bounded by `1`, and whose Fourier coefficients decay like `Cφ · η · (1 + (η m)^2)^{-3/2}` with a constant `Cφ` independent of `ε` and `η`. -/
theorem exists_flat_bump_uniform :
    ∃ Cφ : ℝ, 0 < Cφ ∧ ∀ ε η : ℝ, 0 < ε → 2 * ε ≤ η → η ≤ 1 / 2 →
      ∃ φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ,
        MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)) ∧
        (∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ‖φ ξ‖ ≤ 1) ∧
        (∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, η < ‖ξ‖ → φ ξ = 0) ∧
        (∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ‖ξ‖ ≤ ε → φ ξ = 1) ∧
        (∀ m : ℤ, ‖∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1))‖
          ≤ Cφ * η / (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2)) := by
  -- a fixed smooth bump profile on the line, equal to `1` on `[-1/2, 1/2]` and supported in `(-1,1)`
  let β : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let base : ℝ → ℂ := fun t => ((β t : ℝ) : ℂ)
  have hbase_cont : Continuous base := by
    simpa [base, Function.comp_def] using (Complex.ofRealCLM.continuous.comp β.continuous)
  have hbase_cpt : HasCompactSupport base :=
    β.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hbase_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) base := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => β t) := β.contDiff
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t : ℂ)) :=
      Complex.ofRealCLM.contDiff
    simpa [base, Function.comp_def] using h2.comp h1
  let Base : SchwartzMap ℝ ℂ := hbase_cpt.toSchwartzMap hbase_cd
  obtain ⟨Cψ, hCψ0, hCψdecay⟩ := Work.BourgainPlan.IonescuWainger.schwartz_fourier_decay Base
  have hBft : ∀ u : ℝ, FourierTransform.fourier Base u = FourierTransform.fourier base u :=
    fun u => rfl
  have hbase_norm : ∀ t : ℝ, ‖base t‖ ≤ 1 := by
    intro t
    change ‖((β t : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
      abs_of_nonneg β.nonneg]
    exact β.le_one
  refine ⟨Cψ + 1, by positivity, ?_⟩
  intro ε η hε h2εη hη
  have hηpos : 0 < η := by linarith
  let Ffun : ℝ → ℂ := fun x => base (x / η)
  have hcontF : Continuous Ffun := hbase_cont.comp (continuous_id.div_const η)
  -- the plateau and the support of the scaled profile
  have hFzero : ∀ x : ℝ, η ≤ |x| → Ffun x = 0 := by
    intro x hx
    have hxabs : (1 : ℝ) ≤ |x / η| := by
      rw [abs_div, abs_of_pos hηpos, le_div_iff₀ hηpos]
      linarith
    have hb : β (x / η) = 0 := β.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hxabs)
    change ((β (x / η) : ℝ) : ℂ) = 0
    rw [hb]
    norm_num
  have hFone : ∀ x : ℝ, |x| ≤ ε → Ffun x = 1 := by
    intro x hx
    have hxabs : |x / η| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hηpos, div_le_iff₀ hηpos]
      linarith
    have hb : β (x / η) = 1 := β.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hxabs)
    change ((β (x / η) : ℝ) : ℂ) = 1
    rw [hb]
    norm_num
  -- lift to the circle
  let φ : CircT → ℂ := AddCircle.liftIoc (1 : ℝ) (-1 / 2) Ffun
  have hrep_mem : ∀ ξ : CircT,
      (AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ : ℝ) ∈ Set.Ioc (-1 / 2) ((-1 / 2 : ℝ) + 1) :=
    fun ξ => (AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ).2
  have hrep_mem' : ∀ ξ : CircT,
      (AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ : ℝ) ∈ Set.Ioc (-1 / 2) (1 / 2) := by
    intro ξ
    obtain ⟨h1, h2⟩ := Set.mem_Ioc.mp (hrep_mem ξ)
    exact Set.mem_Ioc.mpr ⟨h1, by linarith⟩
  have hφcoe : ∀ ξ : CircT, φ ξ = Ffun (AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ : ℝ) := by
    intro ξ
    have key := AddCircle.liftIoc_coe_apply (p := (1 : ℝ)) (a := (-1 / 2 : ℝ))
      (f := Ffun) (hrep_mem ξ)
    rw [AddCircle.coe_equivIoc] at key
    exact key
  have hnorm : ∀ ξ : CircT, ‖ξ‖ = |(AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ : ℝ)| := by
    intro ξ
    have hmain : ‖(↑(↑(AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ) : ℝ) : CircT)‖
        = |(AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ : ℝ)| :=
      (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).mpr
        (by rw [abs_one]
            exact abs_le.mpr ⟨by linarith [(hrep_mem' ξ).1], (hrep_mem' ξ).2⟩)
    rw [AddCircle.coe_equivIoc] at hmain
    exact hmain
  have hcont : Continuous φ := by
    refine AddCircle.liftIoc_continuous ?_ ?_
    · rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
      rw [hFzero (-1 / 2) (by rw [abs_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)]; linarith),
          hFzero (1 / 2) (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith)]
    · exact hcontF.continuousOn
  have hb1 : ∀ ξ : CircT, ‖φ ξ‖ ≤ 1 := by
    intro ξ; rw [hφcoe ξ]; exact hbase_norm _
  have hb2 : ∀ ξ : CircT, η < ‖ξ‖ → φ ξ = 0 := by
    intro ξ hξ
    rw [hφcoe ξ]
    exact hFzero _ (by rw [← hnorm ξ]; exact le_of_lt hξ)
  have hb3 : ∀ ξ : CircT, ‖ξ‖ ≤ ε → φ ξ = 1 := by
    intro ξ hξ
    rw [hφcoe ξ]
    exact hFone _ (by rw [← hnorm ξ]; exact hξ)
  have hmem : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)) :=
    MemLp.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb1)
  -- the Fourier coefficients equal the Fourier transform of the scaled profile
  have hFourier : ∀ m : ℤ,
      (∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)))
        = FourierTransform.fourier Ffun (m : ℝ) := by
    intro m
    have hcoeff_eq : (∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)))
        = fourierCoeff φ m := by
      rw [fourierCoeff]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      dsimp only
      rw [fourier_neg, smul_eq_mul, Complex.star_def]
      ring
    have hinterval : fourierCoeff φ m
        = ∫ x in (-1 / 2)..(1 / 2), (fourier (-m) : CircT → ℂ) (↑x) • φ (↑x) := by
      rw [fourierCoeff_eq_intervalIntegral φ m (-1 / 2)]
      rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
      simp
    have hcongr : (∫ x in (-1 / 2)..(1 / 2), (fourier (-m) : CircT → ℂ) (↑x) • φ (↑x))
        = ∫ x in (-1 / 2)..(1 / 2),
            Complex.exp (↑(-2 * Real.pi * x * (m : ℝ)) * Complex.I) * Ffun x := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
      have hx2 : x ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1) := by
        have hx' : x ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) := by
          rw [Set.uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hx
          exact hx
        rw [show (1 / 2 : ℝ) = (-1 / 2) + 1 by norm_num] at hx'
        exact hx'
      have hφx : φ (↑x) = Ffun x := AddCircle.liftIoc_coe_apply hx2
      rw [hφx, smul_eq_mul, fourier_coe_apply]
      congr 1
      congr 1
      push_cast
      ring
    have hsupp : (∫ x in (-1 / 2)..(1 / 2),
          Complex.exp (↑(-2 * Real.pi * x * (m : ℝ)) * Complex.I) * Ffun x)
        = ∫ x, Complex.exp (↑(-2 * Real.pi * x * (m : ℝ)) * Complex.I) * Ffun x := by
      refine intervalIntegral.integral_eq_integral_of_support_subset ?_
      intro t ht
      rw [Function.mem_support] at ht
      have hFt : Ffun t ≠ 0 := fun h0 => ht (by rw [h0, mul_zero])
      have hle : |t| < η := by
        by_contra hcon
        exact hFt (hFzero t (not_lt.mp hcon))
      have h2 := abs_lt.mp hle
      exact ⟨by linarith [h2.1, hη], by linarith [h2.2, hη]⟩
    have hfourierint : (∫ x, Complex.exp (↑(-2 * Real.pi * x * (m : ℝ)) * Complex.I) * Ffun x)
        = FourierTransform.fourier Ffun (m : ℝ) := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      refine integral_congr_ae (ae_of_all _ fun v => ?_)
      simp only [smul_eq_mul]
    exact hcoeff_eq.trans (hinterval.trans (hcongr.trans (hsupp.trans hfourierint)))
  refine ⟨φ, hmem, hb1, hb2, hb3, ?_⟩
  intro m
  rw [hFourier m]
  have hstep : FourierTransform.fourier Ffun (m : ℝ)
      = η * FourierTransform.fourier base (η * (m : ℝ)) :=
    fourier_fun_div_eq base hηpos (m : ℝ)
  rw [hstep]
  have hden : (0 : ℝ) < (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hdec : ‖FourierTransform.fourier base (η * (m : ℝ))‖
      ≤ Cψ / (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2) := by
    rw [le_div_iff₀ hden, mul_comm]
    have h := hCψdecay (η * (m : ℝ))
    rw [hBft] at h
    exact h
  have hnm : ‖(η : ℂ) * FourierTransform.fourier base (η * (m : ℝ))‖
      = η * ‖FourierTransform.fourier base (η * (m : ℝ))‖ := by
    rw [norm_mul]
    congr 1
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
      abs_of_pos hηpos]
  calc ‖η * FourierTransform.fourier base (η * (m : ℝ))‖
      = η * ‖FourierTransform.fourier base (η * (m : ℝ))‖ := hnm
    _ ≤ η * (Cψ / (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hdec hηpos.le
    _ = Cψ * η / (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2) := by ring
    _ ≤ (Cψ + 1) * η / (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2) := by
        apply div_le_div_of_nonneg_right _ hden.le
        nlinarith [hCψ0, hηpos.le]

end

end Work.BourgainPlan.Maximal
