import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.BumpConcrete

namespace Work.IonescuWainger

open MeasureTheory
open scoped BigOperators ENNReal

local notation "CircT" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-- The norm of a real number coerced to `ℂ`. -/
private lemma norm_ofReal_coe (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r

theorem exists_flat_bump {ε η : ℝ} (hε : 0 < ε) (hεη : ε < η) (hη : η < 1 / 2) :
    ∃ (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (C : ℝ), 0 ≤ C ∧
      MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)) ∧
      (∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ‖φ ξ‖ ≤ 1) ∧
      (∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, η < ‖ξ‖ → φ ξ = 0) ∧
      (∀ ξ : Work.BourgainPlan.IonescuWainger.Circle, ‖ξ‖ ≤ ε → φ ξ = 1) ∧
      (∀ m : ℤ, ‖∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1))‖
        ≤ C * η / (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2)) := by
  have hηpos : 0 < η := lt_trans hε hεη
  -- the Schwartz plateau on `ℝ`
  let β : ContDiffBump (0 : ℝ) := ⟨ε, η, hε, hεη⟩
  have hcpt : HasCompactSupport (fun t : ℝ => (β t : ℂ)) :=
    β.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (β t : ℂ)) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β := β.contDiff
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t : ℂ)) :=
      Complex.ofRealCLM.contDiff
    exact h2.comp h1
  let F : SchwartzMap ℝ ℂ := hcpt.toSchwartzMap hcd
  have hcoe : ∀ x : ℝ, (F : ℝ → ℂ) x = ((β x : ℝ) : ℂ) := fun x => rfl
  have hF1 : ∀ x : ℝ, |x| ≤ ε → (F : ℝ → ℂ) x = 1 := by
    intro x hx
    have hb : ((β x : ℝ) : ℂ) = 1 := by
      rw [β.one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)]
      norm_num
    simpa [hcoe x] using hb
  have hF0 : ∀ x : ℝ, η < |x| → (F : ℝ → ℂ) x = 0 := by
    intro x hx
    have hb : ((β x : ℝ) : ℂ) = 0 := by
      rw [β.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; linarith [le_abs_self x])]
      norm_num
    simpa [hcoe x] using hb
  have hFbound : ∀ x : ℝ, ‖(F : ℝ → ℂ) x‖ ≤ 1 := by
    intro x
    have hb : ‖((β x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_ofReal_coe (β x), abs_of_nonneg β.nonneg]
      exact β.le_one
    simpa [hcoe x] using hb
  -- the lift to the circle
  let φ : CircT → ℂ := AddCircle.liftIoc (1 : ℝ) (-1 / 2) (F : ℝ → ℂ)
  have hrep_mem : ∀ ξ : CircT,
      (AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ : ℝ) ∈ Set.Ioc (-1 / 2) ((-1 / 2 : ℝ) + 1) :=
    fun ξ => (AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ).2
  have hrep_mem' : ∀ ξ : CircT,
      (AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ : ℝ) ∈ Set.Ioc (-1 / 2) (1 / 2) := by
    intro ξ
    obtain ⟨h1, h2⟩ := Set.mem_Ioc.mp (hrep_mem ξ)
    exact Set.mem_Ioc.mpr ⟨h1, by linarith⟩
  have hφcoe : ∀ ξ : CircT,
      φ ξ = (F : ℝ → ℂ) (AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ : ℝ) := by
    intro ξ
    have key := AddCircle.liftIoc_coe_apply (p := (1 : ℝ)) (a := (-1 / 2 : ℝ))
      (f := (F : ℝ → ℂ)) (hrep_mem ξ)
    rw [AddCircle.coe_equivIoc] at key
    exact key
  have hnorm : ∀ ξ : CircT,
      ‖ξ‖ = |(AddCircle.equivIoc (1 : ℝ) (-1 / 2) ξ : ℝ)| := by
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
      rw [hF0 (-1 / 2) (by rw [abs_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)]; linarith [hη]),
        hF0 (1 / 2) (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith [hη])]
    · exact (F.continuous).continuousOn
  have hb1 : ∀ ξ : CircT, ‖φ ξ‖ ≤ 1 := by
    intro ξ; rw [hφcoe ξ]; exact hFbound _
  have hb2 : ∀ ξ : CircT, η < ‖ξ‖ → φ ξ = 0 := by
    intro ξ hξ
    rw [hφcoe ξ]
    exact hF0 _ (by rw [hnorm ξ] at hξ; exact hξ)
  have hb3 : ∀ ξ : CircT, ‖ξ‖ ≤ ε → φ ξ = 1 := by
    intro ξ hξ
    rw [hφcoe ξ]
    exact hF1 _ (by rw [← hnorm ξ]; exact hξ)
  have hmem : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)) :=
    MemLp.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall hb1)
  -- Fourier decay of `F`
  obtain ⟨Cf, hCf0, hCfdecay⟩ := Work.BourgainPlan.IonescuWainger.schwartz_fourier_decay F
  refine ⟨φ, Cf / η, by positivity, hmem, hb1, hb2, hb3, ?_⟩
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
          Complex.exp (↑(-2 * Real.pi * x * (m : ℝ)) * Complex.I) * (F : ℝ → ℂ) x := by
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
    have hx2 : x ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1) := by
      have hx' : x ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2) := by
        rw [Set.uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hx
        exact hx
      rw [show (1 / 2 : ℝ) = (-1 / 2) + 1 by norm_num] at hx'
      exact hx'
    have hφx : φ (↑x) = (F : ℝ → ℂ) x := AddCircle.liftIoc_coe_apply hx2
    rw [hφx, smul_eq_mul, fourier_coe_apply]
    congr 1
    congr 1
    push_cast
    ring
  have hsupp : (∫ x in (-1 / 2)..(1 / 2),
        Complex.exp (↑(-2 * Real.pi * x * (m : ℝ)) * Complex.I) * (F : ℝ → ℂ) x)
      = ∫ x, Complex.exp (↑(-2 * Real.pi * x * (m : ℝ)) * Complex.I) * (F : ℝ → ℂ) x := by
    refine intervalIntegral.integral_eq_integral_of_support_subset ?_
    intro t ht
    rw [Function.mem_support] at ht
    have hFt : (F : ℝ → ℂ) t ≠ 0 := fun h0 => ht (by rw [h0, mul_zero])
    have hle : |t| ≤ η := by
      by_contra hcon
      exact hFt (hF0 t (not_le.mp hcon))
    have h2 := abs_le.mp hle
    exact ⟨by linarith [h2.1, hη], by linarith [h2.2, hη]⟩
  have hfourierint : (∫ x, Complex.exp (↑(-2 * Real.pi * x * (m : ℝ)) * Complex.I) * (F : ℝ → ℂ) x)
      = FourierTransform.fourier (F : ℝ → ℂ) (m : ℝ) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [smul_eq_mul]
  have hFourier : (∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)))
      = FourierTransform.fourier (F : ℝ → ℂ) (m : ℝ) :=
    hcoeff_eq.trans (hinterval.trans (hcongr.trans (hsupp.trans hfourierint)))
  rw [hFourier]
  rw [div_mul_cancel₀ Cf (ne_of_gt hηpos)]
  have hdec := hCfdecay (m : ℝ)
  have hApos : (0 : ℝ) < (1 + (m : ℝ) ^ 2) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hBpos : (0 : ℝ) < (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hBA : (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2)
      ≤ (1 + (m : ℝ) ^ 2) ^ ((3 : ℝ) / 2) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    have h1 : η ^ 2 ≤ 1 := by nlinarith [hη, hηpos]
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg (m : ℝ))]
  have h1 : ‖(FourierTransform.fourier (F : ℝ → ℂ)) (m : ℝ)‖
      ≤ Cf / (1 + (m : ℝ) ^ 2) ^ ((3 : ℝ) / 2) := by
    rw [le_div_iff₀ hApos, mul_comm]
    exact hdec
  have h2 : Cf / (1 + (m : ℝ) ^ 2) ^ ((3 : ℝ) / 2)
      ≤ Cf / (1 + (η * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2) :=
    div_le_div_of_nonneg_left hCf0 hBpos hBA
  exact le_trans h1 h2

end

end Work.IonescuWainger
