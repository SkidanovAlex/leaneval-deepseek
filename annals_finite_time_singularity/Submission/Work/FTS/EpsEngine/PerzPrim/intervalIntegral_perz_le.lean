import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.PerzTools.Main
import Submission.Work.FTS.EpsEngine.PerzTools.Exchange
import Submission.Work.FTS.EpsEngine.PerzTools.aesm_uncurry_restricted_theta
import Submission.Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.PerzPrim

theorem intervalIntegral_perz_le {α : ℝ} {k : ℕ} {T τ Cz z : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (hτ0 : 0 ≤ τ) (hτT : τ ∈ Set.Icc 0 T) (hT : 0 ≤ T)
    (hsm : ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmem : ∀ s ∈ Set.Icc 0 T, Work.Spaces.HkMem α k (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    (hperz : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (H s) z θ) ≤ Cz)
    (hCz : 0 ≤ Cz) (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.HkIntegrand α k
          (fun z θ => ∫ s in (0 : ℝ)..τ, H s z θ) z θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => ∫ s in (0 : ℝ)..τ, H s z θ) z θ) ≤ τ ^ 2 * Cz := by
  classical
  set G : ℝ → ℝ → ℝ := fun z θ => ∫ s in (0 : ℝ)..τ, H s z θ with hG
  have hT0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hsub : Set.uIoc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hτ0] at ht
    exact ⟨le_trans le_rfl ht.1.le, le_trans ht.2 hτT.2⟩
  have hcar : Work.FTS.EpsEngine.PerzTools.CarathTheta :=
    Work.FTS.EpsEngine.PerzTools.aesm_uncurry_restricted_theta
  have hexch : Work.FTS.EpsEngine.PerzTools.ExchMixed :=
    Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted
  have hAESM : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EpsEngine.PerzTools.aesm_slice_HkIntegrand_primitive
      (T := T) (a := (0 : ℝ)) (b := τ) (α := α) (k := k) (H := H)
      hcar hexch hT0 hτT hτ0 hsm hmeas hsup hz
  have hnn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k G z θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α k G z θ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k G 0 θ) = fun _ => (0 : ℝ) :=
      funext fun θ => Work.FTS.EpsEngine.PerzTools.HkIntegrand_fst_zero α k G θ
    rw [hzero]
    refine ⟨MeasureTheory.integrableOn_zero, ?_⟩
    simp only [MeasureTheory.integral_zero]
    exact mul_nonneg (sq_nonneg τ) hCz
  · -- the honest case `0 < z`
    have key : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ)
          ≤ ENNReal.ofReal τ * (∫⁻ s in Set.uIoc (0 : ℝ) τ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) := by
      have hIθ : MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))
          = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
      rw [← hIθ]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hq : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ⟩
      have hcv := Work.FTS.EpsEngine.PerzTools.cv_bound (T := T) (a := (0 : ℝ)) (b := τ)
        (α := α) (k := k) (H := H) hexch hT0 hτT hτ0 hsm hmeas hsup hq
      have hconv : (∫ s in (0 : ℝ)..τ, Work.Spaces.HkIntegrand α k (H s) z θ)
          = ∫ s in Set.uIoc (0 : ℝ) τ, Work.Spaces.HkIntegrand α k (H s) z θ := by
        rw [intervalIntegral.integral_of_le hτ0, Set.uIoc_of_le hτ0]
      calc ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ)
          ≤ ENNReal.ofReal ((τ - 0) * ∫ s in (0 : ℝ)..τ,
              Work.Spaces.HkIntegrand α k (H s) z θ) :=
            ENNReal.ofReal_le_ofReal hcv
        _ = ENNReal.ofReal τ * ENNReal.ofReal
              (∫ s in (0 : ℝ)..τ, Work.Spaces.HkIntegrand α k (H s) z θ) := by
            rw [sub_zero, ENNReal.ofReal_mul hτ0]
        _ ≤ ENNReal.ofReal τ * (∫⁻ s in Set.uIoc (0 : ℝ) τ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) := by
            refine mul_le_mul_right ?_ _
            rw [hconv]
            exact Work.FTS.EpsEngine.PerzTools.ofReal_integral_le_lintegral_ofReal
              (fun s => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ)
    have step2 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal τ
          * (∫⁻ s in Set.uIoc (0 : ℝ) τ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)))
        = ENNReal.ofReal τ * ∫⁻ s in Set.uIoc (0 : ℝ) τ,
            ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := by
      rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      symm
      refine MeasureTheory.lintegral_lintegral_swap
        (μ := MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) τ))
        (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun s θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) ?_
      have h3 := Work.FTS.EpsEngine.PerzTools.perz_aesm_HkIntegrand
        (T := T) (α := α) (k := k) (H := H) hcar hsm hmeas hzpos
      exact ((h3.mono_measure
        (MeasureTheory.Measure.prod_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl)
          le_rfl)).aemeasurable).ennreal_ofReal
    have step3 : (∫⁻ s in Set.uIoc (0 : ℝ) τ, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ))
        ≤ ∫⁻ s in Set.uIoc (0 : ℝ) τ, ENNReal.ofReal Cz := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
      have hsT : s ∈ Set.Icc (0 : ℝ) T := hsub hs
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hmem s hsT).1 z hz)
        (Filter.Eventually.of_forall
          (fun θ => Work.Spaces.HkIntegrand_nonneg α k (H s) z θ))]
      exact ENNReal.ofReal_le_ofReal (hperz s hsT)
    have step4 : (∫⁻ s in Set.uIoc (0 : ℝ) τ, ENNReal.ofReal Cz)
        = ENNReal.ofReal Cz * ENNReal.ofReal τ := by
      rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
        Real.volume_uIoc, sub_zero, abs_of_nonneg hτ0]
    have hzFin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
        ≤ ENNReal.ofReal (τ ^ 2 * Cz) := by
      calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k G z θ))
          ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal τ * (∫⁻ s in Set.uIoc (0 : ℝ) τ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ)) :=
            MeasureTheory.lintegral_mono_ae key
        _ = ENNReal.ofReal τ * ∫⁻ s in Set.uIoc (0 : ℝ) τ, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (H s) z θ) := step2
        _ ≤ ENNReal.ofReal τ * ∫⁻ s in Set.uIoc (0 : ℝ) τ, ENNReal.ofReal Cz :=
            mul_le_mul_right step3 _
        _ = ENNReal.ofReal τ * (ENNReal.ofReal Cz * ENNReal.ofReal τ) := by rw [step4]
        _ = ENNReal.ofReal (τ ^ 2 * Cz) := by
            rw [← ENNReal.ofReal_mul hCz, ← ENNReal.ofReal_mul hτ0]
            congr 1
            ring
    have hInt : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.HkIntegrand α k G z θ) Work.Spaces.Iθ :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hAESM
        (Filter.Eventually.of_forall hnn)).mp
        (ne_of_lt (lt_of_le_of_lt hzFin ENNReal.ofReal_lt_top))
    refine ⟨hInt, ?_⟩
    have h2 : ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k G z θ)
        ≤ ENNReal.ofReal (τ ^ 2 * Cz) := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall hnn)]
      exact hzFin
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg τ) hCz)).mp h2

end Work.FTS.EpsEngine.PerzPrim
