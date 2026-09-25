import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstMaximal_single

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal FourierTransform

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "clift" => Work.BourgainPlan.Thm52.circleLift

/-- **The threshold-free form of `mstMaximal_single`.**  `mstMaximal_single` returns its threshold
as an existential `exists s0`; its proof, however, uses the threshold `0`, so the estimate holds
for *every* level `s`.  The proof below is that of `mstMaximal_single`, transcribed verbatim (the
only change is the statement and the threshold). -/
lemma mstMaximal_all (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (l : ℕ) (hl : 1 ≤ l) (χ : ℝ)
    (hχ : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (hη1 : η 0 = 1)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, 0 ≤ s →
      ∀ (g : ℤ → ℂ) (hg : Memℓp g 2),
      ∀ (hA : ∀ n : ℕ, Lp ℂ ⊤ Work.BourgainPlan.Maximal.mstHaar),
      Work.BourgainPlan.Maximal.HasModel P P.natDegree χ η s hA →
      ∀ (hB : Lp ℂ ⊤ Work.BourgainPlan.Maximal.mstHaar),
      Work.BourgainPlan.Maximal.HasBump P.natDegree χ η s hB →
        (∫⁻ m : ℤ, (⨆ n : ℕ, ⨆ (_ : Work.BourgainPlan.Maximal.mstN₀' P s ≤ n), ‖Work.BourgainPlan.IonescuWainger.opMul (hA n) g hg m‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
          ≤ ENNReal.ofReal (C ^ 2)
            * (∫⁻ m : ℤ, ‖Work.BourgainPlan.IonescuWainger.opMul hB g hg m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
  obtain ⟨K, hKpos, T, hT⟩ := mstMS_curve_neg_le_hlMax P hd
  obtain ⟨C₂, hC₂pos, hC₂⟩ :=
    Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_fourierInv_rpow (p := 2)
      (by norm_num)
  obtain ⟨mS, hmS⟩ := Commons.Analysis.Fourier.exists_schwartzMap_eq_one_Icc (1 / 2) (by norm_num)
  obtain ⟨B, hBpos, hBdec⟩ := Commons.Analysis.Fourier.schwartzMap_decay_one_add_sq (𝓕⁻ mS)
  set wf : ℝ → ℂ := fun x => ((𝓕⁻ mS : SchwartzMap ℝ ℂ) : ℝ → ℂ) x with hwf
  have hwf_int : Integrable wf := by rw [hwf]; exact (𝓕⁻ mS).integrable
  have hwf_dec : ∀ z : ℝ, ‖wf z‖ ≤ B / (1 + z ^ 2) := fun z => by
    rw [hwf]; exact hBdec z
  have hwf_fourier : ∀ β : ℝ, β ∈ Set.Icc (-(1/2)) (1/2) → 𝓕 wf β = 1 := by
    intro β hβ
    have h𝓕 : 𝓕 wf = fun y : ℝ => ((mS : SchwartzMap ℝ ℂ) : ℝ → ℂ) y := by
      rw [hwf, SchwartzMap.fourierInv_coe]
      exact (SchwartzMap.continuous mS).fourier_fourierInv_eq mS.integrable
        (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 mS).integrable)
    rw [h𝓕]
    exact hmS β hβ
  refine ⟨C₂ * B * B * (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) + 1,
    by positivity, ?_⟩
  intro s _hs g hg hA hAmod hB hBmod
  set γ : Circ → ℂ := (Work.BourgainPlan.IonescuWainger.ftLp g hg : Circ → ℂ) with hγ
  set Ψc : Circ → ℂ := mstEta P.natDegree χ η s with hΨc
  set φc : ℕ → Circ → ℂ := fun n ξ => mstProf P (2^n) ξ * mstEta P.natDegree χ η s ξ with hφc
  set Wf : ℕ → ℝ → ℂ := fun n => clift (fun ξ => φc n ξ * γ ξ) with hWf
  set Wz : ℝ → ℂ := clift (fun ξ => Ψc ξ * γ ξ) with hWz
  have hMemΨ : MeasureTheory.MemLp Ψc ⊤ haarT := by
    rw [hΨc]; exact mstMS_memLp_mstEta P.natDegree χ η hηc s
  have hMemφ : ∀ n, MeasureTheory.MemLp (φc n) ⊤ haarT := by
    intro n; rw [hφc]; exact mstMS_memLp_modelSym P P.natDegree χ η hηc s (2^n)
  have hAae : ∀ n, ∀ᵐ ξ ∂haarT, (hA n : Circ → ℂ) ξ = φc n ξ := by
    intro n
    filter_upwards [hAmod n] with ξ h
    simpa [hφc] using h
  have hBae : ∀ᵐ ξ ∂haarT, (hB : Circ → ℂ) ξ = Ψc ξ := by
    filter_upwards [hBmod] with ξ h
    simpa [hΨc] using h
  have hAeq : ∀ n, hA n = (hMemφ n).toLp (φc n) := by
    intro n
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp (hMemφ n), hAae n] with ξ h1 h2
    rw [h1, h2]
  have hBeq : hB = hMemΨ.toLp Ψc := by
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hMemΨ, hBae] with ξ h1 h2
    rw [h1, h2]
  have hbridgeA : ∀ n m, Work.BourgainPlan.IonescuWainger.opMul (hA n) g hg m
      = FourierTransformInv.fourierInv (Wf n) (m : ℝ) := by
    intro n m
    rw [hAeq n]
    have h := Work.Maximal.mstMax_bridge (φc n) (hMemφ n) g hg m
    simpa [hWf, hγ] using h
  have hbridgeB : ∀ m, Work.BourgainPlan.IonescuWainger.opMul hB g hg m
      = FourierTransformInv.fourierInv Wz (m : ℝ) := by
    intro m
    rw [hBeq]
    have h := Work.Maximal.mstMax_bridge Ψc hMemΨ g hg m
    simpa [hWz, hγ] using h
  have hMemγ : MeasureTheory.MemLp γ 2 haarT := by
    rw [hγ]; exact MeasureTheory.Lp.memLp _
  have hMemΨγ : MeasureTheory.MemLp (fun ξ : Circ => Ψc ξ * γ ξ) 2 haarT :=
    MeasureTheory.MemLp.mul (p := ⊤) (q := 2) (r := 2) hMemΨ hMemγ
  have hMemφγ : ∀ n, MeasureTheory.MemLp (fun ξ : Circ => φc n ξ * γ ξ) 2 haarT := by
    intro n
    exact MeasureTheory.MemLp.mul (p := ⊤) (q := 2) (r := 2) (hMemφ n) hMemγ
  have hWf_int : ∀ n, Integrable (Wf n) := by
    intro n; rw [hWf]; exact mstMS_integrable_circleLift (hMemφγ n)
  have hWz_int : Integrable Wz := by rw [hWz]; exact mstMS_integrable_circleLift hMemΨγ
  have hWz_two : MeasureTheory.MemLp Wz 2 volume := by
    rw [hWz]; exact mstMS_memLp_two_circleLift hMemΨγ
  have hWz_one : MeasureTheory.MemLp Wz 1 volume := by
    rw [MeasureTheory.memLp_one_iff_integrable]; exact hWz_int
  set ψ : ℝ → ℝ≥0∞ := fun z => ‖FourierTransformInv.fourierInv Wz z‖ₑ with hψ
  have hψmeas : Measurable ψ := by
    rw [hψ]
    exact ((Commons.Analysis.Fourier.continuous_fourierInv_of_integrable Wz hWz_int).enorm).measurable
  have hpoint : ∀ x : ℝ, (⨆ n : ℕ, ‖FourierTransformInv.fourierInv (Wf n) x‖ₑ)
      ≤ ENNReal.ofReal K * ∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c) := by
    intro x
    refine iSup_le (fun n => ?_)
    have hfun : Wf n =ᵐ[volume] (fun y : ℝ => polyProfile P (2^n) (-y) * Wz y) := by
      have h := mstMS_circleLift_mul_mstProf P P.natDegree χ η s (2^n) γ
      simpa [hWf, hWz, hΨc, hφc, hγ] using h
    have hF : FourierTransformInv.fourierInv (Wf n) x
        = FourierTransformInv.fourierInv (fun y : ℝ => polyProfile P (2^n) (-y) * Wz y) x := by
      rw [Real.fourierInv_eq', Real.fourierInv_eq']
      refine integral_congr_ae ?_
      filter_upwards [hfun] with y hy
      rw [hy]
    rw [hF, Work.Maximal.mstMax_curve P (2^n) Wz hWz_int x]
    refine le_trans ?_ (hT n ψ hψmeas x)
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine le_trans (MeasureTheory.enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
    refine lintegral_congr (fun u => ?_)
    rw [hψ]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hident : ∫⁻ x : ℝ, ψ x ^ (2:ℝ) ∂volume
      = ∫⁻ m : ℤ, ‖Work.BourgainPlan.IonescuWainger.opMul hB g hg m‖ₑ ^ (2:ℝ)
          ∂Measure.count := by
    rw [hψ]
    rw [Commons.Analysis.Fourier.lintegral_norm_sq_fourierInv_real hWz_one hWz_two]
    rw [show (fun x : ℝ => ‖Wz x‖ₑ ^ (2:ℝ))
        = (fun x : ℝ => ‖clift (fun ξ : Circ => Ψc ξ * γ ξ) x‖ₑ ^ (2:ℝ)) from by rw [hWz]]
    rw [Work.Maximal.mstMax_lift_norm 2 (by norm_num) (fun ξ : Circ => Ψc ξ * γ ξ)]
    have hBsmul : (∫⁻ ξ : Circ, ‖(fun ξ : Circ => Ψc ξ * γ ξ) ξ‖ₑ ^ (2:ℝ) ∂haarT)
        = ∫⁻ ξ : Circ, ‖(hB • Work.BourgainPlan.IonescuWainger.ftLp g hg :
            MeasureTheory.Lp ℂ 2 haarT) ξ‖ₑ ^ (2:ℝ) ∂haarT := by
      refine lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) hB
        (Work.BourgainPlan.IonescuWainger.ftLp g hg), hBae] with ξ h1 h2
      rw [h1]
      simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, h2, hγ]
    rw [hBsmul, ← mstMS_ofReal_norm_sq_eq_lintegral
      (hB • Work.BourgainPlan.IonescuWainger.ftLp g hg)]
    rw [show (hB • Work.BourgainPlan.IonescuWainger.ftLp g hg : MeasureTheory.Lp ℂ 2 haarT)
        = Work.BourgainPlan.IonescuWainger.ftLp
            (Work.BourgainPlan.IonescuWainger.opMul hB g hg)
            (Work.BourgainPlan.IonescuWainger.opMul_memℓp hB g hg) from
      (Work.BourgainPlan.IonescuWainger.ftLp_opMul hB g hg).symm]
    rw [← lintegral_count_enorm_sq (Work.BourgainPlan.IonescuWainger.opMul hB g hg)
      (Work.BourgainPlan.IonescuWainger.opMul_memℓp hB g hg)]
  have hψfin : ∫⁻ x : ℝ, ψ x ^ (2:ℝ) ∂volume < ⊤ := by
    rw [hident, lintegral_count_enorm_sq (Work.BourgainPlan.IonescuWainger.opMul hB g hg)
      (Work.BourgainPlan.IonescuWainger.opMul_memℓp hB g hg)]
    exact ENNReal.ofReal_lt_top
  have hhl : ∫⁻ x : ℝ, (Commons.Analysis.Maximal.hlMax ψ x) ^ (2:ℝ) ∂volume
      ≤ ENNReal.ofReal 32 * ∫⁻ x : ℝ, ψ x ^ (2:ℝ) ∂volume := by
    have h := Commons.Analysis.Maximal.lintegral_rpow_hlMax_le (ψ := ψ) hψmeas
      (fun x => by rw [hψ]; exact ENNReal.coe_ne_top) (p := 2) (by norm_num) hψfin
    have hc : (8 * (2:ℝ) * 2 ^ ((2:ℝ) - 1) / ((2:ℝ) - 1)) = 32 := by norm_num
    rw [hc] at h
    exact h
  have hreal_const : ∫⁻ x : ℝ,
        (ENNReal.ofReal K * ∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ)
        ∂volume
      = ENNReal.ofReal (K * K) *
        ∫⁻ x : ℝ, (∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ) ∂volume := by
    have hpt : ∀ x : ℝ,
        (ENNReal.ofReal K * ∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ)
        = ENNReal.ofReal (K * K) *
          (∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ) := by
      intro x
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
        ENNReal.ofReal_rpow_of_nonneg hKpos.le (by norm_num : (0:ℝ) ≤ 2), Real.rpow_two, pow_two]
    rw [lintegral_congr hpt,
      lintegral_const_mul' (ENNReal.ofReal (K * K)) _ ENNReal.ofReal_ne_top]
  have hreal_sum : ∫⁻ x : ℝ, (∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ)
        ∂volume
      ≤ (2 * (T.card : ℝ≥0∞)) *
        ((T.card : ℝ≥0∞) * ∫⁻ x : ℝ, (Commons.Analysis.Maximal.hlMax ψ x) ^ (2:ℝ)
          ∂volume) := by
    calc ∫⁻ x : ℝ, (∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ) ∂volume
        ≤ ∫⁻ x : ℝ, (2 * (T.card : ℝ≥0∞)) *
            (∑ c ∈ T, (Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ)) ∂volume :=
          lintegral_mono (fun x => mstMS_sq_sum_le T
            (fun c z => Commons.Analysis.Maximal.hlMax ψ (z - c)) x)
      _ = (2 * (T.card : ℝ≥0∞)) *
            ∫⁻ x : ℝ, ∑ c ∈ T, (Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ)
              ∂volume :=
          lintegral_const_mul' (2 * (T.card : ℝ≥0∞)) _
            (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))
      _ = (2 * (T.card : ℝ≥0∞)) *
            ∑ c ∈ T, ∫⁻ x : ℝ, (Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ)
              ∂volume := by
          rw [lintegral_finsetSum]
          intro c _
          exact ((Commons.Analysis.Maximal.measurable_hlMax ψ).comp
            (measurable_id.sub measurable_const)).pow_const 2
      _ = (2 * (T.card : ℝ≥0∞)) *
            ∑ c ∈ T, ∫⁻ x : ℝ, (Commons.Analysis.Maximal.hlMax ψ x) ^ (2:ℝ) ∂volume := by
          congr 1
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [show (fun x : ℝ => (Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ))
              = (fun x : ℝ => (Commons.Analysis.Maximal.hlMax ψ (x + (-c))) ^ (2:ℝ)) from by
                funext x; rw [sub_eq_add_neg]]
          rw [lintegral_add_right_eq_self
            (fun x : ℝ => (Commons.Analysis.Maximal.hlMax ψ x) ^ (2:ℝ)) (-c)]
      _ = (2 * (T.card : ℝ≥0∞)) *
            ((T.card : ℝ≥0∞) * ∫⁻ x : ℝ, (Commons.Analysis.Maximal.hlMax ψ x) ^ (2:ℝ)
              ∂volume) := by
          congr 1
          rw [Finset.sum_const, nsmul_eq_mul]
  have hconst2 : ENNReal.ofReal (K * K) *
      ((2 * (T.card : ℝ≥0∞)) * ((T.card : ℝ≥0∞) * (ENNReal.ofReal 32 *
        ∫⁻ x : ℝ, ψ x ^ (2:ℝ) ∂volume)))
      = ENNReal.ofReal (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) *
        ∫⁻ x : ℝ, ψ x ^ (2:ℝ) ∂volume := by
    rw [show (T.card : ℝ≥0∞) = ENNReal.ofReal (T.card : ℝ) from
        (ENNReal.ofReal_natCast (T.card)).symm,
      show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) from by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
  have hreal_chain : ∫⁻ x : ℝ, (⨆ n : ℕ, ‖FourierTransformInv.fourierInv (Wf n) x‖ₑ)
        ^ (2:ℝ) ∂volume
      ≤ ENNReal.ofReal (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) *
        ∫⁻ m : ℤ, ‖Work.BourgainPlan.IonescuWainger.opMul hB g hg m‖ₑ ^ (2:ℝ)
          ∂Measure.count := by
    calc ∫⁻ x : ℝ, (⨆ n : ℕ, ‖FourierTransformInv.fourierInv (Wf n) x‖ₑ) ^ (2:ℝ) ∂volume
        ≤ ∫⁻ x : ℝ, (ENNReal.ofReal K *
            ∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ) ∂volume :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow (hpoint x) (by norm_num))
      _ = ENNReal.ofReal (K * K) *
            ∫⁻ x : ℝ, (∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c)) ^ (2:ℝ)
              ∂volume := hreal_const
      _ ≤ ENNReal.ofReal (K * K) *
            ((2 * (T.card : ℝ≥0∞)) * ((T.card : ℝ≥0∞) * (ENNReal.ofReal 32 *
              ∫⁻ x : ℝ, ψ x ^ (2:ℝ) ∂volume))) := by
          refine mul_le_mul_right ?_ (ENNReal.ofReal (K * K))
          refine le_trans hreal_sum ?_
          refine mul_le_mul_right ?_ (2 * (T.card : ℝ≥0∞))
          exact mul_le_mul_right hhl (T.card : ℝ≥0∞)
      _ = ENNReal.ofReal (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) *
            ∫⁻ x : ℝ, ψ x ^ (2:ℝ) ∂volume := hconst2
      _ = ENNReal.ofReal (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) *
            ∫⁻ m : ℤ, ‖Work.BourgainPlan.IonescuWainger.opMul hB g hg m‖ₑ ^ (2:ℝ)
              ∂Measure.count := by rw [hident]
  have hwf_one : ∀ (j : ℕ) (β : ℝ), Wf j β ≠ 0 → 𝓕 wf β = 1 := by
    intro j β hβ
    refine hwf_fourier β ?_
    by_contra hc
    exact hβ (by
      rw [hWf]
      exact Work.BourgainPlan.Thm52.circleLift_of_notMem
        (fun hmem => hc (Set.Ioc_subset_Icc_self hmem)))
  have hlat := hC₂ Wf wf B hWf_int hwf_int hBpos hwf_dec hwf_one
  have hstep1 : ∫⁻ m : ℤ, (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
        ‖Work.BourgainPlan.IonescuWainger.opMul (hA n) g hg m‖ₑ) ^ (2:ℝ) ∂Measure.count
      = ∫⁻ m : ℤ, (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
        ‖FourierTransformInv.fourierInv (Wf n) (m : ℝ)‖ₑ) ^ (2:ℝ) ∂Measure.count := by
    refine lintegral_congr (fun m => ?_)
    congr 1
    exact iSup_congr (fun n => iSup_congr (fun _ => by rw [hbridgeA n m]))
  have hstep2 : ∫⁻ m : ℤ, (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
        ‖FourierTransformInv.fourierInv (Wf n) (m : ℝ)‖ₑ) ^ (2:ℝ) ∂Measure.count
      ≤ ∫⁻ m : ℤ, (⨆ n : ℕ, ‖FourierTransformInv.fourierInv (Wf n) (m : ℝ)‖ₑ) ^ (2:ℝ)
          ∂Measure.count := by
    refine lintegral_mono (fun m => ?_)
    refine ENNReal.rpow_le_rpow (iSup_le (fun n => iSup_le (fun _ => ?_))) (by norm_num)
    exact le_iSup (fun n => ‖FourierTransformInv.fourierInv (Wf n) (m : ℝ)‖ₑ) n
  have hmain : ∫⁻ m : ℤ, (⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
        ‖Work.BourgainPlan.IonescuWainger.opMul (hA n) g hg m‖ₑ) ^ (2:ℝ) ∂Measure.count
      ≤ ENNReal.ofReal (C₂ * B * B) *
        (ENNReal.ofReal (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) *
          ∫⁻ m : ℤ, ‖Work.BourgainPlan.IonescuWainger.opMul hB g hg m‖ₑ ^ (2:ℝ)
            ∂Measure.count) := by
    rw [hstep1]
    refine le_trans hstep2 ?_
    refine le_trans hlat ?_
    rw [show ENNReal.ofReal (C₂ * B ^ (2:ℝ)) = ENNReal.ofReal (C₂ * B * B) from by
      congr 1
      rw [Real.rpow_two, pow_two]
      ring]
    exact mul_le_mul_right hreal_chain (ENNReal.ofReal (C₂ * B * B))
  have hfinal2 : ENNReal.ofReal (C₂ * B * B) *
      (ENNReal.ofReal (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) *
        ∫⁻ m : ℤ, ‖Work.BourgainPlan.IonescuWainger.opMul hB g hg m‖ₑ ^ (2:ℝ)
          ∂Measure.count)
      ≤ ENNReal.ofReal ((C₂ * B * B * (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) + 1) ^ 2) *
        ∫⁻ m : ℤ, ‖Work.BourgainPlan.IonescuWainger.opMul hB g hg m‖ₑ ^ (2:ℝ)
          ∂Measure.count := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      show (C₂ * B * B * (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) + 1) ^ 2
          = (C₂ * B * B * (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) + 1) *
            (C₂ * B * B * (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) + 1) from by
        first | (rw [Real.rpow_two]; ring) | ring]
    refine mul_le_mul_left ?_ (∫⁻ m : ℤ, ‖Work.BourgainPlan.IonescuWainger.opMul hB g hg m‖ₑ ^ (2:ℝ) ∂Measure.count)
    refine ENNReal.ofReal_le_ofReal ?_
    have hx1 : (1:ℝ) ≤ C₂ * B * B * (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) + 1 := by
      have h0 : 0 ≤ C₂ * B * B * (K * K * (2 * (T.card : ℝ)) * (T.card : ℝ) * 32) := by
        positivity
      linarith
    nlinarith [hx1]
  exact le_trans hmain hfinal2

end

end Work.BourgainPlan.Maximal
