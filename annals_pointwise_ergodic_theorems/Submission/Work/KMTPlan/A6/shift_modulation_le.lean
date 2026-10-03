import Mathlib
import Submission.Work.KMTPlan.A6.ShiftModulation
import Submission.Work.KMTPlan.A6.BandDecomp
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

open MeasureTheory
open scoped BigOperators ENNReal
open Work.Analysis.IonescuWainger

namespace Work.KMTPlan.A6

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## The character as a function of its argument

`fourier n` is the character `x ↦ e(n x)` of `AddCircle T`; in particular it is multiplicative in
its argument.  We record this together with the trivial pointwise bound. -/

theorem shiftMod_fourier_add_arg {T : ℝ} (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

theorem shiftMod_norm_fourier_apply {T : ℝ} (n : ℤ) (x : AddCircle T) :
    ‖fourier n x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-! ## The single-frequency difference bound -/

theorem shiftMod_norm_fourier_sub_le (K : ℤ) (m : ℤ) {ξ α : Circ} {Φ : Circ → ℂ}
    (hsupp : SupportedInArc K Φ) (h : Φ (ξ - α) ≠ 0) :
    ‖fourier (T := 1) (-m) ξ - fourier (T := 1) (-m) α‖
      ≤ 2 * Real.pi * |(m : ℝ)| * (2 : ℝ) ^ K := by
  obtain ⟨θ, hθmem, hθ⟩ := hsupp (ξ - α) h
  rw [realArc, Set.mem_Icc] at hθmem
  have hξ : ξ = α + (θ : Circ) := by rw [hθ]; abel
  have hθabs : |θ| ≤ (2 : ℝ) ^ K := abs_le.mpr hθmem
  have hkey : ‖fourier (T := 1) (-m) (θ : Circ) - 1‖ ≤ 2 * Real.pi * |(m : ℝ)| * |θ| := by
    rw [fourier_coe_apply]
    simp only [Complex.ofReal_one, div_one]
    have hexp : (2 : ℂ) * ↑Real.pi * Complex.I * ↑(-m) * ↑θ
        = Complex.I * ↑(2 * Real.pi * (-(m : ℝ)) * θ) := by
      push_cast
      ring
    rw [hexp]
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le
      (x := 2 * Real.pi * (-(m : ℝ)) * θ)).trans ?_
    have habs : ‖(2 * Real.pi * (-(m : ℝ)) * θ : ℝ)‖ = 2 * Real.pi * |(m : ℝ)| * |θ| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [habs]
  calc ‖fourier (T := 1) (-m) ξ - fourier (T := 1) (-m) α‖
      = ‖fourier (T := 1) (-m) α * (fourier (T := 1) (-m) (θ : Circ) - 1)‖ := by
        rw [hξ, shiftMod_fourier_add_arg, mul_sub, mul_one]
    _ = ‖fourier (T := 1) (-m) α‖ * ‖fourier (T := 1) (-m) (θ : Circ) - 1‖ := norm_mul _ _
    _ = ‖fourier (T := 1) (-m) (θ : Circ) - 1‖ := by rw [shiftMod_norm_fourier_apply, one_mul]
    _ ≤ 2 * Real.pi * |(m : ℝ)| * |θ| := hkey
    _ ≤ 2 * Real.pi * |(m : ℝ)| * (2 : ℝ) ^ K :=
        mul_le_mul_of_nonneg_left hθabs (by positivity)

/-! ## The pointwise symbol inequality -/

theorem shiftMod_symbol_bound (K : ℤ) (S : Finset Circ) {Φ : Circ → ℂ}
    (hsupp : SupportedInArc K Φ) (hNA : NonAliasing K S) (m : ℤ) (ξ : Circ) :
    ‖fourier (T := 1) (-m) ξ * iwSymbolSet S Φ ξ
        - ∑ α ∈ S, fourier (T := 1) (-m) α * iwSymbolSet {α} Φ ξ‖
      ≤ (2 * Real.pi * |(m : ℝ)| * (2 : ℝ) ^ K) * ‖iwSymbolSet S Φ ξ‖ := by
  classical
  set T : Finset Circ := S.filter (fun α => iwSymbolSet {α} Φ ξ ≠ 0) with hTdef
  have hmemT : ∀ α, α ∈ T ↔ α ∈ S ∧ iwSymbolSet {α} Φ ξ ≠ 0 := fun α => by
    rw [hTdef, Finset.mem_filter]
  have hTsub : T ⊆ S := fun α hα => ((hmemT α).mp hα).1
  have hzero : ∀ α ∈ S, α ∉ T → iwSymbolSet {α} Φ ξ = 0 := by
    intro α hα hαT
    by_contra hne
    exact hαT ((hmemT α).mpr ⟨hα, hne⟩)
  have hsumS : iwSymbolSet S Φ ξ = ∑ α ∈ T, iwSymbolSet {α} Φ ξ :=
    (iwSymbolSet_singletons_apply S Φ ξ).trans (Finset.sum_subset hTsub hzero).symm
  have hsumD : ∑ α ∈ S, fourier (T := 1) (-m) α * iwSymbolSet {α} Φ ξ
      = ∑ α ∈ T, fourier (T := 1) (-m) α * iwSymbolSet {α} Φ ξ :=
    (Finset.sum_subset hTsub (fun α hα hαT => by rw [hzero α hα hαT, mul_zero])).symm
  have huniq : ∀ a ∈ T, ∀ b ∈ T, a = b := by
    intro a ha b hb
    have haS : a ∈ S := hTsub ha
    have hbS : b ∈ S := hTsub hb
    have hane : iwSymbolSet {a} Φ ξ ≠ 0 := ((hmemT a).mp ha).2
    have hbne : iwSymbolSet {b} Φ ξ ≠ 0 := ((hmemT b).mp hb).2
    by_contra hne
    have hanePhi : Φ (ξ - a) ≠ 0 := by simpa [iwSymbolSet] using hane
    have hbnePhi : Φ (ξ - b) ≠ 0 := by simpa [iwSymbolSet] using hbne
    obtain ⟨θ, hθ, hθξ⟩ := hsupp (ξ - a) hanePhi
    obtain ⟨θ2, hθ2, hθ2ξ⟩ := hsupp (ξ - b) hbnePhi
    have heq : a + (θ : Circ) = b + (θ2 : Circ) := by rw [hθξ, hθ2ξ]; abel
    exact hne (hNA a haS b hbS θ hθ θ2 hθ2 heq).1
  have hdiff : fourier (T := 1) (-m) ξ * iwSymbolSet S Φ ξ
        - ∑ α ∈ S, fourier (T := 1) (-m) α * iwSymbolSet {α} Φ ξ
      = ∑ α ∈ T, (fourier (T := 1) (-m) ξ - fourier (T := 1) (-m) α)
          * iwSymbolSet {α} Φ ξ := by
    rw [hsumS, Finset.mul_sum, hsumD, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun α _ => by ring)
  rw [hdiff]
  rcases T.eq_empty_or_nonempty with hT0 | ⟨α0, hα0⟩
  · rw [hT0, Finset.sum_empty, norm_zero]
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ K := zpow_nonneg (by norm_num) K
    have h3 : (0 : ℝ) ≤ 2 * Real.pi * |(m : ℝ)| * (2 : ℝ) ^ K := by positivity
    exact mul_nonneg h3 (norm_nonneg _)
  · have hTeq : T = {α0} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hα0, fun x hx => huniq x hx α0 hα0⟩
    have hne0 : Φ (ξ - α0) ≠ 0 := by
      have h := ((hmemT α0).mp hα0).2
      simpa [iwSymbolSet] using h
    have hA : iwSymbolSet S Φ ξ = iwSymbolSet {α0} Φ ξ := by
      rw [hsumS, hTeq, Finset.sum_singleton]
    rw [hTeq, Finset.sum_singleton, norm_mul, hA]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact shiftMod_norm_fourier_sub_le K m hsupp hne0

/-! ## The Fourier transform of the band -/

theorem shiftMod_ae_fourierZ_single (S : Finset Circ) {Φ : Circ → ℂ}
    (hΦ : MemLp Φ ⊤ circleMeasure) (F : L2Z) :
    (fun ξ : Circ => ⇑(fourierZ (iwOpSet S Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)) ξ)
      =ᵐ[circleMeasure]
      (fun ξ : Circ => iwSymbolSet S Φ ξ * ⇑(fourierZ F) ξ) := by
  have h1 : fourierZ (iwOpSet S Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)
      = (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ).toLp (iwSymbolSet S Φ)
          • fourierZ F :=
    fourierZ_multiplierOf (iwSymbolSet S Φ) (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F
  rw [h1]
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
      ((Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ).toLp (iwSymbolSet S Φ)) (fourierZ F),
    MemLp.coeFn_toLp (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ)] with ξ h2ξ h3ξ
  rw [h2ξ]
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, h3ξ]

/-! ## The Fourier transform of the shift-modulation difference -/

theorem shiftMod_ae_fourierZ_diff (S : Finset Circ) {Φ : Circ → ℂ}
    (hΦ : MemLp Φ ⊤ circleMeasure) (F : L2Z) (m : ℤ) :
    (fun ξ : Circ => ⇑(fourierZ (shiftL2Z m (iwOpSet S Φ
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)
        - (∑ α ∈ S, (fourier (T := 1) (-m) α) •
            (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)))) ξ)
      =ᵐ[circleMeasure]
      (fun ξ : Circ => (fourier (T := 1) (-m) ξ * iwSymbolSet S Φ ξ
          - ∑ α ∈ S, fourier (T := 1) (-m) α * iwSymbolSet {α} Φ ξ)
        * ⇑(fourierZ F) ξ) := by
  classical
  have hZ : (fun ξ : Circ => ⇑(fourierZ (shiftL2Z m (iwOpSet S Φ
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F))) ξ)
      =ᵐ[circleMeasure]
      (fun ξ : Circ => fourier (T := 1) (-m) ξ
        * (iwSymbolSet S Φ ξ * ⇑(fourierZ F) ξ)) := by
    have h1 := fourierZ_shiftL2Z m (iwOpSet S Φ
      (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)
    have h2 := Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (charLp (-m))
      (fourierZ (iwOpSet S Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F))
    rw [← h1] at h2
    have hchar : ⇑(charLp (-m)) =ᵐ[circleMeasure]
        (fun ξ : Circ => fourier (T := 1) (-m) ξ) :=
      MemLp.coeFn_toLp (memLp_fourier_char (-m))
    filter_upwards [h2, hchar, shiftMod_ae_fourierZ_single S hΦ F] with ξ h2ξ h3ξ h4ξ
    rw [h2ξ]
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, h3ξ, h4ξ]
  have hY : (fun ξ : Circ => ⇑(fourierZ (∑ α ∈ S, (fourier (T := 1) (-m) α) •
        (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F))) ξ)
      =ᵐ[circleMeasure]
      (fun ξ : Circ => ∑ α ∈ S, fourier (T := 1) (-m) α
        * (iwSymbolSet {α} Φ ξ * ⇑(fourierZ F) ξ)) := by
    have hlin : fourierZ (∑ α ∈ S, (fourier (T := 1) (-m) α) •
          (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F))
        = ∑ α ∈ S, (fourier (T := 1) (-m) α) •
            fourierZ (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun α _ => by rw [map_smul])
    rw [hlin]
    have hα : ∀ᵐ ξ ∂circleMeasure, ∀ α ∈ S,
        ⇑((fourier (T := 1) (-m) α) • fourierZ (iwOpSet {α} Φ
            (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)) ξ
          = fourier (T := 1) (-m) α * (iwSymbolSet {α} Φ ξ * ⇑(fourierZ F) ξ) := by
      rw [Filter.eventually_all_finset]
      intro α hαS
      filter_upwards [Lp.coeFn_smul (fourier (T := 1) (-m) α)
          (fourierZ (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)),
        shiftMod_ae_fourierZ_single {α} hΦ F] with ξ h1ξ h2ξ
      rw [h1ξ]
      simp only [Pi.smul_apply, smul_eq_mul, h2ξ]
    filter_upwards [Lp.coeFn_finsetSum S (fun α : Circ => (fourier (T := 1) (-m) α) •
        fourierZ (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)), hα]
      with ξ hsumξ hαξ
    rw [hsumξ, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun α hαS => hαξ α hαS)
  have hsub := Lp.coeFn_sub (fourierZ (shiftL2Z m (iwOpSet S Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)))
    (fourierZ (∑ α ∈ S, (fourier (T := 1) (-m) α) •
        (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)))
  have hcomb : (fun ξ : Circ => ⇑(fourierZ (shiftL2Z m (iwOpSet S Φ
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F))
        - fourierZ (∑ α ∈ S, (fourier (T := 1) (-m) α) •
            (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F))) ξ)
      =ᵐ[circleMeasure]
      (fun ξ : Circ => (fourier (T := 1) (-m) ξ * iwSymbolSet S Φ ξ
          - ∑ α ∈ S, fourier (T := 1) (-m) α * iwSymbolSet {α} Φ ξ)
        * ⇑(fourierZ F) ξ) := by
    filter_upwards [hsub, hZ, hY] with ξ hsubξ hZξ hYξ
    rw [hsubξ, Pi.sub_apply, hZξ, hYξ]
    have hs : iwSymbolSet S Φ ξ = ∑ α ∈ S, iwSymbolSet {α} Φ ξ :=
      iwSymbolSet_singletons_apply S Φ ξ
    have hsumfac : ∑ α ∈ S, fourier (T := 1) (-m) α * (iwSymbolSet {α} Φ ξ * ⇑(fourierZ F) ξ)
        = (∑ α ∈ S, fourier (T := 1) (-m) α * iwSymbolSet {α} Φ ξ) * ⇑(fourierZ F) ξ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun α _ => by ring)
    rw [hsumfac, hs, sub_mul]
    ring
  rw [map_sub fourierZ (shiftL2Z m (iwOpSet S Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F))
      (∑ α ∈ S, (fourier (T := 1) (-m) α) •
        (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F))]
  exact hcomb

/-! ## The `ℓ²` shift-modulation estimate -/

theorem shiftMod_eLpNorm_diff_le (K : ℤ) (S : Finset Circ) {Φ : Circ → ℂ}
    (hΦ : MemLp Φ ⊤ circleMeasure) (hsupp : SupportedInArc K Φ) (hNA : NonAliasing K S)
    (F : L2Z) (m : ℤ) :
    eLpNorm ⇑(shiftL2Z m (iwOpSet S Φ
          (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)
        - ∑ α ∈ S, (fourier (T := 1) (-m) α) •
            (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F))
      2 Measure.count
      ≤ ENNReal.ofReal (2 * Real.pi * |(m : ℝ)| * (2 : ℝ) ^ K) *
          eLpNorm ⇑(iwOpSet S Φ
            (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F) 2 Measure.count := by
  classical
  set C : ℝ := 2 * Real.pi * |(m : ℝ)| * (2 : ℝ) ^ K with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ K := zpow_nonneg (by norm_num) K
    positivity
  set D : L2Z := shiftL2Z m (iwOpSet S Φ
        (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)
      - ∑ α ∈ S, (fourier (T := 1) (-m) α) •
          (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F) with hD
  set TS : L2Z := iwOpSet S Φ
      (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F with hTS
  have hae : ∀ᵐ ξ ∂circleMeasure, ‖⇑(fourierZ D) ξ‖ ≤ C * ‖⇑(fourierZ TS) ξ‖ := by
    filter_upwards [shiftMod_ae_fourierZ_diff S hΦ F m, shiftMod_ae_fourierZ_single S hΦ F]
      with ξ h1ξ h2ξ
    rw [hD, hTS]
    rw [h1ξ, h2ξ, norm_mul, norm_mul]
    have hb : ‖fourier (T := 1) (-m) ξ * iwSymbolSet S Φ ξ
        - ∑ α ∈ S, fourier (T := 1) (-m) α * iwSymbolSet {α} Φ ξ‖ ≤ C * ‖iwSymbolSet S Φ ξ‖ := by
      rw [hC]
      exact shiftMod_symbol_bound K S hsupp hNA m ξ
    calc ‖fourier (T := 1) (-m) ξ * iwSymbolSet S Φ ξ
            - ∑ α ∈ S, fourier (T := 1) (-m) α * iwSymbolSet {α} Φ ξ‖
          * ‖⇑(fourierZ F) ξ‖
        ≤ (C * ‖iwSymbolSet S Φ ξ‖) * ‖⇑(fourierZ F) ξ‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = C * (‖iwSymbolSet S Φ ξ‖ * ‖⇑(fourierZ F) ξ‖) := by ring
  have hmain : eLpNorm ⇑(fourierZ D) 2 circleMeasure
      ≤ ENNReal.ofReal C * eLpNorm ⇑(fourierZ TS) 2 circleMeasure := by
    calc eLpNorm ⇑(fourierZ D) 2 circleMeasure
        ≤ eLpNorm ((C : ℝ) • fun ξ : Circ => ‖⇑(fourierZ TS) ξ‖) 2 circleMeasure :=
          eLpNorm_mono_ae (hf := by pw_aesm) (hae.mono (fun ξ hξ => by
            have hnorm : ‖((C : ℝ) • fun ξ : Circ => ‖⇑(fourierZ TS) ξ‖) ξ‖
                = C * ‖⇑(fourierZ TS) ξ‖ := by
              simp only [Pi.smul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hC0,
                abs_of_nonneg (norm_nonneg _), smul_eq_mul]
            rw [hnorm]
            exact hξ))
      _ = ‖(C : ℝ)‖ₑ * eLpNorm (fun ξ : Circ => ‖⇑(fourierZ TS) ξ‖) 2 circleMeasure :=
          eLpNorm_const_smul (C : ℝ) _ 2 circleMeasure
      _ = ENNReal.ofReal C * eLpNorm ⇑(fourierZ TS) 2 circleMeasure := by
          rw [eLpNorm_norm (hf := by pw_aesm), Real.enorm_eq_ofReal_abs, abs_of_nonneg hC0]
  have hDc : eLpNorm ⇑D 2 Measure.count = eLpNorm ⇑(fourierZ D) 2 circleMeasure := by
    rw [enorm_lp_count D, ← Lp.enorm_def (fourierZ D), ← ofReal_norm, ← ofReal_norm,
      fourierZ.norm_map D]
  have hTSc : eLpNorm ⇑TS 2 Measure.count = eLpNorm ⇑(fourierZ TS) 2 circleMeasure := by
    rw [enorm_lp_count TS, ← Lp.enorm_def (fourierZ TS), ← ofReal_norm, ← ofReal_norm,
      fourierZ.norm_map TS]
  calc eLpNorm ⇑D 2 Measure.count
      = eLpNorm ⇑(fourierZ D) 2 circleMeasure := hDc
    _ ≤ ENNReal.ofReal C * eLpNorm ⇑(fourierZ TS) 2 circleMeasure := hmain
    _ = ENNReal.ofReal C * eLpNorm ⇑TS 2 Measure.count := by rw [hTSc]
    _ = ENNReal.ofReal (2 * Real.pi * |(m : ℝ)| * (2 : ℝ) ^ K) * eLpNorm ⇑TS 2 Measure.count :=
        by rw [hC]

theorem shift_modulation_le (K : ℤ) (S : Finset Work.Analysis.IonescuWainger.Circle)
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hΦ : MeasureTheory.MemLp Φ (⊤ : ENNReal) Work.Analysis.IonescuWainger.circleMeasure)
    (hsupp : Work.Analysis.IonescuWainger.SupportedInArc K Φ)
    (hNA : Work.Analysis.IonescuWainger.NonAliasing K S)
    (F : Work.Analysis.IonescuWainger.L2Z) (m : ℤ) :
    MeasureTheory.eLpNorm (fun n : ℤ =>
        ⇑(Work.Analysis.IonescuWainger.iwOpSet S Φ
            (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F) (n + m) -
          ∑ α ∈ S, fourier (T := 1) (-m) α *
            ⇑(Work.Analysis.IonescuWainger.iwOpSet {α} Φ
                (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F) n)
      2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (2 * Real.pi * |(m : ℝ)| * (2 : ℝ) ^ K) *
          MeasureTheory.eLpNorm
            (⇑(Work.Analysis.IonescuWainger.iwOpSet S Φ
                (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F))
            2 MeasureTheory.Measure.count := by
  have hcoe : (fun n : ℤ =>
        ⇑(iwOpSet S Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F) (n + m)
        - ∑ α ∈ S, fourier (T := 1) (-m) α *
            ⇑(iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F) n)
      =ᵐ[Measure.count]
      ⇑(shiftL2Z m (iwOpSet S Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet S hΦ) F)
        - ∑ α ∈ S, (fourier (T := 1) (-m) α) •
            (iwOpSet {α} Φ (Work.Analysis.IWMultiplier.memLp_iwSymbolSet {α} hΦ) F)) := by
    filter_upwards with n
    simp only [lp.coeFn_sub, lp.coeFn_sum, lp.coeFn_smul, shiftL2Z_apply, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [eLpNorm_congr_ae hcoe]
  exact shiftMod_eLpNorm_diff_le K S hΦ hsupp hNA F m

end Work.KMTPlan.A6
