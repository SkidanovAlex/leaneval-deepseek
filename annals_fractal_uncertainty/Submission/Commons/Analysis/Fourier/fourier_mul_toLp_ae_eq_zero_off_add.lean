import Mathlib
import Submission.Commons.Analysis.Fourier.fourier_mul_support_schwartz
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory FourierTransform Filter
open scoped FourierTransform ENNReal RealInnerProductSpace Topology

namespace Commons.Analysis.Fourier

noncomputable section

variable {d : ℕ}
local notation "𝔼" d:70 => EuclideanSpace ℝ (Fin d)

/-! ### The dual convolution identity

For `u, v ∈ L¹(𝔼 d)`, the Fourier transform of the pointwise product `u · 𝓕⁻v` is the convolution
`y ↦ v y · 𝓕u (ξ - y)`. -/
theorem fourier_mul_fourierInv_eq_integral {u v : 𝔼 d → ℂ}
    (hu : Integrable u (volume : Measure (𝔼 d))) (hv : Integrable v (volume : Measure (𝔼 d))) (ξ : 𝔼 d) :
    𝓕 (fun x => u x * 𝓕⁻ v x) ξ = ∫ y, v y * 𝓕 u (ξ - y) ∂(volume : Measure (𝔼 d)) := by
  set w : 𝔼 d → ℂ := fun x => u x * (Real.fourierChar (-(inner ℝ x ξ)) : ℂ) with hw
  have hwbound : ∀ x, ‖(Real.fourierChar (-(inner ℝ x ξ)) : ℂ)‖ ≤ 1 :=
    fun x => le_of_eq (Circle.norm_coe _)
  have hwmeas : AEStronglyMeasurable (fun x : 𝔼 d => (Real.fourierChar (-(inner ℝ x ξ)) : ℂ)) volume :=
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))).aestronglyMeasurable
  have hwint : Integrable w volume := by
    rw [hw]
    exact hu.mul_bdd hwmeas (Eventually.of_forall hwbound)
  have hvneg : Integrable (fun x : 𝔼 d => v (-x)) volume := by
    rw [← memLp_one_iff_integrable] at hv ⊢
    exact hv.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure (𝔼 d)))
  have hwF : ∀ x, 𝓕 w x = 𝓕 u (x + ξ) := by
    intro x
    rw [hw, Real.fourier_eq, Real.fourier_eq]
    apply integral_congr_ae
    filter_upwards with t
    simp only [Circle.smul_def, smul_eq_mul]
    have hphase : (↑(Real.fourierChar (-(inner ℝ t x))) : ℂ) * ↑(Real.fourierChar (-(inner ℝ t ξ)))
        = ↑(Real.fourierChar (-(inner ℝ t (x + ξ)))) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, inner_add_right, neg_add]
    rw [show (↑(Real.fourierChar (-(inner ℝ t x))) : ℂ) *
          (u t * ↑(Real.fourierChar (-(inner ℝ t ξ))))
        = ((↑(Real.fourierChar (-(inner ℝ t x))) : ℂ) *
            ↑(Real.fourierChar (-(inner ℝ t ξ)))) * u t from by ring,
      hphase]
  have hSA := fourier_integral_mul_selfadjoint (fun x : 𝔼 d => v (-x)) w hvneg hwint
  calc 𝓕 (fun x => u x * 𝓕⁻ v x) ξ
      = ∫ x, (𝓕⁻ v) x • w x := by
        rw [Real.fourier_eq]
        apply integral_congr_ae
        filter_upwards with x
        simp only [hw, Circle.smul_def, smul_eq_mul]
        ring
    _ = ∫ x, (𝓕 fun x => v (-x)) x • w x := by rw [Real.fourierInv_eq_fourier_comp_neg]
    _ = ∫ x, v (-x) * 𝓕 u (x + ξ) := by
        rw [hSA]
        apply integral_congr_ae
        filter_upwards with x
        rw [hwF x]
        exact smul_eq_mul _ _
    _ = ∫ y, v y * 𝓕 u (ξ - y) := by
        rw [← MeasureTheory.integral_neg_eq_self (fun y : 𝔼 d => v y * 𝓕 u (ξ - y))
          (volume : Measure (𝔼 d))]
        apply integral_congr_ae
        filter_upwards with x
        have h : x + ξ = ξ - (-x) := by rw [sub_neg_eq_add, add_comm]
        rw [h]

/-- **Vanishing off the sumset.** If the function-level Fourier transform of `g ∈ L¹` vanishes
off `E` and `Θ ∈ L¹` vanishes a.e. off `F`, then the Fourier transform of `g · 𝓕⁻Θ` vanishes off
the sumset `E + F`. -/
theorem fourier_mul_fourierInv_eq_zero_of_notMem_add {g Θ : 𝔼 d → ℂ}
    (hg : MemLp g 1 (volume : Measure (𝔼 d))) (hΘ : MemLp Θ 1 (volume : Measure (𝔼 d)))
    (E F : Set (𝔼 d))
    (hE : ∀ ξ, ξ ∉ E → 𝓕 g ξ = 0)
    (hΘF : ∀ᵐ y ∂(volume : Measure (𝔼 d)), y ∉ F → Θ y = 0) :
    ∀ ξ, (∀ a ∈ E, ∀ b ∈ F, ξ ≠ a + b) → 𝓕 (fun x => g x * 𝓕⁻ Θ x) ξ = 0 := by
  intro ξ hξ
  rw [fourier_mul_fourierInv_eq_integral (memLp_one_iff_integrable.mp hg)
    (memLp_one_iff_integrable.mp hΘ) ξ]
  have hzero : (fun y => Θ y * 𝓕 g (ξ - y)) =ᵐ[(volume : Measure (𝔼 d))] (fun _ => 0) := by
    filter_upwards [hΘF] with y hy
    by_cases hyF : y ∈ F
    · have hmem : ξ - y ∉ E := fun hc => hξ (ξ - y) hc y hyF (by abel)
      rw [hE (ξ - y) hmem, mul_zero]
    · rw [hy hyF, zero_mul]
  rw [integral_congr_ae hzero, integral_zero]

/-! ### Truncation convergence -/

/-- The `L²` norm of `f` multiplied by the complementary ball indicator tends to zero. -/
lemma tendsto_eLpNorm_cutoff_sub {d : ℕ} (f : 𝔼 d → ℂ) (hf : MemLp f 2 (volume : Measure (𝔼 d))) :
    Tendsto (fun n : ℕ => eLpNorm (fun y : 𝔼 d => f y *
      (Metric.closedBall (0 : 𝔼 d) (n : ℝ)).indicator (fun _ => (1 : ℂ)) y - f y) 2
        (volume : Measure (𝔼 d))) atTop (𝓝 0) := by
  set χ : ℕ → 𝔼 d → ℂ := fun n =>
    (Metric.closedBall (0 : 𝔼 d) (n : ℝ)).indicator (fun _ => (1 : ℂ)) with hχ
  have hχ_meas : ∀ n, Measurable (χ n) := by
    intro n; rw [hχ]; exact measurable_const.indicator measurableSet_closedBall
  have hpoint : ∀ᵐ y ∂(volume : Measure (𝔼 d)),
      Tendsto (fun n : ℕ => ‖f y * χ n y - f y‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    refine Eventually.of_forall fun y => ?_
    have hev : (fun n : ℕ => ‖f y * χ n y - f y‖ₑ ^ (2 : ℝ)) =ᶠ[atTop]
        (fun _ => (0 : ℝ≥0∞)) := by
      filter_upwards [eventually_ge_atTop ⌈‖y‖⌉₊] with n hn
      have hy : y ∈ Metric.closedBall (0 : 𝔼 d) (n : ℝ) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact le_trans (Nat.le_ceil ‖y‖) (Nat.cast_le.mpr hn)
      have h1 : χ n y = 1 := by rw [hχ]; exact Set.indicator_of_mem hy (fun _ => (1 : ℂ))
      rw [h1, mul_one, sub_self]
      simp
    exact Tendsto.congr' hev.symm tendsto_const_nhds
  have hmeas : ∀ n, AEMeasurable (fun y : 𝔼 d => ‖f y * χ n y - f y‖ₑ ^ (2 : ℝ))
      (volume : Measure (𝔼 d)) := by
    intro n
    exact (((hf.aemeasurable.mul (hχ_meas n).aemeasurable).sub hf.aemeasurable).enorm).pow_const 2
  have hdom : ∀ n, (fun y : 𝔼 d => ‖f y * χ n y - f y‖ₑ ^ (2 : ℝ)) ≤ᵐ[(volume : Measure (𝔼 d))]
      (fun y : 𝔼 d => ‖f y‖ₑ ^ (2 : ℝ)) := by
    intro n
    filter_upwards with y
    by_cases hy : y ∈ Metric.closedBall (0 : 𝔼 d) (n : ℝ)
    · have h1 : χ n y = 1 := by rw [hχ]; exact Set.indicator_of_mem hy (fun _ => (1 : ℂ))
      rw [h1, mul_one, sub_self]
      simp
    · have h0 : χ n y = 0 := by rw [hχ]; exact Set.indicator_of_notMem hy (fun _ => (1 : ℂ))
      rw [h0, mul_zero, zero_sub, enorm_neg]
  have hfin : ∫⁻ y : 𝔼 d, ‖f y‖ₑ ^ (2 : ℝ) ∂(volume : Measure (𝔼 d)) ≠ ∞ :=
    ne_of_lt (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hf.2)
  have hdc := tendsto_lintegral_of_dominated_convergence' (fun y : 𝔼 d => ‖f y‖ₑ ^ (2 : ℝ))
    hmeas hdom hfin hpoint
  have hconv : ∀ n : ℕ, eLpNorm (fun y : 𝔼 d => f y * χ n y - f y) 2 (volume : Measure (𝔼 d))
      = (∫⁻ y : 𝔼 d, ‖f y * χ n y - f y‖ₑ ^ (2 : ℝ) ∂(volume : Measure (𝔼 d))) ^ ((1 : ℝ) / 2) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)]
    norm_num
  have hmain : Tendsto (fun n : ℕ => (∫⁻ y : 𝔼 d, ‖f y * χ n y - f y‖ₑ ^ (2 : ℝ)
      ∂(volume : Measure (𝔼 d))) ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
    have hthis := (ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto (0 : ℝ≥0∞)
    have h0 : (0 : ℝ≥0∞) ^ ((1 : ℝ) / 2) = 0 := by simp
    rw [h0] at hthis
    have hdc' : Tendsto (fun n : ℕ => ∫⁻ y : 𝔼 d, ‖f y * χ n y - f y‖ₑ ^ (2 : ℝ)
        ∂(volume : Measure (𝔼 d))) atTop (𝓝 0) := by simpa using hdc
    exact hthis.comp hdc'
  exact hmain.congr' (Eventually.of_forall fun n => (hconv n).symm)

/-! ### Bounded multipliers on `L²` -/

/-- Multiplication by an `L^∞` function is Lipschitz on `L²`. -/
lemma eLpNorm_mul_sub_le {φ f₁ f₂ : 𝔼 d → ℂ} (_hφ : MemLp φ ⊤ (volume : Measure (𝔼 d)))
    (hsm : AEStronglyMeasurable (fun x => f₁ x - f₂ x) (volume : Measure (𝔼 d))) :
    eLpNorm (fun x : 𝔼 d => φ x * f₁ x - φ x * f₂ x) 2 (volume : Measure (𝔼 d)) ≤
      eLpNorm φ ⊤ (volume : Measure (𝔼 d)) * eLpNorm (fun x => f₁ x - f₂ x) 2
        (volume : Measure (𝔼 d)) := by
  have h : (fun x : 𝔼 d => φ x * f₁ x - φ x * f₂ x) = fun x => φ x • (f₁ x - f₂ x) := by
    funext x; rw [smul_eq_mul]; ring
  rw [h]
  exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 hsm φ

/-- The inverse Fourier integral is bounded by the `L¹` norm. -/
lemma norm_fourierInv_le_eLpNorm_one {Θ : 𝔼 d → ℂ} (hΘ : AEStronglyMeasurable Θ
    (volume : Measure (𝔼 d))) (x : 𝔼 d) :
    ‖𝓕⁻ Θ x‖ ≤ (eLpNorm Θ 1 (volume : Measure (𝔼 d))).toReal := by
  rw [Real.fourierInv_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]
  rw [integral_norm_eq_lintegral_enorm hΘ, eLpNorm_one_eq_lintegral_enorm]

/-- **The `L²` version of the support statement** (see the statement below). -/
theorem fourier_mul_toLp_ae_eq_zero_off_add {d : ℕ} (g h : EuclideanSpace ℝ (Fin d) → ℂ)
    (hg1 : MeasureTheory.MemLp g 1 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hgtop : MeasureTheory.MemLp g ⊤ (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hh2 : MeasureTheory.MemLp h 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (E F : Set (EuclideanSpace ℝ (Fin d)))
    (hE : ∀ ξ : EuclideanSpace ℝ (Fin d), ξ ∉ E → FourierTransform.fourier g ξ = 0)
    (hF : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ F →
        ((FourierTransform.fourier (hh2.toLp h) : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) : EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0) :
    ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      (∀ a ∈ E, ∀ b ∈ F, ξ ≠ a + b) →
        ((FourierTransform.fourier
            ((hh2.mul hgtop : MeasureTheory.MemLp (fun x => g x * h x) 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))).toLp (fun x => g x * h x)) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0 := by
  -- abbreviations
  set H : Lp ℂ 2 (volume : Measure (𝔼 d)) := hh2.toLp h with hHdef
  set V : Lp ℂ 2 (volume : Measure (𝔼 d)) := 𝓕 H with hVdef
  have hHcoe : (H : 𝔼 d → ℂ) =ᵐ[(volume : Measure (𝔼 d))] h := by
    rw [hHdef]; exact hh2.coeFn_toLp
  have hVvan : ∀ᵐ ξ ∂(volume : Measure (𝔼 d)), ξ ∉ F → (V : 𝔼 d → ℂ) ξ = 0 := by
    rw [hVdef, hHdef]; exact hF
  -- the cutoff sequence
  set χ : ℕ → 𝔼 d → ℂ := fun n =>
    (Metric.closedBall (0 : 𝔼 d) (n : ℝ)).indicator (fun _ => (1 : ℂ)) with hχdef
  have hχ_meas : ∀ n, Measurable (χ n) := by
    intro n; simp only [hχdef]; exact measurable_const.indicator measurableSet_closedBall
  have hχ_le : ∀ n y, ‖χ n y‖ ≤ 1 := by
    intro n y
    simp only [hχdef]
    by_cases hy : y ∈ Metric.closedBall (0 : 𝔼 d) (n : ℝ)
    · rw [Set.indicator_of_mem hy (fun _ => (1 : ℂ))]; simp
    · rw [Set.indicator_of_notMem hy (fun _ => (1 : ℂ))]; simp
  have hχ_mem2 : ∀ n, MemLp (χ n) 2 (volume : Measure (𝔼 d)) := by
    intro n; simp only [hχdef]
    exact memLp_indicator_const 2 measurableSet_closedBall 1
      (Or.inr measure_closedBall_lt_top.ne)
  have hχ_top : ∀ n, MemLp (χ n) ⊤ (volume : Measure (𝔼 d)) := by
    intro n
    exact memLp_top_of_bound (hχ_meas n).aestronglyMeasurable 1
      (Eventually.of_forall (hχ_le n))
  -- the functions Θₙ and their per-n transforms
  set Θ : ℕ → 𝔼 d → ℂ := fun n y => (V : 𝔼 d → ℂ) y * χ n y with hΘdef
  have hΘ1 : ∀ n, MemLp (Θ n) 1 (volume : Measure (𝔼 d)) := by
    intro n
    have h := MemLp.mul (p := 2) (q := 2) (r := 1) (hχ_mem2 n) (Lp.memLp V)
    rw [hΘdef]
    exact h
  have hΘ2 : ∀ n, MemLp (Θ n) 2 (volume : Measure (𝔼 d)) := by
    intro n
    have h := MemLp.mul (p := ⊤) (q := 2) (r := 2) (Lp.memLp V) (hχ_top n)
    rw [hΘdef]
    exact MemLp.ae_eq (Eventually.of_forall fun y => mul_comm (χ n y) ((V : 𝔼 d → ℂ) y)) h
  set Hn : ℕ → Lp ℂ 2 (volume : Measure (𝔼 d)) :=
    fun n => 𝓕⁻ ((hΘ2 n).toLp (Θ n)) with hHndef
  have hHn_ae : ∀ n, ((Hn n : Lp ℂ 2 (volume : Measure (𝔼 d))) : 𝔼 d → ℂ)
      =ᵐ[(volume : Measure (𝔼 d))] (fun x => 𝓕⁻ (Θ n) x) := by
    intro n
    rw [hHndef]
    exact fourierInv_toLp_ae_eq_fourierInv (hΘ1 n) (hΘ2 n)
  have hHn_fourier : ∀ n, (𝓕 (Hn n) : Lp ℂ 2 (volume : Measure (𝔼 d)))
      = (hΘ2 n).toLp (Θ n) := by
    intro n
    rw [hHndef]
    simp
  have hhn_mem : ∀ n, MemLp (fun x => 𝓕⁻ (Θ n) x) 2 (volume : Measure (𝔼 d)) :=
    fun n => MemLp.ae_eq (hHn_ae n) (Lp.memLp (Hn n))
  -- the product `g · 𝓕⁻Θₙ` is in `L¹ ∩ L²`
  have hgh_mem1 : ∀ n, MemLp (fun x => g x * 𝓕⁻ (Θ n) x) 1 (volume : Measure (𝔼 d)) := by
    intro n
    rw [memLp_one_iff_integrable]
    exact (memLp_one_iff_integrable.mp hg1).mul_bdd (hhn_mem n).aestronglyMeasurable
      (Eventually.of_forall fun x => norm_fourierInv_le_eLpNorm_one (hΘ1 n).aestronglyMeasurable x)
  have hgh_mem2 : ∀ n, MemLp (fun x => g x * 𝓕⁻ (Θ n) x) 2 (volume : Measure (𝔼 d)) := by
    intro n
    have h := MemLp.mul (p := ⊤) (q := 2) (r := 2) (hhn_mem n) hgtop
    exact h
  -- the per-n vanishing
  have hvan : ∀ n, ∀ ξ : 𝔼 d, (∀ a ∈ E, ∀ b ∈ F, ξ ≠ a + b) →
      𝓕 (fun x => g x * 𝓕⁻ (Θ n) x) ξ = 0 := by
    intro n
    refine fourier_mul_fourierInv_eq_zero_of_notMem_add hg1 (hΘ1 n) E F hE ?_
    filter_upwards [hVvan] with y hy hyF
    simp only [hΘdef]
    rw [hy hyF, zero_mul]
  -- the classes of `g · 𝓕⁻Θₙ`
  set Gn : ℕ → Lp ℂ 2 (volume : Measure (𝔼 d)) :=
    fun n => (hgh_mem2 n).toLp (fun x => g x * 𝓕⁻ (Θ n) x) with hGndef
  set G : Lp ℂ 2 (volume : Measure (𝔼 d)) :=
    (hh2.mul hgtop).toLp (fun x => g x * h x) with hGdef
  have hvan_Lp : ∀ n, ∀ᵐ ξ ∂(volume : Measure (𝔼 d)), (∀ a ∈ E, ∀ b ∈ F, ξ ≠ a + b) →
      ((𝓕 (Gn n) : Lp ℂ 2 (volume : Measure (𝔼 d))) : 𝔼 d → ℂ) ξ = 0 := by
    intro n
    have hft := fourier_toLp_eq_fourier_integral (d := d) (hgh_mem1 n) (hgh_mem2 n)
    have hft' : ((𝓕 (Gn n) : Lp ℂ 2 (volume : Measure (𝔼 d))) : 𝔼 d → ℂ)
        =ᵐ[(volume : Measure (𝔼 d))] (fun ξ => 𝓕 (fun x => g x * 𝓕⁻ (Θ n) x) ξ) := hft
    filter_upwards [hft'] with ξ hξ hcond
    rw [hξ]
    exact hvan n ξ hcond
  -- convergence `Hn n → H`
  have hHn_tend : Tendsto Hn atTop (𝓝 H) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hcut := tendsto_eLpNorm_cutoff_sub (d := d) (V : 𝔼 d → ℂ) (Lp.memLp V)
    refine squeeze_zero (f := fun n : ℕ => ‖Hn n - H‖)
      (g := fun n : ℕ => (eLpNorm (fun y : 𝔼 d => (V : 𝔼 d → ℂ) y * χ n y
        - (V : 𝔼 d → ℂ) y) 2 (volume : Measure (𝔼 d))).toReal)
      (fun n => norm_nonneg _) (fun n => ?_) ?_
    · have hae : ((((hΘ2 n).toLp (Θ n) : Lp ℂ 2 (volume : Measure (𝔼 d))) - V : Lp ℂ 2 (volume : Measure (𝔼 d)))
          : 𝔼 d → ℂ) =ᵐ[(volume : Measure (𝔼 d))]
          (fun y => (V : 𝔼 d → ℂ) y * χ n y - (V : 𝔼 d → ℂ) y) := by
        filter_upwards [Lp.coeFn_sub ((hΘ2 n).toLp (Θ n)) V, (hΘ2 n).coeFn_toLp] with y h1 h2
        rw [h1, Pi.sub_apply, h2]
      have h1 : ‖Hn n - H‖ = ‖((hΘ2 n).toLp (Θ n) : Lp ℂ 2 (volume : Measure (𝔼 d))) - V‖ := by
        have hsub : (𝓕 (Hn n - H) : Lp ℂ 2 (volume : Measure (𝔼 d)))
            = (𝓕 (Hn n) : Lp ℂ 2 (volume : Measure (𝔼 d))) - 𝓕 H :=
          (Lp.fourierTransformₗᵢ (𝔼 d) ℂ).map_sub (Hn n) H
        rw [← Lp.norm_fourier_eq (Hn n - H), hsub, hHn_fourier n, hVdef, hHdef]
      rw [h1, Lp.norm_def, eLpNorm_congr_ae hae]
    · have h2 : Tendsto (fun n : ℕ => (eLpNorm (fun y : 𝔼 d => (V : 𝔼 d → ℂ) y * χ n y
          - (V : 𝔼 d → ℂ) y) 2 (volume : Measure (𝔼 d))).toReal) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal (show (0 : ℝ≥0∞) ≠ ∞ by simp)).comp hcut
        have hlim : (ENNReal.toReal (0 : ℝ≥0∞)) = 0 := by simp
        rw [hlim] at this
        simpa only [Function.comp_def, hχdef] using this
      exact h2
  -- convergence `Gn n → G`
  have hL2norm : ∀ n, (eLpNorm (fun x => 𝓕⁻ (Θ n) x - h x) 2 (volume : Measure (𝔼 d))).toReal
      = ‖Hn n - H‖ := by
    intro n
    have hae : (fun x => 𝓕⁻ (Θ n) x - h x) =ᵐ[(volume : Measure (𝔼 d))]
        ((Hn n - H : Lp ℂ 2 (volume : Measure (𝔼 d))) : 𝔼 d → ℂ) := by
      filter_upwards [hHn_ae n, hHcoe, Lp.coeFn_sub (Hn n) H] with x h1 h2 h3
      rw [h3, Pi.sub_apply, h1, h2]
    rw [eLpNorm_congr_ae hae, ← Lp.norm_def]
  have hGn_tend : Tendsto Gn atTop (𝓝 G) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound_lim : Tendsto (fun n : ℕ =>
        (eLpNorm g ⊤ (volume : Measure (𝔼 d))).toReal * ‖Hn n - H‖) atTop (𝓝 0) := by
      have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hHn_tend
      simpa using hnorm.const_mul (eLpNorm g ⊤ (volume : Measure (𝔼 d))).toReal
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hbound_lim
    · have hae : ((Gn n - G : Lp ℂ 2 (volume : Measure (𝔼 d))) : 𝔼 d → ℂ) =ᵐ[(volume : Measure (𝔼 d))]
          (fun x => g x * 𝓕⁻ (Θ n) x - g x * h x) := by
        have hGn : (Gn n : Lp ℂ 2 (volume : Measure (𝔼 d)))
            = (hgh_mem2 n).toLp (fun x => g x * 𝓕⁻ (Θ n) x) := rfl
        have hG : (G : Lp ℂ 2 (volume : Measure (𝔼 d)))
            = (hh2.mul hgtop : MemLp (fun x => g x * h x) 2 (volume : Measure (𝔼 d))).toLp
                (fun x => g x * h x) := rfl
        rw [hGn, hG]
        have hw : (↑↑((hh2.mul hgtop : MemLp (fun x => g x * h x) 2
              (volume : Measure (𝔼 d))).toLp (fun x => g x * h x)) : 𝔼 d → ℂ)
            =ᵐ[(volume : Measure (𝔼 d))] (fun x => g x * h x) :=
          MemLp.coeFn_toLp (hh2.mul hgtop)
        filter_upwards [Lp.coeFn_sub ((hgh_mem2 n).toLp (fun x => g x * 𝓕⁻ (Θ n) x))
          ((hh2.mul hgtop : MemLp (fun x => g x * h x) 2 (volume : Measure (𝔼 d))).toLp
            (fun x => g x * h x)),
          MemLp.coeFn_toLp (hgh_mem2 n), hw] with x h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3]
      calc ‖Gn n - G‖ = (eLpNorm ((Gn n - G : Lp ℂ 2 (volume : Measure (𝔼 d))) : 𝔼 d → ℂ) 2
            (volume : Measure (𝔼 d))).toReal := Lp.norm_def _
        _ = (eLpNorm (fun x => g x * 𝓕⁻ (Θ n) x - g x * h x) 2 (volume : Measure (𝔼 d))).toReal := by
            rw [eLpNorm_congr_ae hae]
        _ ≤ (eLpNorm g ⊤ (volume : Measure (𝔼 d))
              * eLpNorm (fun x => 𝓕⁻ (Θ n) x - h x) 2 (volume : Measure (𝔼 d))).toReal := by
            refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ne_of_lt hgtop.2) ?_) ?_
            · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
                (by norm_num) (by norm_num)]
              refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
              exact ne_of_lt (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := (2 : ℝ≥0∞))
                (by norm_num) (by norm_num) ((hhn_mem n).sub hh2).2)
            · exact eLpNorm_mul_sub_le hgtop
                ((hhn_mem n).aestronglyMeasurable.sub hh2.aestronglyMeasurable)
        _ = (eLpNorm g ⊤ (volume : Measure (𝔼 d))).toReal
              * (eLpNorm (fun x => 𝓕⁻ (Θ n) x - h x) 2 (volume : Measure (𝔼 d))).toReal := by
            rw [ENNReal.toReal_mul]
        _ = (eLpNorm g ⊤ (volume : Measure (𝔼 d))).toReal * ‖Hn n - H‖ := by rw [hL2norm n]
  -- conclude by extracting an a.e. convergent subsequence
  have htendF : Tendsto (fun n : ℕ => (𝓕 (Gn n) : Lp ℂ 2 (volume : Measure (𝔼 d)))) atTop
      (𝓝 (𝓕 G : Lp ℂ 2 (volume : Measure (𝔼 d)))) :=
    (continuous_fourier.tendsto G).comp hGn_tend
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_Lp htendF).exists_seq_tendsto_ae
  filter_upwards [hns, ae_all_iff.mpr hvan_Lp] with ξ hnsξ hall hcond
  refine tendsto_nhds_unique hnsξ ?_
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards with i
  exact (hall (ns i) hcond).symm

end

end Commons.Analysis.Fourier
