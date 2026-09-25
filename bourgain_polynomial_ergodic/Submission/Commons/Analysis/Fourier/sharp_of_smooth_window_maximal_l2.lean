import Mathlib
import Submission.Commons.Analysis.Fourier.boundary_layer_l2_eighth_separated

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

set_option maxHeartbeats 1600000

namespace Sharp8

/-! ## A smooth bump and its properties -/

/-- A fixed smooth bump: `= 1` on `[-1/2,1/2]`, `= 0` off `[-1,1]`, with `0 ≤ φ ≤ 1`. -/
def bump (x : ℝ) : ℝ := Real.smoothTransition (2 - 2 * x) * Real.smoothTransition (2 + 2 * x)

lemma bump_contDiff (n : ℕ) : ContDiff ℝ n bump := by
  unfold bump
  apply ContDiff.mul
  · exact (Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp (by fun_prop)
  · exact (Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp (by fun_prop)

lemma bump_one : ∀ x : ℝ, |x| ≤ 1 / 2 → bump x = 1 := by
  intro x hx
  have h1 : x ≤ 1 / 2 := (abs_le.mp hx).2
  have h2 : -(1 / 2 : ℝ) ≤ x := (abs_le.mp hx).1
  have h3 : (1 : ℝ) ≤ 2 - 2 * x := by linarith
  have h4 : (1 : ℝ) ≤ 2 + 2 * x := by linarith
  unfold bump
  rw [Real.smoothTransition.one_of_one_le h3, Real.smoothTransition.one_of_one_le h4, mul_one]

lemma bump_zero : ∀ x : ℝ, 1 ≤ |x| → bump x = 0 := by
  intro x hx
  unfold bump
  rcases le_total 0 x with h | h
  · have hx1 : 1 ≤ x := by rwa [abs_of_nonneg h] at hx
    have : 2 - 2 * x ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos this, zero_mul]
  · have hx1 : 1 ≤ -x := by rwa [abs_of_nonpos h] at hx
    have : 2 + 2 * x ≤ 0 := by linarith
    rw [Real.smoothTransition.zero_of_nonpos this, mul_zero]

lemma bump_bounds : ∀ x : ℝ, 0 ≤ bump x ∧ bump x ≤ 1 := by
  intro x
  unfold bump
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · rw [← mul_one 1]
    exact mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (by norm_num)

lemma bump_measurable : Measurable bump := (bump_contDiff 0).continuous.measurable

lemma bump_continuous : Continuous bump := (bump_contDiff 0).continuous

/-! ## The dyadic scale and the three kernels (`2π` convention) -/

/-- `h_j = 2^{-(j:ℝ)-1}`. -/
def hJ (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℝ) - 1)

/-- The sharp (indicator) kernel:
`z ↦ ∑_k ∫_{λ_k-h_j}^{λ_k+h_j} e^{-2π i z θ} dθ`. -/
def innerSharp (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) (z : ℝ) : ℂ :=
  ∑ k : Fin N, ∫ θ in (lam k - hJ j)..(lam k + hJ j),
    Complex.exp (-(2 * Real.pi * Complex.I * (z : ℂ) * (θ : ℂ)))

/-- The smooth-window kernel. -/
def innerSmooth (φ : ℝ → ℝ) (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) (z : ℝ) : ℂ :=
  ∑ k : Fin N, ∫ θ in (lam k - hJ j)..(lam k + hJ j),
    (((φ ((θ - lam k) / hJ j)) : ℝ) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * (z : ℂ) * (θ : ℂ)))

/-- The boundary-layer kernel (sharp minus smooth). -/
def innerBound (φ : ℝ → ℝ) (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) (z : ℝ) : ℂ :=
  ∑ k : Fin N, ∫ θ in (lam k - hJ j)..(lam k + hJ j),
    ((1 - φ ((θ - lam k) / hJ j)) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * (z : ℂ) * (θ : ℂ)))

/-- Pointwise identity of the kernels: sharp = smooth + boundary. -/
lemma inner_split (φ : ℝ → ℝ) (hφ : Continuous φ) (N : ℕ) (lam : Fin N → ℝ) (j : ℕ)
    (z : ℝ) :
    innerSharp N lam j z = innerSmooth φ N lam j z + innerBound φ N lam j z := by
  unfold innerSharp innerSmooth innerBound
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← intervalIntegral.integral_add]
  · refine intervalIntegral.integral_congr (fun θ _ => ?_)
    push_cast
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The three band-pass operators, as convolutions with the kernels above. -/
def sharpOp (N : ℕ) (lam : Fin N → ℝ) (g : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, g y * innerSharp N lam j (x - y)

def smoothOp (φ : ℝ → ℝ) (N : ℕ) (lam : Fin N → ℝ) (g : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, g y * innerSmooth φ N lam j (x - y)

def boundOp (φ : ℝ → ℝ) (N : ℕ) (lam : Fin N → ℝ) (g : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, g y * innerBound φ N lam j (x - y)

/-! ## Bridge to the commons `bst` kernel of `BoundaryLayer` -/

/-- The two ways of writing the `2π`-phase factor. -/
lemma exp_two_pi_eq (z θ : ℝ) :
    Complex.exp (-(2 * Real.pi * Complex.I * (z : ℂ) * (θ : ℂ)))
      = Complex.exp (-(Complex.I * (((2 * Real.pi * z : ℝ)) : ℂ) * (θ : ℂ))) := by
  congr 1
  push_cast
  ring

lemma innerBound_eq_bst (φ : ℝ → ℝ) (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) :
    innerBound φ N lam j
      = fun z : ℝ => BoundaryLayer.bst lam φ j (2 * Real.pi * z) := by
  funext z
  simp only [innerBound, BoundaryLayer.bst, BoundaryLayer.Fexp, hJ, BoundaryLayer.hj]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [exp_two_pi_eq]

lemma innerSmooth_eq_bst (φ : ℝ → ℝ) (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) :
    innerSmooth φ N lam j
      = fun z : ℝ => BoundaryLayer.bst lam (fun x => 1 - φ x) j (2 * Real.pi * z) := by
  funext z
  simp only [innerSmooth, BoundaryLayer.bst, BoundaryLayer.Fexp, hJ, BoundaryLayer.hj]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  rw [exp_two_pi_eq]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-! ## Scaling: `MemLp` is preserved by `z ↦ c * z` -/

lemma lintegral_comp_const_mul (c : ℝ) (hc : c ≠ 0)
    {F : ℝ → ℝ≥0∞} (hF : AEMeasurable F volume) :
    ∫⁻ z, F (c * z) = ENNReal.ofReal |c⁻¹| * ∫⁻ u, F u := by
  have hc' : ENNReal.ofReal |c⁻¹| ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff, abs_pos]; exact inv_ne_zero hc
  have hF' : AEMeasurable F (Measure.map (fun z : ℝ => c * z) volume) := by
    rw [Real.map_volume_mul_left hc]
    exact (aemeasurable_smul_measure_iff hc').mpr hF
  rw [← lintegral_map' (f := F) (g := fun z : ℝ => c * z) hF'
    (measurable_const_mul c).aemeasurable]
  rw [Real.map_volume_mul_left hc, lintegral_smul_measure]
  rfl

lemma memLp_comp_const_mul (c : ℝ) (hc : c ≠ 0) {K : ℝ → ℂ}
    (hK : MemLp K 2 (volume : Measure ℝ)) :
    MemLp (fun z : ℝ => K (c * z)) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ => K (c * z)) (volume : Measure ℝ) := by
    have hKmap : AEStronglyMeasurable K (Measure.map (fun z : ℝ => c * z) volume) := by
      rw [Real.map_volume_mul_left hc]
      exact hK.aestronglyMeasurable.smul_measure (ENNReal.ofReal |c⁻¹|)
    exact hKmap.comp_measurable (measurable_const_mul c)
  · rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := (2 : ℝ≥0∞))
      (f := fun z : ℝ => K (c * z)) (by norm_num) (by norm_num) hmeas]
    simp only [ENNReal.toReal_ofNat]
    have hF : AEMeasurable (fun u : ℝ => ‖K u‖ₑ ^ (2 : ℝ)) volume :=
      hK.aestronglyMeasurable.aemeasurable.enorm.pow_const 2
    rw [lintegral_comp_const_mul c hc hF]
    have hKint : ∫⁻ u, ‖K u‖ₑ ^ (2 : ℝ) < ⊤ := by
      have h1 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := (2 : ℝ≥0∞))
        (f := K) (by norm_num) (by norm_num) hK.aestronglyMeasurable).mp hK.eLpNorm_lt_top
      simpa using h1
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKint

lemma memLp_innerBound (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) :
    MemLp (innerBound φ N lam j) 2 (volume : Measure ℝ) := by
  rw [innerBound_eq_bst]
  exact memLp_comp_const_mul (2 * Real.pi) (by positivity)
    (BoundaryLayer.memLp_bst lam hφm hbd j)

lemma memLp_innerSmooth (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) :
    MemLp (innerSmooth φ N lam j) 2 (volume : Measure ℝ) := by
  rw [innerSmooth_eq_bst]
  refine memLp_comp_const_mul (2 * Real.pi) (by positivity)
    (BoundaryLayer.memLp_bst lam (φ := fun x : ℝ => 1 - φ x) ?_ ?_ j)
  · exact hφm.const_sub 1
  · intro x
    obtain ⟨h0, h1⟩ := hbd x
    exact ⟨by linarith, by linarith⟩

lemma memLp_innerBound_shift (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) (x : ℝ) :
    MemLp (fun y : ℝ => innerBound φ N lam j (x - y)) 2 (volume : Measure ℝ) :=
  (memLp_innerBound φ hφm hbd N lam j).comp_measurePreserving (BoundaryLayer.mpSub x)

lemma memLp_innerSmooth_shift (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) (x : ℝ) :
    MemLp (fun y : ℝ => innerSmooth φ N lam j (x - y)) 2 (volume : Measure ℝ) :=
  (memLp_innerSmooth φ hφm hbd N lam j).comp_measurePreserving (BoundaryLayer.mpSub x)

lemma measurable_innerBound (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) :
    Measurable (innerBound φ N lam j) := by
  rw [innerBound_eq_bst]
  exact (BoundaryLayer.measurable_bst lam hφm hbd j).comp (measurable_const_mul (2 * Real.pi))

lemma measurable_innerSmooth (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (N : ℕ) (lam : Fin N → ℝ) (j : ℕ) :
    Measurable (innerSmooth φ N lam j) := by
  rw [innerSmooth_eq_bst]
  refine (BoundaryLayer.measurable_bst lam (φ := fun x : ℝ => 1 - φ x) ?_ ?_ j).comp
    (measurable_const_mul (2 * Real.pi))
  · exact hφm.const_sub 1
  · intro x
    obtain ⟨h0, h1⟩ := hbd x
    exact ⟨by linarith, by linarith⟩

/-! ## Elementary helpers -/

/-- The pointwise inequality `(a+b)^2 ≤ 4(a^2+b^2)` in `ℝ≥0∞`. -/
lemma nn_add_sq_le (a b : NNReal) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have h : ((a + b : NNReal) : ℝ) ^ 2 ≤ 4 * (((a : ℝ)) ^ 2 + ((b : ℝ)) ^ 2) := by
    push_cast
    nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ))]
  exact_mod_cast h

lemma add_rpow_two_le (a b : ℝ≥0∞) :
    (a + b) ^ (2 : ℝ) ≤ 4 * (a ^ (2 : ℝ) + b ^ (2 : ℝ)) := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · simp [ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp [ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← ENNReal.coe_toNNReal ha, ← ENNReal.coe_toNNReal hb]
  push_cast
  exact_mod_cast nn_add_sq_le a.toNNReal b.toNNReal

/-- Measurability of convolution-like integrals. -/
lemma aestronglyMeasurable_conv {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ))
    {k : ℝ → ℂ} (hk : Measurable k) :
    AEStronglyMeasurable (fun x : ℝ => ∫ y : ℝ, g y * k (x - y)) (volume : Measure ℝ) := by
  have hJ' : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2 * k (p.1 - p.2))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    hg.aestronglyMeasurable.convolution_integrand (L := ContinuousLinearMap.mul ℂ ℂ)
      hk.aestronglyMeasurable
  exact hJ'.integral_prod_right'

end Sharp8

theorem sharp_of_smooth_window_maximal_l2
    (hsm : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (lam : Fin N → ℝ),
      (∀ i j : Fin N, i ≠ j → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam i - lam j|) →
      ∀ (φ : ℝ → ℝ), (∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) →
        (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
      ∀ (g : ℝ → ℂ), MeasureTheory.MemLp g 2 MeasureTheory.volume →
        ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, g y *
            (∑ k : Fin N,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                ((φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1)) : ℝ) : ℂ) *
                  Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal ((C * (Real.log ((N : ℝ) + 2)) ^ 2) ^ 2)
            * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (lam : Fin N → ℝ),
      (∀ i j : Fin N, i ≠ j → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam i - lam j|) →
      ∀ (g : ℝ → ℂ), MeasureTheory.MemLp g 2 MeasureTheory.volume →
        ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, g y *
            (∑ k : Fin N,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal ((C * (Real.log ((N : ℝ) + 2)) ^ 2) ^ 2)
            * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
  obtain ⟨C₁, hC₁pos, hswm⟩ := hsm
  obtain ⟨C₂, hC₂pos, hbl⟩ := Commons.Analysis.Fourier.boundary_layer_l2_eighth_separated
  refine ⟨Real.sqrt (4 * C₁ ^ 2 + 4 * C₂ ^ 2 / (Real.log 2) ^ 4), ?_, ?_⟩
  · rw [Real.sqrt_pos]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro N lam hsep g hg
    rw [show (∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, g y *
            (∑ k : Fin N,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.volume)
        = ∫⁻ x, (⨆ j : ℕ, ‖Sharp8.sharpOp N lam g j x‖ₑ) ^ (2 : ℝ)
            ∂MeasureTheory.volume from rfl]
    set L : ℝ := (Real.log ((N : ℝ) + 2)) ^ 2 with hLdef
    have hN2 : (1 : ℝ) < (N : ℝ) + 2 := by linarith [(show (0 : ℝ) ≤ (N : ℝ) by positivity)]
    have hLpos : 0 < L := by
      rw [hLdef]
      exact pow_pos (Real.log_pos hN2) 2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hLge : (Real.log 2) ^ 2 ≤ L := by
      rw [hLdef]
      exact pow_le_pow_left₀ hlog2.le
        (Real.log_le_log (by norm_num) (by linarith [(show (0 : ℝ) ≤ (N : ℝ) by positivity)])) 2
    have hsplit : ∀ (j : ℕ) (x : ℝ),
        Sharp8.sharpOp N lam g j x
          = Sharp8.smoothOp Sharp8.bump N lam g j x
            + Sharp8.boundOp Sharp8.bump N lam g j x := by
      intro j x
      have h1 : Integrable (fun y : ℝ => g y * Sharp8.innerSmooth Sharp8.bump N lam j (x - y))
          (volume : Measure ℝ) :=
        hg.integrable_mul (Sharp8.memLp_innerSmooth_shift Sharp8.bump Sharp8.bump_measurable
          Sharp8.bump_bounds N lam j x)
      have h2 : Integrable (fun y : ℝ => g y * Sharp8.innerBound Sharp8.bump N lam j (x - y))
          (volume : Measure ℝ) :=
        hg.integrable_mul (Sharp8.memLp_innerBound_shift Sharp8.bump Sharp8.bump_measurable
          Sharp8.bump_bounds N lam j x)
      have hcongr : (∫ y : ℝ, g y * Sharp8.innerSharp N lam j (x - y))
          = ∫ y : ℝ, (g y * Sharp8.innerSmooth Sharp8.bump N lam j (x - y)
              + g y * Sharp8.innerBound Sharp8.bump N lam j (x - y)) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Sharp8.inner_split Sharp8.bump Sharp8.bump_continuous N lam j (x - y), mul_add]
      simp only [Sharp8.sharpOp, Sharp8.smoothOp, Sharp8.boundOp]
      rw [hcongr, integral_add h1 h2]
    have hpoint : ∀ x : ℝ,
        (⨆ j : ℕ, ‖Sharp8.sharpOp N lam g j x‖ₑ) ^ (2 : ℝ)
          ≤ 4 * ((⨆ j : ℕ, ‖Sharp8.smoothOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ))
            + 4 * ((⨆ j : ℕ, ‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ)) := by
      intro x
      have h1 : (⨆ j : ℕ, ‖Sharp8.sharpOp N lam g j x‖ₑ)
          ≤ (⨆ j : ℕ, ‖Sharp8.smoothOp Sharp8.bump N lam g j x‖ₑ)
            + (⨆ j : ℕ, ‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ) := by
        refine iSup_le (fun j => ?_)
        rw [hsplit j x]
        exact le_trans (enorm_add_le _ _) (add_le_add
          (le_iSup (fun j : ℕ => ‖Sharp8.smoothOp Sharp8.bump N lam g j x‖ₑ) j)
          (le_iSup (fun j : ℕ => ‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ) j))
      calc (⨆ j : ℕ, ‖Sharp8.sharpOp N lam g j x‖ₑ) ^ (2 : ℝ)
          ≤ ((⨆ j : ℕ, ‖Sharp8.smoothOp Sharp8.bump N lam g j x‖ₑ)
              + (⨆ j : ℕ, ‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ)) ^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow h1 (by norm_num)
        _ ≤ 4 * (((⨆ j : ℕ, ‖Sharp8.smoothOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ))
              + ((⨆ j : ℕ, ‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ))) :=
            Sharp8.add_rpow_two_le _ _
        _ = 4 * ((⨆ j : ℕ, ‖Sharp8.smoothOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ))
            + 4 * ((⨆ j : ℕ, ‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ)) := by
            rw [mul_add]
    have hmeasS : AEMeasurable
        (fun x : ℝ => (⨆ j : ℕ, ‖Sharp8.smoothOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ))
        (volume : Measure ℝ) := by
      refine AEMeasurable.pow_const ?_ 2
      refine AEMeasurable.iSup (fun j => ?_)
      exact ((Sharp8.aestronglyMeasurable_conv hg
        (Sharp8.measurable_innerSmooth Sharp8.bump Sharp8.bump_measurable Sharp8.bump_bounds
          N lam j)).aemeasurable.enorm)
    have hsmooth : ∫⁻ x, (⨆ j : ℕ, ‖Sharp8.smoothOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ)
          ∂(volume : Measure ℝ)
        ≤ ENNReal.ofReal ((C₁ * L) ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) := by
      have h := hswm N lam hsep Sharp8.bump Sharp8.bump_one Sharp8.bump_zero Sharp8.bump_bounds g hg
      rw [← hLdef] at h
      simpa only [Sharp8.smoothOp, Sharp8.innerSmooth, Sharp8.hJ] using h
    have hbound : ∫⁻ x, (⨆ j : ℕ, ‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ)
          ∂(volume : Measure ℝ)
        ≤ ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) := by
      have hble := hbl N lam hsep Sharp8.bump Sharp8.bump_one Sharp8.bump_zero
        Sharp8.bump_bounds g hg
      have hble' : ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y : ℝ, g y *
              (∑ k : Fin N,
                ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                  ((1 - Sharp8.bump ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                    Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖
              ^ (2 : ℝ) ∂(volume : Measure ℝ)
          ≤ ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) := by
        simpa only [ENNReal.rpow_two] using hble
      calc ∫⁻ x, (⨆ j : ℕ, ‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ)
            ∂(volume : Measure ℝ)
          ≤ ∫⁻ x, ∑' j : ℕ, (‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ)
              ∂(volume : Measure ℝ) :=
            lintegral_mono (fun x =>
              BoundaryLayer.sq_iSup_le_tsum (fun j => ‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ))
        _ = ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖∫ y : ℝ, g y *
              (∑ k : Fin N,
                ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                  ((1 - Sharp8.bump ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                    Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖
              ^ (2 : ℝ) ∂(volume : Measure ℝ) := by
            apply lintegral_congr; intro x
            apply tsum_congr; intro j
            rw [BoundaryLayer.enorm_eq_ofReal_norm]
            simp only [Sharp8.boundOp, Sharp8.innerBound, Sharp8.hJ]
        _ ≤ ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) := hble'
    have hstep : ∫⁻ x, (⨆ j : ℕ, ‖Sharp8.sharpOp N lam g j x‖ₑ) ^ (2 : ℝ)
          ∂(volume : Measure ℝ)
        ≤ 4 * (ENNReal.ofReal ((C₁ * L) ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ))
          + 4 * (ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)) := by
      calc ∫⁻ x, (⨆ j : ℕ, ‖Sharp8.sharpOp N lam g j x‖ₑ) ^ (2 : ℝ) ∂(volume : Measure ℝ)
          ≤ ∫⁻ x, (4 * ((⨆ j : ℕ, ‖Sharp8.smoothOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ))
              + 4 * ((⨆ j : ℕ, ‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ)))
              ∂(volume : Measure ℝ) := lintegral_mono hpoint
        _ = 4 * ∫⁻ x, (⨆ j : ℕ, ‖Sharp8.smoothOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ)
              ∂(volume : Measure ℝ)
            + 4 * ∫⁻ x, (⨆ j : ℕ, ‖Sharp8.boundOp Sharp8.bump N lam g j x‖ₑ) ^ (2 : ℝ)
              ∂(volume : Measure ℝ) := by
            rw [lintegral_add_left' (hmeasS.const_mul 4) _]
            rw [lintegral_const_mul' 4 _ (by norm_num)]
            rw [lintegral_const_mul' 4 _ (by norm_num)]
        _ ≤ 4 * (ENNReal.ofReal ((C₁ * L) ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ))
            + 4 * (ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)) :=
            add_le_add (mul_le_mul_right hsmooth 4) (mul_le_mul_right hbound 4)
    have hlog4 : 0 < (Real.log 2) ^ 4 := pow_pos hlog2 4
    have hLnn : 0 ≤ L := hLpos.le
    have hratio : 1 ≤ L ^ 2 / (Real.log 2) ^ 4 := by
      have h1 : ((Real.log 2) ^ 2) ^ 2 ≤ L ^ 2 :=
        pow_le_pow_left₀ (pow_nonneg hlog2.le 2) hLge 2
      have h2 : ((Real.log 2) ^ 2) ^ 2 = (Real.log 2) ^ 4 := by ring
      rw [le_div_iff₀ hlog4, one_mul, ← h2]
      exact h1
    have hmul : 4 * C₂ ^ 2 ≤ 4 * C₂ ^ 2 * (L ^ 2 / (Real.log 2) ^ 4) := by
      have h := mul_le_mul_of_nonneg_left hratio (by positivity : (0 : ℝ) ≤ 4 * C₂ ^ 2)
      simpa using h
    have hreal : 4 * (C₁ * L) ^ 2 + 4 * C₂ ^ 2
        ≤ (Real.sqrt (4 * C₁ ^ 2 + 4 * C₂ ^ 2 / (Real.log 2) ^ 4) * L) ^ 2 := by
      have hSnn : 0 ≤ 4 * C₁ ^ 2 + 4 * C₂ ^ 2 / (Real.log 2) ^ 4 :=
        add_nonneg (by positivity) (div_nonneg (by positivity) hlog4.le)
      conv_rhs => rw [mul_pow, Real.sq_sqrt hSnn]
      have key : 4 * (C₁ * L) ^ 2 + 4 * C₂ ^ 2
          ≤ (4 * C₁ ^ 2 + 4 * C₂ ^ 2 / (Real.log 2) ^ 4) * L ^ 2 := by
        have h1 : 4 * (C₁ * L) ^ 2 = 4 * C₁ ^ 2 * L ^ 2 := by ring
        have h2 : 4 * C₂ ^ 2 * (L ^ 2 / (Real.log 2) ^ 4)
            = 4 * C₂ ^ 2 / (Real.log 2) ^ 4 * L ^ 2 := by ring
        nlinarith [hmul, h1, h2]
      exact key
    have hfinal : 4 * (ENNReal.ofReal ((C₁ * L) ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ)
            ∂(volume : Measure ℝ))
          + 4 * (ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ))
        ≤ ENNReal.ofReal ((Real.sqrt (4 * C₁ ^ 2 + 4 * C₂ ^ 2 / (Real.log 2) ^ 4) * L) ^ 2)
          * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) := by
      set B : ℝ≥0∞ := ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) with hB
      have e1 : (4 : ℝ≥0∞) * (ENNReal.ofReal ((C₁ * L) ^ 2) * B)
          = ENNReal.ofReal (4 * (C₁ * L) ^ 2) * B := by
        rw [← ENNReal.ofReal_ofNat 4, ← mul_assoc,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have e2 : (4 : ℝ≥0∞) * (ENNReal.ofReal (C₂ ^ 2) * B)
          = ENNReal.ofReal (4 * C₂ ^ 2) * B := by
        rw [← ENNReal.ofReal_ofNat 4, ← mul_assoc,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [e1, e2]
      rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) B
    exact le_trans hstep hfinal

end

end Commons.Analysis.Fourier
