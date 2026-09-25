import Mathlib
import Submission.Commons.Analysis.Fourier.boundary_layer_l2

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1600000

namespace SepWin

/-! ## A smooth bump and its properties -/

/-- A fixed smooth bump: `= 1` on `[-1/2,1/2]`, `= 0` off `[-1,1]`, with `0 ≤ φ ≤ 1`.
(Note `ContDiff ℝ ⊤` in Mathlib means *analytic*, which is incompatible with these bump
conditions; hence this file uses `ContDiff ℝ n` for all `n : ℕ` (i.e. `C^∞`).) -/
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

/-! ## The dyadic scale and the three kernels -/

/-- `h_j = 2^{-(j:ℝ)-1}`. -/
def hJ (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℝ) - 1)

lemma hJ_pos (j : ℕ) : 0 < hJ j := Real.rpow_pos_of_pos (by norm_num) _

lemma hJ_le_half (j : ℕ) : hJ j ≤ 1 / 2 := by
  unfold hJ
  calc (2 : ℝ) ^ (-(j : ℝ) - 1) ≤ (2 : ℝ) ^ (-(1 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
        linarith
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

/-- The sharp (indicator) kernel: `z ↦ ∑_k ∫_{λ_k-h_j}^{λ_k+h_j} e^{-i z θ} dθ`. -/
def innerSharp (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) (z : ℝ) : ℂ :=
  ∑ k : Fin K, ∫ θ in (lam k - hJ j)..(lam k + hJ j),
    Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ)))

/-- The smooth-window kernel. -/
def innerSmooth (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) (z : ℝ) : ℂ :=
  ∑ k : Fin K, ∫ θ in (lam k - hJ j)..(lam k + hJ j),
    (φ ((θ - lam k) / hJ j) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ)))

/-- The boundary-layer kernel (sharp minus smooth). -/
def innerBound (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) (z : ℝ) : ℂ :=
  ∑ k : Fin K, ∫ θ in (lam k - hJ j)..(lam k + hJ j),
    ((1 - φ ((θ - lam k) / hJ j)) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ)))

/-- Pointwise identity of the kernels: sharp = smooth + boundary. -/
lemma inner_split (φ : ℝ → ℝ) (hφ : Continuous φ) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ)
    (z : ℝ) :
    innerSharp K lam j z = innerSmooth φ K lam j z + innerBound φ K lam j z := by
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
def sharpOp (K : ℕ) (lam : Fin K → ℝ) (f : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, f y * innerSharp K lam j (x - y)

def smoothOp (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (f : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, f y * innerSmooth φ K lam j (x - y)

def boundOp (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (f : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, f y * innerBound φ K lam j (x - y)

/-! ## Bridge to the commons `bst` kernel of `boundary_layer_l2` -/

lemma hJ_eq_hj (j : ℕ) : hJ j = BoundaryLayer.hj j := rfl

lemma innerBound_eq_bst (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) :
    innerBound φ K lam j = BoundaryLayer.bst lam φ j := by
  funext z
  simp only [innerBound, BoundaryLayer.bst, BoundaryLayer.Fexp, hJ, BoundaryLayer.hj]

lemma innerSmooth_eq_bst (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) :
    innerSmooth φ K lam j = BoundaryLayer.bst lam (fun x => 1 - φ x) j := by
  funext z
  simp only [innerSmooth, BoundaryLayer.bst, BoundaryLayer.Fexp, hJ, BoundaryLayer.hj]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  congr 1
  push_cast
  ring

lemma memLp_innerBound (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) :
    MemLp (innerBound φ K lam j) 2 (volume : Measure ℝ) := by
  rw [innerBound_eq_bst]
  exact BoundaryLayer.memLp_bst lam hφm hbd j

lemma memLp_innerSmooth (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) :
    MemLp (innerSmooth φ K lam j) 2 (volume : Measure ℝ) := by
  rw [innerSmooth_eq_bst]
  refine BoundaryLayer.memLp_bst lam (φ := fun x : ℝ => 1 - φ x) ?_ ?_ j
  · exact hφm.const_sub 1
  · intro x
    obtain ⟨h0, h1⟩ := hbd x
    exact ⟨by linarith, by linarith⟩

lemma memLp_innerBound_shift (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) (x : ℝ) :
    MemLp (fun y : ℝ => innerBound φ K lam j (x - y)) 2 (volume : Measure ℝ) :=
  (memLp_innerBound φ hφm hbd K lam j).comp_measurePreserving (BoundaryLayer.mpSub x)

lemma memLp_innerSmooth_shift (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) (x : ℝ) :
    MemLp (fun y : ℝ => innerSmooth φ K lam j (x - y)) 2 (volume : Measure ℝ) :=
  (memLp_innerSmooth φ hφm hbd K lam j).comp_measurePreserving (BoundaryLayer.mpSub x)

/-! ## Elementary helpers -/

lemma enorm_complex_eq_ofReal (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]; norm_cast

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

/-- A measurability statement for convolution-like integrals. -/
lemma measurable_innerBound (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) :
    Measurable (innerBound φ K lam j) := by
  rw [innerBound_eq_bst]
  exact BoundaryLayer.measurable_bst lam hφm hbd j

lemma measurable_innerSmooth (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) :
    Measurable (innerSmooth φ K lam j) := by
  rw [innerSmooth_eq_bst]
  refine BoundaryLayer.measurable_bst lam (φ := fun x : ℝ => 1 - φ x) ?_ ?_ j
  · exact hφm.const_sub 1
  · intro x
    obtain ⟨h0, h1⟩ := hbd x
    exact ⟨by linarith, by linarith⟩

lemma aestronglyMeasurable_conv {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ))
    {k : ℝ → ℂ} (hk : Measurable k) :
    AEStronglyMeasurable (fun x : ℝ => ∫ y : ℝ, f y * k (x - y)) (volume : Measure ℝ) := by
  have hJ : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2 * k (p.1 - p.2))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    hf.aestronglyMeasurable.convolution_integrand (L := ContinuousLinearMap.mul ℂ ℂ)
      hk.aestronglyMeasurable
  exact hJ.integral_prod_right'

/-- The exact statement of the smooth-window maximal estimate (Bourgain 1989, Lemma 4.13)
used as the single external input below. -/
def SmoothWindowMaximal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
    (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
    ∀ (φ : ℝ → ℝ), (∀ n : ℕ, ContDiff ℝ n φ) →
      (∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) →
      (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
    ∀ (f : ℝ → ℂ), MemLp f 2 (volume : Measure ℝ) →
      ∫⁻ x, (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2 : ℝ) ∂(volume : Measure ℝ)
        ≤ ENNReal.ofReal ((C * (Real.log ((K : ℝ) + 2)) ^ 2) ^ 2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)


/-- The target statement of the file, expressed through `sharpOp`. -/
def TargetStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
    (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
    ∀ (f : ℝ → ℂ), MemLp f 2 (volume : Measure ℝ) →
      ∫⁻ x, (⨆ j : ℕ, ‖sharpOp K lam f j x‖ₑ) ^ (2 : ℝ) ∂(volume : Measure ℝ)
        ≤ ENNReal.ofReal ((C * (Real.log ((K : ℝ) + 2)) ^ 2) ^ 2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ)

theorem target_of_components (hSWM : SmoothWindowMaximal) : TargetStatement := by
  obtain ⟨C₁, hC₁pos, hswm⟩ := hSWM
  obtain ⟨C₂, hC₂pos, hbl⟩ := Commons.Analysis.Fourier.boundary_layer_l2
  refine ⟨Real.sqrt (4 * C₁ ^ 2 + 4 * C₂ ^ 2 / (Real.log 2) ^ 4), ?_, ?_⟩
  · rw [Real.sqrt_pos]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro K lam hsep f hf
    set L : ℝ := (Real.log ((K : ℝ) + 2)) ^ 2 with hLdef
    have hK2 : (1 : ℝ) < (K : ℝ) + 2 := by linarith [(show (0:ℝ) ≤ (K:ℝ) by positivity)]
    have hLpos : 0 < L := by
      rw [hLdef]
      exact pow_pos (Real.log_pos hK2) 2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hLge : (Real.log 2) ^ 2 ≤ L := by
      rw [hLdef]
      exact pow_le_pow_left₀ hlog2.le
        (Real.log_le_log (by norm_num) (by linarith [(show (0:ℝ) ≤ (K:ℝ) by positivity)])) 2
    -- The pointwise splitting of the sharp operator.
    have hsplit : ∀ (j : ℕ) (x : ℝ),
        sharpOp K lam f j x = smoothOp bump K lam f j x + boundOp bump K lam f j x := by
      intro j x
      have h1 : Integrable (fun y : ℝ => f y * innerSmooth bump K lam j (x - y))
          (volume : Measure ℝ) :=
        hf.integrable_mul (memLp_innerSmooth_shift bump bump_measurable bump_bounds K lam j x)
      have h2 : Integrable (fun y : ℝ => f y * innerBound bump K lam j (x - y))
          (volume : Measure ℝ) :=
        hf.integrable_mul (memLp_innerBound_shift bump bump_measurable bump_bounds K lam j x)
      have hcongr : (∫ y : ℝ, f y * innerSharp K lam j (x - y))
          = ∫ y : ℝ, (f y * innerSmooth bump K lam j (x - y)
              + f y * innerBound bump K lam j (x - y)) := by
        apply integral_congr_ae
        filter_upwards with y
        rw [inner_split bump bump_continuous K lam j (x - y), mul_add]
      simp only [sharpOp, smoothOp, boundOp]
      rw [hcongr, integral_add h1 h2]
    -- Pointwise bound on the sup.
    have hpoint : ∀ x : ℝ,
        (⨆ j : ℕ, ‖sharpOp K lam f j x‖ₑ) ^ (2 : ℝ)
          ≤ 4 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2 : ℝ))
            + 4 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2 : ℝ)) := by
      intro x
      have h1 : (⨆ j : ℕ, ‖sharpOp K lam f j x‖ₑ)
          ≤ (⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ)
            + (⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) := by
        refine iSup_le (fun j => ?_)
        rw [hsplit j x]
        exact le_trans (enorm_add_le _ _) (add_le_add
          (le_iSup (fun j : ℕ => ‖smoothOp bump K lam f j x‖ₑ) j)
          (le_iSup (fun j : ℕ => ‖boundOp bump K lam f j x‖ₑ) j))
      calc (⨆ j : ℕ, ‖sharpOp K lam f j x‖ₑ) ^ (2 : ℝ)
          ≤ ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ)
              + (⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ)) ^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow h1 (by norm_num)
        _ ≤ 4 * (((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2 : ℝ))
              + ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2 : ℝ))) := add_rpow_two_le _ _
        _ = 4 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2 : ℝ))
            + 4 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2 : ℝ)) := by rw [mul_add]
    -- Measurability of the smooth part.
    have hmeasS : AEMeasurable
        (fun x : ℝ => (⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2 : ℝ))
        (volume : Measure ℝ) := by
      refine AEMeasurable.pow_const ?_ 2
      refine AEMeasurable.iSup (fun j => ?_)
      exact ((aestronglyMeasurable_conv hf
        (measurable_innerSmooth bump bump_measurable bump_bounds K lam j)).aemeasurable.enorm)
    -- The two component estimates.
    have hsmooth := hswm K lam hsep bump (fun n => bump_contDiff n) bump_one bump_zero
      bump_bounds f hf
    have hbound : ∫⁻ x, (⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2 : ℝ)
        ∂(volume : Measure ℝ)
        ≤ ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) := by
      have hble := hbl K lam hsep bump bump_one bump_zero bump_bounds f hf
      have hbo : ∀ (j : ℕ) (x : ℝ), boundOp bump K lam f j x
          = ∫ y : ℝ, f y * BoundaryLayer.bst lam bump j (x - y) := by
        intro j x
        simp only [boundOp, innerBound, BoundaryLayer.bst, BoundaryLayer.Fexp, hJ,
          BoundaryLayer.hj]
      calc ∫⁻ x, (⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2 : ℝ) ∂(volume : Measure ℝ)
          ≤ ∫⁻ x, ∑' j : ℕ, (‖boundOp bump K lam f j x‖ₑ) ^ (2 : ℝ)
              ∂(volume : Measure ℝ) :=
            lintegral_mono (fun x =>
              BoundaryLayer.sq_iSup_le_tsum (fun j => ‖boundOp bump K lam f j x‖ₑ))
        _ = ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal
              ‖∫ y : ℝ, f y * BoundaryLayer.bst lam bump j (x - y)‖ ^ (2 : ℝ)
              ∂(volume : Measure ℝ) := by
            apply lintegral_congr; intro x
            apply tsum_congr; intro j
            rw [hbo j x, enorm_complex_eq_ofReal,
              ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
        _ ≤ ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2 : ℝ)
              ∂(volume : Measure ℝ) := hble
        _ = ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)
              ∂(volume : Measure ℝ) := by
            congr 1
            apply lintegral_congr; intro x
            rw [enorm_complex_eq_ofReal]
    -- Assembly.
    have hstep : ∫⁻ x, (⨆ j : ℕ, ‖sharpOp K lam f j x‖ₑ) ^ (2 : ℝ) ∂(volume : Measure ℝ)
        ≤ 4 * (ENNReal.ofReal ((C₁ * L) ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ))
          + 4 * (ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)
              ∂(volume : Measure ℝ)) := by
      calc ∫⁻ x, (⨆ j : ℕ, ‖sharpOp K lam f j x‖ₑ) ^ (2 : ℝ) ∂(volume : Measure ℝ)
          ≤ ∫⁻ x, (4 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2 : ℝ))
              + 4 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2 : ℝ)))
              ∂(volume : Measure ℝ) := lintegral_mono hpoint
        _ = 4 * ∫⁻ x, (⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2 : ℝ)
              ∂(volume : Measure ℝ)
            + 4 * ∫⁻ x, (⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2 : ℝ)
              ∂(volume : Measure ℝ) := by
            rw [lintegral_add_left' (hmeasS.const_mul 4) _]
            rw [lintegral_const_mul' 4 _ (by norm_num)]
            rw [lintegral_const_mul' 4 _ (by norm_num)]
        _ ≤ 4 * (ENNReal.ofReal ((C₁ * L) ^ 2)
              * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ))
            + 4 * (ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)
              ∂(volume : Measure ℝ)) :=
            add_le_add (mul_le_mul_right hsmooth 4) (mul_le_mul_right hbound 4)
    -- final constant comparison
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
    have hfinal : 4 * (ENNReal.ofReal ((C₁ * L) ^ 2)
            * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ))
          + 4 * (ENNReal.ofReal (C₂ ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ))
        ≤ ENNReal.ofReal ((Real.sqrt (4 * C₁ ^ 2 + 4 * C₂ ^ 2 / (Real.log 2) ^ 4) * L) ^ 2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) := by
      set B : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ) with hB
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


/-- The inline form of the smooth-window hypothesis implies `SmoothWindowMaximal`. -/
lemma smoothWindowMaximal_of_inline
    (h : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (φ : ℝ → ℝ), (∀ n : ℕ, ContDiff ℝ n φ) →
        (∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) →
        (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
      ∀ (f : ℝ → ℂ), MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
        ∫⁻ x, (⨆ j : ℕ, ENNReal.ofReal ‖∫ y : ℝ, f y *
            (∑ k : Fin K, ∫ θ in (lam k - (2:ℝ)^(-(j:ℝ)-1))..(lam k + (2:ℝ)^(-(j:ℝ)-1)),
              (φ ((θ - lam k) / (2:ℝ)^(-(j:ℝ)-1)) : ℂ) *
              Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖) ^ (2:ℝ)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2)
          * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    SmoothWindowMaximal := by
  obtain ⟨C, hC, h'⟩ := h
  refine ⟨C, hC, ?_⟩
  intro K lam hsep φ hφ h1 h0 hb f hf
  have hh := h' K lam hsep φ hφ h1 h0 hb f hf
  simpa only [BoundaryLayer.enorm_eq_ofReal_norm, smoothOp, innerSmooth, hJ] using hh

end SepWin

theorem separated_maximal_of_smooth_window :
    (∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (φ : ℝ → ℝ), (∀ n : ℕ, ContDiff ℝ n φ) →
        (∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) →
        (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
      ∀ (f : ℝ → ℂ), MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
        ∫⁻ x, (⨆ j : ℕ, ENNReal.ofReal ‖∫ y : ℝ, f y *
            (∑ k : Fin K, ∫ θ in (lam k - (2:ℝ)^(-(j:ℝ)-1))..(lam k + (2:ℝ)^(-(j:ℝ)-1)),
              (φ ((θ - lam k) / (2:ℝ)^(-(j:ℝ)-1)) : ℂ) *
              Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖) ^ (2:ℝ)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2)
          * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)) →
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)),
        ∫⁻ x, (⨆ j : ℕ, ENNReal.ofReal ‖∫ y : ℝ, f y *
            (∑ k : Fin K,
              ∫ θ in (lam k - (2:ℝ)^(-(j:ℝ)-1))..(lam k + (2:ℝ)^(-(j:ℝ)-1)),
                Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖) ^ (2:ℝ)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2)
          * ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  intro hSWM
  obtain ⟨C, hC, hG⟩ :=
    SepWin.target_of_components (SepWin.smoothWindowMaximal_of_inline hSWM)
  refine ⟨C, hC, ?_⟩
  intro K lam hsep f hf
  have hh := hG K lam hsep f hf
  simpa only [BoundaryLayer.enorm_eq_ofReal_norm, SepWin.sharpOp, SepWin.innerSharp, SepWin.hJ]
    using hh


end

end Commons.Analysis.Fourier
