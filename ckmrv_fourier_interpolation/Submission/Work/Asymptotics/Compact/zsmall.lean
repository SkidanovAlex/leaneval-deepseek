/-
# A cusp-smallness toolkit for `K₊^{(24)}` at `z = i t`

This file collects the `O(qⁿ)` facts (with `q = qParamFun z = e^{2πiz}`) about the `z`-atoms
which occur in the five remainder groups `Sm1, …, Sm5` of the cusp expansion of `K₊^{(24)}`,
together with the closure properties of the predicate `IsSmallT T f n` used to combine them.

The results are `τ`-free: they concern functions of `z` only, uniformly on `{T ≤ Im z}`.
They are used by `Submission/Work/Asymptotics/Compact/kplus24_sm_bound.lean`.
-/
import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.cusp_invDelta
import Submission.Work.Asymptotics.jInvariantFun_cusp_second
import Submission.Work.Asymptotics.E4cube_cusp_second
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atTop
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics.Small

open Work.Kernels

/-- `S₀(z) = 1 - 6i/(π z)`, the leading term of `E₂ˢ` at the cusp
(cf. `Work.Asymptotics.Compact.K24.S0`). -/
def S0c (z : ℍ) : ℂ := 1 - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))

/-- `IsSmallT T f n` : `f = O(qⁿ)` on `{z : T ≤ Im z}`, where `q = qParamFun z = e^{2πiz}`. -/
def IsSmallT (T : ℝ) (f : ℍ → ℂ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, T ≤ z.im → ‖f z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ n

/-- `qParamFun z = Ept z ^ 2`. -/
theorem qParamFun_eq_Ept_sq (z : ℍ) : qParamFun z = Work.Residues.Ept z ^ 2 := by
  rw [Work.Residues.Ept, qParamFun, sq, ← Complex.exp_add]
  congr 1; ring

theorem norm_Ept_sq_eq (z : ℍ) : ‖Work.Residues.Ept z‖ ^ 2 = ‖qParamFun z‖ := by
  rw [← norm_pow, qParamFun_eq_Ept_sq]

theorem Ept_inv_sq_eq (z : ℍ) : (Work.Residues.Ept z)⁻¹ ^ 2 = (qParamFun z)⁻¹ := by
  rw [inv_pow, ← qParamFun_eq_Ept_sq]

variable {T T' : ℝ} {f g : ℍ → ℂ} {m n : ℕ}

/-- Raising the threshold weakens the statement. -/
theorem IsSmallT.of_le (hTT' : T ≤ T') (h : IsSmallT T f n) : IsSmallT T' f n := by
  obtain ⟨C, hC, hf⟩ := h
  exact ⟨C, hC, fun z hz => hf z (le_trans hTT' hz)⟩

theorem IsSmallT.congr (h : IsSmallT T f n) (hfg : ∀ z, f z = g z) : IsSmallT T g n := by
  obtain ⟨C, hC, hf⟩ := h
  exact ⟨C, hC, fun z hz => by rw [← hfg z]; exact hf z hz⟩

theorem IsSmallT.congr_of (h : IsSmallT T f n) (hfg : ∀ z, T ≤ z.im → f z = g z) :
    IsSmallT T g n := by
  obtain ⟨C, hC, hf⟩ := h
  exact ⟨C, hC, fun z hz => by rw [← hfg z hz]; exact hf z hz⟩

theorem IsSmallT.bounded (B : ℝ) (hB : 0 < B) (h : ∀ z : ℍ, T ≤ z.im → ‖f z‖ ≤ B) :
    IsSmallT T f 0 := by
  refine ⟨B, hB, fun z hz => ?_⟩
  simpa using h z hz

theorem qParamFun_small (T : ℝ) : IsSmallT T qParamFun 1 :=
  ⟨1, one_pos, fun z _ => by simp⟩

theorem IsSmallT.const_mul (c : ℂ) (h : IsSmallT T f n) :
    IsSmallT T (fun z => c * f z) n := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨‖c‖ * C + 1, by positivity, fun z hz => ?_⟩
  rw [norm_mul]
  have h1 := hf z hz
  have h2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg c)
  have h3 := pow_nonneg (norm_nonneg (qParamFun z)) n
  nlinarith [h2, hC.le]

theorem IsSmallT.neg (h : IsSmallT T f n) : IsSmallT T (fun z => -f z) n := by
  have h' := IsSmallT.const_mul (-1 : ℂ) h
  simpa using h'

theorem IsSmallT.add (hT1 : 1 ≤ T) (hf : IsSmallT T f m) (hg : IsSmallT T g n) :
    IsSmallT T (fun z => f z + g z) (min m n) := by
  obtain ⟨C1, hC1, h1⟩ := hf
  obtain ⟨C2, hC2, h2⟩ := hg
  refine ⟨C1 + C2, by positivity, fun z hz => ?_⟩
  have hp := h1 z hz
  have hq := h2 z hz
  have hq1 := norm_qParamFun_le_one z (le_trans hT1 hz)
  have h3 : ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le (f z) (g z)
  have h4 : ‖qParamFun z‖ ^ n ≤ ‖qParamFun z‖ ^ min m n :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 (min_le_right _ _)
  have h5 : ‖qParamFun z‖ ^ m ≤ ‖qParamFun z‖ ^ min m n :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 (min_le_left _ _)
  have e1 : ‖f z‖ ≤ C1 * ‖qParamFun z‖ ^ min m n := le_trans hp (mul_le_mul_of_nonneg_left h5 hC1.le)
  have e2 : ‖g z‖ ≤ C2 * ‖qParamFun z‖ ^ min m n := le_trans hq (mul_le_mul_of_nonneg_left h4 hC2.le)
  rw [add_mul]
  linarith

theorem IsSmallT.sub (hT1 : 1 ≤ T) (hf : IsSmallT T f m) (hg : IsSmallT T g n) :
    IsSmallT T (fun z => f z - g z) (min m n) := by
  have h := hf.add hT1 hg.neg
  exact h.congr (fun z => by ring)

theorem IsSmallT.mul (hT1 : 1 ≤ T) (hf : IsSmallT T f m) (hg : IsSmallT T g n) :
    IsSmallT T (fun z => f z * g z) (m + n) := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf * Cg + 1, by positivity, fun z hz => ?_⟩
  have h1 := hf z hz
  have h2 := hg z hz
  have hb : (0:ℝ) ≤ Cf * ‖qParamFun z‖ ^ m :=
    mul_nonneg hCf.le (pow_nonneg (norm_nonneg _) m)
  have hc : (0:ℝ) ≤ ‖g z‖ := norm_nonneg _
  have h4 : ‖f z‖ * ‖g z‖ ≤ (Cf * ‖qParamFun z‖ ^ m)
      * (Cg * ‖qParamFun z‖ ^ n) := mul_le_mul h1 h2 hc hb
  have hXY : (0:ℝ) ≤ ‖qParamFun z‖ ^ m * ‖qParamFun z‖ ^ n :=
    mul_nonneg (pow_nonneg (norm_nonneg _) m) (pow_nonneg (norm_nonneg _) n)
  have h5 : (Cf * ‖qParamFun z‖ ^ m) * (Cg * ‖qParamFun z‖ ^ n)
      ≤ (Cf * Cg + 1) * (‖qParamFun z‖ ^ m * ‖qParamFun z‖ ^ n) := by
    nlinarith [hXY, hCf.le, hCg.le]
  rw [norm_mul, pow_add]
  linarith [le_trans h4 h5]

theorem IsSmallT.mono (hT1 : 1 ≤ T) (h : IsSmallT T f n) (hmn : m ≤ n) : IsSmallT T f m := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, fun z hz => ?_⟩
  have h1 := hf z hz
  have hq1 := norm_qParamFun_le_one z (le_trans hT1 hz)
  have h2 : ‖qParamFun z‖ ^ n ≤ ‖qParamFun z‖ ^ m :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 hmn
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hC.le)

/-- `‖S₀ z‖ ≤ 3` for `Im z ≥ 1`. -/
theorem S0c_norm_le (z : ℍ) (hz : 1 ≤ z.im) : ‖S0c z‖ ≤ 3 := by
  have hz1 : (1 : ℝ) ≤ ‖(z : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (z : ℂ)
    rw [UpperHalfPlane.coe_im, abs_of_pos z.im_pos] at h
    linarith
  have hzpos : (0 : ℝ) < ‖(z : ℂ)‖ := lt_of_lt_of_le one_pos hz1
  have h1 : ‖6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))‖ = 6 / (Real.pi * ‖(z : ℂ)‖) := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    try ring
  rw [S0c]
  calc ‖(1 : ℂ) - 6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))‖
      ≤ ‖(1:ℂ)‖ + ‖6 * Complex.I / ((Real.pi : ℂ) * (z : ℂ))‖ := norm_sub_le _ _
    _ = 1 + 6 / (Real.pi * ‖(z:ℂ)‖) := by rw [h1, norm_one]
    _ ≤ 3 := by
        have h2 : 6 / (Real.pi * ‖(z:ℂ)‖) ≤ 6 / Real.pi := by
          rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
          nlinarith [hz1, Real.pi_pos]
        have h3 : 6 / Real.pi ≤ 2 := by
          rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
        linarith

theorem S0c_bounded : IsSmallT 1 S0c 0 :=
  IsSmallT.bounded 3 (by norm_num) (fun z hz => S0c_norm_le z hz)

/-- `E₄ - 1 = O(q)`. -/
theorem E4_sub_one : IsSmallT 1 (fun z => E4Fun z - 1) 1 := by
  obtain ⟨C, hC, h⟩ := E4Fun_two_term
  refine ⟨240 + C, by positivity, fun z hz => ?_⟩
  dsimp only
  have h1 := h z hz
  have hq1 := norm_qParamFun_le_one z hz
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith [hq1, norm_nonneg (qParamFun z)]
  have hsplit : E4Fun z - 1 = (E4Fun z - 1 - 240 * qParamFun z) + 240 * qParamFun z := by ring
  rw [hsplit]
  have h240 : ‖(240 : ℂ) * qParamFun z‖ = 240 * ‖qParamFun z‖ := by
    rw [norm_mul, Complex.norm_ofNat]
  calc ‖(E4Fun z - 1 - 240 * qParamFun z) + 240 * qParamFun z‖
      ≤ ‖E4Fun z - 1 - 240 * qParamFun z‖ + ‖(240 : ℂ) * qParamFun z‖ := norm_add_le _ _
    _ ≤ C * ‖qParamFun z‖ ^ 2 + 240 * ‖qParamFun z‖ := by rw [h240]; linarith
    _ ≤ (240 + C) * ‖qParamFun z‖ ^ 1 := by rw [pow_one]; nlinarith [hC.le, hq2, norm_nonneg (qParamFun z)]

/-- `E₆ - 1 = O(q)`. -/
theorem E6_sub_one : IsSmallT 1 (fun z => E6Fun z - 1) 1 := by
  obtain ⟨C, hC, h⟩ := E6Fun_two_term
  refine ⟨504 + C, by positivity, fun z hz => ?_⟩
  dsimp only
  have h1 := h z hz
  have hq1 := norm_qParamFun_le_one z hz
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith [hq1, norm_nonneg (qParamFun z)]
  have hsplit : E6Fun z - 1 = (E6Fun z - 1 + 504 * qParamFun z) - 504 * qParamFun z := by ring
  rw [hsplit]
  have h504 : ‖(504 : ℂ) * qParamFun z‖ = 504 * ‖qParamFun z‖ := by
    rw [norm_mul, Complex.norm_ofNat]
  calc ‖(E6Fun z - 1 + 504 * qParamFun z) - 504 * qParamFun z‖
      ≤ ‖E6Fun z - 1 + 504 * qParamFun z‖ + ‖(504 : ℂ) * qParamFun z‖ := norm_sub_le _ _
    _ ≤ C * ‖qParamFun z‖ ^ 2 + 504 * ‖qParamFun z‖ := by rw [h504]; linarith
    _ ≤ (504 + C) * ‖qParamFun z‖ ^ 1 := by rw [pow_one]; nlinarith [hC.le, hq2, norm_nonneg (qParamFun z)]

/-- `E₂ - 1 = O(q)`. -/
theorem E2_sub_one : IsSmallT 1 (fun z => E2Fun z - 1) 1 := by
  obtain ⟨C, hC, h⟩ := E2Fun_two_term
  refine ⟨24 + C, by positivity, fun z hz => ?_⟩
  dsimp only
  have h1 := h z hz
  have hq1 := norm_qParamFun_le_one z hz
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith [hq1, norm_nonneg (qParamFun z)]
  have hsplit : E2Fun z - 1 = (E2Fun z - 1 + 24 * qParamFun z) - 24 * qParamFun z := by ring
  rw [hsplit]
  have h24 : ‖(24 : ℂ) * qParamFun z‖ = 24 * ‖qParamFun z‖ := by
    rw [norm_mul, Complex.norm_ofNat]
  calc ‖(E2Fun z - 1 + 24 * qParamFun z) - 24 * qParamFun z‖
      ≤ ‖E2Fun z - 1 + 24 * qParamFun z‖ + ‖(24 : ℂ) * qParamFun z‖ := norm_sub_le _ _
    _ ≤ C * ‖qParamFun z‖ ^ 2 + 24 * ‖qParamFun z‖ := by rw [h24]; linarith
    _ ≤ (24 + C) * ‖qParamFun z‖ ^ 1 := by rw [pow_one]; nlinarith [hC.le, hq2, norm_nonneg (qParamFun z)]

/-- `E₄³ - 1 = O(q)`. -/
theorem E4_cube_sub_one : IsSmallT 1 (fun z => E4Fun z ^ 3 - 1) 1 := by
  obtain ⟨C, hC, h⟩ := E4cube_cusp_second
  refine ⟨720 + C, by positivity, fun z hz => ?_⟩
  dsimp only
  have h1 := h z hz
  have hq1 := norm_qParamFun_le_one z hz
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith [hq1, norm_nonneg (qParamFun z)]
  have hsplit : E4Fun z ^ 3 - 1 = (E4Fun z ^ 3 - 1 - 720 * qParamFun z) + 720 * qParamFun z := by ring
  rw [hsplit]
  have h720 : ‖(720 : ℂ) * qParamFun z‖ = 720 * ‖qParamFun z‖ := by
    rw [norm_mul, Complex.norm_ofNat]
  calc ‖(E4Fun z ^ 3 - 1 - 720 * qParamFun z) + 720 * qParamFun z‖
      ≤ ‖E4Fun z ^ 3 - 1 - 720 * qParamFun z‖ + ‖(720 : ℂ) * qParamFun z‖ := norm_add_le _ _
    _ ≤ C * ‖qParamFun z‖ ^ 2 + 720 * ‖qParamFun z‖ := by rw [h720]; linarith
    _ ≤ (720 + C) * ‖qParamFun z‖ ^ 1 := by rw [pow_one]; nlinarith [hC.le, hq2, norm_nonneg (qParamFun z)]

/-- The second-order remainder of `E₄`: `E₄ - 1 - 240q = O(q²)`. -/
theorem E4_sub_one_second :
    IsSmallT 1 (fun z => E4Fun z - 1 - 240 * qParamFun z) 2 := E4Fun_two_term

/-- The second-order remainder of `E₆`: `E₆ - 1 + 504q = O(q²)`. -/
theorem E6_sub_one_second :
    IsSmallT 1 (fun z => E6Fun z - 1 + 504 * qParamFun z) 2 := E6Fun_two_term

/-- The second-order remainder of `E₂`: `E₂ - 1 + 24q = O(q²)`. -/
theorem E2_sub_one_second :
    IsSmallT 1 (fun z => E2Fun z - 1 + 24 * qParamFun z) 2 := E2Fun_two_term

/-- The second-order remainder of `Δ`: `Δ - q = O(q²)`. -/
theorem delta_sub_q_second : IsSmallT 1 (fun z => DeltaFun z - qParamFun z) 2 := DeltaFun_two_term

/-- `Δ = O(q)`. -/
theorem delta_bound : IsSmallT 1 DeltaFun 1 := by
  obtain ⟨C, hC, h⟩ := DeltaFun_upper
  exact ⟨C, hC, fun z hz => by simpa [pow_one] using h z hz⟩

/-- `E₂ˢ - S₀ = E₂ - 1 = O(q)`. -/
theorem E2S_sub_S0c : IsSmallT 1 (fun z => E2S z - S0c z) 1 :=
  (E2_sub_one).congr (fun z => by rw [TildeFacts.E2S_eq, S0c]; ring)

/-- `E₂ˢ` is bounded. -/
theorem E2S_bounded : IsSmallT 1 E2S 0 := by
  have h := E2S_sub_S0c.mono (le_refl 1) (by norm_num : 0 ≤ 1)
  exact (h.add (le_refl 1) S0c_bounded).congr (fun z => by ring)

/-- `(E₂ˢ)² - S₀² = O(q)`. -/
theorem E2S_sq_sub_S0c_sq : IsSmallT 1 (fun z => E2S z ^ 2 - S0c z ^ 2) 1 := by
  have hmul : IsSmallT 1 (fun z => (E2S z - S0c z) * (E2S z + S0c z)) 1 := by
    have h := E2S_sub_S0c.mul (le_refl 1) (E2S_bounded.add (le_refl 1) S0c_bounded)
    simpa using h
  exact hmul.congr (fun z => by ring)

/-- `Δ` is bounded below by a multiple of `q`. -/
theorem delta_lower : ∃ c : ℝ, 0 < c ∧ ∀ z : ℍ, 1 ≤ z.im →
    c * ‖qParamFun z‖ ≤ ‖DeltaFun z‖ := DeltaFun_lower

/-- `Δ⁻¹ = O(q⁻¹)`. -/
theorem delta_inv_bound : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 ≤ z.im →
    ‖(DeltaFun z)⁻¹‖ ≤ C * ‖qParamFun z‖⁻¹ := by
  obtain ⟨c, hc, hlow⟩ := delta_lower
  refine ⟨c⁻¹, inv_pos.mpr hc, fun z hz => ?_⟩
  have hqpos : 0 < ‖qParamFun z‖ := by rw [norm_qParamFun]; exact Real.exp_pos _
  have hDpos : 0 < ‖DeltaFun z‖ := lt_of_lt_of_le (mul_pos hc hqpos) (hlow z hz)
  rw [norm_inv]
  calc ‖DeltaFun z‖⁻¹ ≤ (c * ‖qParamFun z‖)⁻¹ :=
        (inv_le_inv₀ hDpos (mul_pos hc hqpos)).mpr (hlow z hz)
    _ = c⁻¹ * ‖qParamFun z‖⁻¹ := by rw [mul_inv]

/-- `Δ⁻¹ - q⁻¹ - 24 = O(q)`. -/
theorem delta_inv_small :
    IsSmallT 1 (fun z => (DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24) 1 := by
  obtain ⟨C, hC, h⟩ := cusp_invDelta
  refine ⟨C, hC, fun z hz => ?_⟩
  have h1 := h z hz
  rw [Ept_inv_sq_eq z, norm_Ept_sq_eq z] at h1
  have h2 : (DeltaFun z)⁻¹ - ((qParamFun z)⁻¹ + 24)
      = (DeltaFun z)⁻¹ - (qParamFun z)⁻¹ - 24 := by ring
  rw [h2] at h1
  simpa using h1

/-- `1 - Δ/q = O(q)`. -/
theorem one_sub_delta_div_q : IsSmallT 1 (fun z => 1 - DeltaFun z / qParamFun z) 1 := by
  obtain ⟨C, hC, h⟩ := delta_sub_q_second
  refine ⟨C, hC, fun z hz => ?_⟩
  dsimp only
  have h1 := h z hz
  have hqpos : 0 < ‖qParamFun z‖ := by rw [norm_qParamFun]; exact Real.exp_pos _
  have hq0 : qParamFun z ≠ 0 := qParamFun_ne_zero' z
  have hsplit : 1 - DeltaFun z / qParamFun z = (qParamFun z - DeltaFun z) / qParamFun z := by
    rw [sub_div, div_self hq0]
  rw [hsplit, norm_div]
  have h2 : ‖qParamFun z - DeltaFun z‖ ≤ C * ‖qParamFun z‖ ^ 2 := by
    rw [norm_sub_rev]; exact h1
  calc ‖qParamFun z - DeltaFun z‖ / ‖qParamFun z‖
      ≤ (C * ‖qParamFun z‖ ^ 2) / ‖qParamFun z‖ := div_le_div_of_nonneg_right h2 hqpos.le
    _ = C * ‖qParamFun z‖ ^ 1 := by
        rw [pow_one, div_eq_iff (ne_of_gt hqpos)]; ring

/-- `E₄` is bounded away from `0` near the cusp. -/
theorem E4_inv_bounded : ∃ T : ℝ, 1 ≤ T ∧ IsSmallT T (fun z => (E4Fun z)⁻¹) 0 := by
  obtain ⟨A, hA⟩ := exists_bound_norm_E4Fun_atImInfty
  refine ⟨max A 1, le_max_right _ _, 2, by norm_num, fun z hz => ?_⟩
  have h1 : (1/2 : ℝ) ≤ ‖E4Fun z‖ := hA z (le_trans (le_max_left _ _) hz)
  have hpos : 0 < ‖E4Fun z‖ := by linarith
  rw [norm_inv, pow_zero, mul_one]
  rw [show (2:ℝ) = (1/2)⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr h1

/-- `E₄ z ≠ 0` near the cusp. -/
theorem E4_ne_zero : ∃ T : ℝ, 1 ≤ T ∧ ∀ z : ℍ, T ≤ z.im → E4Fun z ≠ 0 := by
  obtain ⟨A, hA⟩ := exists_bound_norm_E4Fun_atImInfty
  refine ⟨max A 1, le_max_right _ _, fun z hz => ?_⟩
  have h1 : (1/2 : ℝ) ≤ ‖E4Fun z‖ := hA z (le_trans (le_max_left _ _) hz)
  intro h0
  rw [h0, norm_zero] at h1
  linarith

/-- `j(z) = q⁻¹ + 744 + O(q)`. -/
theorem jz_expansion :
    ∃ T : ℝ, 1 ≤ T ∧ IsSmallT T (fun z => jInvariantFun z - (qParamFun z)⁻¹ - 744) 1 := by
  obtain ⟨T0, M0, hT0, hM0, h⟩ := jInvariantFun_cusp_second
  refine ⟨max T0 1, le_max_right _ _, M0, hM0, fun z hz => ?_⟩
  have hz1 : (1:ℝ) ≤ z.im := le_trans (le_max_right _ _) hz
  have h1 := h z (le_trans (le_max_left _ _) hz)
  rw [Ept_inv_sq_eq z, norm_Ept_sq_eq z] at h1
  simpa [pow_one] using h1

/-- The `q²`-order relation `E₄³ - q·j + 24 q·E₄³ = O(q²)`. -/
theorem E4cube_sub_q_j_small :
    ∃ T : ℝ, 1 ≤ T ∧ IsSmallT T (fun z => E4Fun z ^ 3 - qParamFun z * jInvariantFun z
      + 24 * qParamFun z * E4Fun z ^ 3) 2 := by
  obtain ⟨Tj, hTj, hj⟩ := jz_expansion
  obtain ⟨C, hC, hE4c⟩ := E4cube_cusp_second
  refine ⟨max Tj 1, le_trans hTj (le_max_left _ _), ?_⟩
  have hT : (1:ℝ) ≤ max Tj 1 := le_trans hTj (le_max_left _ _)
  have h1 : IsSmallT (max Tj 1) (fun z => E4Fun z ^ 3 - 1 - 720 * qParamFun z) 2 :=
    ⟨C, hC, fun z hz => hE4c z (le_trans hT hz)⟩
  have h2 : IsSmallT (max Tj 1)
      (fun z => qParamFun z * (jInvariantFun z - (qParamFun z)⁻¹ - 744)) 2 :=
    (qParamFun_small (max Tj 1)).mul hT (hj.of_le (le_max_left _ _))
  have h3 : IsSmallT (max Tj 1) (fun z => 24 * qParamFun z * (E4Fun z ^ 3 - 1)) 2 :=
    ((IsSmallT.const_mul (24:ℂ) (qParamFun_small (max Tj 1))).mul hT
      (E4_cube_sub_one.of_le hT)).congr (fun z => by ring)
  have h := (h1.sub hT h2).add hT h3
  refine h.congr_of (fun z hz => ?_)
  have hq : qParamFun z ≠ 0 := qParamFun_ne_zero' z
  field_simp
  ring

/-- `E₆ E₂ˢ / E₄ - S₀ = O(q)`. -/
theorem E6_E2S_div_E4_sub_S0c :
    ∃ T : ℝ, 1 ≤ T ∧ IsSmallT T (fun z => E6Fun z * E2S z / E4Fun z - S0c z) 1 := by
  obtain ⟨Tz, hTz1, hzero⟩ := E4_ne_zero
  obtain ⟨Ti, hTi1, hinv⟩ := E4_inv_bounded
  refine ⟨max Tz Ti, le_trans hTz1 (le_max_left _ _), ?_⟩
  have hT : (1:ℝ) ≤ max Tz Ti := le_trans hTz1 (le_max_left _ _)
  have ha : IsSmallT (max Tz Ti) (fun z => E4Fun z - 1) 1 := E4_sub_one.of_le hT
  have hb : IsSmallT (max Tz Ti) (fun z => E6Fun z - 1) 1 := E6_sub_one.of_le hT
  have hs : IsSmallT (max Tz Ti) (fun z => E2S z - S0c z) 1 := E2S_sub_S0c.of_le hT
  have hc0 : IsSmallT (max Tz Ti) S0c 0 := S0c_bounded.of_le hT
  have hinv' : IsSmallT (max Tz Ti) (fun z => (E4Fun z)⁻¹) 0 := hinv.of_le (le_max_right _ _)
  have hba : IsSmallT (max Tz Ti) (fun z => (E6Fun z - 1) - (E4Fun z - 1)) 1 := hb.sub hT ha
  have hX : IsSmallT (max Tz Ti)
      (fun z => (E2S z - S0c z) + S0c z * ((E6Fun z - 1) - (E4Fun z - 1))
        + (E6Fun z - 1) * (E2S z - S0c z)) 1 := by
    have h1 := (hs.add hT (hc0.mul hT hba))
    have h2 := (hb.mul hT hs).mono hT (by norm_num : 1 ≤ 1 + 1)
    exact (h1.add hT h2).congr (fun z => by ring)
  have h := hX.mul hT hinv'
  refine h.congr_of (fun z hz => ?_)
  have hne : E4Fun z ≠ 0 := hzero z (le_trans (le_max_left _ _) hz)
  field_simp
  ring

/-- `E₆ E₂ˢ / E₄ - S₀ + 24q + 744 q S₀ = O(q²)`. -/
theorem E6_E2S_div_E4_second :
    ∃ T : ℝ, 1 ≤ T ∧ IsSmallT T (fun z => E6Fun z * E2S z / E4Fun z - S0c z
      + 24 * qParamFun z + 744 * qParamFun z * S0c z) 2 := by
  obtain ⟨Tz, hTz1, hzero⟩ := E4_ne_zero
  obtain ⟨Ti, hTi1, hinv⟩ := E4_inv_bounded
  refine ⟨max Tz Ti, le_trans hTz1 (le_max_left _ _), ?_⟩
  have hT : (1:ℝ) ≤ max Tz Ti := le_trans hTz1 (le_max_left _ _)
  have ha : IsSmallT (max Tz Ti) (fun z => E4Fun z - 1) 1 := E4_sub_one.of_le hT
  have hb : IsSmallT (max Tz Ti) (fun z => E6Fun z - 1) 1 := E6_sub_one.of_le hT
  have hs : IsSmallT (max Tz Ti) (fun z => E2S z - S0c z) 1 := E2S_sub_S0c.of_le hT
  have hc0 : IsSmallT (max Tz Ti) S0c 0 := S0c_bounded.of_le hT
  have hinv' : IsSmallT (max Tz Ti) (fun z => (E4Fun z)⁻¹) 0 := hinv.of_le (le_max_right _ _)
  have hq : IsSmallT (max Tz Ti) qParamFun 1 := qParamFun_small _
  have hba : IsSmallT (max Tz Ti) (fun z => (E6Fun z - 1) - (E4Fun z - 1)) 1 := hb.sub hT ha
  have hX : IsSmallT (max Tz Ti)
      (fun z => (E2S z - S0c z) + S0c z * ((E6Fun z - 1) - (E4Fun z - 1))
        + (E6Fun z - 1) * (E2S z - S0c z)) 1 := by
    have h1 := (hs.add hT (hc0.mul hT hba))
    have h2 := (hb.mul hT hs).mono hT (by norm_num : 1 ≤ 1 + 1)
    exact (h1.add hT h2).congr (fun z => by ring)
  -- the second-order pieces
  have hY1 : IsSmallT (max Tz Ti) (fun z => E2Fun z - 1 + 24 * qParamFun z) 2 :=
    E2_sub_one_second.of_le hT
  have hY2 : IsSmallT (max Tz Ti) (fun z => S0c z * ((E6Fun z - 1 + 504 * qParamFun z)
      - (E4Fun z - 1 - 240 * qParamFun z))) 2 :=
    hc0.mul hT ((E6_sub_one_second.of_le hT).sub hT (E4_sub_one_second.of_le hT))
  have hY3 : IsSmallT (max Tz Ti) (fun z => (E6Fun z - 1) * (E2S z - S0c z)) 2 := hb.mul hT hs
  have hY : IsSmallT (max Tz Ti)
      (fun z => (E2Fun z - 1 + 24 * qParamFun z)
        + S0c z * ((E6Fun z - 1 + 504 * qParamFun z) - (E4Fun z - 1 - 240 * qParamFun z))
        + (E6Fun z - 1) * (E2S z - S0c z)) (min 2 (min 2 2)) :=
    (hY1.add hT hY2).add hT hY3
  have hY' : IsSmallT (max Tz Ti)
      (fun z => (E2Fun z - 1 + 24 * qParamFun z)
        + S0c z * ((E6Fun z - 1 + 504 * qParamFun z) - (E4Fun z - 1 - 240 * qParamFun z))
        + (E6Fun z - 1) * (E2S z - S0c z)) 2 := by
    simpa using hY
  have hZ : IsSmallT (max Tz Ti) (fun z => ((E2S z - S0c z) + S0c z * ((E6Fun z - 1) - (E4Fun z - 1))
      + (E6Fun z - 1) * (E2S z - S0c z)) * (E4Fun z - 1) * (E4Fun z)⁻¹) (1 + 1 + 0) :=
    (hX.mul hT ha).mul hT hinv'
  have hZ' : IsSmallT (max Tz Ti) (fun z => ((E2S z - S0c z) + S0c z * ((E6Fun z - 1) - (E4Fun z - 1))
      + (E6Fun z - 1) * (E2S z - S0c z)) * (E4Fun z - 1) * (E4Fun z)⁻¹) 2 := by
    simpa using hZ
  have h := hY'.sub hT hZ'
  refine h.congr_of (fun z hz => ?_)
  have hne : E4Fun z ≠ 0 := hzero z (le_trans (le_max_left _ _) hz)
  simp only [TildeFacts.E2S_eq, S0c]
  field_simp
  ring

end Work.Asymptotics.Small
