import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory

/-- A set integral of a nonnegative function bounded by a constant `C` on the set `s` is at most
`C` times the (real) measure of `s`.  No measurability or integrability of `f` is needed. -/
private lemma setIntegral_le_const_mul_measureReal {s : Set ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hs : MeasurableSet s) (hfin : volume s < ⊤) (hf : ∀ x ∈ s, 0 ≤ f x)
    (hC : ∀ x ∈ s, f x ≤ C) : ∫ x in s, f x ≤ C * volume.real s := by
  have h1 : ‖∫ x in s, f x‖ ≤ C * volume.real s :=
    norm_setIntegral_le_of_norm_le_const_ae' hfin
      (Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf x hx)]
        exact hC x hx)
  have h2 : 0 ≤ ∫ x in s, f x :=
    setIntegral_nonneg_ae hs (Filter.Eventually.of_forall fun x hx => hf x hx)
  rwa [Real.norm_eq_abs, abs_of_nonneg h2] at h1

/-- `(2δ)^e * δ = 2^e * δ^(e+1)`. -/
private lemma two_mul_rpow_mul_self {δ e : ℝ} (hδ : 0 < δ) :
    (2 * δ) ^ e * δ = 2 ^ e * δ ^ (e + 1) := by
  rw [Real.mul_rpow (by norm_num) (le_of_lt hδ), mul_assoc]
  have h : δ ^ (e + 1) = δ ^ e * δ := by simpa using Real.rpow_add hδ e 1
  rw [← h]

/-- The exponent `2 + η` is nonnegative. -/
private lemma two_add_eta_nonneg : (0 : ℝ) ≤ 2 + Work.Spaces.eta := by
  linarith [Work.Spaces.eta_nonneg]

/-- `sin (2x) ≥ 0` for `x ∈ (0, π/4]`. -/
private lemma sin_two_nonneg_of_mem {x : ℝ} (hx0 : 0 < x) (hx4 : x ≤ Real.pi / 4) :
    0 ≤ Real.sin (2 * x) := by
  refine Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) ?_
  linarith [Real.pi_pos]

theorem sin_two_rpow_integral_le (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4) :
    (∫ θ in Set.Ioo (0 : ℝ) δ, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)
        ≤ (2 : ℝ) ^ (2 + Work.Spaces.eta) * δ ^ (3 + Work.Spaces.eta)) ∧
      (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)
        ≤ (2 : ℝ) ^ (2 + Work.Spaces.eta) * δ ^ (3 + Work.Spaces.eta)) ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta) ≤ Real.pi / 2) := by
  have heta := two_add_eta_nonneg
  refine ⟨?_, ?_, ?_⟩
  · -- left end: `sin (2θ) ≤ 2θ ≤ 2δ` on `(0, δ)`
    have hfin : volume (Set.Ioo (0 : ℝ) δ) < ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    have hnn : ∀ x ∈ Set.Ioo (0 : ℝ) δ,
        0 ≤ (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) := by
      intro x hx
      exact Real.rpow_nonneg (sin_two_nonneg_of_mem hx.1 (le_trans (le_of_lt hx.2) hδ4)) _
    have hbd : ∀ x ∈ Set.Ioo (0 : ℝ) δ,
        (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) ≤ (2 * δ) ^ (2 + Work.Spaces.eta) := by
      intro x hx
      have h2x0 : 0 ≤ 2 * x := by linarith [hx.1]
      have hsinle : Real.sin (2 * x) ≤ 2 * δ :=
        le_trans (Real.sin_le h2x0) (by linarith [hx.2])
      exact Real.rpow_le_rpow (Real.sin_nonneg_of_nonneg_of_le_pi h2x0 (by
        linarith [hx.2, hδ4, Real.pi_pos])) hsinle heta
    have hmain := setIntegral_le_const_mul_measureReal measurableSet_Ioo hfin hnn hbd
    rw [Real.volume_real_Ioo_of_le (le_of_lt hδ), sub_zero] at hmain
    calc ∫ x in Set.Ioo (0 : ℝ) δ, (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta)
        ≤ (2 * δ) ^ (2 + Work.Spaces.eta) * δ := hmain
      _ = 2 ^ (2 + Work.Spaces.eta) * δ ^ (2 + Work.Spaces.eta + 1) :=
          two_mul_rpow_mul_self hδ
      _ = 2 ^ (2 + Work.Spaces.eta) * δ ^ (3 + Work.Spaces.eta) := by
          rw [show (2 : ℝ) + Work.Spaces.eta + 1 = 3 + Work.Spaces.eta by ring]
  · -- right end: substitute `u = π/2 - θ`, then `sin (2θ) = sin (2u) ≤ 2u ≤ 2δ`
    have hfin : volume (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) < ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    have hnn : ∀ x ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
        0 ≤ (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) := by
      intro x hx
      refine Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith [hx.1, hδ4, Real.pi_pos]) ?_) _
      linarith [hx.2]
    have hbd : ∀ x ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
        (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) ≤ (2 * δ) ^ (2 + Work.Spaces.eta) := by
      intro x hx
      set u := Real.pi / 2 - x with hu
      have hu0 : 0 < u := by rw [hu]; linarith [hx.2]
      have hud : u < δ := by rw [hu]; linarith [hx.1]
      have hsin0 : 0 ≤ Real.sin (2 * u) :=
        sin_two_nonneg_of_mem hu0 (le_trans (le_of_lt hud) hδ4)
      have hsinle : Real.sin (2 * u) ≤ 2 * δ :=
        le_trans (Real.sin_le (by linarith)) (by linarith)
      have h2x : 2 * x = Real.pi - 2 * u := by rw [hu]; ring
      rw [h2x, Real.sin_pi_sub]
      exact Real.rpow_le_rpow hsin0 hsinle heta
    have hmain := setIntegral_le_const_mul_measureReal measurableSet_Ioo hfin hnn hbd
    rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), show
      Real.pi / 2 - (Real.pi / 2 - δ) = δ by ring] at hmain
    calc ∫ x in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
          (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta)
        ≤ (2 * δ) ^ (2 + Work.Spaces.eta) * δ := hmain
      _ = 2 ^ (2 + Work.Spaces.eta) * δ ^ (2 + Work.Spaces.eta + 1) :=
          two_mul_rpow_mul_self hδ
      _ = 2 ^ (2 + Work.Spaces.eta) * δ ^ (3 + Work.Spaces.eta) := by
          rw [show (2 : ℝ) + Work.Spaces.eta + 1 = 3 + Work.Spaces.eta by ring]
  · -- the whole interval: `sin (2θ) ≤ 1`
    have hIθ : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
    have hfin : volume Work.Spaces.Iθ < ⊤ := by
      rw [hIθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    have hnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) := by
      intro x hx
      rw [hIθ] at hx
      exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
        (by linarith [hx.2])) _
    have hbd : ∀ x ∈ Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (2 + Work.Spaces.eta) ≤ 1 := by
      intro x hx
      rw [hIθ] at hx
      exact Real.rpow_le_one (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hx.1])
        (by linarith [hx.2])) (Real.sin_le_one _) heta
    have hmain := setIntegral_le_const_mul_measureReal measurableSet_Icc hfin hnn hbd
    rw [Real.volume_real_Icc_of_le (by linarith [Real.pi_pos]), sub_zero, one_mul] at hmain
    exact hmain

end Work.FTS.StrongEps.EComparison
