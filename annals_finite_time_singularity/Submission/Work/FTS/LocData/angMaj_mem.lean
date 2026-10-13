/-
# Integrability and the angular mass bound for `angMaj`

This file proves

`IntegrableOn (fun θ => angMaj α θ) Iθ ∧ ∫_{Iθ} angMaj α θ ≤ 1000/(3α) + 10001`

for `0 < α ≤ 1`, where (`Work.FTS.LocData.Defs`)

`angMaj α θ = Γ(θ)² · sin(2θ)^{-γ(α)} + Γ(θ)² · sin(2θ)^{-η} + 1`,

`Γ(θ) = (sin θ cos²θ)^{α/3}`, `γ(α) = 1 + α/10`, `η = 99/100`.

## Mathematics

Write `X = sin(2θ)`, `s = 17α/30 - 1 = 2α/3 - γ(α)`, and remember that on
`Iθ = [0,π/2]` we have `0 ≤ sin θ ≤ 1`, `0 ≤ cos θ ≤ 1`, `X ≥ 0`.

* **First term.** Since `cos²θ ≤ cos θ` on `Iθ`,
  `Γ(θ)² = (sin θ cos²θ)^{2α/3} ≤ (sin θ cos θ)^{2α/3} = (X/2)^{2α/3}
   = 2^{-2α/3} · X^{2α/3}` (using `X = 2 sin θ cos θ`), whence
  `Γ² · X^{-γ} ≤ 2^{-2α/3} · X^{s}`.  As `-1 < s ≤ 0`, `Work.Spaces.sin_two_rpow`
  gives `∫ X^s ≤ 100/(s+1) = 3000/(17α)`.
* **Second term.** `Work.Spaces.Gam_bounds` gives `0 ≤ Γ ≤ 1`, so
  `Γ² · X^{-η} ≤ X^{-η}`, and `∫ X^{-η} ≤ 100/(1-η) = 10000`.
* **Constant.** `∫_{Iθ} 1 = π/2`.
* Finally `2^{-2α/3}·3000/(17α) + 10000 + π/2 ≤ 1000/(3α) + 10001`
  (`α ≤ 1` and `π ≤ 4`), the arithmetic lemma `angMaj_arith` below.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## Elementary `rpow` helper -/

/-- `(X/2)^a = 2^{-a} X^a` for `X ≥ 0`. -/
theorem angMaj_div_two_rpow (X : ℝ) (hX : 0 ≤ X) (a : ℝ) :
    (X / 2) ^ a = 2 ^ (-a) * X ^ a := by
  rw [Real.div_rpow hX (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-! ## The two pointwise bounds -/

/-- **The first angular term is dominated by `X^{17α/30-1}`**, `X = sin(2θ)`:

`Γ(θ)² · sin(2θ)^{-γ(α)} ≤ 2^{-2α/3} · sin(2θ)^{17α/30-1}`  on `Iθ`.

`17α/30 - 1 = 2α/3 - γ(α)` lies in `(-1, 0]` for `0 < α ≤ 1`, so the majorant
is integrable with integral at most `2^{-2α/3}·3000/(17α)`. -/
theorem GamSq_sin_neg_gam_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hX0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; positivity
  have hexp : 2 * α / 3 + -(Work.Spaces.gam α) = 17 * α / 30 - 1 := by
    simp only [Work.Spaces.gam]; ring
  have hne : 2 * α / 3 + -(Work.Spaces.gam α) ≠ 0 := by
    rw [hexp]; intro h; linarith
  -- `Γ² = (sin θ cos²θ)^{2α/3}`
  have hΓ2 : Work.Spaces.Gam α θ ^ 2 = (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) := by
    rw [Work.Spaces.Gam]
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2)]
    congr 1
    ring
  -- `Γ² ≤ (sin θ cos θ)^{2α/3}`, because `cos²θ ≤ cos θ`
  have hc2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc0, hc1]
  have hYle : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * Real.cos θ :=
    mul_le_mul_of_nonneg_left hc2 hs0
  have hstat : Work.Spaces.Gam α θ ^ 2 ≤ (Real.sin θ * Real.cos θ) ^ (2 * α / 3) := by
    rw [hΓ2]
    exact Real.rpow_le_rpow (by positivity) hYle (by linarith : (0 : ℝ) ≤ 2 * α / 3)
  -- `(sin θ cos θ)^{2α/3} X^{-γ} = 2^{-2α/3} X^{2α/3-γ}`
  have hstep2 : (Real.sin θ * Real.cos θ) ^ (2 * α / 3)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    have hY : Real.sin θ * Real.cos θ = Real.sin (2 * θ) / 2 := by
      rw [Real.sin_two_mul]; ring
    rw [hY, angMaj_div_two_rpow _ hX0, mul_assoc, ← Real.rpow_add' hX0 hne, hexp]
  calc Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin θ * Real.cos θ) ^ (2 * α / 3)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right hstat (Real.rpow_nonneg hX0 _)
    _ = 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := hstep2

/-- **The second angular term is dominated by `sin(2θ)^{-η}`**: `Γ ≤ 1` on `Iθ`. -/
theorem GamSq_sin_neg_eta_le (α : ℝ) (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hX0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  have hG2 : Work.Spaces.Gam α θ ^ 2 ≤ 1 := by nlinarith
  exact mul_le_of_le_one_left (Real.rpow_nonneg hX0 _) hG2

/-! ## The closing arithmetic -/

/-- The numerical inequality that closes the estimate.  It follows from
`2^{-2α/3} ≤ 1`, `π ≤ 4` and `α ≤ 1`. -/
theorem angMaj_arith (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    2 ^ (-(2 * α / 3)) * (3000 / (17 * α)) + 10000 + Real.pi / 2
      ≤ 1000 / (3 * α) + 10001 := by
  have hpow1 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
      (by norm_num : (1 : ℝ) ≤ 2) (by linarith : -(2 * α / 3) ≤ 0)
    simpa using h
  have hd : (0 : ℝ) ≤ 3000 / (17 * α) := by positivity
  have h1 : 2 ^ (-(2 * α / 3)) * (3000 / (17 * α)) ≤ 3000 / (17 * α) := by
    have hm := mul_le_mul_of_nonneg_right hpow1 hd
    simpa using hm
  -- `π/2 - 1 ≤ 8000/(51α)`, which is the exact slack in the claim
  have h817 : (1 : ℝ) ≤ 8000 / (51 * α) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 51 * α)]
    nlinarith [hα, hα1]
  have hkey : Real.pi / 2 - 1 ≤ 8000 / (51 * α) :=
    le_trans (by linarith [Real.pi_le_four]) h817
  have hsub : 1000 / (3 * α) - 3000 / (17 * α) = 8000 / (51 * α) := by
    field_simp
    ring
  linarith [h1, hkey, hsub]

/-! ## The main lemma -/

theorem angMaj_mem (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (fun θ => angMaj α θ) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, angMaj α θ ≤ 1000 / (3 * α) + 10001 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- nonnegativity of `sin(2θ)` on `Iθ`
  have hsin2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩))
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  -- exponents
  have hp1 : -1 < 17 * α / 30 - 1 := by linarith
  have hp2 : 17 * α / 30 - 1 ≤ 0 := by linarith
  have he1 : -1 < -(Work.Spaces.eta) := by simp only [Work.Spaces.eta]; norm_num
  have he2 : -(Work.Spaces.eta) ≤ 0 := by simp only [Work.Spaces.eta]; norm_num
  obtain ⟨hIntS1, hBdS1⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1) hp1 hp2
  obtain ⟨hIntS2, hBdS2⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) he1 he2
  -- the integrals of the two trigonometric majorants
  have hBdS1' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by
      field_simp
      ring
    rwa [heq] at hBdS1
  have hBdS2' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ 10000 := by
    have heq : 100 / (-(Work.Spaces.eta) + 1) = 10000 := by
      simp only [Work.Spaces.eta]; norm_num
    rwa [heq] at hBdS2
  -- the first majorant is integrable
  have hM1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
      Work.Spaces.Iθ := hIntS1.const_mul _
  -- the a.e. pointwise bounds
  have hpt1 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact GamSq_sin_neg_gam_le α hα hα1 hθ
  have hpt2 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact GamSq_sin_neg_eta_le α hα hθ
  -- measurability
  have hmeas1 : AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  have hmeas2 : AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  -- integrability of the two terms
  have hf1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ :=
    hM1.mono' hmeas1 (by
      filter_upwards [hpt1, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2 θ h2) _))]
      exact h1)
  have hf2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    hIntS2.mono' hmeas2 (by
      filter_upwards [hpt2, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2 θ h2) _))]
      exact h1)
  -- integral bounds for the two terms
  have hint1 : ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 2 ^ (-(2 * α / 3)) * (3000 / (17 * α)) := by
    have hmono := MeasureTheory.integral_mono_ae hf1 hM1 hpt1
    refine le_trans hmono ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hBdS1' (Real.rpow_nonneg (by norm_num) _)
  have hint2 : ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ 10000 := by
    have hmono := MeasureTheory.integral_mono_ae hf2 hIntS2 hpt2
    exact le_trans hmono hBdS2'
  -- the constant function
  have hInt0 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hvol : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
      Work.Spaces.Iθ, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - 0)]
    ring
  -- the sum
  have hSum : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := hf1.add hf2
  have hangMaj : (fun θ : ℝ => angMaj α θ)
      = fun θ : ℝ => (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) + 1 := by
    funext θ
    rw [angMaj_apply]
  have hintSum : ∫ θ in Work.Spaces.Iθ, angMaj α θ
      = (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        + (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) := by
    rw [hangMaj, MeasureTheory.integral_add hSum hInt0, MeasureTheory.integral_add hf1 hf2]
  constructor
  · rw [hangMaj]; exact hSum.add hInt0
  · rw [hintSum]
    have h12 : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        + (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ 2 ^ (-(2 * α / 3)) * (3000 / (17 * α)) + 10000 :=
      add_le_add hint1 hint2
    rw [hvol]
    linarith [h12, angMaj_arith α hα hα1]

end Work.FTS.LocData
