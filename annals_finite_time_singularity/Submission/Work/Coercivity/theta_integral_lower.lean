import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.CTDefs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Angular coercivity lower bound for the `H^k` integrand

This is the elementary "single term" lower bound used when the `H^k` norm is compared
with a pointwise lower bound for one weighted derivative.  The `H^k` integrand is a sum
of squares (`Work.Spaces.HkIntegrand`), the summand with `i = 0` in its first (pure `D_z`)
part being `(g z θ · w(z)/sin(2θ)^{η/2})²`.  On the interval `(θ₁,θ₂) ⊆ (0,π/2)` the
factor `1/sin(2θ)^{η/2}` is at least `1`, so a pointwise lower bound
`Aref²/16 · z² ≤ g(z,θ)²` propagates to a lower bound for the whole integral over `Iθ`.
-/

namespace Work.Coercivity

set_option autoImplicit false

theorem theta_integral_lower (α : ℝ) (n : ℕ) (g : ℝ → ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    {θ₁ θ₂ Aref : ℝ} (hθ₁ : 0 ≤ θ₁) (hlt : θ₁ < θ₂) (hθ₂ : θ₂ ≤ Real.pi / 2)
    (hint : MeasureTheory.Integrable
      (fun θ => Work.Spaces.HkIntegrand α n g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hlow : ∀ θ ∈ Set.Ioo θ₁ θ₂, Aref ^ 2 / 16 * z ^ 2 ≤ (g z θ) ^ 2) :
    Aref ^ 2 * (θ₂ - θ₁) / 16 * ((Work.Spaces.w z) ^ 2 * z ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ := by
  -- `(θ₁,θ₂) ⊆ Iθ`
  have hsub : Set.Ioo θ₁ θ₂ ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨le_of_lt (lt_of_le_of_lt hθ₁ hθ.1), le_trans (le_of_lt hθ.2) hθ₂⟩
  -- Pointwise lower bound for the full integrand on `(θ₁,θ₂)`.
  have hpt : ∀ θ ∈ Set.Ioo θ₁ θ₂,
      Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ Work.Spaces.HkIntegrand α n g z θ := by
    intro θ hθ
    -- `θ ∈ (0, π/2)`, so `0 < sin(2θ) ≤ 1`
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, hθ₁])
        (by linarith [hθ.2, hθ₂, Real.pi_pos])
    have hsinle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have heta : 0 ≤ Work.Spaces.eta / 2 := by
      have := Work.Spaces.eta_pos; linarith
    have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinpos _
    have hsle : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hsinpos) hsinle heta
    -- `w(z) ≤ w(z)/sin(2θ)^{η/2}`, hence the same for the squares
    have hwz : 0 ≤ Work.Spaces.w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hdiv : Work.Spaces.w z ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
      rw [div_eq_mul_one_div]
      calc Work.Spaces.w z = Work.Spaces.w z * 1 := by ring
        _ ≤ Work.Spaces.w z * (1 / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) :=
            mul_le_mul_of_nonneg_left (one_le_one_div hspos hsle) hwz
    have hsq : (Work.Spaces.w z) ^ 2
        ≤ (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 :=
      pow_le_pow_left₀ hwz hdiv 2
    -- Multiply by the pointwise bound `Aref²/16 · z² ≤ g²`
    have h1 : Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (g z θ) ^ 2 * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 :=
      mul_le_mul (hlow θ hθ) hsq (sq_nonneg _) (sq_nonneg _)
    -- The `i = 0` summand of the `H^k` integrand is dominated by the whole sum
    have h3 : (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α n g z θ := by
      have h4 := Work.Spaces.sq_le_HkIntegrand_z α n g z θ 0 (Nat.zero_le n)
      simpa using h4
    calc Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (g z θ) ^ 2 * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 := h1
      _ = (g z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            rw [mul_pow]
      _ ≤ Work.Spaces.HkIntegrand α n g z θ := h3
  have hIntOn : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α n g z θ) Work.Spaces.Iθ := hint
  have hIntSub : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α n g z θ) (Set.Ioo θ₁ θ₂) :=
    hIntOn.mono_set hsub
  -- The integral of the constant `Aref²/16 · z² · w(z)²` over `(θ₁,θ₂)`
  have hCint : ∫ θ in Set.Ioo θ₁ θ₂, Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2
      = Aref ^ 2 * (θ₂ - θ₁) / 16 * ((Work.Spaces.w z) ^ 2 * z ^ 2) := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have hIntC : MeasureTheory.IntegrableOn
      (fun _ : ℝ => Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioo θ₁ θ₂) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hmono1 : ∫ θ in Set.Ioo θ₁ θ₂, Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ ∫ θ in Set.Ioo θ₁ θ₂, Work.Spaces.HkIntegrand α n g z θ :=
    MeasureTheory.setIntegral_mono_on hIntC hIntSub measurableSet_Ioo hpt
  have hmono2 : ∫ θ in Set.Ioo θ₁ θ₂, Work.Spaces.HkIntegrand α n g z θ
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ :=
    MeasureTheory.setIntegral_mono_set hIntOn
      (Filter.Eventually.of_forall (fun θ => Work.Spaces.HkIntegrand_nonneg α n g z θ))
      hsub.eventuallySubset
  calc Aref ^ 2 * (θ₂ - θ₁) / 16 * ((Work.Spaces.w z) ^ 2 * z ^ 2)
      = ∫ θ in Set.Ioo θ₁ θ₂, Aref ^ 2 / 16 * z ^ 2 * (Work.Spaces.w z) ^ 2 := hCint.symm
    _ ≤ ∫ θ in Set.Ioo θ₁ θ₂, Work.Spaces.HkIntegrand α n g z θ := hmono1
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ := hmono2

end Work.Coercivity
