import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.integral_Itheta_K

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open MeasureTheory Set

/-- On `Iθ = [0,π/2]` the sine is nonnegative. -/
lemma K_facts_sin_nonneg {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) : 0 ≤ Real.sin θ := by
  rw [Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [Real.pi_pos, hθ.2])

/-- `cos²θ ≤ 1` for every real `θ`. -/
lemma K_facts_cos_sq_le_one (θ : ℝ) : Real.cos θ ^ 2 ≤ 1 := by
  nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_nonneg (Real.cos θ - 1)]

/-- The angular weight `K` is continuous. -/
lemma K_facts_continuous : Continuous Spaces.K := by
  unfold Spaces.K
  fun_prop

/-- `K` is nonnegative on `Iθ`. -/
lemma K_facts_nonneg : ∀ θ ∈ Spaces.Iθ, 0 ≤ Spaces.K θ := by
  intro θ hθ
  have h1 : 0 ≤ Real.sin θ := K_facts_sin_nonneg hθ
  have h2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg (Real.cos θ)
  simp only [Spaces.K]
  nlinarith

/-- `K` is bounded by `3` on `Iθ`. -/
lemma K_facts_le_three : ∀ θ ∈ Spaces.Iθ, Spaces.K θ ≤ 3 := by
  intro θ hθ
  have h1 : 0 ≤ Real.sin θ := K_facts_sin_nonneg hθ
  have h1' : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h2 : Real.cos θ ^ 2 ≤ 1 := K_facts_cos_sq_le_one θ
  have h2' : 0 ≤ Real.cos θ ^ 2 := sq_nonneg (Real.cos θ)
  simp only [Spaces.K]
  nlinarith

/-- `K ^ 2` is integrable on the compact interval `Iθ`. -/
lemma K_facts_sq_integrableOn :
    MeasureTheory.IntegrableOn (fun θ => (Spaces.K θ) ^ 2) Spaces.Iθ := by
  rw [Spaces.Iθ]
  exact (K_facts_continuous.pow 2).integrableOn_Icc

/-- Elementary facts about the angular weight `K θ = 3 sin θ cos²θ` on `Iθ = [0, π/2]`:
it is nonnegative, `K θ ^ 2 ≤ 3 * K θ` pointwise (as `K ≤ 3` there), its integral is `1`
(antiderivative `-cos³θ`), and consequently `∫ K² ≤ 3`.

Intended proof: on `Iθ`, `0 ≤ sin θ` and `0 ≤ cos θ ^ 2`, hence `0 ≤ K θ`; `sin θ ≤ 1` and
`cos θ ^ 2 ≤ 1` give `K θ ≤ 3`; thus `K θ ^ 2 ≤ 3 * K θ`. For the integral value use the
calculus identity via `HasDerivAt (fun θ => -(Real.cos θ)^3) (K θ) θ` together with
`intervalIntegral` (after rewriting `∫ θ in Iθ, g θ = ∫ θ in (0:ℝ)..(π/2), g θ`), which
gives `∫ θ in Iθ, K θ = -cos(π/2)^3 + cos 0^3 = 1`. Finally `∫ K² ≤ ∫ 3 * K = 3 * ∫ K = 3`
by integral monotonicity on `Iθ` (`IntegrableOn` of both `K` and `K ^ 2` follows from
continuity on the compact `Iθ`), or directly by the pointwise bound `K ≤ 3`. -/
theorem K_facts :
    (∀ θ ∈ Spaces.Iθ, 0 ≤ Spaces.K θ) ∧
      (∀ θ ∈ Spaces.Iθ, (Spaces.K θ) ^ 2 ≤ 3 * Spaces.K θ) ∧
        (∫ θ in Spaces.Iθ, Spaces.K θ) = 1 ∧
          (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) ≤ 3 := by
  have hKsq : ∀ θ ∈ Spaces.Iθ, (Spaces.K θ) ^ 2 ≤ 3 * Spaces.K θ := by
    intro θ hθ
    calc (Spaces.K θ) ^ 2 = Spaces.K θ * Spaces.K θ := by ring
      _ ≤ 3 * Spaces.K θ :=
          mul_le_mul_of_nonneg_right (K_facts_le_three θ hθ) (K_facts_nonneg θ hθ)
  have hInt3K : MeasureTheory.IntegrableOn (fun θ => 3 * Spaces.K θ) Spaces.Iθ := by
    rw [Spaces.Iθ]
    exact (K_facts_continuous.const_mul 3).integrableOn_Icc
  have hIθmeas : MeasurableSet Spaces.Iθ := by
    rw [Spaces.Iθ]; exact measurableSet_Icc
  have hmono :
      (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) ≤ ∫ θ in Spaces.Iθ, 3 * Spaces.K θ :=
    MeasureTheory.setIntegral_mono_on K_facts_sq_integrableOn hInt3K hIθmeas hKsq
  have hconst : (∫ θ in Spaces.Iθ, 3 * Spaces.K θ) = 3 * ∫ θ in Spaces.Iθ, Spaces.K θ :=
    MeasureTheory.integral_const_mul 3 (fun θ => Spaces.K θ)
  have hlast : (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) ≤ 3 := by
    rw [hconst, integral_Itheta_K] at hmono
    linarith
  exact ⟨K_facts_nonneg, hKsq, integral_Itheta_K, hlast⟩

end Work.Coercivity
