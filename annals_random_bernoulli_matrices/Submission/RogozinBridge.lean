/-
The Lévy–Kolmogorov–Rogozin branch of `eq aux` (Tikhomirov 2020).

`lkrHypothesis C` states the variable-radius Lévy–Kolmogorov–Rogozin
inequality with constant `C` for independent families on a probability space
over the (file-level) universe `u`.  It is the exact shape the shared Commons
development must eventually supply (with its own concentration function,
bridged to `Helpers.levyConcentration`); the degenerate case of a vanishing
denominator is excluded by the hypothesis `0 < D`.

`small_coords_sum_le` is the small-‖x‖∞ case of `eq aux` derived from LKR:
for a unit vector `x` with all `|x i| ≤ 2·r₀` and `r₀` small enough that
`C·r₀ ≤ (1−p)·√(p/9)`, every interval of length `2·r₀` captures the weighted
Bernoulli sum with probability at most `1−p`.

The derivation chain: per-coordinate radii
`ρ_i := if x i = 0 then r₀/2 else |x i|/3` (positive, and `≤ r₀` under the
small-coordinate hypothesis), per-coordinate atom bound `1 − cf_i ≥ p` on
nonzero coordinates, denominator `D ≥ p/9` (`denom_lower`), then
`cf(Σ b x, r₀) ≤ C·r₀/√D ≤ 3·C·r₀/√p ≤ 1−p`.
-/
import Mathlib
import Submission.EqAux
import Submission.Prelim
import Submission.Concentration
import Submission.Commons.Probability.Levy.rogozin_measurable

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Submission.RogozinBridge

noncomputable section

open MeasureTheory ProbabilityTheory Measure Filter unitInterval
open scoped ENNReal BigOperators

universe u

/-- Small-coordinate case of eq aux via Lévy–Kolmogorov–Rogozin. -/
lemma small_coords_sum_le {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {b : Fin n → Ω → ℝ} (hb_meas : ∀ i, Measurable (b i))
    (hb_indep : ProbabilityTheory.iIndepFun b P) {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    (hb_law : ∀ i, HasLaw (b i) (bernoulliMeasure 1 0 p) P)
    {x : Fin n → ℝ} (hx : (∑ i, (x i) ^ 2) = 1)
    {C r₀ : ℝ} (hC : 0 < C) (hr₀ : 0 < r₀)
    (hrm : C * r₀ ≤ (1 - (p : ℝ)) * Real.sqrt ((p : ℝ) / 9))
    (hsmall : ∀ i, |x i| ≤ 2 * r₀)
    (hLKR : ∀ (m : ℕ) (Ω₂ : Type u) [MeasurableSpace Ω₂] (P₂ : Measure Ω₂)
      [MeasureTheory.IsProbabilityMeasure P₂] (ξ₂ : Fin m → Ω₂ → ℝ),
      ProbabilityTheory.iIndepFun ξ₂ P₂ → (∀ i : Fin m, Measurable (ξ₂ i)) → ∀ (r : ℝ), 0 < r → ∀ (ρ₂ : Fin m → ℝ),
      (∀ i, 0 < ρ₂ i) → (∀ i, ρ₂ i ≤ r) →
      (0 < ∑ i, (1 - (Submission.Helpers.levyConcentration P₂ (fun ω => ξ₂ i ω) (ρ₂ i)).toReal) * (ρ₂ i) ^ 2) →
      Submission.Helpers.levyConcentration P₂ (fun ω => ∑ i, ξ₂ i ω) r ≤
        ENNReal.ofReal (C * r / Real.sqrt (∑ i,
          (1 - (Submission.Helpers.levyConcentration P₂ (fun ω => ξ₂ i ω) (ρ₂ i)).toReal) * (ρ₂ i) ^ 2))) :
    ∀ l : ℝ, P.real {ω : Ω | |(∑ i : Fin n, b i ω * x i) - l| ≤ r₀} ≤ (1 - (p : ℝ)) := by
  classical
  have hcf : Submission.Helpers.levyConcentration P (fun ω => ∑ i : Fin n, b i ω * x i) r₀ ≤
      ENNReal.ofReal (1 - (p : ℝ)) := by
    let ρ : Fin n → ℝ := fun i => if x i = 0 then r₀ / 2 else |x i| / 3
    have hρ0 : ∀ i, 0 < ρ i := by
      intro i
      dsimp [ρ]
      by_cases hi : x i = 0
      · have hif : (if x i = 0 then r₀ / 2 else |x i| / 3) = r₀ / 2 := by simp [hi]
        rw [hif]
        exact div_pos hr₀ (by norm_num)
      · have hif : (if x i = 0 then r₀ / 2 else |x i| / 3) = |x i| / 3 := by simp [hi]
        rw [hif]
        exact div_pos (abs_pos.mpr hi) (by norm_num)
    have hρr : ∀ i, ρ i ≤ r₀ := by
      intro i
      dsimp [ρ]
      by_cases hi : x i = 0
      · have hif : (if x i = 0 then r₀ / 2 else |x i| / 3) = r₀ / 2 := by simp [hi]
        rw [hif]
        linarith [hr₀]
      · have hif : (if x i = 0 then r₀ / 2 else |x i| / 3) = |x i| / 3 := by simp [hi]
        rw [hif]
        have hxi : |x i| ≤ 2 * r₀ := hsmall i
        nlinarith [hr₀]
    have hscaled : ProbabilityTheory.iIndepFun (fun i : Fin n => fun ω : Ω => b i ω * x i) P := by
      have hcomp := ProbabilityTheory.iIndepFun.comp hb_indep
        (fun i : Fin n => fun t : ℝ => t * x i) (fun i => by fun_prop)
      simpa [Function.comp_def, mul_comm] using hcomp
    let D : ℝ := ∑ i : Fin n,
      (1 - (Submission.Helpers.levyConcentration P (fun ω => b i ω * x i) (ρ i)).toReal) * (ρ i) ^ 2
    have hDpos : 0 < D := by
      dsimp [D]
      have hlow := Submission.EqAux.denom_lower P hb_meas hp₁ hb_law hx r₀
      have hrew : ((p : ℝ) / 9) ≤
          ∑ i : Fin n,
            (1 - (Submission.Helpers.levyConcentration P (fun ω => b i ω * x i) (ρ i)).toReal) * (ρ i) ^ 2 := by
        simpa [ρ] using hlow
      have hpos : 0 < (p : ℝ) / 9 := by positivity
      exact lt_of_lt_of_le hpos hrew
    have hscaled_meas : ∀ i : Fin n, Measurable (fun ω : Ω => b i ω * x i) := by
      intro i
      exact (hb_meas i).mul measurable_const
    have hL : Submission.Helpers.levyConcentration P (fun ω => ∑ i : Fin n, b i ω * x i) r₀ ≤
        ENNReal.ofReal (C * r₀ / Real.sqrt D) := by
      have hL0 := hLKR n Ω P (fun i : Fin n => fun ω : Ω => b i ω * x i) hscaled hscaled_meas r₀ hr₀ ρ hρ0 hρr hDpos
      simpa [D] using hL0
    have hineq : C * r₀ / Real.sqrt D ≤ 1 - (p : ℝ) := by
      have hlowD : ((p : ℝ) / 9) ≤ D := by
        dsimp [D]
        simpa [ρ] using (Submission.EqAux.denom_lower P hb_meas hp₁ hb_law hx r₀)
      have hsqrt : Real.sqrt ((p : ℝ) / 9) ≤ Real.sqrt D := Real.sqrt_le_sqrt hlowD
      have hDsqrtpos : 0 < Real.sqrt D := by
        have : 0 < Real.sqrt ((p : ℝ) / 9) := by
          rw [Real.sqrt_div (le_of_lt hp₀) 9]
          have : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hp₀
          positivity
        exact lt_of_lt_of_le this hsqrt
      have h1 : C * r₀ ≤ (1 - (p : ℝ)) * Real.sqrt D := by
        calc
          C * r₀ ≤ (1 - (p : ℝ)) * Real.sqrt ((p : ℝ) / 9) := hrm
          _ ≤ (1 - (p : ℝ)) * Real.sqrt D := by
                exact mul_le_mul_of_nonneg_left hsqrt (by linarith [p.property.2])
      exact (div_le_iff₀ hDsqrtpos).2 h1
    have hfin : ENNReal.ofReal (C * r₀ / Real.sqrt D) ≤ ENNReal.ofReal (1 - (p : ℝ)) :=
      ENNReal.ofReal_le_ofReal hineq
    exact le_trans hL hfin
  intro l
  have hτ0 : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
  exact Submission.Prelim.real_mem_le_of_levyConcentration_le P (fun ω => ∑ i : Fin n, b i ω * x i)
    (t := r₀) (τ := 1 - (p : ℝ)) hτ0 hcf l


/-- The full `eq aux` estimate (Tikhomirov `eq: aux`), assembled from the two
branches; the Lévy–Kolmogorov–Rogozin ingredient is supplied by the Commons
theorem `Commons.Probability.Levy.rogozin_measurable`. -/
theorem eq_aux {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P] (b : Fin n → Ω → ℝ)
        (hb_meas : ∀ i, Measurable (b i))
        (hb_indep : ProbabilityTheory.iIndepFun b P)
        (hb_law : ∀ i, HasLaw (b i) (bernoulliMeasure 1 0 p) P)
        {x : Fin n → ℝ} (hx : (∑ i, (x i) ^ 2) = 1),
        ∀ l : ℝ, P.real {ω : Ω | |(∑ i : Fin n, b i ω * x i) - l| ≤ r₀} ≤ (1 - (p : ℝ)) := by
  classical
  rcases (Commons.Probability.Levy.rogozin_measurable) with ⟨C, hC0, hCb⟩
  let r₀ : ℝ := (1 - (p : ℝ)) * Real.sqrt (p : ℝ) / (6 * C)
  have hr₀ : 0 < r₀ := by
    dsimp [r₀]
    have h1m : 0 < 1 - (p : ℝ) := by linarith [hp₁]
    have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hp₀
    exact div_pos (mul_pos h1m hs) (mul_pos (by norm_num) hC0)
  refine ⟨r₀, hr₀, ?_⟩
  intro n Ω mΩ P hP b hb_meas hb_indep hb_law x hx l
  by_cases hbig : ∃ j : Fin n, 2 * r₀ < |x j|
  · exact Submission.Prelim.bernoulli_weighted_sum_large_coord_le P hb_meas hb_indep hb_law hp₁ hbig l
  · have hsmall : ∀ i : Fin n, |x i| ≤ 2 * r₀ := by
      intro i
      by_contra hnot
      exact hbig ⟨i, lt_of_not_ge hnot⟩
    have hrm : C * r₀ ≤ (1 - (p : ℝ)) * Real.sqrt ((p : ℝ) / 9) := by
      have hcancel : C * ((1 - (p : ℝ)) * Real.sqrt (p : ℝ) / (6 * C)) =
          (1 - (p : ℝ)) * Real.sqrt (p : ℝ) / 6 := by
        field_simp [hC0.ne']
      calc
        C * r₀ = C * ((1 - (p : ℝ)) * Real.sqrt (p : ℝ) / (6 * C)) := by rfl
        _ = (1 - (p : ℝ)) * Real.sqrt (p : ℝ) / 6 := hcancel
        _ ≤ (1 - (p : ℝ)) * (Real.sqrt (p : ℝ) / 3) := by
              have ha : 0 ≤ 1 - (p : ℝ) := by linarith [p.property.2]
              have hs : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg (p : ℝ)
              nlinarith
        _ = (1 - (p : ℝ)) * Real.sqrt ((p : ℝ) / 9) := by
              rw [Real.sqrt_div (le_of_lt hp₀) 9]
              norm_num
    have hCb' : ∀ (m : ℕ) (Ω₂ : Type u) [MeasurableSpace Ω₂] (P₂ : Measure Ω₂)
        [MeasureTheory.IsProbabilityMeasure P₂] (ξ : Fin m → Ω₂ → ℝ),
        ProbabilityTheory.iIndepFun ξ P₂ → (∀ i : Fin m, Measurable (ξ i)) → ∀ (r : ℝ), 0 < r → ∀ (ρ : Fin m → ℝ),
        (∀ i, 0 < ρ i) → (∀ i, ρ i ≤ r) →
        (0 < ∑ i, (1 - (Submission.Helpers.levyConcentration P₂ (fun ω => ξ i ω) (ρ i)).toReal) * (ρ i) ^ 2) →
        Submission.Helpers.levyConcentration P₂ (fun ω => ∑ i, ξ i ω) r ≤
          ENNReal.ofReal (C * r / Real.sqrt (∑ i,
            (1 - (Submission.Helpers.levyConcentration P₂ (fun ω => ξ i ω) (ρ i)).toReal) * (ρ i) ^ 2)) := by
      simpa [Submission.Helpers.levyConcentration] using hCb
    exact Submission.RogozinBridge.small_coords_sum_le P hb_meas hb_indep hp₀ hp₁ hb_law hx hC0 hr₀ hrm hsmall hCb' l

end

end Submission.RogozinBridge
