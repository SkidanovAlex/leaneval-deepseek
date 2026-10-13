import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open MeasureTheory

/-- **Cauchy–Schwarz for a finite family with a pointwise squared domination.**

If `g i ^ 2 ≤ h i` for every `i ∈ S`, then
`(∑ i ∈ S, f i * g i) ^ 2 ≤ (∑ i ∈ S, f i ^ 2) * (∑ i ∈ S, h i)`.

The proof is the classical Cauchy–Schwarz inequality `Finset.sum_mul_sq_le_sq_mul_sq`
followed by monotonicity of the product in the second factor. -/
private lemma cs_mode_sum {ι : Type*} (S : Finset ι) (f g h : ι → ℝ)
    (hgh : ∀ i ∈ S, g i ^ 2 ≤ h i) :
    (∑ i ∈ S, f i * g i) ^ 2 ≤ (∑ i ∈ S, f i ^ 2) * (∑ i ∈ S, h i) := by
  have h1 : (∑ i ∈ S, f i * g i) ^ 2 ≤ (∑ i ∈ S, f i ^ 2) * (∑ i ∈ S, g i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq S f g
  have h2 : (∑ i ∈ S, g i ^ 2) ≤ ∑ i ∈ S, h i := Finset.sum_le_sum hgh
  have h3 : 0 ≤ ∑ i ∈ S, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 h3)

theorem modeSum_arith {N : ℕ} {a c : ℕ → ℝ → ℝ} {μ : ℕ → ℝ}
    (hμ : ∀ m, 0 < μ m)
    (hper : ∀ m, m ≤ N →
      μ m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ Real.sqrt (∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2)) :
    (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
        * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2
      ≤ (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m) ^ 2)
          * (∑ m ∈ Finset.range (N + 1),
              ∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
  classical
  -- Per-mode: `(μ m * √(∫ a² w²)) ^ 2 ≤ ∫ c² w²`.
  have hstep : ∀ m ∈ Finset.range (N + 1),
      (μ m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) ^ 2
        ≤ ∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hle := hper m (by omega)
    have hT : 0 ≤ ∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      setIntegral_nonneg_of_ae (Filter.Eventually.of_forall fun z =>
        mul_nonneg (sq_nonneg (c m z)) (sq_nonneg (Work.Spaces.w z)))
    have hA : 0 ≤ μ m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
      mul_nonneg (le_of_lt (hμ m)) (Real.sqrt_nonneg _)
    have h2 := mul_self_le_mul_self hA hle
    have hsq : Real.sqrt (∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * Real.sqrt (∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2)
        = ∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
      rw [← pow_two]
      exact Real.sq_sqrt hT
    rw [hsq] at h2
    rw [pow_two]
    exact h2
  -- Rewrite each summand as `(((m+1)/μ m) * (μ m * √(∫ a² w²)))`.
  have hsum : (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1)
        * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2))
      = ∑ m ∈ Finset.range (N + 1), (((m : ℝ) + 1) / μ m)
          * (μ m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    apply Finset.sum_congr rfl
    intro m _
    have hne : μ m ≠ 0 := ne_of_gt (hμ m)
    field_simp
  rw [hsum]
  exact cs_mode_sum (Finset.range (N + 1))
    (fun m => (((m : ℝ) + 1) / μ m))
    (fun m => μ m * Real.sqrt (∫ z in Work.Spaces.Iz, (a m z) ^ 2 * (Work.Spaces.w z) ^ 2))
    (fun m => ∫ z in Work.Spaces.Iz, (c m z) ^ 2 * (Work.Spaces.w z) ^ 2)
    hstep

end Work.FTS.ClassC
