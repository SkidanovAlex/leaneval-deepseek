/-
# The mixed part of the `H^n`-integrand of `m·f`

Given the Leibniz expansion
`mixed j i (m·f) = ∑_{b≤j} (j.choose b) · (DzIterZ b m) · (mixed (j-b) i f)`
on `(0,∞) × (0,π/2)` and the bound `|DzIterZ b m z| ≤ B` for `b ≤ n`, `z ∈ [0,∞)`,
the second (mixed, `i ≥ 1`) sum of the `H^n`-integrand of `m·f` is bounded by a constant
`K = K(n,B)` times the `H^n`-integrand of `f`.  The proof is Cauchy–Schwarz on each of the
finitely many expansions, combined with the term bound `sq_le_HkIntegrand_mixed`; the points
with `z = 0` or `θ ∈ {0, π/2}` are vacuous because the weight `Wt` (resp. the mixed
derivatives of order `≥ 1`) vanish there.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Coercivity.CommutZBase
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- At an angle with `sin (2θ) = 0`, all mixed derivatives of `θ`-order `≥ 1` vanish. -/
private theorem mixed_eq_zero_of_sin_eq_zero {H : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) {j i : ℕ} (hi : 1 ≤ i) : Spaces.mixed j i H z θ = 0 := by
  have h1 : ∀ z' : ℝ, Spaces.DthIter i H z' θ = 0 :=
    fun z' => Spaces.DthIter_eq_zero_of_sin hθ i hi z'
  rw [Spaces.mixed]
  exact Spaces.DzIter_eq_zero_of_slice_zero (u := Spaces.DthIter i H) (θ := θ) h1 j z

theorem CommutZ_mult_Msum_le (α : ℝ) (n : ℕ) (m : ℝ → ℝ) {B : ℝ}
    (hB : ∀ j ≤ n, ∀ z ∈ Set.Ici (0 : ℝ), |CommutZ.DzIterZ j m z| ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℝ → ℝ,
      (∀ j i : ℕ, 1 ≤ i → i + j ≤ n → ∀ z ∈ Set.Ioi (0 : ℝ),
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Spaces.mixed j i (fun z θ => m z * f z θ) z θ =
          ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
            (CommutZ.DzIterZ b m z * Spaces.mixed (j - b) i f z θ)) →
      ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
        (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if 1 ≤ i ∧ i + j ≤ n then
            (Spaces.mixed j i (fun z θ => m z * f z θ) z θ * Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ K * Spaces.HkIntegrand α n f z θ := by
  have hB0 : 0 ≤ B := by
    have h := hB 0 (Nat.zero_le n) 0 (by simp [Spaces.Iz])
    exact le_trans (abs_nonneg _) h
  set S : ℕ → ℝ := fun j => ∑ b ∈ Finset.range (j + 1), ((j.choose b : ℝ)) ^ 2 with hS
  have hS' : ∀ j, S j = ∑ b ∈ Finset.range (j + 1), ((j.choose b : ℝ)) ^ 2 :=
    fun j => congrFun hS j
  have hSnn : ∀ j, 0 ≤ S j := fun j => by
    rw [hS']
    exact Finset.sum_nonneg fun b _ => sq_nonneg _
  set K : ℝ := ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      if 1 ≤ i ∧ i + j ≤ n then B ^ 2 * S j * (j + 1) else 0 with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [if_pos hc]
      exact mul_nonneg (mul_nonneg (sq_nonneg B) (hSnn j)) (by positivity)
    · rw [if_neg hc]
  refine ⟨K, hK0, ?_⟩
  intro f hexp z hz θ hθ
  set F : ℝ := Spaces.HkIntegrand α n f z θ with hF
  have hFnn : 0 ≤ F := by rw [hF]; exact Spaces.HkIntegrand_nonneg α n f z θ
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hz0
  · -- `z = 0`: the weight `Wt` vanishes
    subst hz0
    have hWt0 : Spaces.Wt α 0 θ = 0 := by simp [Spaces.Wt, Spaces.w]
    have hzero : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n then
          (Spaces.mixed j i (fun z θ => m z * f z θ) 0 θ * Spaces.Wt α 0 θ) ^ 2
        else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ n
      · rw [if_pos hc, hWt0]; ring
      · rw [if_neg hc]
    rw [hzero]
    exact mul_nonneg hK0 hFnn
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · -- interior: Cauchy–Schwarz on each Leibniz expansion
      have hterm : ∀ i j : ℕ, 1 ≤ i → i + j ≤ n →
          (Spaces.mixed j i (fun z θ => m z * f z θ) z θ * Spaces.Wt α z θ) ^ 2
            ≤ (B ^ 2 * S j * (j + 1)) * F := by
        intro i j hi hij
        have hexpji := hexp j i hi hij z hz0 θ hθi
        have hsplit : Spaces.mixed j i (fun z θ => m z * f z θ) z θ * Spaces.Wt α z θ
            = ∑ b ∈ Finset.range (j + 1),
                ((j.choose b : ℝ) * CommutZ.DzIterZ b m z) *
                  (Spaces.mixed (j - b) i f z θ * Spaces.Wt α z θ) := by
          rw [hexpji, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [hsplit]
        have hb1 : (∑ b ∈ Finset.range (j + 1),
              ((j.choose b : ℝ) * CommutZ.DzIterZ b m z) ^ 2) ≤ B ^ 2 * S j := by
          have hstep : ∀ b ∈ Finset.range (j + 1),
              ((j.choose b : ℝ) * CommutZ.DzIterZ b m z) ^ 2
                ≤ ((j.choose b : ℝ)) ^ 2 * B ^ 2 := by
            intro b hb
            have hbn : b ≤ n := by have := Finset.mem_range.mp hb; omega
            have he : |CommutZ.DzIterZ b m z| ≤ B := hB b hbn z (le_of_lt hz0)
            have h2 : (CommutZ.DzIterZ b m z) ^ 2 ≤ B ^ 2 := by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) he 2
            calc ((j.choose b : ℝ) * CommutZ.DzIterZ b m z) ^ 2
                = ((j.choose b : ℝ)) ^ 2 * (CommutZ.DzIterZ b m z) ^ 2 := by ring
              _ ≤ ((j.choose b : ℝ)) ^ 2 * B ^ 2 :=
                  mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
          calc (∑ b ∈ Finset.range (j + 1),
                ((j.choose b : ℝ) * CommutZ.DzIterZ b m z) ^ 2)
              ≤ ∑ b ∈ Finset.range (j + 1), ((j.choose b : ℝ)) ^ 2 * B ^ 2 :=
                Finset.sum_le_sum hstep
            _ = B ^ 2 * ∑ b ∈ Finset.range (j + 1), ((j.choose b : ℝ)) ^ 2 := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun b _ => by ring
            _ = B ^ 2 * S j := by rw [hS']
        have hb2 : (∑ b ∈ Finset.range (j + 1),
              (Spaces.mixed (j - b) i f z θ * Spaces.Wt α z θ) ^ 2) ≤ (j + 1) * F := by
          calc (∑ b ∈ Finset.range (j + 1),
                (Spaces.mixed (j - b) i f z θ * Spaces.Wt α z θ) ^ 2)
              ≤ ∑ _b ∈ Finset.range (j + 1), F := by
                refine Finset.sum_le_sum fun b hb => ?_
                have hbn : i + (j - b) ≤ n := by have := Finset.mem_range.mp hb; omega
                have h := Spaces.sq_le_HkIntegrand_mixed α n f z θ i (j - b) hi hbn
                simpa only [← hF] using h
            _ = (j + 1) * F := by
                simp [Finset.sum_const, nsmul_eq_mul]
        calc (∑ b ∈ Finset.range (j + 1),
              ((j.choose b : ℝ) * CommutZ.DzIterZ b m z) *
                (Spaces.mixed (j - b) i f z θ * Spaces.Wt α z θ)) ^ 2
            ≤ (∑ b ∈ Finset.range (j + 1),
                ((j.choose b : ℝ) * CommutZ.DzIterZ b m z) ^ 2) *
              (∑ b ∈ Finset.range (j + 1),
                (Spaces.mixed (j - b) i f z θ * Spaces.Wt α z θ) ^ 2) :=
              Finset.sum_mul_sq_le_sq_mul_sq _ _ _
          _ ≤ (B ^ 2 * S j) * ((j + 1) * F) :=
              mul_le_mul hb1 hb2 (Finset.sum_nonneg fun b _ => sq_nonneg _)
                (mul_nonneg (sq_nonneg B) (hSnn j))
          _ = (B ^ 2 * S j * (j + 1)) * F := by ring
      calc (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            if 1 ≤ i ∧ i + j ≤ n then
              (Spaces.mixed j i (fun z θ => m z * f z θ) z θ * Spaces.Wt α z θ) ^ 2
            else 0)
          ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              if 1 ≤ i ∧ i + j ≤ n then (B ^ 2 * S j * (j + 1)) * F else 0 := by
            refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ n
            · rw [if_pos hc, if_pos hc]
              exact hterm i j hc.1 hc.2
            · rw [if_neg hc, if_neg hc]
        _ = K * F := by
            rw [hK]
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ n <;> simp [hc]
    · -- boundary angle: the mixed derivatives of order `≥ 1` vanish
      have hsin : Real.sin (2 * θ) = 0 := Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi
      have hzero : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if 1 ≤ i ∧ i + j ≤ n then
            (Spaces.mixed j i (fun z θ => m z * f z θ) z θ * Spaces.Wt α z θ) ^ 2
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        by_cases hc : 1 ≤ i ∧ i + j ≤ n
        · rw [if_pos hc]
          rw [mixed_eq_zero_of_sin_eq_zero hsin hc.1]
          ring
        · rw [if_neg hc]
      rw [hzero]
      exact mul_nonneg hK0 hFnn

end Work.Coercivity
