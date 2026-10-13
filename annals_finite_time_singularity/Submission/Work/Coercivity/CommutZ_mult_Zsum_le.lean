/-
# The pure `D_z` part of the `H^n`-integrand of `m·f`

Given the Leibniz expansion
`DzIter i (m·f) = ∑_{b≤i} (i.choose b) · (DzIterZ b m) · (DzIter (i-b) f)`
on `(0,∞) × [0,π/2]` and the bound `|DzIterZ b m z| ≤ B` for `b ≤ n`, `z ∈ [0,∞)`,
the first (pure `D_z`) sum of the `H^n`-integrand of `m·f` is bounded by a constant
`K = K(n,B)` times the `H^n`-integrand of `f`.  The proof is Cauchy–Schwarz on each of
the finitely many expansions, combined with the term bound `sq_le_HkIntegrand_z`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.CommutZBase
import Submission.Work.Spaces.HkSq_terms

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

theorem CommutZ_mult_Zsum_le (α : ℝ) (n : ℕ) (m : ℝ → ℝ) {B : ℝ}
    (hB : ∀ j ≤ n, ∀ z ∈ Set.Ici (0 : ℝ), |CommutZ.DzIterZ j m z| ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝ → ℝ → ℝ,
      (∀ i ≤ n, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Spaces.Iθ,
        Spaces.DzIter i (fun z θ => m z * f z θ) z θ =
          ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) *
            (CommutZ.DzIterZ b m z * Spaces.DzIter (i - b) f z θ)) →
      ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
        (∑ i ∈ Finset.range (n + 1),
          (Spaces.DzIter i (fun z θ => m z * f z θ) z θ *
            (Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2))) ^ 2)
        ≤ K * Spaces.HkIntegrand α n f z θ := by
  -- `B ≥ 0`, from the `j = 0`, `z = 0` instance of the hypothesis.
  have hB0 : 0 ≤ B := by
    have h := hB 0 (Nat.zero_le n) 0 (by simp [Spaces.Iz])
    exact le_trans (abs_nonneg _) h
  -- The binomial square sums `S i = ∑_{b≤i} (i.choose b)^2`.
  set S : ℕ → ℝ := fun i => ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) ^ 2 with hS
  have hS' : ∀ i, S i = ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) ^ 2 :=
    fun i => congrFun hS i
  have hSnn : ∀ i, 0 ≤ S i := fun i => by
    rw [hS']
    exact Finset.sum_nonneg fun b _ => sq_nonneg _
  refine ⟨∑ i ∈ Finset.range (n + 1), B ^ 2 * S i * (i + 1), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (sq_nonneg B) (hSnn i))
      (by positivity)
  · intro f hexp z hz θ hθ
    set H : ℝ := Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2) with hH
    set F : ℝ := Spaces.HkIntegrand α n f z θ with hF
    have hFnn : 0 ≤ F := by rw [hF]; exact Spaces.HkIntegrand_nonneg α n f z θ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hz0
    · -- `z = 0`: the radial weight vanishes, so every term of the sum is `0`
      subst hz0
      have hH0 : H = 0 := by
        rw [hH]
        simp [Spaces.w]
      have hzero : (∑ i ∈ Finset.range (n + 1),
          (Spaces.DzIter i (fun z θ => m z * f z θ) 0 θ * H) ^ 2) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hH0]
        ring
      rw [hzero]
      exact mul_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg
        (mul_nonneg (sq_nonneg B) (hSnn i)) (by positivity)) hFnn
    · -- `z > 0`: Cauchy–Schwarz on each Leibniz expansion
      have hterm : ∀ i ∈ Finset.range (n + 1),
          (Spaces.DzIter i (fun z θ => m z * f z θ) z θ * H) ^ 2
            ≤ (B ^ 2 * S i * (i + 1)) * F := by
        intro i hi
        have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
        have hexpi := hexp i hin z hz0 θ hθ
        -- the expanded sum, with the factor `H` distributed
        have hsplit : Spaces.DzIter i (fun z θ => m z * f z θ) z θ * H
            = ∑ b ∈ Finset.range (i + 1),
                ((i.choose b : ℝ) * CommutZ.DzIterZ b m z) *
                  (Spaces.DzIter (i - b) f z θ * H) := by
          rw [hexpi, Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
        rw [hsplit]
        -- first factor: the multiplier coefficients
        have hb1 : (∑ b ∈ Finset.range (i + 1),
              ((i.choose b : ℝ) * CommutZ.DzIterZ b m z) ^ 2) ≤ B ^ 2 * S i := by
          have hstep : ∀ b ∈ Finset.range (i + 1),
              ((i.choose b : ℝ) * CommutZ.DzIterZ b m z) ^ 2
                ≤ ((i.choose b : ℝ)) ^ 2 * B ^ 2 := by
            intro b hb
            have hbn : b ≤ n := by have := Finset.mem_range.mp hb; omega
            have he : |CommutZ.DzIterZ b m z| ≤ B := hB b hbn z (le_of_lt hz0)
            have h2 : (CommutZ.DzIterZ b m z) ^ 2 ≤ B ^ 2 := by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) he 2
            calc ((i.choose b : ℝ) * CommutZ.DzIterZ b m z) ^ 2
                = ((i.choose b : ℝ)) ^ 2 * (CommutZ.DzIterZ b m z) ^ 2 := by ring
              _ ≤ ((i.choose b : ℝ)) ^ 2 * B ^ 2 :=
                  mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
          calc (∑ b ∈ Finset.range (i + 1),
                ((i.choose b : ℝ) * CommutZ.DzIterZ b m z) ^ 2)
              ≤ ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) ^ 2 * B ^ 2 :=
                Finset.sum_le_sum hstep
            _ = B ^ 2 * ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) ^ 2 := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun b _ => by ring
            _ = B ^ 2 * S i := by rw [hS']
        -- second factor: the `f`-terms, each bounded by `HkIntegrand`
        have hb2 : (∑ b ∈ Finset.range (i + 1),
              (Spaces.DzIter (i - b) f z θ * H) ^ 2) ≤ (i + 1) * F := by
          calc (∑ b ∈ Finset.range (i + 1), (Spaces.DzIter (i - b) f z θ * H) ^ 2)
              ≤ ∑ _b ∈ Finset.range (i + 1), F := by
                refine Finset.sum_le_sum fun b hb => ?_
                have hbn : i - b ≤ n := by have := Finset.mem_range.mp hb; omega
                have h := Spaces.sq_le_HkIntegrand_z α n f z θ (i - b) hbn
                simpa only [← hH, ← hF] using h
            _ = (i + 1) * F := by
                simp [Finset.sum_const, nsmul_eq_mul]
        calc (∑ b ∈ Finset.range (i + 1),
              ((i.choose b : ℝ) * CommutZ.DzIterZ b m z) *
                (Spaces.DzIter (i - b) f z θ * H)) ^ 2
            ≤ (∑ b ∈ Finset.range (i + 1),
                ((i.choose b : ℝ) * CommutZ.DzIterZ b m z) ^ 2) *
              (∑ b ∈ Finset.range (i + 1), (Spaces.DzIter (i - b) f z θ * H) ^ 2) :=
              Finset.sum_mul_sq_le_sq_mul_sq _ _ _
          _ ≤ (B ^ 2 * S i) * ((i + 1) * F) :=
              mul_le_mul hb1 hb2 (Finset.sum_nonneg fun b _ => sq_nonneg _)
                (mul_nonneg (sq_nonneg B) (hSnn i))
          _ = (B ^ 2 * S i * (i + 1)) * F := by ring
      calc (∑ i ∈ Finset.range (n + 1),
            (Spaces.DzIter i (fun z θ => m z * f z θ) z θ * H) ^ 2)
          ≤ ∑ i ∈ Finset.range (n + 1), (B ^ 2 * S i * (i + 1)) * F :=
            Finset.sum_le_sum hterm
        _ = (∑ i ∈ Finset.range (n + 1), B ^ 2 * S i * (i + 1)) * F := by
            rw [Finset.sum_mul]

end Work.Coercivity
