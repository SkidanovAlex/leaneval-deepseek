import Mathlib
import Submission.Work.KMTAreas.A7.FibreMassHbdDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-- **One term of the Leibniz expansion of the fibre symbol.**

The `(b',a')`-th term of the Leibniz expansion `dp_symbol_eq_leibniz` of
`∂₁^{i₁}∂₂^{i₂}(φ_N ⊗ φ̃_N · weylAvg)` is bounded by the binomial coefficients times
`fibM0C P · q² (1 + S²/N) · N^{(i₁-a') + d b' - 1}` times the two bump derivatives. This is
`pointwise_weighted_bound` (i.e. the sharp symbol estimate `fibM0C_bound` together with the
support case split) with `j₁ = i₁ - a'`, `j₂ = b'`. -/
theorem fibreMass_leibniz_term (P : Polynomial ℤ) (N q k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (hmZ : mZ P q α₁ α₂ = 0) (hN : 1 ≤ N) (hq : 0 < q) (hs₁ : q • α₁ = 0) (hs₂ : q • α₂ = 0)
    (i₁ i₂ : ℕ) (hi₁ : i₁ ≤ 2) (hi₂ : i₂ ≤ 2) {a' b' : ℕ} (ha' : a' ≤ i₁) (hb' : b' ≤ i₂)
    (x y : ℝ) :
    ‖((i₂.choose b' : ℂ) * (i₁.choose a' : ℂ)) * (iteratedDeriv a' (varphiN N k₁) x)
      * (Work.KMTPlan.A6.dp (i₁ - a') b' (fun a b => weylAvg P N α₁ α₂ a b) x y)
      * (iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) y)‖
      ≤ (i₂.choose b' : ℝ) * (i₁.choose a' : ℝ)
        * ((fibM0C P * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
              * (N : ℝ) ^ (((i₁ - a' : ℕ) : ℤ) + (P.natDegree : ℤ) * (b' : ℤ) - 1))
          * (‖iteratedDeriv a' (varphiN N k₁) x‖
              * ‖iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) y‖)) := by
  have hj₁ : i₁ - a' ≤ 2 := by omega
  have hj₂ : b' ≤ 2 := by omega
  have h := pointwise_weighted_bound P N q k₁ k₂ α₁ α₂ hmZ hN hq hs₁ hs₂
    (j₁ := i₁ - a') (j₂ := b') (a' := a') (b' := i₂ - b') hj₁ hj₂ x y
  have hnn : 0 ≤ (i₂.choose b' : ℝ) * (i₁.choose a' : ℝ) := by positivity
  refine (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left h hnn)
  simp only [norm_mul, Complex.norm_natCast]
  ring

/-- **The exponent bookkeeping of the pointwise fibre bound.**

The double sum over `b'` and `a'` of the Leibniz terms, whose kernel factor carries the exponent
`(i₁ - a') + d b' - 1`, factors into the product of the two one-dimensional sums with the overall
prefactor `N^{i₁-1}` — the form in which `fibreMass_pointwise` states its bound. Purely a `zpow`
bookkeeping identity (`N ≠ 0` is what makes the additive law available). -/
theorem fibreMass_double_sum_factor (N A : ℝ) (hN : N ≠ 0) (i₁ i₂ d : ℕ) (pf qf : ℕ → ℝ) :
    (∑ b' ∈ Finset.range (i₂ + 1), ∑ a' ∈ Finset.range (i₁ + 1),
        (i₂.choose b' : ℝ) * (i₁.choose a' : ℝ)
          * ((A * N ^ (((i₁ - a' : ℕ) : ℤ) + (d : ℤ) * (b' : ℤ) - 1)) * (pf a' * qf b')))
      = (A * N ^ ((i₁ : ℤ) - 1))
          * ((∑ a' ∈ Finset.range (i₁ + 1), (i₁.choose a' : ℝ) * (N ^ (a' : ℤ))⁻¹ * pf a')
            * (∑ b' ∈ Finset.range (i₂ + 1), (i₂.choose b' : ℝ)
                * N ^ ((d : ℤ) * (b' : ℤ)) * qf b')) := by
  have key : ∀ b' ∈ Finset.range (i₂ + 1), ∀ a' ∈ Finset.range (i₁ + 1),
      (i₂.choose b' : ℝ) * (i₁.choose a' : ℝ)
        * ((A * N ^ (((i₁ - a' : ℕ) : ℤ) + (d : ℤ) * (b' : ℤ) - 1)) * (pf a' * qf b'))
      = A * N ^ ((i₁ : ℤ) - 1) * ((i₁.choose a' : ℝ) * (N ^ (a' : ℤ))⁻¹ * pf a')
          * ((i₂.choose b' : ℝ) * N ^ ((d : ℤ) * (b' : ℤ)) * qf b') := by
    intro b' hb' a' ha'
    have hai : a' ≤ i₁ := by have := Finset.mem_range.mp ha'; omega
    have hcast : (((i₁ - a' : ℕ) : ℤ)) = (i₁ : ℤ) - (a' : ℤ) := by
      rw [Nat.cast_sub hai]
    have hpow : N ^ (((i₁ - a' : ℕ) : ℤ) + (d : ℤ) * (b' : ℤ) - 1)
        = N ^ ((i₁ : ℤ) - 1) * (N ^ (a' : ℤ))⁻¹ * N ^ ((d : ℤ) * (b' : ℤ)) := by
      rw [hcast]
      rw [show (i₁ : ℤ) - ↑a' + ↑d * ↑b' - 1 = (i₁ : ℤ) - 1 + -(↑a') + ↑d * ↑b' from by ring]
      rw [← zpow_neg, ← zpow_add₀ hN, ← zpow_add₀ hN]
    rw [hpow]
    ring
  calc (∑ b' ∈ Finset.range (i₂ + 1), ∑ a' ∈ Finset.range (i₁ + 1),
        (i₂.choose b' : ℝ) * (i₁.choose a' : ℝ)
          * ((A * N ^ (((i₁ - a' : ℕ) : ℤ) + (d : ℤ) * (b' : ℤ) - 1)) * (pf a' * qf b')))
      = ∑ b' ∈ Finset.range (i₂ + 1), ∑ a' ∈ Finset.range (i₁ + 1),
          A * N ^ ((i₁ : ℤ) - 1) * ((i₁.choose a' : ℝ) * (N ^ (a' : ℤ))⁻¹ * pf a')
            * ((i₂.choose b' : ℝ) * N ^ ((d : ℤ) * (b' : ℤ)) * qf b') :=
        Finset.sum_congr rfl (fun b' hb' => Finset.sum_congr rfl (fun a' ha' => key b' hb' a' ha'))
    _ = (A * N ^ ((i₁ : ℤ) - 1))
          * ((∑ a' ∈ Finset.range (i₁ + 1), (i₁.choose a' : ℝ) * (N ^ (a' : ℤ))⁻¹ * pf a')
            * (∑ b' ∈ Finset.range (i₂ + 1), (i₂.choose b' : ℝ)
                * N ^ ((d : ℤ) * (b' : ℤ)) * qf b')) := by
        rw [Finset.sum_mul_sum (Finset.range (i₁ + 1)) (Finset.range (i₂ + 1))
              (fun a' => (i₁.choose a' : ℝ) * (N ^ (a' : ℤ))⁻¹ * pf a')
              (fun b' => (i₂.choose b' : ℝ) * N ^ ((d : ℤ) * (b' : ℤ)) * qf b')]
        rw [Finset.mul_sum]
        simp only [Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b' _ => Finset.sum_congr rfl (fun a' _ => by ring))

/-- **The pointwise fibre bound for the §6 symbol.**  For `i₁,i₂ ≤ 2`, the mixed derivative
`∂₁^{i₁}∂₂^{i₂}` of the symbol `σ = φ_N ⊗ φ̃_N · weylAvg P N α₁ α₂` at an arbitrary point `(x,y)`
is bounded by the binomial expansion of the two one-dimensional bump derivatives, with the
symbol-difference constant `fibM0C P · q² (1 + S²/N)` and the overall scale `N^{i₁-1}`.

This is the pointwise half of the derivative bound for the fibre symbol (the `l₂ = 0` column of
`mod-approx`); the `L¹`-counterpart is `kernel_hbd_bound`. -/
theorem fibreMass_pointwise (P : Polynomial ℤ) (N q k₁ k₂ : ℕ)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (hmZ : mZ P q α₁ α₂ = 0) (hN : 1 ≤ N) (hq : 0 < q) (hs₁ : q • α₁ = 0) (hs₂ : q • α₂ = 0)
    (i₁ i₂ : ℕ) (hi₁ : i₁ ≤ 2) (hi₂ : i₂ ≤ 2) (x y : ℝ) :
    ‖Work.KMTPlan.A6.dp i₁ i₂ (fun a b => varphiN N k₁ a * varphitildeN P.natDegree N k₂ b
        * weylAvg P N α₁ α₂ a b) x y‖
      ≤ (fibM0C P * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (N : ℝ) ^ ((i₁ : ℤ) - 1))
        * ((∑ a' ∈ Finset.range (i₁ + 1), (i₁.choose a' : ℝ) * ((N : ℝ) ^ (a' : ℤ))⁻¹
              * ‖iteratedDeriv a' (varphiN N k₁) x‖)
          * (∑ b' ∈ Finset.range (i₂ + 1), (i₂.choose b' : ℝ)
              * (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
              * ‖iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) y‖)) := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  rw [dp_symbol_eq_leibniz P N k₁ k₂ α₁ α₂ i₁ i₂ hi₁ hi₂ x y]
  have hstep1 : ‖∑ b' ∈ Finset.range (i₂ + 1), ∑ a' ∈ Finset.range (i₁ + 1),
        ((i₂.choose b' : ℂ) * (i₁.choose a' : ℂ)) * (iteratedDeriv a' (varphiN N k₁) x)
          * (Work.KMTPlan.A6.dp (i₁ - a') b' (fun a b => weylAvg P N α₁ α₂ a b) x y)
          * (iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) y)‖
      ≤ ∑ b' ∈ Finset.range (i₂ + 1), ∑ a' ∈ Finset.range (i₁ + 1),
        (i₂.choose b' : ℝ) * (i₁.choose a' : ℝ)
          * ((fibM0C P * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
                * (N : ℝ) ^ (((i₁ - a' : ℕ) : ℤ) + (P.natDegree : ℤ) * (b' : ℤ) - 1))
            * (‖iteratedDeriv a' (varphiN N k₁) x‖
                * ‖iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) y‖)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun b' _ => norm_sum_le _ _)).trans ?_
    refine Finset.sum_le_sum (fun b' hb' => Finset.sum_le_sum (fun a' ha' => ?_))
    have ha'i : a' ≤ i₁ := by have := Finset.mem_range.mp ha'; omega
    have hb'i : b' ≤ i₂ := by have := Finset.mem_range.mp hb'; omega
    exact fibreMass_leibniz_term P N q k₁ k₂ α₁ α₂ hmZ hN hq hs₁ hs₂ i₁ i₂ hi₁ hi₂
      ha'i hb'i x y
  exact hstep1.trans (le_of_eq (fibreMass_double_sum_factor (N : ℝ)
    (fibM0C P * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))) hN0 i₁ i₂ P.natDegree
    (fun a' => ‖iteratedDeriv a' (varphiN N k₁) x‖)
    (fun b' => ‖iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) y‖)))

end

end Work.KMTAreas.A7
