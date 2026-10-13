/-
# `Work.FTS.PhiStar.FlatWAux.QmDerivBound`

The growth bound for the divided angular modes
`Qm m θ = gC (2m+1) (sin θ)/(2 sin θ)` used by the resummation in `FlatW_psiSeries`:

  `∃ C : ℕ → ℝ, (∀ l, 0 ≤ C l) ∧ ∀ m ≥ 1, ∀ l ≤ 8, ∀ θ ∈ (0, π/2),
     |iteratedDeriv l (Qm m) θ| ≤ C l * (2m+1)^(2l+2)`.

The mathematical content and the proof route are documented in
`Submission/Work/FTS/PhiStar/FlatWAux/QmDeriv/{Basic,Trig,Expansion,Sup}.lean`, which this file
aggregates; the two input facts are the trigonometric form of the Gegenbauer polynomial
(`gC_eq_famTrig`) and the Schur–Gegenbauer energy identity (`psiAngDefs`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.QmDeriv.Expansion
import Submission.Work.FTS.PhiStar.FlatWAux.QmDeriv.Sup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

theorem QmDerivBound : ∃ C : ℕ → ℝ, (∀ l, 0 ≤ C l) ∧
    ∀ (m : ℕ), 1 ≤ m → ∀ (l : ℕ), l ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |iteratedDeriv l (Work.FTS.PhiStar.FlatWAux.Qm m) θ| ≤ C l * (2 * (m : ℝ) + 1) ^ (2 * l + 2) := by
  refine ⟨fun l => 2 ^ (2 * l + 2) + 100, fun l => by positivity, ?_⟩
  intro m hm l _ θ hθ
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h := Qm_sup_bound hm hθ
    have hnn : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 := by positivity
    have hC : (100 : ℝ) ≤ 2 ^ (2 * 0 + 2) + 100 := by norm_num
    calc |iteratedDeriv 0 (Qm m) θ| = |Qm m θ| := by rw [iteratedDeriv_zero]
      _ ≤ 100 * (2 * (m : ℝ) + 1) ^ 2 := h
      _ ≤ (2 ^ (2 * 0 + 2) + 100) * (2 * (m : ℝ) + 1) ^ (2 * 0 + 2) := by
          rw [show 2 * 0 + 2 = 2 from rfl]
          nlinarith [hC, hnn]
  · have h := Qm_iteratedDeriv_bound (m := m) (l := l) hm hθ
    have hbase : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have h1 : (2 * (m : ℝ) + 1) ^ (l + 3) ≤ (2 * (m : ℝ) + 1) ^ (2 * l + 2) :=
      pow_le_pow_right₀ hbase (by omega)
    have h2 : (0 : ℝ) ≤ 2 ^ (2 * l + 2) := by positivity
    have h3 : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ (2 * l + 2) := by positivity
    calc |iteratedDeriv l (Qm m) θ| ≤ 2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (l + 3) := h
      _ ≤ 2 ^ (2 * l + 2) * (2 * (m : ℝ) + 1) ^ (2 * l + 2) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ ≤ (2 ^ (2 * l + 2) + 100) * (2 * (m : ℝ) + 1) ^ (2 * l + 2) := by
          nlinarith [h2, h3]

end Work.FTS.PhiStar.FlatWAux
