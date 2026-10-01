import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.DirichletCharacter.Bounds

namespace Commons.NumberTheory.DirichletCharacter

/-- Burgess' bound for a primitive Dirichlet character modulo a cubefree modulus `q`.

Quantifier structure: as stated, the constant `C` is allowed to depend on all the data
of the problem (`q`, `χ`, `hχ`, `ε`, `k`), because `∃ C` is quantified after all of them.
Consequently the estimate is a consequence of the trivial pointwise bound `‖χ n‖ ≤ 1`:
the sum has `H` terms, hence `‖∑ …‖ ≤ H ≤ q`, while for the non-negative exponents
`a = (k+1)/(4k²) + ε` and `b = 1 - 1/k` one has `q ≤ q * q^a * H^b` (as `q ≥ 1` and
`H ≥ 1`).  The classical Burgess bound requires `C` to be *uniform* in `q`, which is a
strictly stronger statement than the one formalized here (there `∃ C` must precede `q`). -/
theorem burgess_charSum_cubefree {q : ℕ} [NeZero q] (hcube : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (h1 : χ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
      ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
        C * (q : ℝ) ^ ((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  set a : ℝ := (k + 1 : ℝ) / (4 * k ^ 2) + ε with ha_def
  set b : ℝ := 1 - 1 / (k : ℝ) with hb_def
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℕ) < q := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast this
  have hq_one : (1 : ℝ) ≤ (q : ℝ) := by
    have : (1 : ℕ) ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : (0 : ℕ) < k := by omega
    exact_mod_cast this
  have hk_one : (1 : ℝ) ≤ (k : ℝ) := by
    have : (1 : ℕ) ≤ k := by omega
    exact_mod_cast this
  have ha_nonneg : 0 ≤ a := by
    rw [ha_def]
    have hden : (0 : ℝ) < 4 * (k : ℝ) ^ 2 := by nlinarith [hk_pos]
    have hnum : (0 : ℝ) < (k : ℝ) + 1 := by linarith [hk_pos]
    have hpos : 0 < ((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) := div_pos hnum hden
    linarith
  have hb_nonneg : 0 ≤ b := by
    rw [hb_def]
    have hle : (1 : ℝ) / (k : ℝ) ≤ 1 := by
      rw [div_le_one hk_pos]; exact hk_one
    linarith
  refine ⟨(q : ℝ), hq_pos, ?_⟩
  intro N H hN hH hHq
  have hH_one : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHq' : (H : ℝ) ≤ (q : ℝ) := by exact_mod_cast hHq
  have hqa : (1 : ℝ) ≤ (q : ℝ) ^ a := Real.one_le_rpow hq_one ha_nonneg
  have hHb : (1 : ℝ) ≤ (H : ℝ) ^ b := Real.one_le_rpow hH_one hb_nonneg
  have hS : ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ (H : ℝ) := by
    calc ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖
        ≤ ∑ n ∈ Finset.Ioc N (N + H), ‖χ n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ioc N (N + H), (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro n _
            exact χ.norm_le_one (n : ZMod q)
      _ = ((Finset.Ioc N (N + H)).card : ℝ) := by simp
      _ = (H : ℝ) := by simp [Nat.card_Ioc]
  calc ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ (H : ℝ) := hS
    _ ≤ (q : ℝ) := hHq'
    _ ≤ (q : ℝ) * (q : ℝ) ^ a * (H : ℝ) ^ b := by
          have h1 : (q : ℝ) ≤ (q : ℝ) * (q : ℝ) ^ a := by
            have := mul_le_mul_of_nonneg_left hqa (le_of_lt hq_pos)
            simpa using this
          have h2 : (q : ℝ) * (q : ℝ) ^ a ≤ (q : ℝ) * (q : ℝ) ^ a * (H : ℝ) ^ b := by
            have hnn : (0 : ℝ) ≤ (q : ℝ) * (q : ℝ) ^ a :=
              mul_nonneg (le_of_lt hq_pos) (le_of_lt (Real.rpow_pos_of_pos hq_pos a))
            have := mul_le_mul_of_nonneg_left hHb hnn
            simpa using this
          exact h1.trans h2

end Commons.NumberTheory.DirichletCharacter