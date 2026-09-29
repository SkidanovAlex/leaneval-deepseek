import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.Scale.prop9_aux
import Submission.Work.TMComp.C7Aux.towerAssembly
import Submission.Work.TMComp.LocCantor.dyadic_level_pairing

/-!
# The base scale of the [BJ] scale tower

The tower of `Work.TMComp.C7Aux.tower_le` starts at a scale `N₀` which must carry

* the level `100κ < L_{N₀}`, and
* the *pairing* `(9/10)·L_{N₀} < L_{2N₀}`.

When the *true* exponent at `E` is large (`100κ < lyap α lam E`) the level is automatic at
every scale (`lyap ≤ L_n`), and the pairing is produced by the dyadic pigeonhole of [BJ] §4
(`LocCantor.dyadic_level_pairing`): along the chain `t, 2t, 4t, …` the level `> 100κ` at the
top forces some doubling to carry the pairing, so it suffices to take the chain long enough.

This is the scale selection used by any tower starting from an approximant `a/q` of `α`
(`Cκ⁻² ≤ q`): the base scale is `N₀ = t·2^j` with `t = ⌈Cκ⁻²q⌉` and `j < J` the pigeonhole
index.  No upper bound on `N₀` is needed for the tower, only the lower one
`Cκ⁻²q ≤ N₀`.
-/

open MeasureTheory Filter Topology Set
open Work.TMC7Core

noncomputable section

namespace Work.TMComp.C7Aux

/-- **The base scale of the [BJ] tower.**  If the true exponent at `E` is large
(`100κ < lyap`), then for every `q ≥ 1` there is a scale `N₀ ≥ Cκ⁻²q` carrying the level
`100κ < L_{N₀}` and the pairing `(9/10)·L_{N₀} < L_{2N₀}`. -/
theorem exists_base_pairing {lam : ℝ} {K : Set ℝ} {C₀ C κ : ℝ} (hC₀ : HasLEBound lam K C₀)
    (hκ : 0 < κ) {α : ℝ} {q : ℕ} (hq : 1 ≤ q) (hqC : C * (κ ^ 2)⁻¹ ≤ (q : ℝ))
    {E : ℝ} (hE : E ∈ K) (hL : 100 * κ < lyap α lam (E : ℂ)) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (N₀ : ℝ)
      ∧ 100 * κ < lyapAvg α lam (E : ℂ) N₀
      ∧ (9 / 10) * lyapAvg α lam (E : ℂ) N₀ < lyapAvg α lam (E : ℂ) (2 * N₀) := by
  classical
  have hC₀pos : 0 < C₀ := hC₀.1
  set t : ℕ := max 1 (Nat.ceil (C * (κ ^ 2)⁻¹ * (q : ℝ))) with ht
  have ht1 : 1 ≤ t := le_max_left _ _
  have htC : C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (t : ℝ) := by
    have h1 : (Nat.ceil (C * (κ ^ 2)⁻¹ * (q : ℝ)) : ℝ) ≤ (t : ℝ) := by
      have := le_max_right (1 : ℕ) (Nat.ceil (C * (κ ^ 2)⁻¹ * (q : ℝ)))
      exact_mod_cast this
    have h2 := Nat.le_ceil (C * (κ ^ 2)⁻¹ * (q : ℝ))
    linarith
  set J : ℕ := Nat.ceil (Real.log (C₀ / (100 * κ)) / Real.log (10 / 9)) + 1 with hJ
  have hJcond : Real.log (C₀ / (100 * κ)) / Real.log (10 / 9) < (J : ℝ) := by
    rw [hJ]
    push_cast
    linarith [Nat.le_ceil (Real.log (C₀ / (100 * κ)) / Real.log (10 / 9))]
  have ht1' : 1 ≤ t * 2 ^ J :=
    le_trans ht1 (Nat.le_mul_of_pos_right t (pow_pos (by norm_num) J))
  have htop : 100 * κ < lyapAvg α lam (E : ℂ) (t * 2 ^ J) :=
    lt_of_lt_of_le hL (Scale.lyap_le_lyapAvg α lam (E : ℂ) ht1')
  obtain ⟨j, hjJ, hp⟩ := LocCantor.dyadic_level_pairing (fun n => lyapAvg α lam (E : ℂ) n) t J C₀ κ
    hκ ht1 (fun m _ => Scale.lyapAvg_two_le α lam (E : ℂ) m)
    (fun m => lyapAvg_le_of_hasLEBound hC₀ hE α m) htop hJcond
  have hj1 : 1 ≤ t * 2 ^ j :=
    le_trans ht1 (Nat.le_mul_of_pos_right t (pow_pos (by norm_num) j))
  refine ⟨t * 2 ^ j, hj1, ?_, ?_, ?_⟩
  · calc C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (t : ℝ) := htC
      _ ≤ ((t * 2 ^ j : ℕ) : ℝ) := by
          have h : t ≤ t * 2 ^ j := by
            calc t = t * 1 := (mul_one t).symm
              _ ≤ t * 2 ^ j := Nat.mul_le_mul_left t (Nat.one_le_two_pow)
          exact_mod_cast h
  · exact lt_of_lt_of_le hL (Scale.lyap_le_lyapAvg α lam (E : ℂ) hj1)
  · have h2N : 2 * (t * 2 ^ j) = t * 2 ^ (j + 1) := by
      rw [pow_succ]; ring
    rw [h2N]
    exact hp

end Work.TMComp.C7Aux
