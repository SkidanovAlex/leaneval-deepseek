import Mathlib
import Submission.Work.TMC7Core.Scale.rational_case
import Submission.Work.TMC7Core.Scale.scale_step_avg
import Submission.Work.TMC7Core.Scale.pairing_step

/-!
# `Work.TMC7Core.Scale.scale_tower_step`

The per-stage step of the Bourgain--Jitomirskaya scale *tower* (AJ [BJ] Lemma 7 chain): from
the affine scale step `Scale.AvgStep.scale_step_avg` (finite-scale form of [BJ] Lemma 6) and
the pairing recurrence `Scale.pairing_step` one obtains, at a single base scale `N`,
approximant `a/q` and multiplier `m`,

* the **non-affine** relation `|L_{mN} + L_N − 2 L_{2N}| ≤ (4C₀+1)e^{−cκq/2} + 4C₀/m`
  (the affine relation plus the elementary bound `|L_N − L_{2N}| ≤ C₀` coming from
  `L_{2N} ≤ L_N ≤ C₀`), and
* the **defect recursion** `|(L_{mN} − L_{2mN}) − (1/m)(L_N − L_{2N})| ≤ 2(4C₀+1)e^{−cκq/2}`,
  which is `Scale.pairing_step` verbatim.

These are exactly the two per-stage hypotheses of the tower assembly
(`Work.TMComp.C7Aux.towerAssembly.tower_le`).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Scale

open Work.TMC7Core Work.TMC7Core.Lyap

/-- Elementary combination of the affine scale step with the crude bound `|L_N − L_{2N}| ≤ C₀`:
the affine relation `|X + (1 − 2/mm)Y − (2 − 2/mm)Z| ≤ Err` together with `|Y − Z| ≤ C₀`
gives the non-affine relation `|X + Y − 2Z| ≤ Err + 4C₀/mm`. -/
private theorem tower_step_arith {X Y Z Err C₀ mm : ℝ} (hmm : 0 < mm)
    (haff : |X + (1 - 2 / mm) * Y - (2 - 2 / mm) * Z| ≤ Err)
    (hDabs : |Y - Z| ≤ C₀) (hC₀ : 0 ≤ C₀) :
    |X + Y - 2 * Z| ≤ Err + 4 * C₀ / mm := by
  have key : X + Y - 2 * Z
      = (X + (1 - 2 / mm) * Y - (2 - 2 / mm) * Z) + (2 / mm) * (Y - Z) := by
    field_simp
    ring
  rw [key]
  have h2 : |(2 / mm) * (Y - Z)| ≤ (2 / mm) * C₀ := by
    have h1 : |(2 / mm) * (Y - Z)| = (2 / mm) * |Y - Z| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / mm)]
    rw [h1]
    exact mul_le_mul_of_nonneg_left hDabs (by positivity)
  calc |(X + (1 - 2 / mm) * Y - (2 - 2 / mm) * Z) + (2 / mm) * (Y - Z)|
      ≤ |X + (1 - 2 / mm) * Y - (2 - 2 / mm) * Z| + |(2 / mm) * (Y - Z)| :=
        abs_add_le_real' _ _
    _ ≤ Err + (2 / mm) * C₀ := add_le_add haff h2
    _ ≤ Err + 4 * C₀ / mm := by
        have h3 : (2 / mm) * C₀ ≤ 4 * C₀ / mm := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          have h4 : (0 : ℝ) < mm⁻¹ := inv_pos.mpr hmm
          nlinarith [hC₀, h4]
        linarith

theorem scale_tower_step (lam : ℝ) (Kset : Set ℝ) (c C C₀ : ℝ)
    (hLDT : HasLDTOn lam Kset c C) (hC₀ : HasLEBound lam Kset C₀) (hc1 : c ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 100) (E : ℝ) (hE : E ∈ Kset)
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Nat.Coprime (Int.natAbs a) q)
    (hqC : C * (κ ^ 2)⁻¹ ≤ (q : ℝ))
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2))
    (N : ℕ) (hN : C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (N : ℝ))
    (hL : 100 * κ < lyapAvg α lam (E : ℂ) N)
    (h2N : (9 / 10) * lyapAvg α lam (E : ℂ) N < lyapAvg α lam (E : ℂ) (2 * N))
    (m : ℕ) (hm : 3 ≤ m)
    (hmq : ((2 * m : ℕ) : ℝ) < Real.exp (c * κ * (q : ℝ) / 2)) :
    |lyapAvg α lam (E : ℂ) (m * N) + lyapAvg α lam (E : ℂ) N
        - 2 * lyapAvg α lam (E : ℂ) (2 * N)|
        ≤ (4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2)) + 4 * C₀ / (m : ℝ)
    ∧ |(lyapAvg α lam (E : ℂ) (m * N) - lyapAvg α lam (E : ℂ) (2 * (m * N)))
        - (1 / (m : ℝ)) * (lyapAvg α lam (E : ℂ) N - lyapAvg α lam (E : ℂ) (2 * N))|
        ≤ 2 * ((4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2))) := by
  -- the multiplier bound needed by the (affine) scale step
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmq' : (m : ℝ) < Real.exp (c * κ * (q : ℝ) / 2) := by
    have hle : (m : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast (show m ≤ 2 * m by omega)
    linarith
  refine ⟨?_, pairing_step lam Kset c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α a q hq hcop hqC hα N hN
    hL h2N m hm hmq⟩
  -- the affine scale step at the multiplier `m`
  have haff := AvgStep.scale_step_avg lam Kset c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α a q hq hcop
    hqC hα N hN hL h2N m hm hmq'
  -- the elementary bound `|L_N − L_{2N}| ≤ C₀`
  have hBle : lyapAvg α lam (E : ℂ) N ≤ C₀ := hasLEBound_lyapAvg_le hC₀ hE α N
  have hCB : lyapAvg α lam (E : ℂ) (2 * N) ≤ lyapAvg α lam (E : ℂ) N :=
    lyapAvg_two_le α lam (E : ℂ) N
  have hDabs : |lyapAvg α lam (E : ℂ) N - lyapAvg α lam (E : ℂ) (2 * N)| ≤ C₀ := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  exact tower_step_arith hmpos haff hDabs (le_of_lt hC₀.1)

end Work.TMC7Core.Scale
