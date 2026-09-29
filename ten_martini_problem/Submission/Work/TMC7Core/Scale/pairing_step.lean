import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.Scale.prop9_aux
import Submission.Work.TMC7Core.Scale.scale_step_avg

/-!
# The pairing recurrence of the scale chain

Two applications of the finite-scale step (`Scale/scale_step_avg.lean`) at the same base scale,
with multipliers `m` and `2m`, give the recurrence for the pairing defect
`δ_N = L_N − L_{2N}`:  `δ_{mN} = (1/m)·δ_N + O(ε)`,  with `ε = (4C₀+1)e^{−cκq/2}`.

Together with the step itself this is exactly the pair of hypotheses `chain_sum` consumes
(`hrec` and `hδ`).  This file is separate from `prop9_final.lean` so that the latter does not
depend on the avalanche principle and can be verified while `Avalanche/` is in flux.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Scale

open Work.TMC7Core Work.TMC7Core.Lyap

/-- **Pairing recurrence.**  Two applications of the scale step (`scale_step_avg`) at the same
base scale `N`, with multipliers `m` and `2m`, give the recurrence for the pairing defect
`δ_N = L_N - L_{2N}`:
`δ_{mN} = (1/m) δ_N + O(ε)`,  `ε = (4C₀+1)e^{-cκq/2}`.
Together with the step itself this is exactly the input of `chain_sum` (`hrec` and `hδ`). -/
theorem pairing_step (lam : ℝ) (K : Set ℝ) (c C C₀ : ℝ) (hLDT : HasLDTOn lam K c C)
    (hC₀ : HasLEBound lam K C₀) (hc1 : c ≤ 1) (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 100)
    (E : ℝ) (hE : E ∈ K) (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime (Int.natAbs a) q) (hqC : C * (κ ^ 2)⁻¹ ≤ (q : ℝ))
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2)) (N : ℕ)
    (hN : C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (N : ℝ)) (hL : 100 * κ < lyapAvg α lam (E : ℂ) N)
    (h2N : (9 / 10) * lyapAvg α lam (E : ℂ) N < lyapAvg α lam (E : ℂ) (2 * N))
    (m : ℕ) (hm : 3 ≤ m) (hmq : ((2 * m : ℕ) : ℝ) < Real.exp (c * κ * (q : ℝ) / 2)) :
    |(lyapAvg α lam (E : ℂ) (m * N) - lyapAvg α lam (E : ℂ) (2 * (m * N)))
      - (1 / (m : ℝ)) * (lyapAvg α lam (E : ℂ) N - lyapAvg α lam (E : ℂ) (2 * N))|
      ≤ 2 * ((4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2))) := by
  have hmq' : (m : ℝ) < Real.exp (c * κ * (q : ℝ) / 2) := by
    have hle : (m : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by push_cast; nlinarith [hm]
    linarith
  have h1 := AvgStep.scale_step_avg lam K c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α a q hq hcop hqC
    hα N hN hL h2N m hm hmq'
  have h2 := AvgStep.scale_step_avg lam K c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α a q hq hcop hqC
    hα N hN hL h2N (2 * m) (by omega) hmq
  have e1 : (2 * m) * N = 2 * (m * N) := by ring
  rw [e1] at h2
  have hcast2 : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have h2' : |lyapAvg α lam (E : ℂ) (2 * (m * N))
        + (1 - 1 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
        - (2 - 1 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N)|
      ≤ (4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2)) := by
    have h2m : (1 - 2 / ((2 * m : ℕ) : ℝ)) = 1 - 1 / (m : ℝ) := by
      rw [hcast2]; field_simp
    have h2M : (2 - 2 / ((2 * m : ℕ) : ℝ)) = 2 - 1 / (m : ℝ) := by
      rw [hcast2]; field_simp
    rwa [h2m, h2M] at h2
  have hx : |lyapAvg α lam (E : ℂ) (m * N) + (1 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
      - (2 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N)|
      ≤ (4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2)) := h1
  have htri : |(lyapAvg α lam (E : ℂ) (m * N) + (1 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
        - (2 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N))
      - (lyapAvg α lam (E : ℂ) (2 * (m * N)) + (1 - 1 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
        - (2 - 1 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N))|
      ≤ 2 * ((4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2))) := by
    have h1lo : -((4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2)))
        ≤ lyapAvg α lam (E : ℂ) (m * N) + (1 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
          - (2 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N) :=
      (abs_le.mp hx).1
    have h1hi : lyapAvg α lam (E : ℂ) (m * N) + (1 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
          - (2 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N)
        ≤ (4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2)) := (abs_le.mp hx).2
    have h2lo : -((4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2)))
        ≤ lyapAvg α lam (E : ℂ) (2 * (m * N)) + (1 - 1 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
          - (2 - 1 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N) :=
      (abs_le.mp h2').1
    have h2hi : lyapAvg α lam (E : ℂ) (2 * (m * N)) + (1 - 1 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
          - (2 - 1 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N)
        ≤ (4 * C₀ + 1) * Real.exp (-(c * κ * (q : ℝ) / 2)) := (abs_le.mp h2').2
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hid : (lyapAvg α lam (E : ℂ) (m * N) + (1 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
        - (2 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N))
      - (lyapAvg α lam (E : ℂ) (2 * (m * N)) + (1 - 1 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
        - (2 - 1 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N))
      = (lyapAvg α lam (E : ℂ) (m * N) - lyapAvg α lam (E : ℂ) (2 * (m * N)))
        - (1 / (m : ℝ)) * (lyapAvg α lam (E : ℂ) N - lyapAvg α lam (E : ℂ) (2 * N)) := by
    ring
  rwa [hid] at htri

