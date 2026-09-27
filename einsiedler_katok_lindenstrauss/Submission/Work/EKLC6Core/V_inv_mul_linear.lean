import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLRelCross.flower_balls
import Submission.Work.EKLComp.inv_mem_V

/-!
# `Work.EKLC6Core.V_inv_mul_linear`

The displacement neighbourhood

`V δ = {g : SL₃(ℝ) | ∀ i j, |g i j - 1 i j| < δ}`

is stable under inversion and under the "difference" operation, *linearly* in the radii: there is
a constant `C > 0` with

* `g ∈ V η → g⁻¹ ∈ V (C η)`,
* `g ∈ V η → h ∈ V s → g⁻¹ * h ∈ V (s + C η (1 + s))`

for `0 < η ≤ 1/2` and `s ≥ 0`.  Concretely `C = 30` works:

* `Work.EKLComp.inv_mem_V` gives `g⁻¹ ∈ V (10 η)` (`det g = 1`, so `g⁻¹` is the adjugate of `g`,
  whose entries are `2 × 2` minors of `g`; a minor deviates from its value for the identity by at
  most `4η + 2η² ≤ 5η`, and the code proves the slightly weaker bound `10 η`);
* `Work.EKLRelCross.entries_mul_sub_one_le` gives, for `A = ↑(g⁻¹)` and `B = ↑h`,
  `|(A * B) i j - 1 i j| < 10η + s + 3 * (10η) * s = 10η + s + 30ηs`, and
  `10η + s + 30ηs ≤ s + 30η(1 + s)` because `10 ≤ 30` and `30 ≤ 30`.
-/

namespace Work.EKLC6Core

open Work.EKLContract

theorem V_inv_mul_linear :
    ∃ C : ℝ, 0 < C ∧
      (∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∀ g : Work.EKLContract.SL3,
        g ∈ Work.EKLContract.V η → g⁻¹ ∈ Work.EKLContract.V (C * η)) ∧
      (∀ η s : ℝ, 0 < η → η ≤ 1 / 2 → 0 ≤ s → ∀ g h : Work.EKLContract.SL3,
        g ∈ Work.EKLContract.V η → h ∈ Work.EKLContract.V s →
          g⁻¹ * h ∈ Work.EKLContract.V (s + C * η * (1 + s))) := by
  refine ⟨30, by norm_num, ?_, ?_⟩
  · intro η hη hη2 g hg i j
    have h1 : η ≤ 1 := by linarith
    have h := Work.EKLComp.inv_mem_V hη h1 hg i j
    have h2 : 10 * η < 30 * η := by linarith
    linarith
  · intro η s hη hη2 hs g h hg hh i j
    have h1 : η ≤ 1 := by linarith
    have hginv : g⁻¹ ∈ Work.EKLContract.V (10 * η) := Work.EKLComp.inv_mem_V hη h1 hg
    have h10 : (0 : ℝ) ≤ 10 * η := by linarith
    have hb := Work.EKLRelCross.entries_mul_sub_one_le
      (A := ((g⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ))
      (B := ((h : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j hginv hh h10 hs
    have hcoe : (((g⁻¹ * h) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        = ((g⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
          * ((h : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) :=
      Matrix.SpecialLinearGroup.coe_mul _ _
    have harith : 10 * η + s + 3 * (10 * η) * s ≤ s + 30 * η * (1 + s) := by
      nlinarith [hη]
    show |(((g⁻¹ * h) : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < s + 30 * η * (1 + s)
    rw [hcoe]
    linarith

end Work.EKLC6Core
