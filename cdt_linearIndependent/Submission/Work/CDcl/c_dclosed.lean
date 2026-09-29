import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.Work.CDcl.setup
import Submission.Work.CDcl.invsum
import Submission.Work.CDcl.asm
import Submission.Work.CDcl.x_relation
import Submission.Work.CDcl.easy_relations
import Submission.Work.CDcl.g_ode

/-!
# `Work.CDcl.c_dclosed`: the ℚ(y)-span of the 17 functions is closed under `d/dy`

The 16 "easy" functions are handled by `Work.CDcl.easy_relations`; the derivative of `G'''`
(whose value is `G''''`) is handled by the order-4 ODE `Work.CDcl.g_ode`.
-/

namespace Work.CDcl

open Submission.CDTPlan

theorem c_dclosed (hP : PureFacts) : CDClosed := by
  intro m n ra rb rab r0 hmn
  obtain ⟨q1, A1, hq1, h1⟩ := easy_relations hP m n ra rb rab r0 hmn
  obtain ⟨q2, A2, c2, hq2, h2⟩ :=
    g_ode (2 * (m : ℚ) + 1) (2 * (n : ℚ) + 1) ra rb rab r0
  have hG0eq : GC m n ra rb rab r0
      = G0 (2 * (m : ℚ) + 1) (2 * (n : ℚ) + 1) ra rb rab r0 := by
    show Submission.CDT.sympSym (PC m n ra rb rab r0)
      = Submission.CDT.sympSym (Submission.CDT.logP (2 * (m : ℚ) + 1) (2 * (n : ℚ) + 1)
          ra rb rab r0)
    congr 1
  have hone : seventeen m n ra rb rab r0 0 = (1 : PowerSeries ℚ) := rfl
  have hGk : ∀ k : Fin 4, seventeen m n ra rb rab r0 (idx k)
      = (PowerSeries.derivative (R := ℚ))^[(k : ℕ)]
          (G0 (2 * (m : ℚ) + 1) (2 * (n : ℚ) + 1) ra rb rab r0) := by
    intro k
    fin_cases k <;> rfl
  refine ⟨q1 * q2, mul_ne_zero hq1 hq2, ?_⟩
  refine ⟨fun i j => if i = 8 then q1 * odeRow c2 A2 j else q2 * A1 i j, ?_⟩
  intro i
  dsimp only
  split_ifs with hi8
  · subst hi8
    have hd8 : PowerSeries.derivative (R := ℚ) (seventeen m n ra rb rab r0 8)
        = (PowerSeries.derivative (R := ℚ))^[4]
            (G0 (2 * (m : ℚ) + 1) (2 * (n : ℚ) + 1) ra rb rab r0) := by
      show PowerSeries.derivative (R := ℚ) ((PowerSeries.derivative (R := ℚ))^[3] (GC m n ra rb rab r0)) = _
      rw [hG0eq]
      simp only [Function.iterate_succ_apply']
    -- reduce the RHS to `q1 * (…)`
    rw [show (∑ j : Fin 17,
          ((q1 * odeRow c2 A2 j : Polynomial ℚ) : PowerSeries ℚ)
            * seventeen m n ra rb rab r0 j)
        = (q1 : PowerSeries ℚ) * (∑ j : Fin 17,
            ((odeRow c2 A2 j : Polynomial ℚ) : PowerSeries ℚ)
              * seventeen m n ra rb rab r0 j) by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      push_cast
      ring]
    rw [sum_odeRow]
    rw [hone]
    simp only [hGk]
    rw [show (c2 : PowerSeries ℚ) * 1 + ∑ x : Fin 4, (A2 x : PowerSeries ℚ)
          * (PowerSeries.derivative (R := ℚ))^[(x : ℕ)]
              (G0 (2 * (m : ℚ) + 1) (2 * (n : ℚ) + 1) ra rb rab r0)
        = (∑ x : Fin 4, (A2 x : PowerSeries ℚ)
            * (PowerSeries.derivative (R := ℚ))^[(x : ℕ)]
              (G0 (2 * (m : ℚ) + 1) (2 * (n : ℚ) + 1) ra rb rab r0)) + (c2 : PowerSeries ℚ)
        from by ring]
    rw [← h2]
    rw [hd8]
    push_cast
    ring
  · have hh := h1 i hi8
    rw [show ((q1 * q2 : Polynomial ℚ) : PowerSeries ℚ)
          * PowerSeries.derivative (R := ℚ) (seventeen m n ra rb rab r0 i)
        = (q2 : PowerSeries ℚ) * ((q1 : PowerSeries ℚ)
            * PowerSeries.derivative (R := ℚ) (seventeen m n ra rb rab r0 i)) by
      push_cast
      ring]
    rw [hh]
    rw [show (∑ j : Fin 17, ((q2 * A1 i j : Polynomial ℚ) : PowerSeries ℚ)
          * seventeen m n ra rb rab r0 j)
        = (q2 : PowerSeries ℚ) * (∑ j : Fin 17, ((A1 i j : Polynomial ℚ) : PowerSeries ℚ)
            * seventeen m n ra rb rab r0 j) by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      push_cast
      ring]

end Work.CDcl
