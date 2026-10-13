/-
# `Work.FTS.PhiStar.FlatWAux.QmDeriv.Basic` — elementary facts for the `Qm` bounds

Support module for `QmDerivBound`: nonnegativity of the `famC` coefficients of the
trigonometric form of the Gegenbauer polynomial, the cast normalisation of `2m+1`, and the
identification of `Qm m` on the open interval with `gC (2m+1) (sin θ)/(2 sin θ)`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.FamLopAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

open Set Filter MeasureTheory

lemma famC_nonneg (k : ℤ) : 0 ≤ Work.FTS.PhiStar.famC k := by
  unfold Work.FTS.PhiStar.famC
  split_ifs with h
  · apply div_nonneg
    · refine Finset.prod_nonneg (fun i _ => ?_)
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    · exact Nat.cast_nonneg _
  · exact le_refl 0

lemma cast_two_mul_add_one (m : ℕ) : (((2 * m + 1 : ℕ) : ℝ)) = 2 * (m : ℝ) + 1 := by
  push_cast
  ring

theorem Qm_eq {m : ℕ} {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    Qm m θ = Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) / (2 * Real.sin θ) := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  rw [Qm, Work.FTS.PhiStar.Gegenbauer.eFam, Work.Construction.s2_eq, Real.sin_two_mul]
  field_simp

end Work.FTS.PhiStar.FlatWAux
