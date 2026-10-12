import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Ring.Lemmas
import Submission.Work.BoseBoxFock.LatticeBoxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open Finset

noncomputable section

/-- The canonical coercion `ℕ → ℝ≥0` commutes with finite suprema. -/
lemma nnreal_sup_cast_nat (n : Fin 3 → ℕ) :
    ((Finset.univ.sup n : ℕ) : NNReal) = Finset.univ.sup fun i => ((n i : ℕ) : NNReal) := by
  apply le_antisymm
  · obtain ⟨b, -, hb⟩ :=
      Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3)) ⟨0, Finset.mem_univ 0⟩ n
    rw [hb]
    exact Finset.le_sup (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i => ((n i : ℕ) : NNReal)) (Finset.mem_univ b)
  · rw [Finset.sup_le_iff]
    intro b _
    exact_mod_cast Finset.le_sup (s := (Finset.univ : Finset (Fin 3))) (f := n) (Finset.mem_univ b)

/-- The `ℤ`-norm of an integer is the cast of its `natAbs` (`NNReal.natCast_natAbs`), so the
Pi-norm of `m : Fin 3 → ℤ` is the cast of the sup-norm `K m`. -/
theorem NormEqKcast (m : Fin 3 → ℤ) : ‖m‖ = ((K m : ℕ) : ℝ) := by
  rw [Pi.norm_def]
  have h1 : (Finset.univ.sup fun b : Fin 3 => ‖m b‖₊) =
      (Finset.univ.sup fun b : Fin 3 => (((m b).natAbs : ℕ) : NNReal)) :=
    Finset.sup_congr rfl fun b _ => (NNReal.natCast_natAbs (m b)).symm
  rw [h1, ← nnreal_sup_cast_nat (fun b : Fin 3 => (m b).natAbs)]
  simp only [NNReal.coe_natCast]
  rfl

end

end Work.BoseBoxFock
