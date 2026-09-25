import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
import Submission.NK.Ramification.herbrandInv_le_iff

namespace NK.Ramification

/-- The upper-numbered ramification filtration `v ↦ G^v = G_{ψ(v)}` is antitone: a larger upper
index gives a smaller subgroup.  This follows from the fact that `ψ` is the upper adjoint of the
Herbrand function `φ` (`herbrandInv_le_iff`) and hence is monotone, together with the antitonicity
of the lower-numbered filtration. -/
theorem upperRamificationSubgroup_antitone {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)] :
    Antitone (NK.Ramification.upperRamificationSubgroup (K := K) A) := by
  intro v w hvw
  -- `ψ` is monotone: `ψ v ≤ ψ w`.
  have hψ : NK.Ramification.herbrandInv (K := K) A v ≤
      NK.Ramification.herbrandInv (K := K) A w := by
    rw [NK.Ramification.herbrandInv_le_iff]
    -- `w ≤ φ (ψ w)` because `ψ w` is the least index with `w ≤ φ (·)`.
    have hw : (w : ℚ) ≤ NK.Ramification.herbrand (K := K) A
        (NK.Ramification.herbrandInv (K := K) A w) :=
      (NK.Ramification.herbrandInv_le_iff (K := K) A w _).mp le_rfl
    exact le_trans (by exact_mod_cast hvw) hw
  -- The lower-numbered filtration is antitone.
  show NK.Ramification.ramificationSubgroup (K := K) A
        (NK.Ramification.herbrandInv (K := K) A w) ≤
      NK.Ramification.ramificationSubgroup (K := K) A
        (NK.Ramification.herbrandInv (K := K) A v)
  exact NK.Ramification.ramificationSubgroup_antitone A hψ

end NK.Ramification
