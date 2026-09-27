import Mathlib
import Submission.Work.EKLComp.ErgMax.USCDefs
import Submission.Work.EKLComp.ErgMax.USC_finite
import Submission.Work.EKLComp.USC_limsup
import Submission.Work.EKLComp.prop92

/-!
# C4c — assembly of `P_USC'` from EKL Prop 9.2

`P_USC'` is the conjunction of the two clauses `P_USC'_finite` (clause (i)) and
`Work.EKLComp.USC_limsup` (clause (ii)), both of which consume only the single fact
`AtomSmallEntropy` (EKL Prop 9.2).  The latter is proved elsewhere as `Work.EKLComp.prop92`
(EKL §9, Prop 9.2: an `AtomSmall` partition computes the entropy of every invariant
probability carried by `K`).
-/

namespace Work.EKLComp.ErgMax

open Work.EKLContract

noncomputable section

theorem P_USC'_of_atomSmall
    (h : ∀ (t : Fin 3 → ℝ), (∃ i j : Fin 3, t i ≠ t j) → ∀ (K : Set X3), IsCompact K →
      (∀ x ∈ K, aDiag t • x ∈ K) → AtomSmallEntropy t K) : P_USC' := by
  intro t ht K hK hfwd
  exact ⟨P_USC'_finite h t ht K hK hfwd, Work.EKLComp.USC_limsup h t ht K hK hfwd⟩

/-- `P_USC'` (the corrected form of the frozen `P_USC`, with the necessary non-degeneracy
hypothesis on `t`), from EKL Prop 9.2. -/
theorem P_USC'_proof : P_USC' :=
  P_USC'_of_atomSmall fun t ht K hK hfwd => Work.EKLComp.prop92 t ht K hK hfwd

end

end Work.EKLComp.ErgMax
