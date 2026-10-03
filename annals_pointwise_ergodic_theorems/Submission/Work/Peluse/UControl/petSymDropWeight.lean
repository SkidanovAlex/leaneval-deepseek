import Mathlib
import Submission.Work.Peluse.UControl.PetStateSym

/-!
# Dropping the constant slots from a symbolic PET state

`PetStateSym.dropSym S J` is the symbolic state obtained from `S` by discarding the slots indexed by
the finset `J` (the slots that are absorbed into the base function at a PET step).  Its index type is
the subtype `{i : S.ι // i ∈ Jᶜ}` and its slot polynomials are the restrictions of those of `S`.

`petSymDropWeight` says that the weight vector of `S` does not change when the dropped slots are
constant: `weight` reads off the number of *distinct leading coefficients* among the slots of a
given degree `j`, and the constant slots of `J` (which is what the hypothesis `hJ` says) have degree
`0`, so they contribute nothing to the coordinate `j ≥ 1`.  Note that the hypothesis `hj : 1 ≤ j` is
essential: the coordinate `j = 0` *does* change, since every constant slot of `J` carries a leading
coefficient that survives in `S` but not in `dropSym S J`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable def PetStateSym.dropSym {k : ℕ} (S : Work.Peluse.UControl.PetStep.PetStateSym k) (J : Finset S.ι) :
    Work.Peluse.UControl.PetStep.PetStateSym k where
  ι := {i : S.ι // i ∈ Jᶜ}
  finι := inferInstance
  decι := inferInstance
  P := fun i => S.P i.1

theorem petSymDropWeight {k d : ℕ} (S : Work.Peluse.UControl.PetStep.PetStateSym k) (J : Finset S.ι)
    (hJ : ∀ i ∈ J, (S.P i).natDegree = 0) {j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d) :
    ((PetStateSym.dropSym S J).weight d) ⟨j, Nat.lt_succ_of_le hjd⟩
      = (S.weight d) ⟨j, Nat.lt_succ_of_le hjd⟩ := by
  show (((Finset.univ : Finset {i : S.ι // i ∈ Jᶜ}).filter
      (fun i => (S.P i.1).natDegree = (⟨j, Nat.lt_succ_of_le hjd⟩ : Fin (d + 1)))).image
      (fun i => (S.P i.1).leadingCoeff)).card
    = (((Finset.univ : Finset S.ι).filter
      (fun i => (S.P i).natDegree = (⟨j, Nat.lt_succ_of_le hjd⟩ : Fin (d + 1)))).image
      (fun i => (S.P i).leadingCoeff)).card
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hid, hix⟩
    exact ⟨i.1, hid, hix⟩
  · rintro ⟨i, hid, hix⟩
    have hi : i ∈ Jᶜ := by
      simp only [Finset.mem_compl]
      intro hmem
      have h0 := hJ i hmem
      omega
    exact ⟨⟨i, hi⟩, hid, hix⟩

end Work.Peluse.UControl
