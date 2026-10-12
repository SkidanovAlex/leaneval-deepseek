import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixGlue.Wiring.Shift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Wiring.ShiftHam` — translation invariance of the corpus Hamiltonian

`ham_comp_cellShift`: the corpus Hamiltonian `𝓗 N v` (`ChallengeDeps.lean`) is invariant under
the diagonal translation `cellShift N c` — its kinetic part because the second derivative
commutes with translations (`Submission.BoseGases.partialLaplacian_cellShift`), its interaction
part because relative coordinates are unchanged (`Submission.BoseGases.cellShift_sub`).

The two corollaries `abox_sq_eq_box` and `abox_ham_eq_box` are the concrete transport of a
corner-box state to the centred box used by the wiring: for a state supported in `box N L`, the
shifted state `x ↦ Ψ (x + c)` has the same centred-box `L²` norm and the same Hamiltonian
expectation as `Ψ` in the corner box.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Translation invariance of the corpus Hamiltonian**: `𝓗 N v (Ψ ∘ cellShift c) = (𝓗 N v Ψ) ∘ cellShift c`. -/
theorem ham_comp_cellShift {N : ℕ} {v : ℝ³ → ℝ} (c : ℝ³) (Ψ : X N → ℝ) (w : X N) :
    𝓗 N v (fun z : X N => Ψ (cellShift N c z)) w = 𝓗 N v Ψ (cellShift N c w) := by
  rw [𝓗, 𝓗]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      rw [Submission.BoseGases.partialLaplacian_cellShift]
  · refine Finset.sum_congr rfl fun ij _ => ?_
    obtain ⟨i, j⟩ := ij
    simp only [Prod.fst, Prod.snd]
    rw [Submission.BoseGases.cellShift_sub N c w i j]

/-- **The centred-box `L²` norm of the shifted state equals the corner-box norm.** -/
theorem abox_sq_eq_box {N : ℕ} {L : ℝ} (hL : 0 < L) {Ψ : X N → ℝ}
    (hsupp : tsupport Ψ ⊆ box N L) :
    (∫ x in abox N L, ((fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) x) ^ 2)
      = ∫ w in box N L, (Ψ w) ^ 2 := by
  have hF : HasCompactSupport (fun x : X N =>
      ((fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) x) ^ 2) := by
    refine IsCompact.of_isClosed_subset (Submission.BoseGases.abox_compact N hL)
      (isClosed_tsupport _) ?_
    refine subset_trans (closure_mono ?_) (tsupport_shift_neg_cubeC_subset_abox hsupp)
    intro x hx
    exact fun h => hx (by simp [h])
  have h := setIntegral_box_shift_self (N := N) hL
    (fun x : X N => ((fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) x) ^ 2) hF
  simpa [cellShift_neg_cubeC_cubeC] using h.symm

/-- **The centred-box Hamiltonian expectation of the shifted state equals the corner-box one.** -/
theorem abox_ham_eq_box {N : ℕ} {L : ℝ} (hL : 0 < L) {v : ℝ³ → ℝ} {Ψ : X N → ℝ}
    (hsupp : tsupport Ψ ⊆ box N L) :
    (∫ x in abox N L,
        (fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) x
          * 𝓗 N v (fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) x)
      = ∫ w in box N L, Ψ w * 𝓗 N v Ψ w := by
  have hF : HasCompactSupport (fun x : X N =>
      (fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) x
        * 𝓗 N v (fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) x) := by
    refine IsCompact.of_isClosed_subset (Submission.BoseGases.abox_compact N hL)
      (isClosed_tsupport _) ?_
    refine subset_trans (closure_mono ?_) (tsupport_shift_neg_cubeC_subset_abox hsupp)
    intro x hx
    exact fun h => hx (by simp [h])
  have h := setIntegral_box_shift_self (N := N) hL
    (fun x : X N => (fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) x
      * 𝓗 N v (fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) x) hF
  have hpt : ∀ w : X N,
      (fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) (cellShift N (cubeC L) w)
        * 𝓗 N v (fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) (cellShift N (cubeC L) w)
      = Ψ w * 𝓗 N v Ψ w := by
    intro w
    show Ψ (cellShift N (-(cubeC L)) (cellShift N (cubeC L) w))
        * 𝓗 N v (fun z : X N => Ψ (cellShift N (-(cubeC L)) z))
            (cellShift N (cubeC L) w)
      = Ψ w * 𝓗 N v Ψ w
    rw [cellShift_neg_cubeC_cubeC N L w]
    congr 1
    rw [ham_comp_cellShift (c := -(cubeC L)) Ψ (cellShift N (cubeC L) w),
      cellShift_neg_cubeC_cubeC N L w]
  have h2 : (∫ w in box N L,
      (fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) (cellShift N (cubeC L) w)
        * 𝓗 N v (fun z : X N => Ψ (cellShift N (-(cubeC L)) z)) (cellShift N (cubeC L) w))
      = ∫ w in box N L, Ψ w * 𝓗 N v Ψ w :=
    MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.box_measurable N L) (fun w _ => hpt w)
  rw [← h2]
  exact h.symm

end Work.BoseFixGlue
