import Submission.Work.WilG4c.PolyCombDefs
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4c

open WilkiesDesign
open Work.WilG0 Work.WilG1

namespace PolyComb

/-! ### Coordinate bookkeeping for `sigY` -/

@[simp] theorem sigY_castSucc (m k : ℕ) (i : Fin k) (j : Fin m) :
    sigY m k i (Fin.castSucc j) = Fin.castAdd k (Fin.castSucc j) := by
  simp [sigY]

@[simp] theorem sigY_last (m k : ℕ) (i : Fin k) :
    sigY m k i (Fin.last m) = Fin.natAdd (m + 1) i := by
  simp [sigY]

/-- Pointwise description of the pullback of `graphOf H` along `sigY m k i`. -/
theorem mem_sigY (m k : ℕ) (i : Fin k) (H : (Fin m → ℝ) → ℝ) (z : Fin (m + 1 + k) → ℝ) :
    z ∘ sigY m k i ∈ graphOf H ↔
      z (Fin.natAdd (m + 1) i) = H (fun j : Fin m => z (Fin.castAdd k (Fin.castSucc j))) := by
  simp only [graphOf, Set.mem_ofPred_eq, Function.comp_apply, Fin.init_def, sigY_last,
    sigY_castSucc]

/-! ### Coordinates of `snocIt` -/

theorem snocIt_yIdx (m k : ℕ) (x : Fin (m + 1) → ℝ) (w : Fin k → ℝ) (i : Fin k) :
    snocIt (m + 1) k x w (yIdx m k i) = w i := by
  rw [yIdx, snocIt_natAdd]

theorem snocIt_valIdx (m k : ℕ) (x : Fin (m + 1) → ℝ) (w : Fin k → ℝ) :
    snocIt (m + 1) k x w (valIdx m k) = x (Fin.last m) := by
  rw [valIdx, snocIt_castAdd]

theorem snocIt_xPart (m k : ℕ) (x : Fin (m + 1) → ℝ) (w : Fin k → ℝ) :
    (fun j : Fin m => snocIt (m + 1) k x w (Fin.castAdd k (Fin.castSucc j))) = Fin.init x := by
  funext j
  rw [snocIt_castAdd, Fin.init_def]

theorem snocIt_yPart (m k : ℕ) (x : Fin (m + 1) → ℝ) (w : Fin k → ℝ) :
    (fun i : Fin k => snocIt (m + 1) k x w (yIdx m k i)) = w := by
  funext i
  rw [yIdx, snocIt_natAdd]

/-! ### The polynomial `value - P(y)` -/

theorem eval_combPoly (m k : ℕ) (P : MvPolynomial (Fin k) ℝ) (z : Fin (m + 1 + k) → ℝ) :
    MvPolynomial.eval z (combPoly m k P) =
      z (valIdx m k) - MvPolynomial.eval (fun i : Fin k => z (yIdx m k i)) P := by
  rw [combPoly, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_rename]
  rfl

theorem combPoly_totalDegree_le (m k : ℕ) (P : MvPolynomial (Fin k) ℝ) :
    (combPoly m k P).totalDegree ≤ P.totalDegree + 1 := by
  rw [combPoly]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  rw [max_le_iff]
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.totalDegree_X]; omega
  · exact le_trans (MvPolynomial.totalDegree_rename_le _ _) (by omega)

/-! ### Characterisation of membership in the constructed set -/

/-- Membership of the glued vector `snocIt (m+1) k x w` in
`(⋂ i, pullback of graphOf (H i)) ∩ {value - P(y) = 0}`. -/
theorem snocIt_mem (m k : ℕ) (H : Fin k → (Fin m → ℝ) → ℝ) (P : MvPolynomial (Fin k) ℝ)
    (x : Fin (m + 1) → ℝ) (w : Fin k → ℝ) :
    snocIt (m + 1) k x w ∈
        ((⋂ i : Fin k, {z : Fin (m + 1 + k) → ℝ | z ∘ sigY m k i ∈ graphOf (H i)}) ∩
          {z : Fin (m + 1 + k) → ℝ | MvPolynomial.eval z (combPoly m k P) = 0}) ↔
      (∀ i, w i = H i (Fin.init x)) ∧ x (Fin.last m) = MvPolynomial.eval w P := by
  rw [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Set.mem_ofPred_eq] at h2
    refine ⟨fun i => ?_, ?_⟩
    · have hi := (mem_sigY m k i (H i) (snocIt (m + 1) k x w)).mp (h1 i)
      rw [snocIt_xPart, snocIt_natAdd] at hi
      exact hi
    · rw [eval_combPoly, snocIt_valIdx, snocIt_yPart] at h2
      exact sub_eq_zero.mp h2
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, ?_⟩
    · refine (mem_sigY m k i (H i) (snocIt (m + 1) k x w)).mpr ?_
      rw [snocIt_xPart, snocIt_natAdd]
      exact h1 i
    · simp only [Set.mem_ofPred_eq, eval_combPoly, snocIt_valIdx, snocIt_yPart, h2, sub_self]

/-! ### The projected set is the graph of the polynomial combination -/

theorem mem_graphOf_iff {m : ℕ} (f : (Fin m → ℝ) → ℝ) (z : Fin (m + 1) → ℝ) :
    z ∈ graphOf f ↔ z (Fin.last m) = f (Fin.init z) := Iff.rfl

theorem projLastIter_eq_graph (m k : ℕ) (H : Fin k → (Fin m → ℝ) → ℝ)
    (P : MvPolynomial (Fin k) ℝ) :
    projLastIter (m + 1) k
        ((⋂ i : Fin k, {z : Fin (m + 1 + k) → ℝ | z ∘ sigY m k i ∈ graphOf (H i)}) ∩
          {z : Fin (m + 1 + k) → ℝ | MvPolynomial.eval z (combPoly m k P) = 0})
      = graphOf (fun x : Fin m → ℝ => MvPolynomial.eval (fun i => H i x) P) := by
  rw [projLastIter_eq]
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := hx
    obtain ⟨h1, h2⟩ := (snocIt_mem m k H P x w).mp hw
    rw [mem_graphOf_iff, h2, show w = (fun i : Fin k => H i (Fin.init x)) from funext h1]
  · intro hx
    rw [mem_graphOf_iff] at hx
    exact ⟨fun i => H i (Fin.init x), (snocIt_mem m k H P x _).mpr ⟨fun i => rfl, hx⟩⟩

end PolyComb

end Work.WilG4c
