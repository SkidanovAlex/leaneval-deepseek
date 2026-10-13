import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.API

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG Work.WilG0 Work.WilG1

/-- **Coordinate regrouping of a family of `n` pictures.**

Given `n` families `φ j` on `ℝ^{(p+1)+n} = ℝ^{p} × ℝ × ℝ^{n}` (parameter block of size
`p + 1`, variable block of size `n`), build the new family on `ℝ^{p} × ℝ^{n+1}`
(parameter block of size `p`, variable block of size `n + 1`) whose value at
`(l, z)` is `φ i (l, z 0) (z 1, …, z n)` — i.e. the first coordinate `z 0` of the new
variable block is fed to `φ i` as its *last* parameter, and the remaining coordinates
`z 1, …, z n` are its variables.  The two graphs live in the same ambient space
`ℝ^{p+n+2}` with the same coordinate ordering, so each of the `n + 1` resulting graphs is
`Ω`-definable with format and degree only additively larger.

The `n + 1`-st case (`j = 0`) is the graph of the projection `(l, z) ↦ z 0`, a coordinate
hyperplane; for `j = i.succ` the graph is `famGraph (φ i)` transported along the identity of
`Fin ((p+1)+n+1) = Fin (p+(n+1)+1)`. -/
theorem phiPtCoordGraph (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (a c : ℕ),
      ∀ (F1 D1 : ℕ) (φ : Fin n → (Fin (p + 1) → ℝ) → (Fin n → ℝ) → ℝ),
        (∀ j, WilkiesDesign.CG.famGraph (φ j) ∈ S.Ω F1 D1 ((p + 1) + n + 1)) →
        ∀ j : Fin (n + 1), WilkiesDesign.CG.famGraph
              (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
                Fin.cases (z 0) (fun i : Fin n => φ i (Fin.snoc l (z 0)) (Fin.tail z)) j) ∈
            S.Ω (F1 + a) (D1 + c) (p + (n + 1) + 1) := by
  refine ⟨p + n + 2, 1, ?_⟩
  intro F1 D1 φ hφ j
  refine Fin.cases ?_ ?_ j
  · -- `j = 0`: the graph of the projection `(l, z) ↦ z 0`, a coordinate hyperplane.
    have hset : famGraph (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
          Fin.cases (z 0) (fun i : Fin n => φ i (Fin.snoc l (z 0)) (Fin.tail z)) 0)
        = {w : Fin (p + (n + 1) + 1) → ℝ |
            w (Fin.last (p + (n + 1))) = w (Fin.castSucc (Fin.natAdd p 0))} := by
      ext w
      simp only [famGraph, graphOf, Set.mem_ofPred_eq, Fin.init_def, Fin.cases_zero]
    rw [hset]
    have h := Omega.coordEq_mem (S := S) 0 (Fin.last (p + (n + 1)))
      (Fin.castSucc (Fin.natAdd p 0))
    exact Omega.mono h (by omega) (by simp)
  · -- `j = i.succ`: transport `famGraph (φ i)` along `((p+1)+n+1) = (p+(n+1)+1)`.
    intro i
    have he : (p + 1) + n + 1 = p + (n + 1) + 1 := by omega
    have hset : famGraph (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
          Fin.cases (z 0) (fun i : Fin n => φ i (Fin.snoc l (z 0)) (Fin.tail z)) i.succ)
        = (he ▸ famGraph (φ i)) := by
      ext z
      rw [cast_mem_iff]
      simp only [famGraph, graphOf, Set.mem_ofPred_eq, Fin.cases_succ, Fin.init_def]
      rw [show Fin.last (p + (n + 1)) = Fin.cast he (Fin.last (p + 1 + n)) from by
        apply Fin.ext; simp]
      -- the parameter block: `(z 0, …, z p)` on both sides
      have hA : (Fin.snoc (fun i : Fin p => z (Fin.castAdd (n + 1) i).castSucc)
            (z (Fin.natAdd p 0).castSucc))
          = (fun i : Fin (p + 1) => z (Fin.cast he (Fin.castAdd n i).castSucc)) := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · rw [Fin.snoc_last]
          apply congrArg z; apply Fin.ext; simp
        · intro j
          rw [Fin.snoc_castSucc]
          apply congrArg z; apply Fin.ext; simp
      -- the variable block: `(z 1, …, z n)` on both sides
      have hB : (Fin.tail (fun j : Fin (n + 1) => z (Fin.natAdd p j).castSucc))
          = (fun j : Fin n => z (Fin.cast he (Fin.natAdd (p + 1) j).castSucc)) := by
        funext j
        rw [Fin.tail_def]
        apply congrArg z; apply Fin.ext; simp [Fin.val_cast]; omega
      rw [hA, hB]
    rw [hset]
    exact Omega.mono (Omega_cast he (hφ i)) (by omega) (by omega)

end Work.WilG4c
