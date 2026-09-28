import Mathlib
import Submission.Work.Stems.homotopyGroup_loop

/-!
# Triviality of the low homotopy groups of a loop space

If `π_i (X, pt)` is trivial for every `i ≤ N` with `i ≠ d` (where `2 ≤ d ≤ N`), then
`π_i (Ω X, Path.refl pt)` is trivial for every `i ≤ N - 1` with `i ≠ d - 1`.

This is the loop-space shift `π_{i+1} (X, pt) ≃ π_i (Ω X, Path.refl pt)`
(`Work.Stems.curryEquivGroup`, available for *every* `i : ℕ`, including `i = 0`) applied to the
hypothesis at the shifted index `i + 1`; the two numerical side conditions `i + 1 ≤ N` and
`i + 1 ≠ d` follow from `i ≤ N - 1`, `i ≠ d - 1` and `2 ≤ d`, and a surjection out of a
subsingleton has subsingleton target.
-/

namespace Work.Stems.RankOne

open scoped Topology Topology.Homotopy unitInterval

theorem loop_pi_subsingleton {X : Type} [TopologicalSpace X] (pt : X) {N d : ℕ}
    (hd : 2 ≤ d) (hdN : d ≤ N)
    (h : ∀ i : ℕ, i ≤ N → i ≠ d → Subsingleton (HomotopyGroup (Fin i) X pt)) :
    ∀ i : ℕ, i ≤ N - 1 → i ≠ d - 1 →
      Subsingleton (HomotopyGroup (Fin i) (Path pt pt) (Path.refl pt)) := by
  intro i hi hne
  have hsub : Subsingleton (HomotopyGroup (Fin (i + 1)) X pt) :=
    h (i + 1) (by omega) (by omega)
  exact @Function.Surjective.subsingleton _ _ (Work.Stems.curryEquivGroup (X := X) (x := pt) i)
    hsub (Work.Stems.curryEquivGroup (X := X) (x := pt) i).surjective

end Work.Stems.RankOne
