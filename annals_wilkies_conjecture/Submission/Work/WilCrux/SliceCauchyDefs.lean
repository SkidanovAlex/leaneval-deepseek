/-
  WilCrux — vocabulary for the revised step N4b (`SliceDerivJointCont`).

  The proof of the *first* conjunct of N4b runs a Baire argument on the sets

    `sliceCauchySet G j k ε`
      = `{w : ∃ η ∈ (1/(k+1), 1], ∀ z z', 0 ≠ z, ‖z‖ < η, 0 ≠ z',
              ‖z'‖ < η → the fibre partials ∂_{z_j} of `famFun G` at `(w,z)` and `(w,z')`
              both exist and differ by less than `ε`}`.

  These sets are `Ω`-definable with format and degree *independent of `j`, `k` and `ε`*
  (`Work.WilCrux.sliceCauchy_mem`), they cover the open set `Q` pointwise
  (`Work.WilCrux.sliceCauchy_cover`), and the uniform threshold `1/(k+1)` makes the property
  uniform on the interior of the set: this is what turns the Baire step into the *joint*
  statement of N4b.

  Note the deliberate use of the *off-sheet* partial derivative of `famFun G`
  (`Work.WilG4b.dDir` on `Work.WilG4b.c1Loc`) rather than the slice derivative
  `fderiv ℝ (G w) 0`: the value at the sheet `fderiv ℝ (G w) 0 (Pi.single j 1)` is the
  *limit* of the partials as `z → 0`, and is itself not `Ω`-definable.  The two agree on
  `{z ≠ 0}` (`Work.WilCrux.famFun_dDir_append`).
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4c.StepCleanDefs

set_option autoImplicit false
noncomputable section

namespace Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-- The uniform Cauchy set of the `z_j`-partial of a definable family `G`: the parameters `w`
for which the off-sheet partial `∂_{z_j}(famFun G)(w, ·)` has oscillation `< ε` on the
punctured ball of some radius `η ∈ (1/(k+1), 1]`.  The threshold `1/(k+1)` is what makes the
property uniform on the interior of the set. -/
def sliceCauchySet {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (j : Fin b)
    (k : ℕ) (ε : ℝ) : Set (Fin a → ℝ) :=
  {w | ∃ η : ℝ, 1 / ((k : ℝ) + 1) < η ∧ η ≤ 1 ∧
      ∀ (z z' : Fin b → ℝ), z ≠ 0 → ‖z‖ < η → z' ≠ 0 → ‖z'‖ < η →
        Fin.append w z ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun G) ∧
        Fin.append w z' ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun G) ∧
        |Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w z) -
         Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w z')| < ε}

/-- The **good set** at level `ε`: the parameters `w` such that, in a whole neighbourhood of `w`,
the off-sheet partial `∂_{z_j}(famFun G)(w', ·)` is defined (its arguments lie in `c1Loc`) and has
oscillation `< ε` on a punctured ball around `0`.

The `c1Loc` conjuncts are essential: the only `Ω`-atom available for the values of `∂_{z_j}`
(`hder`) is the *derivative graph* `Work.WilG4b.derivGraph`, which pins the value only over
`c1Loc`; off `c1Loc` the total function `Work.WilG4b.dDir` takes junk values that are not
`Ω`-definable.  (Compare `sliceCauchySet`, which carries the same guards.) -/
def goodSet {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (j : Fin b) (ε : ℝ) :
    Set (Fin a → ℝ) :=
  {w | ∃ η > 0, ∀ (w' : Fin a → ℝ) (z z' : Fin b → ℝ),
      dist w' w < η → z ≠ 0 → ‖z‖ < η → z' ≠ 0 → ‖z'‖ < η →
        Fin.append w' z ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun G) ∧
        Fin.append w' z' ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun G) ∧
        |Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w' z) -
         Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w' z')| < ε}

/-- The **failure set** at level `ε`: the complement of `goodSet`.  Explicitly, `w ∈ failSet G j ε`
iff for every `η > 0` there are `w'` with `dist w' w < η` and `z, z'` with
`0 < ‖z‖, ‖z'‖ < η` such that either one of `Fin.append w' z`, `Fin.append w' z'` lies outside
`c1Loc`, or the two partials differ by at least `ε`.  (This is the form in which the `Ω`-calculus
produces it: the negation of the `∃ y y'`-description of the "difference `< ε`" condition.) -/
def failSet {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (j : Fin b) (ε : ℝ) :
    Set (Fin a → ℝ) :=
  (goodSet G j ε)ᶜ

/-- A point at which `f` is `C¹` lies in the interior of its `C¹`-locus `c1Loc f`. -/
theorem mem_c1Loc_of_contDiffAt {m : ℕ} {f : (Fin m → ℝ) → ℝ} {x : Fin m → ℝ}
    (h : ContDiffAt ℝ 1 f x) : x ∈ Work.WilG4b.c1Loc f := by
  rw [Work.WilG4b.c1Loc]
  obtain ⟨u, hu, hcu⟩ := h.contDiffOn (m := ((1 : ℕ) : WithTop ℕ∞)) le_rfl (by simp)
  have hxint : x ∈ interior u := mem_interior_iff_mem_nhds.mpr hu
  have hsub : interior u ⊆ {y : Fin m → ℝ | ContDiffAt ℝ 1 f y} := by
    intro y hy
    exact hcu.contDiffAt (mem_interior_iff_mem_nhds.mp hy)
  exact interior_maximal hsub isOpen_interior hxint

end Work.WilCrux
