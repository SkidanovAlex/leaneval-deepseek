import Mathlib
import Submission.Work.WilG4c.StepCleanDefs

/-!
# `contDiffAt_of_mem_cell_disjoint_badLoc`

If a set `κ ⊆ ℝ^{p+(n+1)}` is disjoint from the bad locus `badLoc (F i) r` of the `i`-th
family member, then every point `Fin.append l x` of `κ` is a `C^r` point of `famFun (F i)`,
hence — reading `famFun (F i)` as `F i` on `ℝ^p × ℝ^{n+1}` — the slice `y ↦ F i l y` is `C^r`
at `x`.

The only content is the reparametrisation `y ↦ Fin.append l y`, which is a smooth (indeed
affine) map of `ℝ^{n+1}` into `ℝ^{p+(n+1)}`.
-/

namespace Work.WilG4c

/-- The slice `y ↦ Fin.append l y` of `ℝ^{p+(n+1)}` (parameters first, then the `n+1` fibre
coordinates) is smooth: each of its components is either a constant or a projection. -/
theorem contDiffAt_finAppend {p n : ℕ} (l : Fin p → ℝ) (x : Fin (n + 1) → ℝ) (k : ℕ) :
    ContDiffAt ℝ k (fun y : Fin (n + 1) → ℝ => (Fin.append l y : Fin (p + (n + 1)) → ℝ)) x := by
  rw [contDiffAt_pi]
  intro s
  refine Fin.addCases (fun i => ?_) (fun j => ?_) s
  · simp only [Fin.append_left]
    exact contDiffAt_const
  · simp only [Fin.append_right]
    exact contDiffAt_apply ℝ ℝ j x

/-- Reading the family member `f` as the function `famFun f` on `ℝ^{p+(n+1)}`, its value at
the point `Fin.append l y` with parameters `l` and fibre coordinates `y` is `f l y`. -/
theorem famFun_finAppend {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (y : Fin (n + 1) → ℝ) :
    famFun f (Fin.append l y) = f l y := by
  simp [famFun, Fin.append_left, Fin.append_right]

theorem contDiffAt_of_mem_cell_disjoint_badLoc {p n r k : ℕ}
    (F : Fin k → (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (κ : Set (Fin (p + (n + 1)) → ℝ)) (i : Fin k)
    (hdisj : Disjoint κ (Work.WilG4c.badLoc (F i) r))
    {l : Fin p → ℝ} {x : Fin (n + 1) → ℝ} (h : Fin.append l x ∈ κ) :
    ContDiffAt ℝ r (F i l) x := by
  -- A point of `κ` lies in the complement of the bad locus, i.e. in the interior of the
  -- `C^r`-locus of `famFun (F i)`, hence is a `C^r` point of `famFun (F i)`.
  have hz : Fin.append l x ∉ badLoc (F i) r := Set.disjoint_left.mp hdisj h
  have hg : ContDiffAt ℝ r (famFun (F i)) (Fin.append l x) := by
    have hmem : Fin.append l x ∈
        interior {z | ContDiffAt ℝ r (famFun (F i)) z} := by
      simpa [badLoc, cLoc] using hz
    exact interior_subset hmem
  -- The slice `y ↦ Fin.append l y` is smooth, so composing gives the `C^r`-ness of the
  -- unrestricted function `y ↦ F i l y`.
  have hcomp : ContDiffAt ℝ r
      (famFun (F i) ∘ fun y : Fin (n + 1) → ℝ =>
        (Fin.append l y : Fin (p + (n + 1)) → ℝ)) x :=
    hg.comp x (contDiffAt_finAppend l x r)
  have hfun : (famFun (F i) ∘ fun y : Fin (n + 1) → ℝ =>
        (Fin.append l y : Fin (p + (n + 1)) → ℝ)) = F i l :=
    funext fun y => famFun_finAppend (F i) l y
  exact hfun ▸ hcomp

end Work.WilG4c
