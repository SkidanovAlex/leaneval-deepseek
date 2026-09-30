import Mathlib
import Submission.Work.Aspherical.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology unitInterval

set_option linter.style.haveILetI false

namespace Work.Aspherical

/-- The boundary of `I^k` (`k ≥ 2`) is path connected: every boundary point can be joined,
inside the boundary, to the origin corner `0`. -/
theorem cube_boundary_joined_zero (k : ℕ) (hk : 2 ≤ k) {y : I^Fin k}
    (hy : y ∈ Cube.boundary (Fin k)) :
    JoinedIn (Cube.boundary (Fin k)) y (0 : I^Fin k) := by
  obtain ⟨i, hi⟩ := hy
  haveI : Nontrivial (Fin k) := by
    have : k.AtLeastTwo := ⟨hk⟩
    infer_instance
  -- Step 1: keep coordinate `i` fixed (it lies in `{0,1}`) and move all other
  -- coordinates to `0`.
  have h1 : JoinedIn (Cube.boundary (Fin k)) y (fun j => if j = i then y i else 0) :=
    JoinedIn.mono
      (JoinedIn.pi (s := fun j : Fin k => if j = i then ({y i} : Set I) else Set.univ)
        (by
          intro j
          by_cases hj : j = i
          · subst hj
            simp only [ite_true]
            exact JoinedIn.refl (Set.mem_singleton _)
          · simp only [ite_eq_right hj]
            exact joinedIn_univ.mpr (PathConnectedSpace.joined (y j) (0 : I))))
      (by
        intro x hx
        rw [Set.mem_univ_pi] at hx
        refine ⟨i, ?_⟩
        have hxi : x i = y i := by
          have := hx i
          simp only [ite_true, Set.mem_singleton_iff] at this
          exact this
        rw [hxi]
        exact hi)
  -- Step 2: now coordinate `i` is the only possibly nonzero one; use a second
  -- coordinate `l ≠ i` (which is constantly `0`) to witness the boundary while
  -- moving coordinate `i` from `y i` to `0`.
  have h2 : JoinedIn (Cube.boundary (Fin k)) (fun j => if j = i then y i else 0)
      (0 : I^Fin k) := by
    obtain ⟨l, hl⟩ := exists_ne i
    exact JoinedIn.mono
      (JoinedIn.pi (s := fun j : Fin k => if j = l then ({0} : Set I) else Set.univ)
        (by
          intro j
          by_cases hj : j = l
          · subst hj
            simp only [ite_true]
            rw [ite_eq_right hl]
            exact JoinedIn.refl (Set.mem_singleton _)
          · simp only [ite_eq_right hj]
            exact joinedIn_univ.mpr
              (PathConnectedSpace.joined ((fun j => if j = i then y i else 0) j) (0 : I))))
      (by
        intro x hx
        rw [Set.mem_univ_pi] at hx
        refine ⟨l, ?_⟩
        have hxl : x l = 0 := by
          have := hx l
          simp only [ite_true, Set.mem_singleton_iff] at this
          exact this
        exact Or.inl hxl)
  exact h1.trans h2

/-- Any two points of the boundary of the `k`-cube `I^k` (`k ≥ 2`) can be joined by a path
staying inside the boundary. (Here `I^k = (Fin k → ↥(Set.Icc 0 1))` and `Cube.boundary (Fin k)`
is the set of points with some coordinate equal to `0` or `1`.) -/
theorem cube_joinedIn_boundary (k : ℕ) (hk : 2 ≤ k) {y y' : Fin k → ↥(Set.Icc (0:ℝ) 1)}
    (hy : y ∈ Cube.boundary (Fin k)) (hy' : y' ∈ Cube.boundary (Fin k)) :
    JoinedIn (Cube.boundary (Fin k)) y y' := by
  exact (cube_boundary_joined_zero k hk hy).trans (cube_boundary_joined_zero k hk hy').symm

end Work.Aspherical
