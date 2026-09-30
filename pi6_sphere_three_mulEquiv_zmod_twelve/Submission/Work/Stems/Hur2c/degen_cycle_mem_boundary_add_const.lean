import Mathlib
import Submission.Work.Stems.Hur2c.degen_cycle_degen_boundary

namespace Work.Stems.Hur2c

open Work.Stems.Cubical

/-- **A degenerate `(k+1)`-cycle is a boundary modulo the constant cube.**

This is the chain-level statement needed to see that `ΨLin` (Hutchings' linearised filling) kills
degenerate `(k+1)`-cycles, for a space whose homotopy groups vanish in degrees `1, …, k`.

The proof uses the *degeneracy-compatible* filling tower of
`Work.RatHurewicz.DCTower` (`Submission/Work/RatHurewicz/DCTowerDefs.lean`): the filling of a
degenerate cube is again degenerate, so the `(k+1)`-cycle `d` and the constant correction
`aug d • const` differ by the boundary of a *degenerate* `(k+2)`-chain
(`Work.Stems.Hur2c.degen_cycle_mem_range_degen`).  The missing vanishing of `π_{k+1}(X, x₀)` — which
the plain chain contraction of the tower identity would need — is replaced by the degeneracy of
`d`. -/
theorem degen_cycle_mem_boundary_add_const (k : ℕ) (X : Type) [TopologicalSpace X] (x₀ : X)
    (hk : 1 ≤ k)
    (hpc : PathConnectedSpace X)
    (hconn : ∀ i : ℕ, 1 ≤ i → i ≤ k → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (d : Work.Stems.Cubical.Cub (k + 1) X)
    (hd : d ∈ Work.RatHurewicz.Deg (k + 1) X)
    (hcyc : Work.Stems.Cubical.cubD k X d = 0) :
    d ∈ LinearMap.range (Work.Stems.Cubical.cubD (k + 1) X) ⊔
      Work.RatHurewicz.ConstChain (k + 1) X x₀ := by
  -- the connectivity hypothesis of the décalage, including `π₀` from path connectedness
  have hconn' : ∀ i : ℕ, i ≤ k → Subsingleton (HomotopyGroup (Fin i) X x₀) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have hsub : Subsingleton (ZerothHomotopy X) :=
        (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
      haveI := hsub
      exact (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).injective.subsingleton
    · exact hconn i hpos hi
  obtain ⟨D, _hDmem, hDbd⟩ := degen_cycle_mem_range_degen k x₀ hconn' d hd hcyc
  -- `cubD (k+1) X D = aug d • const - d`
  have hD : d = Work.RatHurewicz.aug (X := X) (k + 1) d •
        Finsupp.single (Work.RatHurewicz.cconst (k + 1) x₀) (1 : ℤ)
      - Work.Stems.Cubical.cubD (k + 1) X D := by
    rw [hDbd]
    abel
  rw [hD]
  refine Submodule.sub_mem _
    (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left ⟨D, rfl⟩)
  rw [Work.RatHurewicz.ConstChain]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

end Work.Stems.Hur2c
