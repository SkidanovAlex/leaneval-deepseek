import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Chart.chartRes_cover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.Chart

universe u

open scoped AlgebraicGeometry

/-- **An invariant basic open between a point and an invariant open inside an affine chart.**

If `U` is a `Γ`-invariant affine open of `X`, `W ≤ U` a `Γ`-invariant open and `y ∈ W`, then there
is a `Γ`-invariant section `s` over `U` whose basic open is a `Γ`-invariant open neighbourhood of
`y` contained in `W`.

The proof picks a section `f` over `U` whose basic open is contained in `W` and contains the whole
`Γ`-orbit of `y` (this exists by prime avoidance, `sections_basicOpen_finset`), and then takes the
norm `∏ g • f` of `f` (`invariantSection_orbit`), which is fixed by `Γ`, does not vanish at `y`
and vanishes at least where `f` does. -/
theorem exists_basicOpen_invariant_sub {Γ : Type u} [Group Γ] [Fintype Γ] {X : AlgebraicGeometry.Scheme.{u}}
    (A : Work.SymQuot.GAction Γ X) {U : X.Opens} (hUa : AlgebraicGeometry.IsAffineOpen U)
    (hUi : A.IsInvariantOpen U) {W : X.Opens} (hWi : A.IsInvariantOpen W) (hWU : W ≤ U)
    {y : X} (hy : y ∈ W) :
    ∃ s : ↥(Work.SymQuot.GAction.invariants A U hUi),
      y ∈ X.basicOpen (s : Γ(X, U)) ∧ X.basicOpen (s : Γ(X, U)) ≤ W := by
  classical
  have hyU : y ∈ U := hWU hy
  -- The orbit of `y` is contained in the invariant open `W`.
  set S : Finset X := Finset.univ.image (fun g : Γ => A.hom g y) with hSdef
  have hS : ∀ s ∈ S, s ∈ W := by
    intro s hs
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hs
    exact hWi.smul_mem hy g
  -- A section over `U` whose basic open lies in `W` and contains the orbit of `y`.
  obtain ⟨f, hfW, hfS⟩ := sections_basicOpen_finset hUa hWU S hS
  -- Its norm is a fixed section over `U` with the same properties at `y`.
  obtain ⟨h, hh, hhf, hyh⟩ := invariantSection_orbit A hUi ⟨y, hyU⟩ f
    (fun g => hfS _ (Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩))
  refine ⟨⟨h, ?_⟩, ?_, ?_⟩
  · rw [Work.SymQuot.GAction.mem_invariants_iff]
    intro g
    exact hh g⁻¹
  · exact hyh
  · exact hhf.trans hfW

end Work.SymQuot.Chart
