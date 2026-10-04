import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.StemsB.sphSimplyConnected

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
Part of area C (owner H4). ROUTE (pure topology).
- G is a local homeomorphism. M is compact, so G is proper and closed; its image is open and closed, so G is surjective (the sphere is connected).
- A proper local homeomorphism onto a Hausdorff, locally connected space is a covering map. Search Mathlib for `IsCoveringMap` and
  `IsLocalHomeomorph`; prove the finite-fibre version directly if needed.
- The sphere is SIMPLY CONNECTED: Submission.Work.StemsB.sphSimplyConnected (n) (hn : 2 ≤ n), copied from our pi_sphere library.
  Import Submission.Work.StemsB.sphSimplyConnected. SphereD E is `sphere 0 1` in EuclideanSpace ℝ (Fin (finrank ℝ E + 1)).
- A covering of a simply connected base by a path-connected space is injective (path lifting and uniqueness of lifts; Mathlib has
  lifting for covering maps: IsCoveringMap.liftPath / monodromy).
- Bijective + local diffeomorphism gives a Diffeomorph (Mathlib IsLocalDiffeomorph, diffeomorphOfBijective or equivalent).

OUTCOME.  The route above goes through verbatim, and all the library facts it needs are in this pin of
Mathlib:

* `isLocalHomeomorph_iff_isCoveringMap` ("a local homeomorphism from a compact Hausdorff space to a
  Hausdorff space is a covering map") turns `IsLocalDiffeomorph` into `IsCoveringMap` with no work.
* `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` (homotopy lifting) plus
  `IsCoveringMap.eq_liftPath_iff'` and `IsCoveringMap.liftPath_const` give injectivity: the lemma
  `cover_injective` below, stated for an arbitrary covering map.
* `IsLocalDiffeomorph.diffeomorphOfBijective` assembles the diffeomorphism.

Nothing here is specific to the dimension or to the Ricci-flow side of the project; the only
`hdim`-dependent input is `Work.StemsB.sphSimplyConnected` for the (simply connected, hence
preconnected) sphere of dimension `≥ 2`.
-/

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Work.Diff.C
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

/-- **A covering map over a simply connected base whose total space is path connected is
injective.**  If `p x = p y`, join `x` to `y` by a path `Γ`; its projection is a loop at `p x`,
hence homotopic rel `{0,1}` to the constant loop because the base is simply connected; homotopy
lifting (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`) then makes `Γ` end where the lift
of the constant path ends, i.e. at `x`. -/
theorem cover_injective
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
    (cov : IsCoveringMap p) [SimplyConnectedSpace X] [PathConnectedSpace E] :
    Function.Injective p := by
  intro x y h
  let Γ : Path x y := PathConnectedSpace.somePath x y
  -- the constant path at `p x`, regarded as a path from `p x` to `p y` via `h`
  let c : Path (p x) (p y) := ⟨ContinuousMap.const unitInterval (p x), rfl, h⟩
  -- `Γ.map p` and `c` are homotopic rel `{0,1}` because the base is simply connected
  have hrel : ContinuousMap.HomotopicRel (Γ.map cov.continuous).toContinuousMap
      c.toContinuousMap {0, 1} :=
    SimplyConnectedSpace.paths_homotopic (Γ.map cov.continuous) c
  -- homotopy lifting: the two lifted endpoints agree
  have key := cov.liftPath_apply_one_eq_of_homotopicRel hrel x
    ((Γ.map cov.continuous).source) rfl
  -- the lift of `Γ.map p` starting at `x` is `Γ` itself
  have hL : Γ.toContinuousMap = cov.liftPath (Γ.map cov.continuous).toContinuousMap x
      (Γ.map cov.continuous).source := by
    refine (cov.eq_liftPath_iff' ((Γ.map cov.continuous).source)).mpr ⟨?_, Γ.source⟩
    ext t
    rfl
  have hval : cov.liftPath (Γ.map cov.continuous).toContinuousMap x
      (Γ.map cov.continuous).source 1 = Γ 1 := by
    rw [← hL]
    rfl
  -- the lift of the constant path starting at `x` is the constant path at `x`
  have hR : cov.liftPath c.toContinuousMap x rfl 1 = x := by
    have hc : cov.liftPath c.toContinuousMap x rfl = ContinuousMap.const unitInterval x :=
      cov.liftPath_const (e := x) (x := p x) rfl
    rw [hc]
    rfl
  have hone : Γ 1 = x := by rw [← hval, key, hR]
  rw [← hone, Γ.target]

theorem diffeo_of_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    {G : M → SphereD E} (hG : IsLocalDiffeomorph I (𝓡 (Module.finrank ℝ E)) ∞ G) :
    Nonempty (M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯ SphereD E) := by
  -- the sphere `S^{finrank ℝ E}` is simply connected (hence preconnected) since `finrank ℝ E ≥ 2`
  haveI : SimplyConnectedSpace (SphereD E) :=
    Work.StemsB.sphSimplyConnected (Module.finrank ℝ E) hdim
  -- a local homeomorphism from the compact `M` to the Hausdorff sphere is a covering map
  have hcov : IsCoveringMap G := by
    rw [← isLocalHomeomorph_iff_isCoveringMap]
    exact hG.isLocalHomeomorph
  -- injectivity: covering map over a simply connected base, path-connected total space
  have hinj : Function.Injective G := cover_injective hcov
  -- surjectivity: the image is open and closed and the sphere is preconnected
  have hsurj : Function.Surjective G := by
    have hopen : IsOpen (range G) := hG.isOpen_range
    have hclosed : IsClosed (range G) := (isCompact_range hG.isLocalHomeomorph.continuous).isClosed
    have hne : (range G).Nonempty :=
      ⟨G (Classical.choice (inferInstance : Nonempty M)), mem_range_self _⟩
    have hall : range G = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
    intro y
    exact mem_range.mp (hall ▸ mem_univ y)
  -- a bijective local diffeomorphism is a diffeomorphism
  exact ⟨hG.diffeomorphOfBijective ⟨hinj, hsurj⟩⟩

end Work.Diff.C
