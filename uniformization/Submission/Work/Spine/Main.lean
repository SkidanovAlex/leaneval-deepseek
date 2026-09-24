import Submission.Work.Spine.Spine

/-!
# `Work.Spine.Main` — the deliverable of the subproject

Two theorems, in namespace `Work.Spine`:

* `isFreeGroup_fundamentalGroup_of_noncompact`: `π₁` of a connected second countable non-compact
  Riemann surface is free (Johansson/Stallings);
* `simplyConnectedSpace_of_subsingleton_hom_toReal`: Hubbard Theorem 1.1.2's topological step — a
  connected non-compact Riemann surface with no non-trivial homomorphism `π₁ → ℝ` is simply
  connected.

Both are immediately reduced (in `Submission/Work/Spine/Spine.lean`) to the single geometric input
`Work.Spine.exists_homotopyEquiv_oneDimCWComplex_of_noncompact` — the spine theorem of
Johansson/Stallings — and to the assembly layer in `Submission/Work/Spine/Basic.lean`.
-/

namespace Work.Spine

/-- **Freeness of `π₁` of a connected non-compact Riemann surface** (Johansson/Stallings).

A connected, second countable, non-compact surface has the homotopy type of a one-dimensional CW
complex, hence its fundamental group is free.  Under the universal-coefficient description
`Hom(π₁ X x, ℝ) = H¹(X;ℝ)`, this is the statement that an open Riemann surface with vanishing first
real cohomology is simply connected (Hubbard, *Teichmüller theory* Vol. 1, Theorem 1.1.2). -/
theorem isFreeGroup_fundamentalGroup_of_noncompact
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x : X) : IsFreeGroup (FundamentalGroup X x) :=
  isFreeGroup_fundamentalGroup_of_noncompact_of_spine hX x

/-- **Hubbard 1.1.2, the topological step.**  If `X` is a connected non-compact Riemann surface and
every homomorphism `π₁(X,x) → ℝ` is trivial, then `X` is simply connected.

*A free group with no non-trivial homomorphism to `ℝ` is trivial*: a free group of rank `≥ 1` has a
generator, and sending that generator to `1 ∈ ℝ` and all other generators to `0` gives a non-trivial
homomorphism.  Combined with Johansson's theorem (freeness of `π₁` of an open surface) this proves
the claim. -/
theorem simplyConnectedSpace_of_subsingleton_hom_toReal
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x : X) [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)] :
    SimplyConnectedSpace X :=
  simplyConnectedSpace_of_subsingleton_hom_toReal_of_spine hX x

end Work.Spine
