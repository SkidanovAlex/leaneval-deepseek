import Mathlib
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.puncturedBallSphere
import Submission.Work.Cohomology.ballPairHomologyTopOne

set_option synthInstance.maxHeartbeats 400000

/-!
# The relative homology of a punctured open ball

For `n ≥ 1`, a point `y` of `EuclideanSpace ℝ (Fin n)` and `r > 0`, the `n`-th relative singular
homology (with `ℤ` coefficients) of the pair consisting of the open ball `Metric.ball y r` and its
complement of `{y}` is `ℤ`:

`Hₙ(B, B ∖ {y}; ℤ) ≅ ℤ`.

This is the local homology of an `n`-manifold at a point, in the flat model.

## Structure of the proof

The long exact sequence of the pair `(B, B ∖ {y})`

`Hₙ(B) ⟶ Hₙ(B, B ∖ {y}) --δ--> Hₙ₋₁(B ∖ {y}) ⟶ Hₙ₋₁(B)`

computes the group, because `B` is convex, hence contractible
(`Work.Cohomology.homologyContractible` kills its positive-degree homology), so that `δ` is an
isomorphism (`Work.Cohomology.hPairδ_isIso`, the trick of
`Submission/Work/Cohomology/diskPairHomologyTop.lean`).  The complement `B ∖ {y}` deformation
retracts onto the unit sphere `Sⁿ⁻¹ ⊆ ℝⁿ` (`Work.Cohomology.puncturedBallSphere`), so
`Hₙ₋₁(B ∖ {y}) ≅ Hₙ₋₁(Sⁿ⁻¹) ≅ ℤ` by `Work.Cohomology.sphereHomologyTop` and
`Work.Cohomology.homologyIso_of_homotopyEquiv`.

For `n = 1` the long exact sequence stops at `H₀`, and the same argument computes the reduced
`H₀` of the two point space `S⁰`; this is `Work.Cohomology.ballPairHomologyTopOne`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Metric

namespace Work.Cohomology

noncomputable section

/-! ## The two ingredients of the computation -/

/-- The open ball `Metric.ball y r` is contractible (`r > 0`): it is a nonempty convex subset of
the Euclidean space. -/
theorem ball_contractible (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    ContractibleSpace (TopCat.of (Metric.ball y r)) := by
  show ContractibleSpace ↥(Metric.ball y r)
  exact Convex.contractibleSpace (convex_ball y r) ⟨y, Metric.mem_ball_self hr⟩

/-- **The top relative homology of the punctured open ball, `n ≥ 2`.**

Here the long exact sequence of the pair has two vanishing terms `Hₙ(B) = Hₙ₋₁(B) = 0`, so the
connecting map `δ : Hₙ(B, B∖{y}) ⟶ Hₙ₋₁(B∖{y})` is an isomorphism, and the punctured ball is
homotopy equivalent to `Sⁿ⁻¹` (`Work.Cohomology.puncturedBallSphere`), whose `(n-1)`-st homology
is `ℤ` (`Work.Cohomology.sphereHomologyTop`). -/
theorem ballPairHomologyTopGeTwo (n : ℕ) (hn : 2 ≤ n) (y : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hr : 0 < r) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of (Metric.ball y r))
      {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin n)) ≠ y}).homology n
        ≅ ModuleCat.of ℤ ℤ) := by
  haveI hcontr : ContractibleSpace (TopCat.of (Metric.ball y r)) := ball_contractible n y r hr
  have hn1 : 1 ≤ n := by omega
  -- the ball has vanishing homology in degrees `n` and `n - 1`
  have hz1 : IsZero ((singularChains ℤ (TopCat.of (Metric.ball y r))).homology n) :=
    homologyContractible n (by omega)
  have hz0 : IsZero ((singularChains ℤ (TopCat.of (Metric.ball y r))).homology (n - 1)) :=
    homologyContractible (n - 1) (by omega)
  have hδ : IsZero ((singularChains ℤ (TopCat.of (Metric.ball y r))).homology ((n - 1) + 1)) := by
    rw [Nat.sub_add_cancel hn1]; exact hz1
  -- hence the connecting map of the pair is an isomorphism
  haveI hiso : IsIso (hPairδ (TopCat.of (Metric.ball y r))
      {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin n)) ≠ y} (n - 1)) :=
    hPairδ_isIso _ _ _ hδ hz0
  -- the punctured ball is homotopy equivalent to `Sⁿ⁻¹`
  have he := Classical.choice (puncturedBallSphere n hn1 y r hr)
  refine ⟨(eqToIso (congrArg (fun k => (relChains (TopCat.of (Metric.ball y r))
      {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin n)) ≠ y}).homology k)
      (Nat.sub_add_cancel hn1))).symm ≪≫ asIso (hPairδ _ _ (n - 1))
      ≪≫ Classical.choice (homologyIso_of_homotopyEquiv he (n - 1)) ≪≫ ?_⟩
  -- and `Hₙ₋₁(Sⁿ⁻¹) ≅ ℤ`
  exact (Nat.sub_add_cancel hn1) ▸ Classical.choice (sphereHomologyTop (n - 1) (by omega))

/-! ## The main statement -/

/-- **The relative homology of a punctured open ball.**

For `n ≥ 1`, a point `y` of `EuclideanSpace ℝ (Fin n)` and `r > 0`, the `n`-th relative singular
homology (with `ℤ` coefficients) of the pair consisting of the open ball `Metric.ball y r` and its
complement of `{y}` is `ℤ`.

Suggested route: the long exact sequence of the pair `(B, B ∖ {y})` (`hPairδ`, `hPair_exact₁`,
`hPair_exact₃` and the trick of `hPairδ_isIso` in `Submission/Work/Cohomology/diskPairHomologyTop.lean`),
the contractibility of the ball (`convex_ball`, `Convex.contractibleSpace`, `homologyContractible`)
and `Work.Cohomology.sphereHomologyTop`, using that `B ∖ {y}` deformation retracts onto the sphere
of radius `r/2` around `y` (`homologyIso_of_homotopyEquiv`, in
`Submission/Work/Cohomology/sphereHomologyTop.lean`).  For `n = 1` the same sequence computes the
reduced `H₀` of a two point space: `Work.Cohomology.reducedH0OfTwoPoints` and
`Work.Cohomology.ker_eps_homotopyEquiv`. -/
theorem ballPairHomologyTop (n : ℕ) (hn : 1 ≤ n) (y : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hr : 0 < r) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of (Metric.ball y r))
      {z : Metric.ball y r | (z : EuclideanSpace ℝ (Fin n)) ≠ y}).homology n
        ≅ ModuleCat.of ℤ ℤ) := by
  rcases eq_or_lt_of_le hn with h1 | h1
  · -- `n = 1`: `H₁` of the pair is the reduced `H₀` of the two point space `S⁰`
    subst h1
    exact ballPairHomologyTopOne y r hr
      (Classical.choice (puncturedBallSphere 1 le_rfl y r hr))
  · -- `n ≥ 2`: the connecting map is an isomorphism onto `Hₙ₋₁(Sⁿ⁻¹)`
    exact ballPairHomologyTopGeTwo n h1 y r hr

end

end Work.Cohomology
