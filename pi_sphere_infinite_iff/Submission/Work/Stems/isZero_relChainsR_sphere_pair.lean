import Mathlib
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Serre.periodicity_of_pairComparison
import Submission.Work.Stems.product_ratH_vanishing

/-!
# The relative rational homology of `(Sⁿ, {s₀})` vanishes away from degree `n`

For `i ≥ 2`, `i ≠ n` and any base point `s₀ : Sⁿ`, the relative rational homology
`H_i(Sⁿ, {s₀}; ℚ)` vanishes.

The proof is the exactness chase in the long exact sequence of the pair `(Sⁿ, {s₀})`,

`H_i({s₀};ℚ) → H_i(Sⁿ;ℚ) → H_i(Sⁿ,{s₀};ℚ) → H_{i-1}({s₀};ℚ) → H_{i-1}(Sⁿ;ℚ)`,

packaged as `Work.Stems.isZero_relChainsR_homology_of_isZero_abs`: the two outer terms vanish
because

* `H_i(Sⁿ;ℚ) = 0` for `i ≠ 0, n` — for `n ≥ 1` this is `Work.StemsB.sphRatHomology`
  (`H_*(Sⁿ;ℚ)` is that of a sphere), and for `n = 0`, where `S⁰` is the two-point space
  `{±1}` and hence discrete (totally disconnected), it is
  `AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`;
* `H_{i-1}({s₀};ℚ) = 0` because `{s₀}` is a one-point space and `i - 1 > 0`
  (`Work.Stems.isZero_ratH_singleton`).

Note that `hi : 2 ≤ i` is exactly what makes both of these available: it gives `i ≠ 0`
(so that `H_i(Sⁿ;ℚ) = 0` for `n = 0` as well) and `i - 1 > 0`.
-/

set_option linter.style.haveILetI false

namespace Work.Stems

open CategoryTheory CategoryTheory.Limits

theorem isZero_relChainsR_sphere_pair (n i : ℕ) (hi : 2 ≤ i) (hin : i ≠ n) (s₀ : Work.Serre.Sph n) :
    CategoryTheory.Limits.IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.Sph n))
      ({s₀} : Set (Work.Serre.Sph n))).homology i) := by
  have hi1 : 1 ≤ i := by omega
  refine isZero_relChainsR_homology_of_isZero_abs ℚ (TopCat.of (Work.Serre.Sph n))
    ({s₀} : Set (Work.Serre.Sph n)) i hi1 ?_ ?_
  · -- `H_i(Sⁿ;ℚ) = 0`, the "non-top" vanishing of the absolute homology of the sphere
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- `n = 0`: `S⁰ = {±1} ⊆ ℝ` is discrete, hence totally disconnected
      subst hn0
      haveI hd : DiscreteTopology ↥(Work.Cohomology.sphSet 1) :=
        Work.Cohomology.discreteTopology_sphSet_one
      haveI : DiscreteTopology (Work.Serre.Sph 0) :=
        (Homeomorph.setCongr (Work.Cohomology.sphereSet_eq 1)).symm.discreteTopology
      haveI : TotallyDisconnectedSpace (Work.Serre.Sph 0) := inferInstance
      exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (ModuleCat ℚ) i (ModuleCat.of ℚ ℚ) (TopCat.of (Work.Serre.Sph 0)) (by omega)
    · obtain ⟨-, h⟩ := Work.StemsB.sphRatHomology n hnpos
      exact h i (by omega) hin
  · -- `H_{i-1}({s₀};ℚ) = 0`: a one-point space is rationally acyclic in positive degrees
    exact isZero_ratH_singleton (Work.Serre.Sph n) s₀ (by omega)

end Work.Stems
