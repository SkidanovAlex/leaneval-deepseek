import Mathlib
import Submission.NK.HeckeL.Artin
import Submission.NK.HeckeL.Basic
import Submission.NK.NUV2.HeckeLAbel.tendsto_LSeries_of_partial_sum_bound
import Submission.NK.NUV2.HeckeLCoeff.LSeriesSummable_heckeCoeff
import Submission.NK.NUV2.HeckeLCoeff.heckeLSeries_eq_LSeries_heckeCoeff
import Submission.NK.NUV2.RouteB.heckeCoeff_theta_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.RouteB

open Filter Finset
open scoped Topology

-- RULE of the project lead (2026-09-24): there are NO licensed inputs and NO out-of-scope
-- statements; every named Prop that is TRUE must be PROVED by building the mathematics.
-- `declare_false` is only for a statement that is actually false, WITH a counterexample.
-- This statement is TRUE (Hecke 1917) and must be built.
-- Note: the partial-sum bound `rayClassCount_sub_isBigO` as currently stated is FALSE for
-- arbitrary S (see CRUX_IS_FALSE_NOTES.md); the right input is a uniform `∃ θ < 1` bound on the
-- character-twisted partial sums (i.e. over ideals coprime to the modulus of U). Build that.
theorem heckeInput_build :
    ∀ (K : Type) [Field K] [NumberField K] (U : Subgroup (NK.GlobalCFT.Idele K)),
      IsOpen (U : Set (NK.GlobalCFT.Idele K)) →
      Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) →
      ∀ (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : NK.HeckeL.RayChar K U), χ ≠ 1 →
      (∃ 𝔭 : NK.HeckeL.PrimeIdeal K,
        χ (NK.HeckeL.classOfIdeal K U 𝔭.asIdeal) ≠ 1) →
      Nonempty (NK.HeckeL.HeckeLRegularAtOne K U S χ) := by
  intro K _ _ U hU hfin S χ hχ hprime
  obtain ⟨C, θ, hCpos, hθ0, hθ1, hbd⟩ :=
    heckeCoeff_theta_bound K U hU hfin S χ hχ hprime
  obtain ⟨L, hL⟩ := NK.NUV2.HeckeLAbel.tendsto_LSeries_of_partial_sum_bound
    (NK.HeckeL.heckeCoeff K U S χ) θ C hθ0 hθ1 hCpos.le hbd
    (fun σ hσ => NK.NUV2.HeckeLCoeff.LSeriesSummable_heckeCoeff K U S χ hσ)
  refine ⟨⟨L, ?_⟩⟩
  refine Tendsto.congr' ?_ hL
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (NK.NUV2.HeckeLCoeff.heckeLSeries_eq_LSeries_heckeCoeff K U S χ hσ).symm

end NK.NUV2.RouteB
