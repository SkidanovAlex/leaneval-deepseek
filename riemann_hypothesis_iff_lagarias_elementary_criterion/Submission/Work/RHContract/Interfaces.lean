import Submission.Work.RHContract.Defs
import Submission.Commons.NumberTheory.Robin.robin_caFval_small
import Submission.Commons.NumberTheory.Robin.robin_of_ca_cover_clean
import Submission.Commons.NumberTheory.Robin.robin_upper_le_55440
import Submission.Commons.NumberTheory.Robin.robin_upper_of_large
import Submission.Commons.NumberTheory.Robin.not_rh_exists_nontrivial_zero_gt_half
import Submission.Commons.NumberTheory.Lagarias.riemannHypothesis_iff_lagarias_inequality

/-!
# `Work.RHContract.Interfaces` — the replacement contract, assembled

The three areas of `Submission/Work/RHContract/Defs.lean`

* `RobinCAFrom1530` (AREA A),
* `LandauInput`      (AREA B1),
* `TransferInput`    (AREA B2),

imply the challenge theorem `RiemannHypothesis ↔ LagariasElementaryCriterion`
(`rh_iff_of_areas'`), using only *proved* commons theorems:

* `Commons.NumberTheory.Robin.robin_caFval_small` — Robin at CA numbers with `ξ(ε) < 1530`
  (`55441 ≤ M`);
* `Commons.NumberTheory.Robin.robin_upper_le_55440` — the certified finite range
  `5041 ≤ n ≤ 55440`;
* `Commons.NumberTheory.Robin.robin_of_ca_cover_clean` — Robin at all CA values `≥ 55440`
  implies Robin for every `n ≥ 55441` (Alaoglu–Erdős / Robin covering);
* `Commons.NumberTheory.Robin.robin_upper_of_large` — glues the finite range to `n ≥ 5041`;
* `Commons.NumberTheory.Lagarias.riemannHypothesis_iff_lagarias_inequality` — Lagarias §3.

The case split at `ξ = 1530` is exactly complementary, since both `robin_caFval_small`'s
support-supremum and `Work.RHPlan.caXi ε` are *literally* `(caSupport ε).sup id`.
-/

open scoped ArithmeticFunction.sigma

namespace Work.RHContract

noncomputable section

/-- **Robin at every CA value `M ≥ 55440`, from AREA A.**  Split on `ξ(ε) < 1530`:
the small-`ξ` branch is the proved `robin_caFval_small`, the complementary branch is AREA A
`RobinCAFrom1530`.  The single exceptional value `M = 55440` is the certified finite range. -/
theorem robinBound_ca_of_areaA (hA : RobinCAFrom1530) (hRH : RiemannHypothesis) :
    ∀ M : ℕ, Work.RHPlan.IsColossallyAbundant M → 55440 ≤ M → Work.RHPlan.RobinBound M := by
  intro M hM h55440
  rcases hM with ⟨ε, hε, hEq⟩
  subst hEq
  by_cases hxi : (Work.RHPlan.caXi ε : ℝ) < 1530
  · by_cases h55441 : 55441 ≤ Work.RHPlan.caNumber ε
    · refine Commons.NumberTheory.Robin.robin_caFval_small hRH (Work.RHPlan.caNumber ε) ?_ h55441
      refine ⟨ε, hε, rfl, ?_⟩
      have hsup : Work.RHPlan.caXi ε < 1530 := by exact_mod_cast hxi
      simpa [Work.RHPlan.caXi, Work.RHPlan.caSupport] using hsup
    · have hM55440 : Work.RHPlan.caNumber ε = 55440 := by omega
      rw [hM55440]
      exact Commons.NumberTheory.Robin.robin_upper_le_55440 55440 (by norm_num) (le_refl 55440)
  · have hbig : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := le_of_not_gt hxi
    exact hA hRH ε hε hbig

/-- **Direction `RH ⟹ Robin` for `n ≥ 5041`, from AREA A.** -/
theorem robin_upper_of_areaA (hA : RobinCAFrom1530) :
    RiemannHypothesis → ∀ n : ℕ, 5041 ≤ n →
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
        Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  intro hRH n hn
  refine Commons.NumberTheory.Robin.robin_upper_of_large (fun m hm => ?_) n hn
  refine Commons.NumberTheory.Robin.robin_of_ca_cover_clean (fun M hM h55440 => ?_) m hm
  exact robinBound_ca_of_areaA hA hRH M hM h55440

/-- **Direction `¬RH ⟹ counterexamples to Robin`, from AREAS B1 and B2.**  `LandauInput`
turns `¬RH` into `PsiTailOscillation`, and `TransferInput` turns that into `SigmaOscillation`
— *literally* the hypothesis `h22` of
`Commons.NumberTheory.Lagarias.riemannHypothesis_iff_lagarias_inequality`. -/
theorem sigmaOscillation_of_areas (hL : LandauInput) (hT : TransferInput) :
    ¬ RiemannHypothesis → ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧
      Filter.Frequently (fun n : ℕ =>
        ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≥
          Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
            C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β)
        Filter.atTop :=
  fun h => hT (hL h)

/-- **THE REPLACEMENT CONTRACT.**  The three areas (AREA A = regions I+II+III of the CA
range `ξ ≥ 1530`; AREA B1 = the Landau/Mellin step; AREA B2 = the lcm transfer) yield
`RiemannHypothesis ↔ LagariasElementaryCriterion`.

This is a genuine proof: the body only appeals to the three area hypotheses and the proved
commons theorems listed in the module doc comment. -/
theorem rh_iff_of_areas' (hA : RobinCAFrom1530) (hL : LandauInput) (hT : TransferInput) :
    RiemannHypothesis ↔ LeanEval.NumberTheory.LagariasElementaryCriterion := by
  have htop := Commons.NumberTheory.Lagarias.riemannHypothesis_iff_lagarias_inequality
    (robin_upper_of_areaA hA) (sigmaOscillation_of_areas hL hT)
  rw [Work.RHPlan.lagariasElementaryCriterion_iff]
  exact htop

end

end Work.RHContract
