import Mathlib
import Submission.Work.EKLComp.USCBasic

/-!
# A bump function centered at a point, constant `1` off the `η`-ball

`X₃ = SL₃(ℝ)/SL₃(ℤ)` is a locally compact regular (indeed Hausdorff) space, and
`ball η x₀` is an open neighbourhood of `x₀` (`prove_USC.isOpen_ball`,
`prove_USC.self_mem_ball`).  Urysohn's lemma in its locally compact form
(`exists_continuous_zero_one_of_isCompact`, which assumes only `RegularSpace` and
`LocallyCompactSpace`, and a *compact* rather than closed first set) therefore produces a
continuous `f : X₃ → ℝ` with `f = 0` at `x₀`, `f = 1` off `ball η x₀`, and values in `[0,1]`.
No metric on `X₃` is needed.
-/

namespace Work.EKLComp

open MeasureTheory Filter Topology

theorem exists_bump (x₀ : Work.EKLContract.X3) {η : ℝ} (hη : 0 < η) : ∃ Φ : Work.EKLContract.X3 → ℝ, Continuous Φ ∧ (∀ x, 0 ≤ Φ x ∧ Φ x ≤ 1) ∧ Φ x₀ = 0 ∧ ∀ x, x ∉ Work.EKLComp.ball η x₀ → Φ x = 1 := by
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_continuous_zero_one_of_isCompact (s := ({x₀} : Set Work.EKLContract.X3))
      (t := (ball η x₀)ᶜ) isCompact_singleton (isOpen_ball η x₀).isClosed_compl
      (Set.disjoint_compl_right_iff_subset.mpr
        (Set.singleton_subset_iff.mpr (self_mem_ball hη x₀)))
  refine ⟨f, f.continuous, fun x => hf01 x, hf0 (Set.mem_singleton x₀), ?_⟩
  intro x hx
  exact hf1 (by simpa using hx)

end Work.EKLComp
