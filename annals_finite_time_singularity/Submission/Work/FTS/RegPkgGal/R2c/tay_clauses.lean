import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.R2.RepairFinal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R2c

/-!
# `R2c`: the Taylor clauses with the two angular endpoint *limits* as hypotheses

This file proves `tay_clauses` in the `R2c` shape: instead of the (too strong) smoothness
hypothesis on a neighbourhood of the closed angular range (`R2b`), or the (too strong)
hypothesis that the angular slices are *continuous* on `Iθ` (`R2.tay_clauses_of_continuous`),
the two endpoint conditions are supplied as one-sided *limits*:

* `hcont0`  : `θ ↦ g z θ τ → g z 0 τ` as `θ → 0⁺`,
* `hcontπ` : `θ ↦ g z θ τ → g z (π/2) τ` as `θ → (π/2)⁻`.

Together with the joint `C¹` hypothesis `hsm` on the *open* quadrant these say exactly that
every angular slice `θ ↦ g z θ τ` is continuous on the closed interval `Iθ = [0, π/2]`
(for `z > 0`), which is the minimal repair identified by the counterexample
`Work.FTS.RegPkgGal.R2.tay_clauses_refuted` (a jump of the slice at an angular endpoint is
invisible to `D_θ` and to `VanishTheta`).  The conclusion is then the proved
`Work.FTS.RegPkgGal.R2.tay_clauses_of_continuous`.
-/

/-- **Continuity of an angular slice on the closed interval.**

From the joint `C¹` hypothesis on the open quadrant (which gives continuity at every interior
point of the slice) and the two one-sided endpoint limits, the slice is continuous on
`Iθ = [0, π/2]`. -/
private lemma slice_continuousOn {g : ℝ → ℝ → ℝ → ℝ} {τ z : ℝ}
    (hsm : ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (g z 0 τ)))
    (hπ : Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds (g z (Real.pi / 2) τ))) :
    ContinuousOn (fun θ => g z θ τ) Work.Spaces.Iθ := by
  have hIoo : ContinuousOn (fun θ : ℝ => g z θ τ) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun θ : ℝ => (z, θ)) (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have h2 := hsm.continuousOn.comp h1 (fun θ hθ => ⟨hz, hθ⟩)
    simpa [Function.comp_def, Function.uncurry] using h2
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hx0 | rfl
  · rcases lt_or_eq_of_le hx.2 with hxπ | rfl
    · exact (hIoo.continuousAt (isOpen_Ioo.mem_nhds ⟨hx0, hxπ⟩)).continuousWithinAt
    · refine ContinuousWithinAt.mono (ContinuousWithinAt.insert hπ) (fun y hy => ?_)
      rcases lt_or_eq_of_le hy.2 with h | h
      · exact Or.inr h
      · exact Or.inl h
  · refine ContinuousWithinAt.mono (ContinuousWithinAt.insert h0) (fun y hy => ?_)
    rcases lt_or_eq_of_le hy.1 with h | h
    · exact Or.inr h
    · exact Or.inl h.symm

theorem tay_clauses {α S Cθ K Q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hCθ : 0 ≤ Cθ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (g z 0 τ)))
    (hcontπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (g z (Real.pi / 2) τ)))
    (hquad0 : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, g 0 θ τ = 0)
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |g z θ τ| ≤ K * z ^ 2)
    (hlinz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Q * z) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K' * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K' * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K' * z ^ 2 * |θ - θ'| ^ α) := by
  refine Work.FTS.RegPkgGal.R2.tay_clauses_of_continuous hα hα1 hS hCθ hK hQ hsm hd hvt
    hquad hlinz ?_
  intro τ hτ z hz hz2
  exact slice_continuousOn (hsm τ hτ) hz (hcont0 τ hτ z (le_of_lt hz))
    (hcontπ τ hτ z (le_of_lt hz))

end Work.FTS.RegPkgGal.R2c
