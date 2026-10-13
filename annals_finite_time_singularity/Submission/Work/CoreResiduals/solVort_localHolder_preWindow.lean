import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.exists_eps_min_lam
import Submission.Work.CoreResiduals.solVort_holder_of_lam_ge
import Submission.Work.ConstructionInstance.solVort_holder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- **Local `α`-Hölder regularity of the constructed vorticity around every time of the
half-window `preWindow P.T = Ioo (-2) P.T`.**  This is the local-`x`-Hölder clause of the
admissibility bundle `BSAdmissibleOnWindow` at `ω = solVort P`: near every `t₀ ∈ preWindow P.T`
there are `ε > 0`, an exponent `c > 0` and a constant `C` (all independent of `a, b`) with

  `‖solVort P a t - solVort P b t‖ ≤ C * ‖a - b‖ ^ c`   for all `t ∈ Ioo (t₀-ε) (t₀+ε)`.

The proof localises in time and then quotes the quantitative uniform-Hölder lemma.  Since
`preWindow P.T` is open, `exists_eps_min_lam` supplies `ε > 0` with `Icc (t₀-ε) (t₀+ε) ⊆
preWindow P.T` together with a *uniform* lower bound `m ≤ λ̄ s` on that interval
(`m = λ̄ t₀ / 2 > 0`, by continuity of `λ̄`, which is differentiable on `preWindow`).  The
uniformity of the Hölder constant in `t` is exactly the content of `solVort_holder_of_lam_ge`:
for every `δ > 0` a single constant works at *all* times with `λ̄ ≥ δ` — so `m ≤ λ̄ s` gives one
`H` valid at every `s ∈ Ioo (t₀-ε) (t₀+ε)`, regardless of whether the time is positive or negative
(this is where the restriction of `solVort_holder_strip` to the strip `Icc 0 S` would not suffice).
Writing the `dist`-inequality of `HolderWith.dist_le` as a norm inequality finishes the proof with
`c = α > 0` and `C = H`. -/
theorem solVort_localHolder_preWindow {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t₀ ∈ Work.ConstructionInstance.preWindow P.T, ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧
      ∃ C : ℝ, ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ a b : Work.CoreResiduals.R3,
        ‖Work.ConstructionInstance.solVort P a t - Work.ConstructionInstance.solVort P b t‖
          ≤ C * ‖a - b‖ ^ c := by
  intro t₀ ht₀
  -- a two-sided neighbourhood of `t₀` inside the half-window, on which `λ̄ ≥ m > 0` uniformly
  obtain ⟨ε, hε, hsub, m, hm, hmle⟩ := exists_eps_min_lam P.hlam P.hlamdif ht₀
  -- a single Hölder constant for all times at which the modulation is at least `m`
  obtain ⟨H, hH⟩ := solVort_holder_of_lam_ge P (δ := m) hm
  refine ⟨ε, hε, (α : ℝ), P.hα, (H : ℝ), fun t ht a b => ?_⟩
  have hmem : t ∈ Set.Icc (t₀ - ε) (t₀ + ε) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  -- the slice at time `t` is `α`-Hölder with constant `H`, since `m ≤ λ̄ t`
  have h := (hH t (hmle t hmem)).dist_le a b
  rwa [dist_eq_norm, dist_eq_norm] at h

end Work.CoreResiduals
