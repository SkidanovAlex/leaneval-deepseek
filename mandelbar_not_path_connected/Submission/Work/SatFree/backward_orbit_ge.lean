import Mathlib
import Submission.Work.SatFree.backward_step

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SatFree

open Work.FatouCoord.Flower

/-- `Work.SatFree.backward_orbit` with an arbitrary landing threshold: for a parabolic germ
`f z = z + z² h z` with the quantitative bounds `ParabolicBounds`, and all `W`, `m` and `M ≥ M₀`,
if `M + m * C ≤ sgauge W` then some `W'` has `sgauge W' ≥ M` and `(f^[m]) (-1/W') = -1/W`.

Same induction as `Work.SatFree.backward_orbit` (which is the case `M = M₀`): its private one-step
result loses `C₀` of `sgauge` per step and needs only `M₀ ≤ sgauge V`, supplied by
`M₀ ≤ M ≤ M + m*C ≤ sgauge W`. -/
theorem backward_orbit_ge {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ M₀ C : ℝ, 1 ≤ C ∧ ∀ (W : ℂ) (m : ℕ) (M : ℝ), M₀ ≤ M →
      M + (m : ℝ) * C ≤ Work.FatouCoord.Flower.sgauge W →
      ∃ W' : ℂ, M ≤ Work.FatouCoord.Flower.sgauge W' ∧ (f^[m]) (-1 / W') = -1 / W := by
  obtain ⟨M₀, C₀, _hM₀pos, hC₀nn, hst⟩ := backward_step hb
  have hCnn : 0 ≤ max C₀ 1 := le_trans hC₀nn (le_max_left _ _)
  refine ⟨M₀, max C₀ 1, le_max_right _ _, ?_⟩
  -- The induction is over the number of steps, with the landing threshold `M ≥ M₀` fixed.
  have key : ∀ (m : ℕ) (M : ℝ), M₀ ≤ M → ∀ V : ℂ,
      M + (m : ℝ) * max C₀ 1 ≤ sgauge V →
      ∃ V' : ℂ, M ≤ sgauge V' ∧ (f^[m]) (-1 / V') = -1 / V := by
    intro m
    induction m with
    | zero =>
      intro M _hM V hV
      exact ⟨V, by simpa using hV, by simp⟩
    | succ j ih =>
      intro M hM V hV
      have hcast : M + ((j : ℝ) + 1) * max C₀ 1 ≤ sgauge V := by
        simpa [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hV
      have hM₀le : M₀ ≤ sgauge V := by
        have h0 : (0 : ℝ) ≤ ((j : ℝ) + 1) * max C₀ 1 := mul_nonneg (by positivity) hCnn
        linarith
      obtain ⟨V₁, hV₁f, hV₁g⟩ := hst V hM₀le
      have hstep : M + (j : ℝ) * max C₀ 1 ≤ sgauge V₁ := by
        have hle : C₀ ≤ max C₀ 1 := le_max_left _ _
        linarith
      obtain ⟨V', hV'g, hV'f⟩ := ih M hM V₁ hstep
      exact ⟨V', hV'g, by rw [Function.iterate_succ_apply', hV'f, hV₁f]⟩
  exact fun W m M hM hW => key m M hM W hW

end Work.SatFree
