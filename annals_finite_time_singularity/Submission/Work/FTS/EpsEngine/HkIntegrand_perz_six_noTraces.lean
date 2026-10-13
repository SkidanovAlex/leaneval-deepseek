/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/HkIntegrand_perz_six_noTraces.lean`

**The per-`z` energy bound of the level-`6` `ℋ`-integrand, with NO trace hypothesis:**

  `∫_θ HkIntegrand α 6 f z θ ≤ C (1 + w z ^ 2) (1 + |f|_{ℋ⁸})²`   for every `α ∈ (0,1]`,
  every `f` of class `C^∞` on the open quadrant with `HkMem α 8 f`, and every `z ∈ Iz`.

This is the level-`6` companion of the delivered
`Work.FTS.EpsEngine.HkIntegrand_perz_le_noTraces` (level `4`, honesty `ℋ⁶`), needed by the
`k ≤ 8` branch of the scheme (the projected iterates `Pz (J_ε ·)` are `ℋ⁸`-honest).

## Proof

The `ℋ⁶`-integrand is the sum of its `z`-slots (`i ≤ 6`, weight `w z/sin(2θ)^{η/2}`) and its
mixed slots (`1 ≤ i`, `i + j ≤ 6`, weight `W = w z · sin(2θ)^{-γ/2}`).  The two families are
estimated separately, each at the fixed `z`, by the radial resp. the angular *window*
(not half-line) inequality — which is why no boundary-trace hypothesis is needed:

* `Work.FTS.EpsEngine.HkIntegrand_zslot_perz_six_noTraces`: the `z`-slots;
* `Work.FTS.EpsEngine.mixed_slot_perz_le8`: the mixed slots, through the level-`8` angular
  window estimate `Work.FTS.EpsEngine.sliceAng_le8`.

The finite-sum bookkeeping (integrability of every summand, exchange of the sum and the
`θ`-integral, and the arithmetic `(k+1)·Cz + (k+1)²·Cm`) is done *once*, at arbitrary level, in
`Work.FTS.EpsEngine.HkIntegrand_perz_le_of_halves`; the present theorem is its `k = 6` instance.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.PerzAssemblyGen
import Submission.Work.FTS.EpsEngine.SixMixed
import Submission.Work.FTS.EpsEngine.HkIntegrand_zslot_perz_six_noTraces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

theorem HkIntegrand_perz_six_noTraces :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 8 f →
      ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α 8 f) ^ 2 := by
  obtain ⟨Cz, hCzpos, hCz⟩ := HkIntegrand_zslot_perz_six_noTraces
  obtain ⟨Cm, hCmpos, hCm⟩ := mixed_slot_perz_le8
  exact HkIntegrand_perz_le_of_halves 6 Cz Cm hCzpos hCmpos hCz hCm

end Work.FTS.EpsEngine
