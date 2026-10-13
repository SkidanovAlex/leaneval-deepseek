import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.biotSavart_decay
import Submission.Work.FTS.PressureOn.biotSavartDecayExplicit
import Submission.Work.StabilityFar.Decay.biotSavart_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

namespace Work.FTS.PressureOn

/-- **Slope bound for the Biot–Savart velocity in the time variable** (piece of
`tendsto_timeDeriv_physVel`).

If the vorticity slices `ω · s`, `s ∈ Icc 0 S`, are bounded by `M`, supported in `B(0,R)` and
a.e. strongly measurable, and if `ω` is Lipschitz in time on `[0,S]` with constant `C`, then for
`t ∈ Icc 0 S` and every `y ∈ (t,S)` the difference quotient of `physVel ω` in time is bounded
uniformly in `x` and `y` at the far-field rate `(1+‖x‖²)⁻¹`:

  `‖(y - t)⁻¹ • (physVel ω x y - physVel ω x t)‖ ≤ 3 C R (1 + 4 R²) / (1 + ‖x‖²)`.

Recipe:
* `physVel ω x s = biotSavart (ω · s) x` (`Work.FTS.Physical.physVel_apply`), and
  `Work.StabilityFar.Decay.biotSavart_sub` (f := `ω · y`, g := `ω · t`, both bounded by `M ≥ 0`,
  supported in `B(0,R)`, a.e. strongly measurable) gives
  `physVel ω x y - physVel ω x t = biotSavart (ω · y - ω · t) x`;
* the difference field is bounded by `C (y - t)` (`hlip` at `(y,t)`, `|y-t| = y-t > 0`) and is
  supported in `B(0,R)`;
* the explicit-constant far-field decay (state and prove the following helper in your own file,
  copying the proof of `Work.FTS.PressureOn.biotSavart_decay` from
  `Submission/Work/FTS/PressureOn/biotSavart_decay.lean`, which glues
  `Work.LWP.BiotSavart.norm_biotSavart_near` and `Work.LWP.BiotSavart.farField_decay_const`):
  for `M ≥ 0`, `R ≥ 0`, `∀ y, ‖g y‖ ≤ M`, `∀ y, g y ≠ 0 → y ∈ closedBall 0 R` and all `x`,
  `‖biotSavart g x‖ ≤ (3 * M * R * (1 + 4 * R ^ 2)) / (1 + ‖x‖ ^ 2)`
  (`Work.FTS.PressureOn.biotSavart_decay` only gives `∃ K`, so you need this explicit form);
* finish with `norm_smul`/`Real.norm_eq_abs`, `abs_of_pos (sub_pos.mpr hy.1)` and `field_simp`/
  `ring` on the arithmetic, using `0 < y - t` and `0 < 1 + ‖x‖ ^ 2`. -/
theorem normSlopePhysVelLe {ω : R3 → ℝ → R3} {S t M C R : ℝ}
    (ht : t ∈ Set.Icc 0 S) (hM : 0 ≤ M) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hsupp : ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hbdd : ∀ s ∈ Set.Icc 0 S, ∀ x, ‖ω x s‖ ≤ M)
    (hmeas : ∀ s ∈ Set.Icc 0 S,
      MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume)
    (hlip : ∀ x, ∀ s ∈ Set.Icc 0 S, ∀ s' ∈ Set.Icc 0 S, ‖ω x s - ω x s'‖ ≤ C * |s - s'|) :
    ∀ x : R3, ∀ y ∈ Set.Ioo t S,
      ‖(y - t)⁻¹ • (Work.FTS.Physical.physVel ω x y - Work.FTS.Physical.physVel ω x t)‖
        ≤ (3 * C * R * (1 + 4 * R ^ 2)) / (1 + ‖x‖ ^ 2) := by
  intro x y hy
  -- `y` lies in the time strip `[0,S]` as well
  have hyIcc : y ∈ Set.Icc 0 S := ⟨le_trans ht.1 (le_of_lt hy.1), le_of_lt hy.2⟩
  have hyt : 0 < y - t := sub_pos.mpr hy.1
  -- bounds and supports of the two vorticity slices
  have hfy : ∀ z, ‖ω z y‖ ≤ M := fun z => hbdd y hyIcc z
  have hft : ∀ z, ‖ω z t‖ ≤ M := fun z => hbdd t ht z
  have hsy : ∀ z, ω z y ≠ 0 → z ∈ Metric.closedBall (0 : R3) R := fun z hz =>
    by simpa [Metric.mem_closedBall, dist_eq_norm] using hsupp y hyIcc z hz
  have hst : ∀ z, ω z t ≠ 0 → z ∈ Metric.closedBall (0 : R3) R := fun z hz =>
    by simpa [Metric.mem_closedBall, dist_eq_norm] using hsupp t ht z hz
  -- additivity of the Biot–Savart operator on the difference of the two slices
  have hsub : Work.LWP.biotSavart (fun z => ω z y - ω z t) x
      = Work.LWP.biotSavart (fun z => ω z y) x - Work.LWP.biotSavart (fun z => ω z t) x := by
    have h := Work.StabilityFar.Decay.biotSavart_sub (f := fun z => ω z y) (g := fun z => ω z t)
      hR hM hfy hft hsy hst (hmeas y hyIcc) (hmeas t ht) x
    rwa [show (fun z => ω z y) - (fun z => ω z t) = fun z => ω z y - ω z t from by
      funext z; rw [Pi.sub_apply]] at h
  have hdiff : Work.FTS.Physical.physVel ω x y - Work.FTS.Physical.physVel ω x t
      = Work.LWP.biotSavart (fun z => ω z y - ω z t) x := by
    rw [Work.FTS.Physical.physVel_apply ω x y, Work.FTS.Physical.physVel_apply ω x t, ← hsub]
  -- the difference field is bounded by `C (y - t)` and supported in `B(0,R)`
  have hyM : (0 : ℝ) ≤ C * (y - t) := mul_nonneg hC (le_of_lt hyt)
  have hgbdd : ∀ z, ‖ω z y - ω z t‖ ≤ C * (y - t) := by
    intro z
    have h := hlip z y hyIcc t ht
    rwa [abs_of_pos hyt] at h
  have hgsupp : ∀ z, ω z y - ω z t ≠ 0 → z ∈ Metric.closedBall (0 : R3) R := by
    intro z hz
    rcases eq_or_ne (ω z y) 0 with h | h
    · refine hst z ?_
      intro h0
      exact hz (by rw [h, h0, sub_zero])
    · exact hsy z h
  -- the explicit-constant far-field decay of the difference field
  have hdec := biotSavartDecayExplicit hR hyM hgbdd hgsupp x
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyt)]
  calc (y - t)⁻¹ * ‖Work.LWP.biotSavart (fun z => ω z y - ω z t) x‖
      ≤ (y - t)⁻¹ * (3 * (C * (y - t)) * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hdec (inv_nonneg.mpr (le_of_lt hyt))
    _ = 3 * C * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2) := by
        have h1 : y - t ≠ 0 := ne_of_gt hyt
        have h2 : (1 : ℝ) + ‖x‖ ^ 2 ≠ 0 := by positivity
        field_simp

end Work.FTS.PressureOn

/-- **Slope bound for the Biot–Savart velocity in the time variable**, under its canonical
qualified name `Work.FTS.PressureOn.normSlopePhysVelLe` (the skeleton of this file opened the
namespace `Work.FTS.PressureOn` twice, which places the declaration above at
`Work.FTS.PressureOn.Work.FTS.PressureOn.normSlopePhysVelLe`; this is the same theorem, with the
name consumers use).  See the docstring above for the statement and the proof. -/
theorem normSlopePhysVelLe {ω : R3 → ℝ → R3} {S t M C R : ℝ}
    (ht : t ∈ Set.Icc 0 S) (hM : 0 ≤ M) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hsupp : ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hbdd : ∀ s ∈ Set.Icc 0 S, ∀ x, ‖ω x s‖ ≤ M)
    (hmeas : ∀ s ∈ Set.Icc 0 S,
      MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume)
    (hlip : ∀ x, ∀ s ∈ Set.Icc 0 S, ∀ s' ∈ Set.Icc 0 S, ‖ω x s - ω x s'‖ ≤ C * |s - s'|) :
    ∀ x : R3, ∀ y ∈ Set.Ioo t S,
      ‖(y - t)⁻¹ • (Work.FTS.Physical.physVel ω x y - Work.FTS.Physical.physVel ω x t)‖
        ≤ (3 * C * R * (1 + 4 * R ^ 2)) / (1 + ‖x‖ ^ 2) :=
  _root_.Work.FTS.PressureOn.Work.FTS.PressureOn.normSlopePhysVelLe
    ht hM hC hR hsupp hbdd hmeas hlip

end Work.FTS.PressureOn
