import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.continuous_quasiPeriodic_surjective
import Submission.Work.RPB.B5.continuous_slice_of_continuousOn_prod
import Submission.Work.RPB.B5.continuous_of_continuousOn_Ici_of_quasiPeriodic

/-!
# `AcZero_surj`: the `τ = 0` phase slice of the collar is onto `ℝ`

For every level `σ ≥ 0` the map `t ↦ Ac 0 σ t` — the phase of the collar
(`Work.RPB.B5.LagData`) at isotopy time `τ = 0` and level `σ` — is surjective onto `ℝ`.

This is what turns the collar branch of the assembled family into a graph over the `t`-axis at
`τ = 0`, and it is used (via `LagFamily.start`-type statements) to see that the assembled family
hits the zero section for every `x ≤ -√2`.

## Why this is not immediate from the smoothness field

`D.hAsm` gives only

`ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Ac z.1 z.2.1 z.2.2) (Icc 0 1 ×ˢ univ ×ˢ Ici 0)`,

i.e. smoothness in `(τ, σ, t)` for `τ ∈ [0,1]`, **all** `σ : ℝ` and `t ≥ 0`.  The half line
`t ≥ 0` is essential: the collar is built by glueing the chord chart to the far circles through a
cutoff in the level, and only the statement on `t ≥ 0` is available from the sibling
constructions.  Hence the slice `t ↦ Ac 0 σ t` is only *a priori* known to be continuous for
`t ≥ 0`, while the theorem needs all `t : ℝ`.

Two ingredients bridge the gap:

* `continuous_slice_of_continuousOn_prod` turns `D.hAsm.continuousOn` into
  `ContinuousOn (fun t => Ac 0 σ t) (Set.Ici 0)`;
* the quasi-periodicity `D.hAper : Ac τ σ (t + 2π) = Ac τ σ t + 2π` lets us *shift any point into
  the half line*: choosing `k : ℕ` with `t + k·2π > 0`, iterating gives
  `Ac 0 σ s = Ac 0 σ (s + k·2π) - k·2π` for **every** `s`, and the right hand side is continuous
  at `t` because `t + k·2π > 0` is an interior point of `Ici 0`.  This is
  `continuous_of_continuousOn_Ici_of_quasiPeriodic`.

Once `t ↦ Ac 0 σ t` is continuous on `ℝ`, surjectivity is immediate from the quasi-periodicity
`f (t + 2π) = f t + 2π`: `continuous_quasiPeriodic_surjective` shows that a continuous
`f : ℝ → ℝ` with `f (t + c) = f t + c` and `c > 0` is onto (the values are unbounded above and
below along the shift, and the range, being the continuous image of `ℝ`, is an interval).
-/

open scoped ContDiff

namespace Work.RPB.B5

/-- **Continuity of the `τ = 0` phase slice of the collar.**  For every level `σ` (no positivity
needed) the map `t ↦ D.Ac 0 σ t` is continuous on `ℝ`: smoothness of `Ac` on the half line
`t ≥ 0` (`D.hAsm`) together with the `2π`-quasi-periodicity `D.hAper`. -/
theorem AcZero_continuous (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) (σ : ℝ) :
    Continuous (fun t : ℝ => D.Ac 0 σ t) := by
  have hc : (0 : ℝ) < 2 * Real.pi := by positivity
  -- The slice is continuous on the half line on which `Ac` is known to be smooth.
  have hOn : ContinuousOn (fun t : ℝ => D.Ac 0 σ t) (Set.Ici 0) :=
    continuous_slice_of_continuousOn_prod (s := Set.Icc (0 : ℝ) 1) (u := Set.univ)
      (T := Set.Ici (0 : ℝ)) (x := (0 : ℝ)) (y := σ)
      ⟨le_refl 0, zero_le_one⟩ (Set.mem_univ σ) D.hAsm.continuousOn
  -- Shift into the half line and undo the shift with the quasi-periodicity.
  exact continuous_of_continuousOn_Ici_of_quasiPeriodic hc hOn (fun t => D.hAper 0 σ t)

theorem AcZero_surj (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) :
    ∀ σ : ℝ, 0 ≤ σ → ∀ v : ℝ, ∃ t : ℝ, D.Ac 0 σ t = v := by
  intro σ _ v
  exact continuous_quasiPeriodic_surjective (by positivity : (0 : ℝ) < 2 * Real.pi)
    (AcZero_continuous CI a D σ) (fun t => D.hAper 0 σ t) v

end Work.RPB.B5
