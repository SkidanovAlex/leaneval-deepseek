import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A.e. measurability of the sampled boundary trace

For `f` of class `Work.FTS.EllipticEst.SmoothOpen` (i.e. `C^∞` on the open quadrant
`(0,∞) × (0,π/2)`) the sampled trace

`z ↦ limUnder atTop (fun n : ℕ => f z (1 / (n + 2)))`

is a.e. measurable w.r.t. `volume.restrict (Ioi 0)`.

The mathematical content is that `Filter.limUnder atTop` of a family of measurable
functions indexed by `ℕ` is measurable (`MeasureTheory.StronglyMeasurable.limUnder`:
`Filter.lim` is the limit of the filter when it exists, and the constant
`Classical.choice` junk value otherwise, so its measurability is not automatic).  The
only input needed is that each sampled slice `z ↦ f z θ_n`, `θ_n = 1/(n+2) ∈ (0, π/2)`,
is measurable on `Ioi 0`, which follows from `SmoothOpen.curry_z`: the `z`-slice at an
interior angle is `C^∞` on `Ioi 0`, hence continuous there.
-/

namespace Work.FTS.StrongEps.EpsLocalPStar

open MeasureTheory Set Filter

theorem aemeasurable_traceSeq {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    AEMeasurable
      (fun z : ℝ => Filter.limUnder Filter.atTop (fun n : ℕ => f z (1 / (n + 2 : ℝ))))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
  -- Work on the subtype `Ioi 0`: a measurable function on it gives an a.e. measurable
  -- function for the restricted measure.
  refine aemeasurable_restrict_of_measurable_subtype measurableSet_Ioi ?_
  -- The sampled angles `1/(n+2)` lie in the open quadrant's angle range `(0, π/2)`.
  have hθn : ∀ n : ℕ, (1 : ℝ) / (n + 2 : ℝ) ∈ Set.Ioo 0 (Real.pi / 2) := by
    intro n
    constructor
    · positivity
    · have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hle : (1 : ℝ) / (n + 2 : ℝ) ≤ 1 / 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
      linarith [Real.pi_gt_three]
  -- Each sampled slice, viewed on the subtype `Ioi 0`, is continuous, hence strongly
  -- measurable.
  have hslice : ∀ n : ℕ, StronglyMeasurable
      (fun z : Set.Ioi (0:ℝ) => f z.1 (1 / (n + 2 : ℝ))) := by
    intro n
    exact ((hso.curry_z (hθn n)).continuousOn.comp_continuous
      continuous_subtype_val (fun z => z.2)).stronglyMeasurable
  -- `limUnder` of a sequence of strongly measurable functions is strongly measurable.
  have hlim : StronglyMeasurable
      (fun z : Set.Ioi (0:ℝ) => Filter.limUnder Filter.atTop
        (fun n : ℕ => f z.1 (1 / (n + 2 : ℝ)))) :=
    StronglyMeasurable.limUnder (l := Filter.atTop)
      (f := fun (n : ℕ) (z : Set.Ioi (0:ℝ)) => f z.1 (1 / (n + 2 : ℝ))) hslice
  exact hlim.measurable

end Work.FTS.StrongEps.EpsLocalPStar
