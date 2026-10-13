/-
# The boundary value of the joint angular integral: `NOf f 0 = 0`

`NOf f r = ∫_{(r,∞) × Iθ} K(θ) ∂_z f(z,θ)` is the *joint* (hence honest) form of the angular
integral `-∫_{Iθ} K(θ) f(r,θ) dθ`; the paper's integration-by-parts computation of the zero mode
of `L₁₂(𝓛_Γ f)` needs its value at the left endpoint `r = 0`.

The two hypotheses of the statement supply exactly what is needed:

* `hrel : r * uOf f r = - NOf f r` for `r > 0` identifies `NOf f` on `(0,∞)` with
  `-r · L₁₂dens f r` (`uOf f = L12dens f`),
* `hcont` says `NOf f` is continuous at `0` within `[0,∞)`, i.e. `r * uOf f r → -NOf f 0` as
  `r → 0⁺`.

The third ingredient is *not* a consequence of the two above: it is the integrability hypothesis
`L12Hyp.hintL2` that `L₁₂dens f` is integrable on `(0,∞)`.  It is indispensable: a profile with a
genuine jump at `z = 0` (say `f z θ = φ z` where `φ ≡ 1` on `(0,1]`, `φ z = 1/z` for large `z`
and `φ 0 = 0`) satisfies `hrel` and `hcont` but has `NOf f 0 = -∫_{Iθ} K = -1`, precisely because
then `L₁₂dens f r ~ 1/r` is *not* integrable at `0`.

With integrability, the conclusion is forced: if `L := -NOf f 0 ≠ 0` then `|uOf f r| ≥ |L|/(2r)`
for all small `r > 0`, so `|uOf f|` dominates the non-integrable function `|L|/(2r)` on a
right-neighbourhood of `0`; this is exactly
`Work.FTS.EllipticEst.le_zero_of_tendsto_nhdsGT_zero_of_integrableOn_div` applied to
`F z = |z * uOf f z|` (so that the nonnegativity hypothesis of that lemma holds), whose conclusion
`|-NOf f 0| ≤ 0` gives `NOf f 0 = 0`.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Apriori.ZeroMode.L12_ZMDefs
import Submission.Work.FTS.EllipticEst.le_zero_of_tendsto_nhdsGT_zero_of_integrableOn_div

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

theorem ZM_Nfun_zero {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f)
    (hrel : ∀ r : ℝ, 0 < r → r * Work.FTS.Apriori.ZeroMode.uOf f r
      = - Work.FTS.Apriori.ZeroMode.NOf f r)
    (hcont : ContinuousWithinAt (Work.FTS.Apriori.ZeroMode.NOf f) (Set.Ici 0) 0) :
    Work.FTS.Apriori.ZeroMode.NOf f 0 = 0 := by
  -- `uOf f = L12dens f`, which is integrable on `(0,∞)` by the hypothesis `hintL2`.
  have hInt : MeasureTheory.IntegrableOn (uOf f) (Set.Ioi 0) := H.hintL2
  -- `hcont` transfers from `[0,∞)` to the filter `𝓝[>] 0` of the right-hand neighbourhoods.
  have hcont' : Tendsto (NOf f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (NOf f 0)) :=
    hcont.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
  -- `hrel` identifies `r * uOf f r` with `-NOf f r` on `(0,∞)`.
  have hev : (fun r : ℝ => -NOf f r) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun r : ℝ => r * uOf f r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hrel r hr).symm
  -- Hence `r * uOf f r → -NOf f 0` as `r → 0⁺`.
  have hlim : Tendsto (fun r : ℝ => r * uOf f r) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-(NOf f 0))) := hcont'.neg.congr' hev
  -- Taking absolute values, the same is true of `|r * uOf f r|`, with limit `|-NOf f 0|`.
  have hlimAbs : Tendsto (fun r : ℝ => |r * uOf f r|) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds |-(NOf f 0)|) := hlim.abs
  -- `|uOf f|` is integrable on `(0,∞)`, and for `z > 0` it agrees with `|z * uOf f z| / z`.
  have hIntAbs : MeasureTheory.IntegrableOn (fun z : ℝ => |uOf f z|) (Set.Ioi 0) := hInt.abs
  have hIntDiv : MeasureTheory.IntegrableOn (fun z : ℝ => |z * uOf f z| / z) (Set.Ioi 0) :=
    hIntAbs.congr_fun (fun z hz => by
      rw [abs_mul, abs_of_pos hz, mul_div_cancel_left₀ _ (ne_of_gt hz)]) measurableSet_Ioi
  -- The integrability lemma forces the limit of `|r * uOf f r|` at `0⁺` to be `≤ 0`.
  have hle : |-(NOf f 0)| ≤ 0 :=
    Work.FTS.EllipticEst.le_zero_of_tendsto_nhdsGT_zero_of_integrableOn_div
      (F := fun z : ℝ => |z * uOf f z|) (fun z _ => abs_nonneg (z * uOf f z)) hIntDiv hlimAbs
  have hzero : -(NOf f 0) = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  exact neg_eq_zero.mp hzero

end Work.FTS.Apriori.ZeroMode
