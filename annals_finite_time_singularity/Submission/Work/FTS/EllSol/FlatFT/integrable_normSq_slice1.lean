import Mathlib.Analysis.Fourier.LpSpace
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped FourierTransform

namespace Work.FTS.EllSol.FlatFT

/-- The Fourier slice `slice1 h` of a continuous compactly supported `h` is square-integrable.
Indeed `h ∈ L¹ ∩ L²`, so Plancherel gives that `𝓕 h` (which is `slice1 h` pointwise) lies in
`L²`, and `‖·‖ ^ 2` of an `L²` function is integrable.  This is the "left-hand side is finite"
half of Plancherel, `plancherelSlice1`. -/
theorem integrable_normSq_slice1 {h : ℝ → ℂ} (hh : Continuous h) (hs : HasCompactSupport h) :
    MeasureTheory.Integrable (fun ξ : ℝ => ‖Work.FTS.EllSol.FlatFT.slice1 h ξ‖ ^ 2) := by
  have hInt : Integrable h := hh.integrable_of_hasCompactSupport hs
  have hMem : MemLp h 2 (volume : Measure ℝ) := hh.memLp_of_hasCompactSupport hs
  have hF : MemLp (((𝓕 (hMem.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) 2 volume :=
    Lp.memLp _
  refine (hF.integrable_norm_pow (by norm_num)).congr ?_
  filter_upwards [fourier_lp_ae_eq hInt hMem] with ξ hξ
  rw [slice1_eq_fourier h ξ, ← hξ]

end Work.FTS.EllSol.FlatFT
