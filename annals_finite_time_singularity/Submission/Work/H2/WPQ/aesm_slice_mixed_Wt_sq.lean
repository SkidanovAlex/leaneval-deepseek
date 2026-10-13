import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.WPQ

set_option autoImplicit false

/-! ## Continuity of the weighted mixed slot on the open quadrant

The integrand `(z,θ) ↦ (D_z^jD_θ^i f z θ · W z θ)²` is continuous on the open quadrant
`(0,∞) × (0,π/2)`: the mixed derivative is `C^∞` there because `f` is `C^∞` on the larger
strip `(-1,∞) × (0,π/2)` in which the open quadrant sits, and `W = w · sin(2θ)^{-γ/2}` is
continuous there since `z > 0` and `0 < θ < π/2`.  The open quadrant differs from
`Iz ×ˢ Iθ` by the three null segments `{0} × Iθ`, `Iz × {0}`, `Iz × {π/2}`, which is what
`Work.Spaces.aesm_slice_of_continuousOn_Qd` turns into a.e. strong measurability. -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
private abbrev QdW : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

private lemma QdW_subset_quadU : QdW ⊆ Work.Spaces.quadU :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) subset_rfl

/-- `sin (2θ) > 0` for `θ ∈ (0, π/2)`. -/
private lemma sin_two_pos_QdW {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The product weight `W = w · w_θ` is continuous on the open quadrant. -/
private lemma continuousOn_Wt_QdW (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) QdW := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) QdW := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsp : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      QdW :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (sin_two_pos_QdW hp.2)))
  have hmul := hw.mul hsp
  have heq : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        * (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) := rfl
  rw [heq]
  exact hmul

/-- The mixed derivative `D_z^jD_θ^i f` is continuous on the open quadrant. -/
private lemma continuousOn_mixed_QdW (f : ℝ → ℝ → ℝ) (hf : Work.FTS.LocData.SmoothQuad f)
    (j i : ℕ) : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) QdW :=
  ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf j i).continuousOn).mono
    QdW_subset_quadU

/-- **A.e. strong measurability of a weighted mixed derivative in the interior class.**  For `g`
smooth on the open quadrant and `z > 0`, the `θ`-slice of `(D_z^j D_θ^i g · W)²` is a.e. strongly
measurable for the restricted Lebesgue measure on `Iθ`.  (The function is continuous on the open
quadrant, which differs from `Iθ` only in the two endpoints: `(z,θ) ↦ mixed j i f z θ` is
continuous there by `Work.FTS.LocData.contDiffOn_mixed`, and `Wt α z θ = w z · sin(2θ)^{-γ/2}`
is continuous there because `z > 0` and `0 < θ < π/2`; then
`Work.Spaces.aesm_slice_of_continuousOn_Qd` upgrades continuity on the open square to a.e. strong
measurability on `Iθ`.) -/
theorem aesm_slice_mixed_Wt_sq (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2) ?_ hz
  exact ((continuousOn_mixed_QdW f hf j i).mul (continuousOn_Wt_QdW α)).pow 2

end Work.H2.WPQ
