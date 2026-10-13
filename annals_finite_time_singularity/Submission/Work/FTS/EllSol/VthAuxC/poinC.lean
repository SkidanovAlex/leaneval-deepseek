import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.ropPoincareAe
import Submission.Work.FTS.EllipticEst.Cores.Repair.DzShift
import Submission.Work.FTS.EllSol.VthAux.AeClean.SliceThree
import Submission.Work.H2W.weakSliceZContinuousAe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VthAuxC

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
# `poinC` — the level-`4` angular Poincaré estimate for `ellShift α g Φg`

The target is the angular Poincaré estimate for the straightened unknown
`U = ellShift α g Φg` of a datum whose *weak* elliptic class is part of the hypotheses:

`EllWeakPos α 4 (orthSource g) U` supplies the equation, the Dirichlet data, the smoothness on the
open quadrant and the honesty `HkMem α 4 (∂_θ²U)`; the level-`4` angular Poincaré then gives
`HkMem α 4 U`, `HkMem α 4 (∂_θU)` and the two norm comparisons.

## Route

Apply the (proved) `Work.FTS.EllSol.ropPoincareAe`, which needs, besides the weak class, the two
endpoint *traces* of the radial iterates of the slices:

* for `j ≤ 3` at every `z > 0` (pointwise),
* for `j = 4` for almost every `z > 0`,

and the endpoint *values* `D_z^j U z 0 = D_z^j U z (π/2) = 0` for `j ≤ 4`.

The values come from the Dirichlet data (`VanishTheta`, transported by `D_z^j`, which differentiates
only in `z`).  The traces come from slice continuity plus those values; and slice continuity is
read off the weak class by *shifting it down*:

* `EllWeakPos_DzIter_one_shift_of_two_le` gives
  `EllWeakPos α 3 (D_z F) (D_z U)`, `EllWeakPos α 2 (D_z²F) (D_z²U)`, `EllWeakPos α 1 (D_z³F) (D_z³U)`;
* `AeClean.sliceContinuous_of_weakPos_fts` turns each of those into the pointwise continuity of
  the corresponding slice — this covers `j ≤ 3`;
* `H2W.weakSliceZContinuousAe` applied to the level-`2` shift gives the continuity of
  `D_z²(D_z²U) = D_z⁴U` on a conull set of `z` — this covers `j = 4`.

Neither the class `ClassC α g` nor the positivity of the solution nor the smoothness of `Φg` is
needed for this step; the weak class of the straightened unknown is exactly the honest budget.
-/

/-! ## Glue I: a slice which is continuous on `Iθ` and vanishes at an endpoint has limit `0` there

(Local copies of `tendsto_zero_of_continuousOn_Iθ_left/right`.) -/

theorem pc_tendsto_zero_left {u : ℝ → ℝ} (hc : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) :
    Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h1 : ContinuousWithinAt u Work.Spaces.Iθ 0 :=
    hc.continuousWithinAt (by rw [Work.Spaces.Iθ]; exact ⟨le_refl 0, by positivity⟩)
  have h2 : Tendsto u (nhdsWithin (0 : ℝ) Work.Spaces.Iθ) (nhds 0) := by
    simpa [h0] using h1.tendsto
  have hmem : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Iio (Real.pi / 2), ?_, ?_⟩
    · exact isOpen_Iio.mem_nhds (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])
    · intro x hx
      exact hx.1
  have heq : nhdsWithin (0 : ℝ) (Set.Iio (Real.pi / 2) ∩ Set.Ioi 0)
      = nhdsWithin (0 : ℝ) (Set.Ioi 0) := nhdsWithin_inter_of_mem hmem
  refine h2.mono_left ?_
  rw [← heq]
  exact nhdsWithin_mono 0 (fun θ hθ => ⟨le_of_lt hθ.2, le_of_lt hθ.1⟩)

theorem pc_tendsto_zero_right {u : ℝ → ℝ} (hc : ContinuousOn u Work.Spaces.Iθ)
    (h0 : u (Real.pi / 2) = 0) :
    Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have h1 : ContinuousWithinAt u Work.Spaces.Iθ (Real.pi / 2) :=
    hc.continuousWithinAt (by rw [Work.Spaces.Iθ]; exact ⟨by positivity, le_refl _⟩)
  have h2 : Tendsto u (nhdsWithin (Real.pi / 2) Work.Spaces.Iθ) (nhds 0) := by
    simpa [h0] using h1.tendsto
  have hmem : Set.Ioi (0 : ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Set.Ioi (0 : ℝ), ?_, ?_⟩
    · exact isOpen_Ioi.mem_nhds (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])
    · intro x hx
      exact hx.1
  have heq : nhdsWithin (Real.pi / 2) (Set.Ioi 0 ∩ Set.Iio (Real.pi / 2))
      = nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := nhdsWithin_inter_of_mem hmem
  refine h2.mono_left ?_
  rw [← heq]
  exact nhdsWithin_mono (Real.pi / 2) (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

/-! ## Glue II: the endpoint values of the radial iterates -/

theorem pc_dzIter_value_zero {f : ℝ → ℝ → ℝ} (hvan : Work.Spaces.VanishTheta f) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j f z 0 = 0
  | 0, z => hvan.1 z
  | j + 1, z => by
    show z * deriv (fun z' => Work.Spaces.DzIter j f z' 0) z = 0
    have h0 : (fun z' => Work.Spaces.DzIter j f z' 0) = fun _ => (0 : ℝ) :=
      funext fun z' => pc_dzIter_value_zero hvan j z'
    rw [h0]
    simp

theorem pc_dzIter_value_pi_half {f : ℝ → ℝ → ℝ} (hvan : Work.Spaces.VanishTheta f) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j f z (Real.pi / 2) = 0
  | 0, z => hvan.2 z
  | j + 1, z => by
    show z * deriv (fun z' => Work.Spaces.DzIter j f z' (Real.pi / 2)) z = 0
    have h0 : (fun z' => Work.Spaces.DzIter j f z' (Real.pi / 2)) = fun _ => (0 : ℝ) :=
      funext fun z' => pc_dzIter_value_pi_half hvan j z'
    rw [h0]
    simp

/-! ## The slice continuity of the radial iterates of a level-`4` weak datum -/

/-- **Pointwise slice continuity, `j ≤ 3`.**  For a datum of the weak class at level `4`, the
slices `θ ↦ D_z^jΨ z θ` are continuous on `Iθ` at *every* `z > 0`, for `j ≤ 3`.  (`D_z^j` is
differentiated only in the radial variable, so `D_z^jΨ` is again of the weak class at level
`4 - j ≥ 1`, and `sliceContinuous_of_weakPos_fts` applies.) -/
theorem pc_slice_continuous_le_three {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 4 F Ψ)
    (j : ℕ) (hj : j ≤ 3) (z : ℝ) (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ) Work.Spaces.Iθ := by
  have h3 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 4) (by norm_num) h
  have h2 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 3) (by norm_num) h3
  have h1 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 2) (by norm_num) h2
  interval_cases j
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllSol.VthAux.AeClean.sliceContinuous_of_weakPos_fts 4 (by norm_num) α F Ψ hα h z hz
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllSol.VthAux.AeClean.sliceContinuous_of_weakPos_fts 3 (by norm_num) α
        (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) hα h3 z hz
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllSol.VthAux.AeClean.sliceContinuous_of_weakPos_fts 2 (by norm_num) α
        (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 F))
        (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 Ψ)) hα h2 z hz
  · simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllSol.VthAux.AeClean.sliceContinuous_of_weakPos_fts 1 (by norm_num) α
        (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 F)))
        (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 Ψ))) hα h1 z hz

/-- A.e. statements on `Iz` which hold at every `z > 0` transfer to `Ioi 0` (the two sets differ
by the null set `{0}`). -/
theorem pc_ae_Ioi_of_ae_Iz {p : ℝ → Prop}
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z → p z) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), p z := by
  have h1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), 0 < z → p z :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioi_subset_Ici_self h
  filter_upwards [h1, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz hzmem
  exact hz (Set.mem_Ioi.mp hzmem)

/-- **Almost-everywhere slice continuity, `j = 4`.**  For a datum of the weak class at level `4`
(with `α ≤ 1/4`), the slice `θ ↦ D_z⁴Ψ z θ` is continuous on `Iθ` for almost every `z > 0`: the
level-`2` shift of the class has its second radial iterate controlled by
`H2W.weakSliceZContinuousAe`, and `D_z²(D_z²Ψ) = D_z⁴Ψ`. -/
theorem pc_slice_continuous_four_ae {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 4 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ContinuousOn (fun θ : ℝ => Work.Spaces.DzIter 4 Ψ z θ) Work.Spaces.Iθ := by
  have h3 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 4) (by norm_num) h
  have h2 := Work.FTS.EllipticEst.Cores.Repair.EllWeakPos_DzIter_one_shift_of_two_le
    (α := α) (k := 3) (by norm_num) h3
  have h4 := Work.H2W.weakSliceZContinuousAe α
    (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 F))
    (Work.Spaces.DzIter 1 (Work.Spaces.DzIter 1 Ψ)) hα hα4 h2
  refine pc_ae_Ioi_of_ae_Iz ?_
  filter_upwards [h4] with z hz
  intro hzpos
  have h4z := (hz hzpos).2
  simpa only [Work.Spaces.Iθ, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h4z

/-- **The endpoint traces of a level-`4` weak datum.**  The `j ≤ 3` traces hold at every `z > 0`
and the `j = 4` trace almost everywhere. -/
theorem pc_traces {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 4 F Ψ) :
    (∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ψ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) ∧
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 Ψ z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 Ψ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hvan : Work.Spaces.VanishTheta Ψ := ⟨h.zero, h.pi_half⟩
  refine ⟨fun j hj z hz => ?_, ?_⟩
  · exact ⟨pc_tendsto_zero_left (pc_slice_continuous_le_three hα h j hj z hz)
        (pc_dzIter_value_zero hvan j z),
      pc_tendsto_zero_right (pc_slice_continuous_le_three hα h j hj z hz)
        (pc_dzIter_value_pi_half hvan j z)⟩
  · filter_upwards [pc_slice_continuous_four_ae hα hα4 h] with z hz
    exact ⟨pc_tendsto_zero_left hz (pc_dzIter_value_zero hvan 4 z),
      pc_tendsto_zero_right hz (pc_dzIter_value_pi_half hvan 4 z)⟩

/-! ## The target -/

theorem poinC : ∃ C α₀ : ℝ, 0 < C ∧ 0 < α₀ ∧
    ∀ (α : ℝ) (g Φg : ℝ → ℝ → ℝ), 0 < α → α ≤ α₀ → Work.FTS.EllSol.ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg → Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
        (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α 4 (Work.FTS.EllSol.ellShift α g Φg) ∧
      Work.Spaces.HkMem α 4 (Work.Spaces.pth (Work.FTS.EllSol.ellShift α g Φg)) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.EllSol.ellShift α g Φg)
        ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg)) ∧
      Work.Spaces.HkNorm α 4 (Work.Spaces.pth (Work.FTS.EllSol.ellShift α g Φg))
        ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllSol.ropPoincareAe
  refine ⟨C, 1 / 4, hCpos, by norm_num, ?_⟩
  intro α g Φg hα hα4 _hcls _hsol _hsm hW
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨htr3, htr4⟩ := pc_traces (α := α) (F := Work.Elliptic.orthSource g)
    (Ψ := Work.FTS.EllSol.ellShift α g Φg) hα hα4 hW
  have hvan : Work.Spaces.VanishTheta (Work.FTS.EllSol.ellShift α g Φg) :=
    ⟨hW.zero, hW.pi_half⟩
  exact hC α (Work.FTS.EllSol.ellShift α g Φg) hα hα1 hW.smooth htr3 htr4
    (fun j _hj z _hz => ⟨pc_dzIter_value_zero hvan j z,
      pc_dzIter_value_pi_half hvan j z⟩) hW.memB

end

end Work.FTS.EllSol.VthAuxC
