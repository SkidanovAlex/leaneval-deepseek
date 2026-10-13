import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.AngAWeak.aeEnergyWAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeS1

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Slice tools for the level-`0` a.e. class -/

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
theorem ae_mem_Ioo_Iθ_fts :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have h : (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) : Measure ℝ)
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The unweighted angular square of a level-`0` honest function is integrable on `Iθ`: divide
the radial weight `(w z)²` out of the `w²`-weighted slice integrability supplied by `HkMem`. -/
theorem slice_sq_of_HkMem_fts {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sgU hmem hz

/-- **`AM–GM` for slice products**: the product of two functions whose angular squares are
integrable is integrable, provided it is a.e. strongly measurable on `Iθ`. -/
theorem slice_mul_of_sq_fts {f g : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ)
    (hm : MeasureTheory.AEStronglyMeasurable (fun θ => f θ * g θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => f θ * g θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' ((hf.add hg).const_mul (1 / 2)) hm ?_
  filter_upwards with θ
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f θ| - |g θ|), sq_abs (f θ), sq_abs (g θ)]

/-- A function continuous on the **open** quadrant has an a.e. strongly measurable angular slice
at every `z > 0` (the two endpoints of `Iθ` are a null set). -/
theorem aesm_slice_of_cont_fts {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hf : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.AngAWeak.Qd) :
    MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.FTS.EllipticEst.AngAWeak.aestronglyMeasurable_of_continuousOn_Ioo <|
    hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hθ => Work.FTS.EllipticEst.AngAWeak.mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩)

/-- **The six a.e. slice-integrability conditions of the truncated level-0 energy identity** for a
datum of the almost-everywhere class `H2W.Ae.AeData`: for almost every `z > 0`, the angular fibres
`θ ↦ bslOp α u z θ · u z θ`, `θ ↦ Lzero u z θ · u z θ`, `θ ↦ ∂_z²u z θ · u z θ`,
`θ ↦ ∂_zu z θ · u z θ`, `θ ↦ (z ∂_zu z θ)²` and `θ ↦ u z θ²` are integrable on `Iθ = [0,π/2]`.
This is the hypothesis `hslice` consumed by `H2W.AeW.aeTruncWHon` (the truncated energy identity)
and by `AngAWeak.CutEnergy.aeCutEnergyIneq` (the truncated energy inequality). -/
theorem aeSliceConds (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ := by
  -- in fact all six conditions hold for *every* `z > 0` (`hC` is not needed).
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  -- joint continuity of the angular slices on the open quadrant
  have hu_cont : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.AngAWeak.Qd :=
    (h.smooth 0).continuousOn_zero
  have hpz_cont : ContinuousOn (Function.uncurry (Work.Spaces.pz u))
      Work.FTS.EllipticEst.AngAWeak.Qd :=
    (Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ
      (U := Work.FTS.EllipticEst.AngAWeak.Qd)
      Work.FTS.EllipticEst.AngAWeak.isOpen_Qd (n := 0)
      (by simpa only [Work.FTS.EllipticEst.AngAWeak.Qd] using h.smooth 1)).continuousOn_zero
  have hpz2_cont : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 u))
      Work.FTS.EllipticEst.AngAWeak.Qd :=
    Work.FTS.EllipticEst.AngAWeak.continuousOn_uncurry_pzIter_two
      (fun n => by simpa only [Work.FTS.EllipticEst.AngAWeak.Qd] using h.smooth n)
  -- the degrees of freedom `u` and `z ∂_z u` are honest
  have hu_mem : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h
  have hg_mem : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  -- the angular squares
  have hU2 : MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
    slice_sq_of_HkMem_fts hu_mem hz
  have hG2 : MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2) Work.Spaces.Iθ :=
    slice_sq_of_HkMem_fts h.memG hz
  have hB2 : MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
      Work.Spaces.Iθ := by
    simpa only [Work.FTS.EllipticEst.H2W.Ae.grad] using slice_sq_of_HkMem_fts hg_mem hz
  have hR2 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2) Work.Spaces.Iθ :=
    slice_sq_of_HkMem_fts h.memRad2 hz
  have hP2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz u z θ) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_of_mul_const (c := z ^ 2)
      (pow_ne_zero 2 (ne_of_gt hz))
      (hB2.congr_fun (fun θ _ => by ring) measurableSet_Icc)
  have hP22 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pzIter 2 u z θ) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_of_mul_const (c := (z ^ 2) ^ 2)
      (pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz)))
      (hR2.congr_fun (fun θ _ => by ring) measurableSet_Icc)
  -- the products of two square-integrable slices
  have hGu : MeasureTheory.IntegrableOn (fun θ => G z θ * u z θ) Work.Spaces.Iθ :=
    slice_mul_of_sq_fts hG2 hU2
      ((Work.FTS.EllipticEst.AngAWeak.aesm_slice_G h hz).mul (aesm_slice_of_cont_fts hz hu_cont))
  have hPu : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ)
      Work.Spaces.Iθ :=
    slice_mul_of_sq_fts hP2 hU2
      ((aesm_slice_of_cont_fts hz hpz_cont).mul (aesm_slice_of_cont_fts hz hu_cont))
  have hP2u : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ)
      Work.Spaces.Iθ :=
    slice_mul_of_sq_fts hP22 hU2
      ((aesm_slice_of_cont_fts hz hpz2_cont).mul (aesm_slice_of_cont_fts hz hu_cont))
  -- `Lzero u · u` through the equation `Lzero u = G + α²z²∂_zzu + α(5+α)z∂_zu` on the quadrant
  have hLuu : MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
      Work.Spaces.Iθ := by
    have hsum : MeasureTheory.IntegrableOn (fun θ => G z θ * u z θ
        + ((α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 u z θ * u z θ)
          + (α * (5 + α) * z) * (Work.Spaces.pz u z θ * u z θ))) Work.Spaces.Iθ :=
      hGu.add ((hP2u.const_mul _).add (hPu.const_mul _))
    refine hsum.congr ?_
    filter_upwards [ae_mem_Ioo_Iθ_fts] with θ hθ
    have hbsl : Work.Elliptic.bslOp α u z θ = G z θ := h.eq z hz θ hθ.1 hθ.2
    have hkey : Work.Elliptic.Lzero u z θ = G z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + (α * (5 + α) * z) * Work.Spaces.pz u z θ := by
      rw [← hbsl, Work.Elliptic.bslOp_apply]; ring
    rw [hkey]; ring
  -- `bslOp α u · u = G · u` on *all* of `Iθ` (both products vanish at the two endpoints)
  have hBuu : MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
      Work.Spaces.Iθ := by
    refine hGu.congr_fun (fun θ hθ => ?_) measurableSet_Icc
    show G z θ * u z θ = Work.Elliptic.bslOp α u z θ * u z θ
    by_cases h0 : θ = 0
    · rw [h0, Work.FTS.EllipticEst.H2W.Ae.AeData.dirZero h z]; ring
    · by_cases hpi : θ = Real.pi / 2
      · rw [hpi, Work.FTS.EllipticEst.H2W.Ae.AeData.dirPi h z]; ring
      · rw [h.eq z hz θ (lt_of_le_of_ne hθ.1 (Ne.symm h0)) (lt_of_le_of_ne hθ.2 hpi)]
  exact ⟨hBuu, hLuu, hP2u, hPu, hB2, hU2⟩

end

end Work.FTS.EllipticEst.AeS1
