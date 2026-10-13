/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular energy of the slice `z²∂_z²Ψ` is finite

The requested lemma `Work.H2W.asliceLzero1Energy`: for a datum `(F, Ψ)` of the weak class
`TT.EllWeakPos α 2 F Ψ` and every `z > 0`, the angular slice

  `θ ↦ (Lzero1 (fun θ' => z² ∂_z²Ψ (z,θ')) θ)² · sin(2θ)^{-η}`

is integrable on `Iθ = [0, π/2]`.

## Why it is true, and the route

`Lzero1 = -∂_θθ + ∂_θ(tan θ ·) - 6` is the `θ`-slice of the angular operator `Lzero` of the
elliptic section; applied to the *second radial slice* `z²∂_z²Ψ` it would at first sight need
two angular derivatives of `z²∂_z²Ψ` with the singular coefficients `tan θ`, `sec²θ`, which the
weak class does not control at the endpoints (Ψ is only smooth on the *open* quadrant).  The
cancellation is that `bslOp α` commutes with the radial operator `z²∂_z²`
(`H2W.bslOp_zsq_pzIter2`), so on the open quadrant

  `Lzero (z²∂_z²Ψ) = z²∂_z²F + α² D_z²(z²∂_z²Ψ) + 5α D_z(z²∂_z²Ψ)`     (`D_z = z∂_z`),

and `z²∂_z²F = D_z²F - D_zF`.  Every term on the right is a pure `D_z`-slot of one of the three
`HkMem` fields of the weak class, so its `η`-weighted square is integrable on the angular slice
(`SourceBound.integrableOn_DzIter_sq_mul_sEta`), which is exactly what `HkMem α 2` records.

## Contents

* `sliceQ Ψ = z²∂_z²Ψ` and `sliceBF α Ψ`, the smooth representative of the right-hand side;
* `zsq_pzIter2_bslOp_eq` : `z²∂_z²(bslOp α Ψ) = D_z²F - D_zF` on the open quadrant;
* `Lzero1_slice_eq_sliceBF` : the identity above, in the form consumed below;
* `asliceLzero1Energy` : the target.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceSlots
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.H2W.momentChainAe
import Submission.Work.FTS.EllipticEst.remov.SourceBound.integrableOn_DzIter_sq_mul_sEta
import Submission.Work.FTS.EllipticEst.remov.SourceBound.aesm_F_slots
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open
import Submission.Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2
import Submission.Work.FTS.EllipticEst.remov.SourceBound.SliceAlgebra
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceAesmSq
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The twice radially differentiated slice -/

/-- `sliceQ Ψ = z² ∂_z²Ψ`, the second radially differentiated slice of `Ψ`. -/
def sliceQ (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- `z²∂_z²Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_sliceQ {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (sliceQ Ψ) :=
  Work.FTS.EllipticEst.remov.SourceBound.smoothOpen_zsq_mul_pzIter_two h

/-- The smooth representative of the right-hand side of the identity of the module docstring:
`z²∂_z²(bslOp α Ψ) + α²D_z²(z²∂_z²Ψ) + 5αD_z(z²∂_z²Ψ)`, with the source replaced by the
`C^∞` function `bslOp α Ψ` (which agrees with `F` on the open quadrant only). -/
def sliceBF (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
    + α ^ 2 * Work.Spaces.DzIter 2 (sliceQ Ψ) z θ
    + 5 * α * Work.Spaces.DzIter 1 (sliceQ Ψ) z θ

/-- `sliceBF α Ψ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_sliceBF (α : ℝ) {Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (sliceBF α Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ) :=
    Work.FTS.EllipticEst.remov.SourceBound.smoothOpen_zsq_mul_pzIter_two
      (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen h)
  have h2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 2 (sliceQ Ψ)) :=
    (smoothOpen_sliceQ h).DzIter 2
  have h3 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 (sliceQ Ψ)) :=
    (smoothOpen_sliceQ h).DzIter 1
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl h1
        (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) h2))
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (5 * α) h3)) ?_
  intro z θ _ _ _
  rfl

/-! ## The two algebraic identities on the open quadrant -/

/-- **The radial identity for the source.**  On the open quadrant, where `bslOp α Ψ = F`, one has
`z²∂_z²(bslOp α Ψ) = z²∂_z²F`, and since `z²∂_z²g = D_z²g - D_zg` for `C^∞` `g`
(`AgmonSlice.zsq_pzIter2_eq_open`), also `z²∂_z²(bslOp α Ψ) = D_z²F - D_zF`. -/
theorem zsq_pzIter2_bslOp_eq (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hSO : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
        = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hSO
  have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
      = Work.Spaces.DzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
        - Work.Spaces.DzIter 1 (Work.Elliptic.bslOp α Ψ) z θ := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open (Work.Elliptic.bslOp α Ψ) hFso hz hθ
  rw [h1, Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := Work.Elliptic.bslOp α Ψ)
      (G := F) heq 2 z θ hz hθ0 hθ1,
    Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := Work.Elliptic.bslOp α Ψ)
      (G := F) heq 1 z θ hz hθ0 hθ1]

/-- **The source identity for the twice radially differentiated slice.**  On the open quadrant,

  `Lzero (z²∂_z²Ψ) = D_z²F - D_zF + α² D_z²(z²∂_z²Ψ) + 5α D_z(z²∂_z²Ψ)`,

equivalently `Lzero1 (fun θ' => z²∂_z²Ψ (z,θ')) θ = sliceBF α Ψ z θ`.  This is the identity
that removes the singular angular coefficients of `Lzero1`. -/
theorem Lzero1_slice_eq_sliceBF (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hSO : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Lzero1 (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
        = sliceBF α Ψ z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hQso : Work.FTS.EllipticEst.SmoothOpen (sliceQ Ψ) := smoothOpen_sliceQ hSO
  have hBF : z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ
      = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ :=
    zsq_pzIter2_bslOp_eq α F Ψ heq hSO z θ hz hθ0 hθ1
  -- the equation for the `z²∂_z²`-slice, from the commutation of `bslOp α` with `z²∂_z²`
  have hbsl : Work.Elliptic.bslOp α (sliceQ Ψ) z θ = z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
    change Work.Elliptic.bslOp α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 F z θ
    exact
      Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2 α F Ψ
        (fun z hz' θ hθ0' hθ1' => heq z θ hz' hθ0' hθ1')
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hSO) z hz θ hθ0 hθ1
  -- `Lzero` expressed through `bslOp`, in the `z²∂_z²` form of each radial slot
  have hlin : Work.Elliptic.Lzero (sliceQ Ψ) z θ
      = Work.Elliptic.bslOp α (sliceQ Ψ) z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (sliceQ Ψ) z θ)
        + (α * (5 + α)) * (z * Work.Spaces.pz (sliceQ Ψ) z θ) := by
    simp only [Work.Elliptic.bslOp_apply]
    ring
  have hQ2 : z ^ 2 * Work.Spaces.pzIter 2 (sliceQ Ψ) z θ
      = Work.Spaces.DzIter 2 (sliceQ Ψ) z θ - Work.Spaces.DzIter 1 (sliceQ Ψ) z θ := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open (sliceQ Ψ) hQso hz hθ
  have hz1 : z * Work.Spaces.pz (sliceQ Ψ) z θ = Work.Spaces.DzIter 1 (sliceQ Ψ) z θ := rfl
  have hF2 : z ^ 2 * Work.Spaces.pzIter 2 F z θ
      = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := by
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 F z θ
        = z ^ 2 * Work.Spaces.pzIter 2 (Work.Elliptic.bslOp α Ψ) z θ := by
      congr 1
      refine Work.Elliptic.pzIter_congr_nhds 2 ?_
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact (heq z' θ hz' hθ0 hθ1).symm
    rw [h1, hBF]
  have hstep : Work.FTS.EllipticEst.Lzero1 (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ
      = Work.Elliptic.Lzero (sliceQ Ψ) z θ :=
    Work.FTS.EllipticEst.remov.Lzero1_slice_eq (sliceQ Ψ) z θ
  rw [hstep, hlin, hbsl, hF2, hQ2, hz1]
  simp only [sliceBF]
  rw [hBF]
  ring

/-! ## Elementary square bounds -/

private theorem add_sq_le_three_aux (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

private theorem sub_sq_le_two_aux (a b : ℝ) : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a + b)]

/-! ## The target -/

theorem asliceLzero1Energy (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1
          (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  intro z hz
  have hSO : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hQso : Work.FTS.EllipticEst.SmoothOpen (sliceQ Ψ) := smoothOpen_sliceQ hSO
  have hBFso : Work.FTS.EllipticEst.SmoothOpen (sliceBF α Ψ) := smoothOpen_sliceBF α hSO
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hSO
  have heq : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ :=
    fun z θ hz' hθ0 hθ1 => h.eq z hz' θ hθ0 hθ1
  have hid := Lzero1_slice_eq_sliceBF α F Ψ heq hSO
  have hBF := zsq_pzIter2_bslOp_eq α F Ψ heq hSO
  -- a.e. strong measurability of the target integrand, from the `C^∞` representative
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.FTS.EllipticEst.Lzero1
          (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (Work.FTS.EllipticEst.remov.SourceBound.aesm_slice_sq_mul_sEta
      hBFso.continuousOn hz).congr ?_
    filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
    rw [hid z θ hz hθ.1 hθ.2]
  -- the four `D_z`-slots of the three `HkMem` fields
  have hmemQ : Work.Spaces.HkMem α 2 (sliceQ Ψ) := h.memA
  have hAESM_Q : ∀ i : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.Spaces.DzIter i (sliceQ Ψ) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun i => Work.FTS.EllipticEst.remov.SourceBound.aesm_slice_sq_mul_sEta
      ((hQso.DzIter i).continuousOn) hz
  have hAESM_F : ∀ i : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.Spaces.DzIter i F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro i
    refine (Work.FTS.EllipticEst.remov.SourceBound.aesm_slice_sq_mul_sEta
      ((hFso.DzIter i).continuousOn) hz).congr ?_
    filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
    rw [← Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (F := Work.Elliptic.bslOp α Ψ)
      (G := F) heq i z θ hz hθ.1 hθ.2]
  have hintQ : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter i (sliceQ Ψ) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    fun i hi => Work.FTS.EllipticEst.remov.SourceBound.integrableOn_DzIter_sq_mul_sEta
      hmemQ i hi hz (hAESM_Q i)
  have hintF : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter i F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    fun i hi => Work.FTS.EllipticEst.remov.SourceBound.integrableOn_DzIter_sq_mul_sEta
      h.memF i hi hz (hAESM_F i)
  -- the pointwise majorant
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => 3 * (((2 * ((Work.Spaces.DzIter 2 F z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
          + 2 * ((Work.Spaces.DzIter 1 F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          + α ^ 4 * ((Work.Spaces.DzIter 2 (sliceQ Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ))
        + 25 * α ^ 2 * ((Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ))) Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => 2 * ((Work.Spaces.DzIter 2 F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        Work.Spaces.Iθ := (hintF 2 le_rfl).const_mul 2
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => 2 * ((Work.Spaces.DzIter 1 F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        Work.Spaces.Iθ := (hintF 1 (by norm_num)).const_mul 2
    have h3 : MeasureTheory.IntegrableOn
        (fun θ => α ^ 4 * ((Work.Spaces.DzIter 2 (sliceQ Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iθ :=
      (hintQ 2 le_rfl).const_mul (α ^ 4)
    have h4 : MeasureTheory.IntegrableOn
        (fun θ => 25 * α ^ 2 * ((Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iθ :=
      (hintQ 1 (by norm_num)).const_mul (25 * α ^ 2)
    have hsum := (((h1.add h2).add h3).add h4).const_mul 3
    exact hsum
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
  have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.remov.SourceBound.sEta_nonneg_Ioo hθ
  rw [hid z θ hz hθ.1 hθ.2, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hs)]
  simp only [sliceBF]
  rw [hBF z θ hz hθ.1 hθ.2]
  have hfin : (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ
        + α ^ 2 * Work.Spaces.DzIter 2 (sliceQ Ψ) z θ
        + 5 * α * Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2
      ≤ 3 * ((2 * (Work.Spaces.DzIter 2 F z θ) ^ 2
            + 2 * (Work.Spaces.DzIter 1 F z θ) ^ 2)
          + α ^ 4 * (Work.Spaces.DzIter 2 (sliceQ Ψ) z θ) ^ 2
          + 25 * α ^ 2 * (Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2) := by
    have h3 := add_sq_le_three_aux (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ)
      (α ^ 2 * Work.Spaces.DzIter 2 (sliceQ Ψ) z θ)
      (5 * α * Work.Spaces.DzIter 1 (sliceQ Ψ) z θ)
    have h2 := sub_sq_le_two_aux (Work.Spaces.DzIter 2 F z θ) (Work.Spaces.DzIter 1 F z θ)
    nlinarith [h3, h2]
  calc (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ
        + α ^ 2 * Work.Spaces.DzIter 2 (sliceQ Ψ) z θ
        + 5 * α * Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      ≤ 3 * ((2 * (Work.Spaces.DzIter 2 F z θ) ^ 2
            + 2 * (Work.Spaces.DzIter 1 F z θ) ^ 2)
          + α ^ 4 * (Work.Spaces.DzIter 2 (sliceQ Ψ) z θ) ^ 2
          + 25 * α ^ 2 * (Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2)
        * Work.FTS.EllipticEst.sEta θ := mul_le_mul_of_nonneg_right hfin hs
    _ = 3 * (((2 * ((Work.Spaces.DzIter 2 F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 2 * ((Work.Spaces.DzIter 1 F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          + α ^ 4 * ((Work.Spaces.DzIter 2 (sliceQ Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ))
        + 25 * α ^ 2 * ((Work.Spaces.DzIter 1 (sliceQ Ψ) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)) := by
        ring

end Work.H2W
