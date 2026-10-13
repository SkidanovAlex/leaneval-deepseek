import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeEnergyWAux
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeW2SliceBundle` — the a.e. slice integrability bundle of the level-`0` a.e. class

For a datum `AeData α u G` of the almost-everywhere class of the level-`0` elliptic estimate,
for almost every `z > 0` the six angular fibres occurring in the truncated level-`0` energy
identity are integrable on `Iθ = [0,π/2]`:

`bslOp α u · u`, `Lzero u · u`, `∂_zzu · u`, `∂_zu · u`, `(z ∂_zu)²`, `u²`.

The proof is *pointwise in `z`* (the a.e. statement is therefore immediate): for `z > 0`

* the unweighted angular squares of `u`, `∂_zu` and `∂_zzu` are integrable because
  `HkMem α 0` of `u` (`Dispatch.hkMem_uM`), of `z ∂_zu` (`Dispatch.hkMem_gradUD`) and of
  `z²∂_zzu` (a field of `AeData`) gives the *weighted* integrability
  (`AngAWeak.integrableOn_slice_sq_mul_w_sq`), and the weight `w z ≠ 0` may be divided out;
  `G` is the same with the field `AeData.memG`;
* the products `G·u`, `(∂_zu)·u`, `(∂_zzu)·u` follow from `2|XY| ≤ X² + Y²` and the continuity
  of the slices on the open angular interval;
* `Lzero u · u` is *not* obtained from the `tan θ`-form of `Lzero` (whose middle term is not
  controlled by the available squares) but from the identity
  `Lzero u = G + α²z²∂_zzu + α(5+α)z∂_zu` on the open quadrant, which is `bslOp α u = G`
  (`AeData.eq`) rearranged;
* `bslOp α u · u` agrees with `G·u` on *all* of `Iθ`, since at the two endpoints the factor `u`
  vanishes (`AeData.dirZero`, `AeData.dirPi`) so both products are `0`.
-/

namespace Work.FTS.EllipticEst.Cores.Pieces

open MeasureTheory Set Filter

set_option autoImplicit false

/-- The unweighted angular square of a level-`0` honest function is integrable on `Iθ`, for
`z > 0`: divide the weight `(w z)²` out of `AngAWeak.integrableOn_slice_sq_mul_w_sq`. -/
private theorem aew2_integrableOn_sq_of_HkMem {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_mul_w_sq hmem (le_of_lt hz)).1.congr_fun
      (fun θ _ => by ring) measurableSet_Icc
  exact Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_of_mul_const hw h1

/-- `AM–GM` for a product of two functions whose angular squares are integrable. -/
private theorem aew2_integrableOn_mul_of_sq {f g : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2) Work.Spaces.Iθ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => f θ * g θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => f θ * g θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' ((hf.add hg).const_mul (1 / 2)) hmeas ?_
  filter_upwards with θ
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f θ| - |g θ|), sq_abs (f θ), sq_abs (g θ)]

/-- A function continuous on the **open** quadrant has an a.e. strongly measurable angular
slice at every `z > 0`. -/
private theorem aew2_aesm_slice {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hf : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.AngAWeak.Qd) :
    MeasureTheory.AEStronglyMeasurable (fun θ => f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  Work.FTS.EllipticEst.AngAWeak.aestronglyMeasurable_of_continuousOn_Ioo <| by
    have hc : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry f p)
        Work.FTS.EllipticEst.AngAWeak.Qd := hf
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun θ hθ => Work.FTS.EllipticEst.AngAWeak.mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩)

theorem AeW2SliceBundle (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2) Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ := by
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  -- joint continuity of the slices on the open quadrant
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
  -- the degrees of freedom `u`, `z ∂_zu` are honest
  have hu_mem : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h
  have hg_mem : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  -- the angular squares
  have hU2 : MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
    aew2_integrableOn_sq_of_HkMem hu_mem hz
  have hG2 : MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2) Work.Spaces.Iθ :=
    aew2_integrableOn_sq_of_HkMem h.memG hz
  have hB2 : MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
      Work.Spaces.Iθ := by
    simpa only [Work.FTS.EllipticEst.H2W.Ae.grad] using aew2_integrableOn_sq_of_HkMem hg_mem hz
  have hR2 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2) Work.Spaces.Iθ :=
    aew2_integrableOn_sq_of_HkMem h.memRad2 hz
  have hP2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz u z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_of_mul_const (c := z ^ 2)
      (pow_ne_zero 2 (ne_of_gt hz))
      (hB2.congr_fun (fun θ _ => by ring) measurableSet_Icc)
  have hP22 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pzIter 2 u z θ) ^ 2)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_of_mul_const (c := (z ^ 2) ^ 2)
      (pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz)))
      (hR2.congr_fun (fun θ _ => by ring) measurableSet_Icc)
  -- the products
  have hGu : MeasureTheory.IntegrableOn (fun θ => G z θ * u z θ) Work.Spaces.Iθ :=
    aew2_integrableOn_mul_of_sq hG2 hU2
      ((Work.FTS.EllipticEst.AngAWeak.aesm_slice_G h hz).mul (aew2_aesm_slice hz hu_cont))
  have hPu : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ)
      Work.Spaces.Iθ :=
    aew2_integrableOn_mul_of_sq hP2 hU2
      ((aew2_aesm_slice hz hpz_cont).mul (aew2_aesm_slice hz hu_cont))
  have hP2u : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ)
      Work.Spaces.Iθ :=
    aew2_integrableOn_mul_of_sq hP22 hU2
      ((aew2_aesm_slice hz hpz2_cont).mul (aew2_aesm_slice hz hu_cont))
  -- `Lzero u · u` through the equation `Lzero u = G + α²z²∂_zzu + α(5+α)z∂_zu`
  have hLuu : MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
      Work.Spaces.Iθ := by
    have hsum : MeasureTheory.IntegrableOn (fun θ => G z θ * u z θ
        + ((α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 u z θ * u z θ)
          + (α * (5 + α) * z) * (Work.Spaces.pz u z θ * u z θ))) Work.Spaces.Iθ :=
      hGu.add ((hP2u.const_mul _).add (hPu.const_mul _))
    refine hsum.congr ?_
    filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hθ
    have hbsl : Work.Elliptic.bslOp α u z θ = G z θ := h.eq z hz θ hθ.1 hθ.2
    have hkey : Work.Elliptic.Lzero u z θ = G z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + (α * (5 + α) * z) * Work.Spaces.pz u z θ := by
      rw [← hbsl, Work.Elliptic.bslOp_apply]; ring
    rw [hkey]; ring
  -- `bslOp α u · u = G · u` on all of `Iθ` (both products vanish at the endpoints)
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

end Work.FTS.EllipticEst.Cores.Pieces
