import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds
import Submission.Work.FTS.FireFix.Prime.PhysVortHolderSlice
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.Stability.holderWith_of_dist_le
-- ===== merged: Submission.Work.FTS.FireFix.Prime.physVel_isContDiffHolder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set

set_option autoImplicit false

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

/-! ## The embedding of a time slice -/

/-- The injection of the space slot, `inl : ℝ³ →L[ℝ] ℝ³ × ℝ`, `v ↦ (v, 0)`; it is the derivative
of the slice embedding `x ↦ (x, τ)`. -/
def sliceIncl : R3 →L[ℝ] R3 × ℝ := ContinuousLinearMap.inl ℝ R3 ℝ

@[simp] theorem sliceIncl_apply (v : R3) : sliceIncl v = (v, 0) := rfl

theorem norm_sliceIncl_le_one : ‖sliceIncl‖ ≤ 1 := by
  simpa only [sliceIncl] using
    (ContinuousLinearMap.norm_inl_le_one (𝕜 := ℝ) (E := R3) (F := ℝ))

theorem hasFDerivAt_sliceEmb (τ : ℝ) (x : R3) :
    HasFDerivAt (fun x : R3 => (x, τ)) sliceIncl x := by
  simpa only [sliceIncl] using hasFDerivAt_prodMk_left (𝕜 := ℝ) x τ

/-! ## The space slot of the within-derivative on the strip is the derivative of the slice -/

/-- **The identification of the derivative of a time slice.**  For `τ ∈ [0,S]` and `F` any field on
the spacetime, the ambient derivative of the slice `x ↦ F (x,τ)` is the space slot (i.e. the
composition with `inl`) of the within-derivative of `F` on the strip `univ ×ˢ Icc 0 S`.

Nothing about the strip beyond `τ ∈ [0,S]` is used: the embedding `x ↦ (x,τ)` maps `ℝ³` into the
strip, and along it the strip is *open* in the space direction, so the within-derivative in that
direction is two-sided. -/
theorem fderiv_slice_eq {S τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) {F : R3 × ℝ → R3} {x : R3}
    (hdiff : DifferentiableWithinAt ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ)) :
    fderiv ℝ (fun x : R3 => F (x, τ)) x
      = (fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ)) ∘L sliceIncl := by
  have hF' : HasFDerivWithinAt F (fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ) := hdiff.hasFDerivWithinAt
  have hE' : HasFDerivWithinAt (fun x : R3 => (x, τ)) sliceIncl Set.univ x :=
    (hasFDerivAt_sliceEmb τ x).hasFDerivWithinAt
  have hmap : Set.MapsTo (fun x : R3 => (x, τ)) Set.univ (Set.univ ×ˢ Set.Icc (0 : ℝ) S) :=
    fun _ _ => ⟨trivial, hτ⟩
  have hcomp : HasFDerivWithinAt (fun x : R3 => F (x, τ))
      ((fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ)) ∘L sliceIncl) Set.univ x :=
    HasFDerivWithinAt.comp x hF' hE' hmap
  have h := hcomp.fderivWithin (uniqueDiffWithinAt_univ (𝕜 := ℝ) (x := x))
  rwa [fderivWithin_univ] at h

/-! ## The extraction of a slice from the strip statement -/

/-- **`IsContDiffHolderOn` on a full-space strip restricts to `IsContDiffHolder` on each time
slice.**  If `F` is jointly `C^{1,α}` on `ℝ³ × [0,S]` (in the within-the-set sense), then for every
`τ ∈ [0,S]` the slice `x ↦ F (x,τ)` is `C^{1,α}` on all of `ℝ³` in the *ambient* sense, with the
same Hölder exponent and the same (or smaller) constant. -/
theorem isContDiffHolder_slice {S τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) (α : NNReal) {F : R3 × ℝ → R3}
    (h : IsContDiffHolderOn ℝ α F (Set.univ ×ˢ Set.Icc (0 : ℝ) S)) :
    IsContDiffHolder ℝ α (fun x : R3 => F (x, τ)) := by
  have hsmooth : ContDiffOn ℝ 1 F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) := h.1
  have hmem : ∀ x : R3, (x, τ) ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) S := fun _ => ⟨trivial, hτ⟩
  have hdiff : ∀ x : R3, DifferentiableWithinAt ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ) :=
    fun x => (hsmooth (x, τ) (hmem x)).differentiableWithinAt one_ne_zero
  have key : ∀ x : R3, fderiv ℝ (fun x : R3 => F (x, τ)) x
      = (fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ)) ∘L sliceIncl :=
    fun x => fderiv_slice_eq hτ (hdiff x)
  refine ⟨?_, ?_, ?_⟩
  · -- the `C¹` block: pre-compose with the smooth embedding `x ↦ (x,τ)`
    have hemb : ContDiff ℝ 1 (fun x : R3 => (x, τ)) :=
      (contDiff_id (𝕜 := ℝ)).prodMk (contDiff_const (c := τ))
    have h2 : ContDiffOn ℝ 1 (fun x : R3 => F (x, τ)) Set.univ :=
      hsmooth.comp hemb.contDiffOn (fun _ _ => hmem _)
    exact contDiffOn_univ.mp h2
  · -- the boundedness block: the within-derivative is bounded on the strip
    have hbdd : Bornology.IsBounded
        ((fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S)) ''
          (Set.univ ×ˢ Set.Icc (0 : ℝ) S)) := h.2.1
    obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hbdd
    refine isBounded_iff_forall_norm_le.mpr ⟨B * ‖sliceIncl‖, ?_⟩
    rintro _ ⟨x, -, rfl⟩
    rw [key x]
    calc ‖fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ) ∘L sliceIncl‖
        ≤ ‖fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ)‖ * ‖sliceIncl‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B * ‖sliceIncl‖ :=
          mul_le_mul_of_nonneg_right (hB _ ⟨(x, τ), hmem x, rfl⟩) (norm_nonneg _)
  · -- the Hölder block: the two space slots differ by at most the full within-derivatives
    obtain ⟨C, hC⟩ := h.2.2
    refine ⟨C, Work.Stability.holderWith_of_dist_le (r := α) (fun x y => ?_)⟩
    have hL : dist (fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ))
        (fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (y, τ))
        ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
      have h1 := hC.dist_le (x := (x, τ)) (y := (y, τ)) (hmem x) (hmem y)
      have h2 : dist (x, τ) (y, τ) = dist x y := by
        rw [Prod.dist_eq]
        simp only [dist_self]
        exact max_eq_left dist_nonneg
      rwa [h2] at h1
    rw [dist_eq_norm, key x, key y, ← ContinuousLinearMap.sub_comp]
    calc ‖(fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ)
          - fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (y, τ)) ∘L sliceIncl‖
        ≤ ‖fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ)
            - fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (y, τ)‖ * ‖sliceIncl‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = dist (fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, τ))
            (fderivWithin ℝ F (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (y, τ)) * ‖sliceIncl‖ := by
          rw [dist_eq_norm]
      _ ≤ ((C : ℝ) * dist x y ^ (α : ℝ)) * 1 :=
          mul_le_mul hL norm_sliceIncl_le_one (norm_nonneg _) (by positivity)
      _ = (C : ℝ) * dist x y ^ (α : ℝ) := by ring

/-! ## The time-constant vorticity bundle and the slice transfer -/



end Work.FTS.FireFix.Prime
end
end
-- ===== merged: Submission.Work.FTS.Physical.BiotSavart.contDiffOn_uncurry_ico =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

set_option linter.unusedVariables false

namespace Work.FTS.Physical.BiotSavart



end Work.FTS.Physical.BiotSavart
end
