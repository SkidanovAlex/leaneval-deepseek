/-
# `Work.FTS.Regularity.physVel_isContDiffHolder` — the *slice* form of the N7 transfer

The transfer theorem of node N7 states that the reconstructed velocity of a `RegPkg'` profile is
*jointly* `C^{1,α}` on the strip `ℝ³ × [0,S]`:

  `IsContDiffHolderOn ℝ ⟨α,_⟩ (physVel α A B g).uncurry (univ ×ˢ Icc 0 S)`,

which is the space–time Schauder estimate of `Work.CoreResiduals.BiotSavart` applied to the
vorticity bundle `BSAdmissibleStripFull α (physVort α A B g) R S`
(`Work.FTS.Regularity.physVort_bundle`).  The challenge's own clause, however, is the *ambient*
class of each time slice:

  `IsContDiffHolder ℝ ⟨α,_⟩ (fun x => physVel α A B g x τ)`.

This module performs that extraction, and it does so directly from the *Schauder estimate itself*
(`Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds`), with the vorticity held **constant in
time** at the slice `τ`.  That is the sharpest route: the space–time estimate only ever needs *one*
Hölder constant for the time-constant bundle, so of the whole N7 bundle only the three purely
*spatial* clauses of the slice are consumed here — compact support (`physVort_support`), uniform
boundedness (`physVort_bound`) and the slice `α`-Hölder estimate (`physVort_holder_slice`) — while
the time-differentiability clauses are satisfied by the constant field, whose `timeDeriv` vanishes
identically.

## The two ingredients

* `fderiv_slice_eq` / `isContDiffHolder_slice`: the strip `univ ×ˢ Icc 0 S` is a product whose
  first factor is *all* of `ℝ³`, so although `fderivWithin` on the strip differs from the ambient
  `fderiv` in the time slot (the strip has a boundary at `τ = 0` resp. `τ = S`), the *space* slot
  of the within-derivative is two-sided, hence is exactly the ambient derivative of the slice:

    `fderiv ℝ (fun x => F (x, τ)) x = (fderivWithin ℝ F (univ ×ˢ Icc 0 S) (x,τ)) ∘L inl`

  with `inl : ℝ³ →L ℝ³ × ℝ`, `v ↦ (v,0)`.  Since `‖inl‖ ≤ 1`, both the boundedness and the
  `α`-Hölder clause of `fderivWithin` pass to the ambient derivative of the slice *with the same
  constant*; the `C¹` clause is the pre-composition with the smooth embedding `x ↦ (x,τ)`, which
  maps `ℝ³` into the strip because `τ ∈ [0,S]`.
* `physVel_isContDiffHolder`: the vorticity slice is packed into the time-constant bundle
  `BSAdmissibleStripFull α (fun y _ => physVort α A B g y τ) R S`, the space–time Schauder estimate
  is applied to it, and the result is restricted to the slice by the extraction theorem.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.FireFix.Prime.physVort_support
import Submission.Work.FTS.FireFix.Prime.physVort_bound
import Submission.Work.FTS.FireFix.Prime.PhysVortHolderSlice
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds
import Submission.Work.FTS.RegPkgGal.Basic

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

/-- **The Schauder estimate at a single time slice.**  For `τ ∈ [0,S]`, the vorticity slice
`ω_τ = physVort α A B g · τ` — compactly supported, bounded and `α`-Hölder — is admissible for the
space–time Schauder estimate as the *time-constant* field `(y,s) ↦ ω_τ(y)`, whence the velocity
`BS ω_τ` is `C^{1,α}` on all of `ℝ³`.  (The endpoint clause `TimeDerivStrip` is satisfied because
the constant field has `timeDeriv = 0`.) -/
theorem physVel_slice_contDiffHolder {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    IsContDiffHolderOn ℝ (⟨α, h.hα.le⟩ : NNReal)
      (fun q : R3 × ℝ => Work.LWP.biotSavart (fun y => physVort α A B g y τ) q.1)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) S) := by
  have hα0 : 0 < ((⟨α, h.hα.le⟩ : NNReal) : ℝ) := by simpa using h.hα
  have hα1 : ((⟨α, h.hα.le⟩ : NNReal) : ℝ) < 1 := by
    have : α < 1 := by linarith [h.hα13]
    simpa using this
  obtain ⟨R, hR0, hsupp⟩ := physVort_support h
  obtain ⟨M, _hM0, hM⟩ := physVort_bound h
  obtain ⟨C, hC0, hC⟩ := physVort_holder_slice h
  set ω : R3 → ℝ → R3 := fun y _ => physVort α A B g y τ with hωdef
  -- the field is constant in the time slot: its time modulus and its time derivative vanish
  have hconst : ∀ (y : R3) (s : ℝ), ω y s = physVort α A B g y τ := fun _ _ => by
    simp only [hωdef]
  have hderiv : ∀ (y : R3) (s : ℝ), FiniteTimeSingularity.timeDeriv ω y s = 0 := by
    intro y s
    simp only [FiniteTimeSingularity.timeDeriv, hωdef, deriv_const]
  have hholder : ∀ s ∈ Set.Icc (0 : ℝ) S,
      HolderWith ⟨C, hC0⟩ (⟨α, h.hα.le⟩ : NNReal) (ω · s) := by
    intro s _
    refine Work.Stability.holderWith_of_dist_le (fun x y => ?_)
    have heq : dist (ω x s) (ω y s)
        = ‖physVort α A B g x τ - physVort α A B g y τ‖ := by
      rw [dist_eq_norm, hconst x s, hconst y s]
    calc dist (ω x s) (ω y s)
        = ‖physVort α A B g x τ - physVort α A B g y τ‖ := heq
      _ ≤ C * ‖x - y‖ ^ α := hC τ hτ x y
      _ = ((⟨C, hC0⟩ : NNReal) : ℝ) * dist x y ^ (((⟨α, h.hα.le⟩ : NNReal)) : ℝ) := by
          rw [dist_eq_norm]
  have haesm : ∀ s ∈ Set.Icc (0 : ℝ) S,
      MeasureTheory.AEStronglyMeasurable (ω · s) MeasureTheory.volume := by
    intro s _
    have hcont : Continuous (fun y : R3 => ω y s) := by
      refine Work.CoreResiduals.BiotSavart.continuous_of_holder h.hα hC0 (fun a b => ?_)
      rw [hconst a s, hconst b s]
      exact hC τ hτ a b
    exact hcont.aestronglyMeasurable
  have htd : ∀ s ∈ Set.Icc (0 : ℝ) S, ∀ y : R3,
      HasDerivAt (fun u : ℝ => ω y u) (FiniteTimeSingularity.timeDeriv ω y s) s := by
    intro s _ y
    rw [hderiv y s]
    simpa only [hconst] using hasDerivAt_const s (physVort α A B g y τ)
  have hbun : Work.CoreResiduals.BSAdmissibleStripFull (⟨α, h.hα.le⟩ : NNReal) ω R S := by
    refine ⟨⟨hR0, ?_, ⟨M, ?_⟩, ⟨⟨C, hC0⟩, hholder⟩, ⟨0, ?_⟩, haesm⟩, ⟨htd, ⟨0, ?_⟩, ?_⟩,
      ⟨0, ?_⟩⟩
    · intro s _ y hy
      exact hsupp τ hτ y (by simpa only [hconst y s] using hy)
    · intro s _ y
      simpa only [hconst y s] using hM τ hτ y
    · intro y s _ s' _
      simp only [hconst, sub_self, norm_zero]
      exact mul_nonneg le_rfl (Real.rpow_nonneg (abs_nonneg _) _)
    · intro s _ y
      simp [hderiv]
    · intro s _
      simpa only [hderiv] using
        (MeasureTheory.aestronglyMeasurable_const (b := (0 : R3)) (μ := MeasureTheory.volume))
    · intro y s _ s' _
      simp only [hderiv, sub_self, norm_zero]
      exact mul_nonneg le_rfl (Real.rpow_nonneg (abs_nonneg _) _)
  simpa only [hωdef] using
    (Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds hα0 hα1).2.2 ω R S h.hS hbun

theorem physVel_isContDiffHolder {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    IsContDiffHolder ℝ (⟨α, h.hα.le⟩ : NNReal)
      (fun x : Work.FTS.Regularity.R3 => Work.FTS.Regularity.physVel α A B g x τ) := by
  have hstrip := physVel_slice_contDiffHolder h hτ
  have hslice := isContDiffHolder_slice hτ (⟨α, h.hα.le⟩ : NNReal) hstrip
  simpa only [physVel] using hslice

end Work.FTS.FireFix.Prime
