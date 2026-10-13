/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability bookkeeping for the angular Poincaré estimate in the `C^∞` class

This module collects the measure-theoretic inputs of the per-`z` comparison
`HkIntegrand_integral_le_pth2_open`:

* `Sfun α θ = sin(2θ)^{-η} + sin(2θ)^{2-γ} + sin(2θ)^{4-γ}` — the fixed integrable angular
  weight produced by the boundary conditions in `slicePhi` (with `Sfun_nonneg`,
  `integrableOn_Sfun`, `integral_Sfun_le`);
* `ae_eq_of_forall_Ioo` — an equality that holds at every interior angle holds a.e. on `Iθ`
  (the two endpoints are null): this is how the per-`z` pointwise comparison, which needs the
  operators' Clairaut identities only on the open quadrant, is turned into an a.e. bound;
* `integrableOn_HkIntegrand_terms_open` — the `C^∞` version of
  `Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms`: the individual summands of the
  integrand are integrable as soon as the full integrand is and the angular slices of the
  iterates are continuous (the analytic `Work.Spaces.SmoothNbhd` hypothesis of the original is
  used there only for that continuity);
* `slice_data_integrable_of_HkIntegrand_open` — the `C^∞` version of
  `Blocks.slice_data_integrable_of_HkIntegrand`: for `f : SmoothOpenθ` and `z > 0`, the
  integrability (on `Iθ`) of the weighted derivatives `D_z^j (∂_θ² f)` and `D_z^j D_θ^m (∂_θ² f)`
  — i.e. exactly the integrability input of the slice estimates for the slice
  `u_j = θ' ↦ D_z^j f z θ'` — follows from the integrability of the full `ℋ^k`-integrand of
  `∂_θ² f` at the level `z`, by stripping the radial weight `(w z)²` and using the
  identifications `ThetaU.sliceV_DzIter_open` / `ThetaU.LopIter_sliceV_DzIter_eq_mixed_open`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceIdents
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

variable {f : ℝ → ℝ → ℝ}

/-! ## The fixed angular weight `Sfun` -/

/-- `Sfun α θ = sin(2θ)^{-η} + sin(2θ)^{2-γ} + sin(2θ)^{4-γ}`: the three fixed integrable
terms attached to `sliceA u` in `slicePhi`. -/
def Sfun (α θ : ℝ) : ℝ :=
  Work.FTS.EllipticEst.thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
    + (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)

theorem Sfun_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Sfun α θ := by
  rw [Sfun]
  exact add_nonneg (add_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ)
    (Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hθ) _))
    (Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hθ) _)

private lemma gam_le_two {α : ℝ} (hα : α ≤ 1) : 0 ≤ 2 - Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

private lemma gam_le_four {α : ℝ} (hα : α ≤ 1) : 0 ≤ 4 - Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

theorem integrableOn_Sfun {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (Sfun α) Work.Spaces.Iθ := by
  have h1 := Work.FTS.EllipticEst.integrableOn_thEta.1
  have h2 := (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (gam_le_two hα1)).1
  have h3 := (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (gam_le_four hα1)).1
  unfold Sfun
  exact (h1.add h2).add h3

theorem integral_Sfun_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∫ θ in Work.Spaces.Iθ, Sfun α θ) ≤ 10000 + Real.pi := by
  have h1 := Work.FTS.EllipticEst.integrableOn_thEta
  have h2 := Work.FTS.EllipticEst.integrableOn_sin_two_rpow (gam_le_two hα1)
  have h3 := Work.FTS.EllipticEst.integrableOn_sin_two_rpow (gam_le_four hα1)
  have h12 : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ := h1.1.add h2.1
  unfold Sfun
  rw [MeasureTheory.integral_add (f := fun θ =>
        Work.FTS.EllipticEst.thEta θ + (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (g := fun θ => (Real.sin (2 * θ)) ^ (4 - Work.Spaces.gam α)) h12 h3.1,
    MeasureTheory.integral_add (f := Work.FTS.EllipticEst.thEta)
      (g := fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) h1.1 h2.1]
  linarith [h1.2, h2.2, h3.2, Real.pi_pos]

/-! ## Interior equalities are a.e. equalities on `Iθ` -/

/-- `Iθ` and its interior differ by the two null endpoints. -/
theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc).symm

/-- An equality of functions holding at every interior angle holds a.e. on `Iθ`. -/
theorem ae_eq_of_forall_Ioo {u v : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ = v θ) :
    u =ᵐ[volume.restrict Work.Spaces.Iθ] v := by
  rw [Filter.EventuallyEq, MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-! ## Integrability of the individual summands -/

private lemma measurable_wdivsin_right (z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  exact measurable_const.div (hsin.pow_const _)

private lemma measurable_Wt_right (α z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.Wt α z θ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.measurable_sin.comp (measurable_const.mul measurable_id)
  have hpow : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
    hsin.pow_const _
  have : Measurable (fun θ : ℝ => Work.Spaces.w z *
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := measurable_const.mul hpow
  simpa [Work.Spaces.Wt, Work.Spaces.wTheta] using this

/-- Honesty of the individual summands of the `ℋ^k`-integrand, with the smoothness of the data
replaced by the continuity of the angular slices of the iterates (the only use made of
`Work.Spaces.SmoothNbhd` in the analytic original). -/
theorem integrableOn_HkIntegrand_terms_open (α : ℝ) (k : ℕ) (G : ℝ → ℝ → ℝ) {z : ℝ}
    (hDz : ∀ i : ℕ, ContinuousOn (fun θ => Work.Spaces.DzIter i G z θ) Work.Spaces.Iθ)
    (hMx : ∀ j i : ℕ, ContinuousOn (fun θ => Work.Spaces.mixed j i G z θ) Work.Spaces.Iθ)
    (h : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k G z θ)
      Work.Spaces.Iθ) :
    (∀ i ≤ k, MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.DzIter i G z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ) ∧
      (∀ i j : ℕ, 1 ≤ i → i + j ≤ k → MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ) := by
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  refine ⟨fun i hi => ?_, fun i j hi hij => ?_⟩
  · have haesm1 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.DzIter i G z θ)
        (volume.restrict Work.Spaces.Iθ) := (hDz i).aestronglyMeasurable hIθ
    have haesm2 : AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        (volume.restrict Work.Spaces.Iθ) :=
      (measurable_wdivsin_right z).aestronglyMeasurable
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (Work.Spaces.DzIter i G z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (haesm1.mul haesm2).pow 2
    refine h.mono' haesm (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_z α k G z θ i hi
  · have haesm1 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.mixed j i G z θ)
        (volume.restrict Work.Spaces.Iθ) := (hMx j i).aestronglyMeasurable hIθ
    have haesm2 : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.Wt α z θ)
        (volume.restrict Work.Spaces.Iθ) := (measurable_Wt_right α z).aestronglyMeasurable
    have haesm : AEStronglyMeasurable
        (fun θ : ℝ => (Work.Spaces.mixed j i G z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := (haesm1.mul haesm2).pow 2
    refine h.mono' haesm (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α k G z θ i j hi hij

/-! ## Stripping the radial weight -/

private lemma w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  have h1 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  have h2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
  rw [Work.Spaces.w]
  exact div_ne_zero h1 h2

/-- Stripping the radial weight from a pure `D_z`-summand of the `ℋ^k`-integrand. -/
private lemma inv_w_sq_mul_zsummand (z θ c : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) :
    ((Work.Spaces.w z) ^ 2)⁻¹ *
        (c * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = c ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (w_ne_zero_of_pos hz)
  have hB : (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    rw [← pow_two]; exact Work.FTS.EllipticEst.w_div_sin_sq hθ z
  calc ((Work.Spaces.w z) ^ 2)⁻¹ *
        (c * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = ((Work.Spaces.w z) ^ 2)⁻¹ * (c ^ 2 *
          ((Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by ring
    _ = ((Work.Spaces.w z) ^ 2)⁻¹ *
          (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by rw [hB]
    _ = c ^ 2 * Work.FTS.EllipticEst.thEta θ := by
        rw [show ((Work.Spaces.w z) ^ 2)⁻¹ *
              (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ))
              = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
                * (c ^ 2 * Work.FTS.EllipticEst.thEta θ) from by ring,
            inv_mul_cancel₀ hw, one_mul]

/-- Stripping the radial weight from a mixed summand of the `ℋ^k`-integrand. -/
private lemma inv_w_sq_mul_mixed (z θ α c : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) (hz : 0 < z) :
    ((Work.Spaces.w z) ^ 2)⁻¹ * (c * Work.Spaces.Wt α z θ) ^ 2
      = c ^ 2 * Work.FTS.EllipticEst.thGam α θ := by
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (w_ne_zero_of_pos hz)
  have hB : Work.Spaces.Wt α z θ * Work.Spaces.Wt α z θ
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ := by
    rw [← pow_two]; exact Work.FTS.EllipticEst.Wt_sq hθ α z
  calc ((Work.Spaces.w z) ^ 2)⁻¹ * (c * Work.Spaces.Wt α z θ) ^ 2
      = ((Work.Spaces.w z) ^ 2)⁻¹ *
          (c ^ 2 * (Work.Spaces.Wt α z θ * Work.Spaces.Wt α z θ)) := by ring
    _ = ((Work.Spaces.w z) ^ 2)⁻¹ *
          (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ)) := by rw [hB]
    _ = c ^ 2 * Work.FTS.EllipticEst.thGam α θ := by
        rw [show ((Work.Spaces.w z) ^ 2)⁻¹ *
              (c ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ))
              = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
                * (c ^ 2 * Work.FTS.EllipticEst.thGam α θ) from by ring,
            inv_mul_cancel₀ hw, one_mul]

/-- The integrability input of the slice estimates for the slice `u_j = θ' ↦ D_z^j f z θ'`,
derived from the integrability of the `ℋ^k`-integrand of `∂_θ² f` at the level `z > 0`. -/
theorem slice_data_integrable_of_HkIntegrand_open (α : ℝ) (k : ℕ) (hsm : SmoothOpenθ f)
    {z : ℝ} (hz : 0 < z) (j : ℕ) (hj : j ≤ k)
    (hInt : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
      (∀ m ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter m
            (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) := by
  have hterms := integrableOn_HkIntegrand_terms_open α k (Work.Spaces.pthIter 2 f)
    (fun i => (hsm.pthIter 2).continuousOn_slice_DzIter i hz)
    (fun j i => (hsm.pthIter 2).continuousOn_slice_mixed j i hz) hInt
  constructor
  · refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.const_mul (hterms.1 j hj) ((Work.Spaces.w z) ^ 2)⁻¹)
      ?_ measurableSet_Icc
    intro θ hθ
    change ((Work.Spaces.w z) ^ 2)⁻¹ *
        (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ
    rw [sliceV_DzIter_open hsm j hz (Iθ_subset_Ioo hθ)]
    exact inv_w_sq_mul_zsummand z θ _ hθ hz
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    refine MeasureTheory.IntegrableOn.congr_fun_ae
      (MeasureTheory.Integrable.const_mul (hterms.2 m j hm1 (by omega))
        ((Work.Spaces.w z) ^ 2)⁻¹) ?_
    refine ae_eq_of_forall_Ioo (fun θ hθ => ?_)
    change ((Work.Spaces.w z) ^ 2)⁻¹ *
        (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.FTS.EllipticEst.LopIter m
            (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ
    rw [LopIter_sliceV_DzIter_eq_mixed_open hsm j m hz hθ]
    exact inv_w_sq_mul_mixed z θ α _ ⟨hθ.1.le, hθ.2.le⟩ hz

end Work.FTS.EllipticEst.ThetaU
