import Mathlib
import Submission.Work.Lattice.MaxNormPolygon
import Submission.Work.Dani.LiftFamily
import Submission.Work.Lattice.CnormIntegral
import Submission.GeometryOfNumbers.FlowLatticeCovolume
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_comp_det
import Submission.Commons.Analysis.InnerProductSpace.norm_map_exteriorPower_of_linearIsometry
import Submission.Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal

/-!
# The endpoints of the max-norm Grayson polygon of the §3 flow

The accounting (`Submission.AccountingOneSided.lemma4_identity`) consumes the **closure**
identity `Σ_s Λ s · (jb (s+1) − jb s) = 0`, which for the max-norm polygon is exactly
`Σ_{i<d} Λ_i(t) = c_t(d) − c_t(0) = 0` — the vanishing of the polygon at both endpoints.

* at `j = 0` the data is `0` by definition and the largest convex minorant vanishes there;
* at `j = d` the max-norm data is `0`: for the §3 lattice `Λ₀ = g(ℤᵈ)` (`g` a linear isometry)
  every `ℝ`-independent family `v : Fin d → Λ₀` has `cnorm (⋀^d (a_t(⋀v))) ≥ 1` (the lift
  `v = g ∘ m` with `m` integral, the flow determinant `1`, the isometry invariance of the
  top exterior power and `intWedge_norm_ge_one`), while the family `g ∘ (B d)` attains `0`.

Module `Submission.Work.Lattice.MaxNormEndpoints`, namespace `Submission.MaxNormEndpoints`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormFlow
open Submission.FlowRateAsymptotic
open Submission.FlowDataMax
open Submission.MaxNormPolygon
open Submission.Polygon

namespace Submission.MaxNormEndpoints

variable {d : ℕ}

/-! ### The top exterior power: `cnorm = ‖·‖`, and the flow determinant -/

/-- **For the top exterior power the sup norm is the Euclidean norm.** -/
lemma cnorm_top_eq_norm (w : WK d d) : cnorm (d := d) (le_refl d) w = ‖w‖ := by
  refine le_antisymm (cnorm_le_norm (d := d) (le_refl d) w) ?_
  have h := norm_le_sqrt_card_mul_cnorm (d := d) (k := d) (le_refl d) w
  have h1 : Real.sqrt (Nat.choose d d) = 1 := by simp
  rwa [h1, one_mul] at h

/-- **The determinant of the exponential two-scale flow is `1`** (it is unimodular). -/
lemma det_eFlow {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) :
    LinearMap.det (eFlow (d := d) ℓ t) = 1 := by
  have hcast : (((d - ℓ : ℕ)) : ℝ) = (d : ℝ) - (ℓ : ℝ) := Nat.cast_sub (le_of_lt hℓd)
  rw [eFlow_eq, Submission.FlowLattice.det_scaleMap_twoScale _ _ ℓ (le_of_lt hℓd),
    Submission.FlowLattice.exp_pow_neg_div ℓ hℓ0 t]
  have h2 : (Real.exp (t / (((d - ℓ : ℕ)) : ℝ))) ^ (d - ℓ) = Real.exp t := by
    rw [hcast]
    exact Submission.FlowLattice.exp_pow_div_sub hℓd t
  rw [h2, ← Real.exp_add]
  ring_nf
  simp

lemma abs_det_eFlow {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) :
    |LinearMap.det (eFlow (d := d) ℓ t)| = 1 := by
  rw [det_eFlow (d := d) hℓ0 hℓd t, abs_one]

/-- The finrank of `ℝᵈ` is `d`. -/
lemma finrank_RD : Module.finrank ℝ (RD d) = d := by
  simp [RD, EuclideanSpace]

/-- An isometry preserves the Euclidean norm of the top-degree wedge of any family. -/
lemma norm_iMulti_comp_isometry_top (g : RD d ≃ₗᵢ[ℝ] RD d) (m : Fin d → RD d) :
    ‖exteriorPower.ιMulti ℝ d (fun i => g (m i))‖ = ‖exteriorPower.ιMulti ℝ d m‖ := by
  simpa [Function.comp_def] using
    (Commons.Analysis.InnerProductSpace.norm_map_exteriorPower_of_linearIsometry
      (f := g) (w := exteriorPower.ιMulti ℝ d m))

/-! ### The max-norm data at the top rank -/

/-- **The max-norm rank-`d` data of the §3 flow lattice `g(ℤᵈ)` is `0`.** -/
theorem flowMaxData_top_eq_zero {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) :
    flowMaxData (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t d
      (le_refl d) = 0 := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le hℓ0 (le_of_lt hℓd)
  -- The elementwise lower bound.
  have hlow : ∀ r ∈ flowMaxDataSet (d := d)
      (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t d (le_refl d),
      0 ≤ r := by
    rintro r ⟨v, hvmem, hvli, rfl⟩
    obtain ⟨m, hmmem, hmv⟩ := Submission.LiftFamily.exists_int_lift (d := d)
      (g : RD d ≃ₗ[ℝ] RD d) d v hvmem
    have hmli : LinearIndependent ℝ m := Submission.LiftFamily.linearIndependent_of_lift
      (d := d) (g : RD d ≃ₗ[ℝ] RD d) hmv hvli
    have hcnorm : cnorm (d := d) (le_refl d)
        (exteriorPower.map d (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ d v)) =
        ‖exteriorPower.ιMulti ℝ d m‖ := by
      rw [cnorm_top_eq_norm (d := d), exteriorPower.map_apply_ιMulti]
      simp only [Function.comp_def]
      rw [Commons.Analysis.InnerProductSpace.norm_iMulti_comp_det (d := d)
        (finrank_RD (d := d)) (eFlow (d := d) ℓ t) v hvli]
      rw [abs_det_eFlow (d := d) hℓ0 hℓd t, one_mul]
      rw [show v = fun i => g (m i) from (funext hmv).symm, norm_iMulti_comp_isometry_top]
    have hge1 : 1 ≤ ‖exteriorPower.ιMulti ℝ d m‖ :=
      Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one (d := d) (j := d) hd0
        m (fun r tt => Submission.CnormIntegral.intPoints_coord_int (d := d) (m r) (hmmem r) tt)
        hmli
    rw [hcnorm]
    exact Real.log_nonneg hge1
  -- the witness family `g ∘ (B d)`
  have hwit_li : LinearIndependent ℝ (fun i : Fin d => g ((B d) i)) := by
    have hB : LinearIndependent ℝ (⇑(B d)) := by
      simpa using (B d).toBasis.linearIndependent
    have hker : LinearMap.ker ((g : RD d ≃ₗᵢ[ℝ] RD d) : RD d →ₗ[ℝ] RD d) = ⊥ :=
      LinearMap.ker_eq_bot.mpr g.injective
    exact hB.map' ((g : RD d ≃ₗᵢ[ℝ] RD d) : RD d →ₗ[ℝ] RD d) hker
  have hwit_mem : ∀ i : Fin d, g ((B d) i) ∈
      Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d) := fun i =>
    Submission.ImageLattice.imageBasis_mem_imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d) i
  have hwit_val : Real.log (cnorm (d := d) (le_refl d)
      (exteriorPower.map d (eFlow (d := d) ℓ t)
        (exteriorPower.ιMulti ℝ d (fun i : Fin d => g ((B d) i))))) = 0 := by
    have h1 : cnorm (d := d) (le_refl d)
        (exteriorPower.map d (eFlow (d := d) ℓ t)
          (exteriorPower.ιMulti ℝ d (fun i : Fin d => g ((B d) i)))) = 1 := by
      rw [cnorm_top_eq_norm (d := d), exteriorPower.map_apply_ιMulti]
      simp only [Function.comp_def]
      rw [Commons.Analysis.InnerProductSpace.norm_iMulti_comp_det (d := d)
        (finrank_RD (d := d)) (eFlow (d := d) ℓ t)
        (fun i : Fin d => g ((B d) i)) hwit_li]
      rw [abs_det_eFlow (d := d) hℓ0 hℓd t, one_mul]
      rw [norm_iMulti_comp_isometry_top]
      exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal (B d)
        (B d).orthonormal hd0
    rw [h1, Real.log_one]
  have hwit : Real.log (cnorm (d := d) (le_refl d)
      (exteriorPower.map d (eFlow (d := d) ℓ t)
        (exteriorPower.ιMulti ℝ d (fun i : Fin d => g ((B d) i))))) ∈
      flowMaxDataSet (d := d)
        (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t d (le_refl d) :=
    ⟨fun i => g ((B d) i), hwit_mem, hwit_li, rfl⟩
  refine le_antisymm ?_ (le_csInf ⟨_, hwit⟩ hlow)
  refine csInf_le ⟨0, fun b hb => hlow b hb⟩ ?_
  rw [← hwit_val]
  exact hwit

/-- **The max-norm data at rank `d` vanishes** for the §3 lattice. -/
lemma maxData_top_eq_zero {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) :
    maxData (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
      ℓ t d = 0 := by
  rw [maxData_apply_of (d := d)
    (show 1 ≤ d from lt_of_lt_of_le hℓ0 (le_of_lt hℓd)) (le_refl d)]
  exact flowMaxData_top_eq_zero (d := d) hℓ0 hℓd g t

/-- The max-norm data at rank `0` vanishes. -/
lemma maxData_zero (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) :
    maxData (d := d) Λ₀ ℓ t 0 = 0 :=
  maxData_apply_of_not (d := d) (by omega)

/-- **The left endpoint of the max-norm polygon vanishes.** -/
lemma maxPolygon_zero (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) :
    maxPolygon (d := d) Λ₀ ℓ t 0 = 0 :=
  largestConvexMinorant_zero_left d (maxData (d := d) Λ₀ ℓ t) (maxData_zero (d := d) Λ₀ ℓ t)

/-- **The right endpoint of the max-norm polygon vanishes** for the §3 lattice. -/
lemma maxPolygon_top {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) :
    maxPolygon (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
      ℓ t d = 0 :=
  largestConvexMinorant_zero_right d _
    (maxData_top_eq_zero (d := d) hℓ0 hℓd g t)

/-- **The closure identity of the accounting**: the slopes of the max-norm polygon of the §3
flow lattice sum to zero. -/
theorem maxSlope_sum_eq_zero {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) :
    (∑ i ∈ Finset.range d,
      maxSlope (d := d) (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d))
        ℓ t i) = 0 := by
  have h := sum_slopes_eq_zero_of_ends (c := maxPolygon (d := d)
    (Submission.ImageLattice.imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t)
    (maxPolygon_zero (d := d) _ ℓ t) (maxPolygon_top (d := d) hℓ0 hℓd g t)
  simpa [maxSlope] using h

/-- The max-norm polygon is discrete-convex (hence its slopes are nondecreasing). -/
lemma maxPolygon_convex (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (t : ℝ) :
    DiscreteConvexOn (maxPolygon (d := d) Λ₀ ℓ t) d :=
  largestConvexMinorant_convex d _

end Submission.MaxNormEndpoints

end
