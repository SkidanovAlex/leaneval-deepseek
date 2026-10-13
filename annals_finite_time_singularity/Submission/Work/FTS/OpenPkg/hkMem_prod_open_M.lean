/-
# `Submission/Work/FTS/OpenPkg/hkMem_prod_open_M.lean`

The honesty (`HkMem`) of the radial product `r · g` in the **open-quadrant** class, with the
majorant of the radial slots `b ≤ 3` supplied by the *caller* as a plain constant `M` rather
than by the radial Hardy quantity `Rr r` of `radialMul_field.lean`.

The proof is the one-quantity swap of `Work.FTS.OpenPkg.hkMem_prod_open`: the pointwise
`ℋ⁴`-integrand bound `prodK_bound` (the `Classical.choose_spec` of
`Work.FTS.Nonlinear.Pieces.RNP.RNP24.hkIntegrand_prod_le_rad_uniform`) only ever consumes
`(D_z^b r z)² ≤ M` for `b ≤ 3`; the constancy of `M` in `z` removes the need for the radial
Hardy step `dzdIter_sq_le_Rr_open`, and the only remaining input beyond `hgm` is the
integrability of the single radial slot `(D_z^4 r)²w²` (from `hrm`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.radialMul_field

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlinear.RadialProd
open Work.FTS.EllipticEst (SmoothOpen Q0)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## The `θ`-slice bound with a constant radial majorant -/

/-- The angular-slice bound at a fixed `z > 0`, with the radial slots `b ≤ 3` dominated by the
constant `M`.  This is `slice_le_open` with `Rr r` replaced by `M`. -/
theorem slice_le_open_M (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (M : ℝ)
    (hr : SmoothOpen (fun z _ => r z)) (hg : SmoothOpen g)
    (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b r z) ^ 2 ≤ M)
    (hK3 : MeasureTheory.IntegrableOn (fun θ => smE θ * Qg g θ) Work.Spaces.Iθ)
    (hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ), (g z θ) ^ 2 ≤ Qg g θ)
    (hgm : Work.Spaces.HkMem α 4 g) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
      ≤ prodK * M * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) := by
  have hM0 : 0 ≤ M :=
    le_trans (sq_nonneg (Work.Elliptic.DzdIter 0 r 1))
      (hM 0 (by norm_num) 1 (Set.mem_Ioi.mpr (by norm_num)))
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hstep1 : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (prodK * M * Work.Spaces.HkIntegrand α 4 g z θ
          + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (smE θ * Qg g θ)) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
      ((hgm.1 z hzI).const_mul _ |>.add (hK3.const_mul _)) ?_
    filter_upwards [hQg, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hQ hθ
    exact (prodK_bound hM0 hM
        (fun i _ z hz θ hθ => leibniz_rad_Dz r g hr hg i z hz θ hθ)
        (fun i j hi hij z hz θ hθ => leibniz_rad_mixed r g hr hg j i hi z hz θ hθ)
        hθ hz hQ).trans (le_of_eq (by ring))
  have hstep2 : (∫ θ in Work.Spaces.Iθ,
        (prodK * M * Work.Spaces.HkIntegrand α 4 g z θ
          + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (smE θ * Qg g θ)))
      = prodK * M * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) := by
    rw [MeasureTheory.integral_add ((hgm.1 z hzI).const_mul _) (hK3.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hstep2] at hstep1
  exact hstep1

/-! ## The main theorem -/

theorem hkMem_prod_open_M (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (M : ℝ)
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z))
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hrm : Work.Spaces.HkMem α 4 (fun z _ => r z))
    (hgm : Work.Spaces.HkMem α 4 g)
    (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter b r z) ^ 2 ≤ M)
    (hK3 : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.Nonlinear.RadialProd.smE θ
        * Work.FTS.Nonlinear.RadialProd.Qg g θ) Work.Spaces.Iθ)
    (hQg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ), (g z θ) ^ 2 ≤ Work.FTS.Nonlinear.RadialProd.Qg g θ) :
    Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) := by
  have hM0 : 0 ≤ M :=
    le_trans (sq_nonneg (Work.Elliptic.DzdIter 0 r 1))
      (hM 0 (by norm_num) 1 (Set.mem_Ioi.mpr (by norm_num)))
  have hrg : SmoothOpen (fun z θ => r z * g z θ) := smoothOpen_sepMul hr hg
  have hPint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := integrable_DzdIter_sq_open α r hr hrm 4 (by norm_num)
  set G : ℝ → ℝ := fun z => prodK * M * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g z θ)
      + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, smE θ * Qg g θ) with hG
  have hGint : MeasureTheory.Integrable G (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hG]
    exact (hgm.2.const_mul _).add ((hPint.const_mul _).mul_const _)
  constructor
  · intro z hz
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z from hz) with hzpos | rfl
    · have haesm : MeasureTheory.AEStronglyMeasurable
          (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        Work.H2.T1Q.aesm_Iθ_of_continuousOn
          ((hrg.continuousOn_HkIntegrand α 4).comp
            ((continuous_const.prodMk continuous_id).continuousOn)
            (fun θ hθ => ⟨hzpos, hθ⟩))
      have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => prodK * M
            * Work.Spaces.HkIntegrand α 4 g z θ
          + prodK * ((Work.Elliptic.DzdIter 4 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
            * (smE θ * Qg g θ)) Work.Spaces.Iθ :=
        ((hgm.1 z hz).const_mul _).add (hK3.const_mul _)
      refine MeasureTheory.Integrable.mono' hInt haesm ?_
      filter_upwards [hQg, Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hQ hθ
      rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
      exact (prodK_bound hM0 hM
          (fun i _ z hz θ hθ => leibniz_rad_Dz r g hr hg i z hz θ hθ)
          (fun i j hi hij z hz θ hθ => leibniz_rad_mixed r g hr hg j i hi z hz θ hθ)
          hθ hzpos hQ).trans (le_of_eq (by ring))
    · have hzero : (fun θ : ℝ =>
            Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) 0 θ)
          = fun _ => (0 : ℝ) := by
        funext θ
        simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
      rw [hzero]
      exact integrableOn_zero
  · have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) p.1 p.2)
        (hrg.continuousOn_HkIntegrand α 4)).integral_prod_right'
    refine MeasureTheory.Integrable.mono' hGint haesm ?_
    have hmeas : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
        = MeasureTheory.volume.restrict Work.Spaces.Iz :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))
    rw [← hmeas]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
    rw [hG]
    exact slice_le_open_M α r g M hr hg hM hK3 hQg hgm hz

end Work.FTS.OpenPkg
