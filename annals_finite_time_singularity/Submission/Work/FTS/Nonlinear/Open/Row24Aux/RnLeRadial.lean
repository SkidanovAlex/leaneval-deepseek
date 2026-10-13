import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row24

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open.Row24Aux

/-- The radial `D_z⁴`-slot of the fundamental-model radial factor `FK g = Qang g 0` satisfies

  `∫_z (D_z⁴ (FK g) z)² w(z)² dz ≤ (9·(π/2)) · HkSq α 4 g`,

with `(DzdIter 4 (FK g))² w²` integrable on `Iz = [0,∞)`.

This is the `α`-lossless radial estimate of row 24 (field `N4Norm.fkH` in the §8 table):
`DzdIter 4 (FK g) = Qang g 4` almost everywhere, so Cauchy–Schwarz in `θ` against `Ktheta`
gives the bound with constant `∫_θ Ktheta θ² ≤ 9·(π/2)` (`|Ktheta θ| ≤ 3` on `Iθ`), while
the weighted square of the `D_z⁴`-slot is dominated by the `ℋ⁴`-integrand. -/
theorem RnLeRadial {α : ℝ} {g : Work.FTS.Galerkin.Fn}
    (hsh : Work.FTS.LocData.SmoothQuad g) (hhmem : Work.Spaces.HkMem α 4 g)
    (hα1 : α ≤ 1) (hα : 0 < α) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter 4 (Work.Construction.FK g) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.DzdIter 4 (Work.Construction.FK g) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
        ≤ (9 * (Real.pi / 2)) * Work.Spaces.HkSq α 4 g := by
  obtain ⟨hint, hbound⟩ :=
    Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral hα hα1 hsh hhmem (i := 4) (by norm_num)
  have hFK : Work.Construction.FK g = fun z => Work.Elliptic.Qang g 0 z := by
    funext z
    rw [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    rw [Work.Elliptic.Ktheta_eq_K]
    ring
  have hae := Work.FTS.Nonlinear.N4Fields.DzdIter_Qang_ae hsh hhmem
  have hcongr' : (fun z => (Work.Elliptic.DzdIter 4 (Work.Construction.FK g) z) ^ 2
        * (Work.Spaces.w z) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))]
      (fun z => (Work.Elliptic.Qang g 4 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))),
      (Work.Elliptic.DzdIter 4 (Work.Construction.FK g) z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.Qang g 4 z) ^ 2 * (Work.Spaces.w z) ^ 2
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    filter_upwards [hae, MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with z hz1 hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    rw [hFK, hz1 hzpos 4 (Finset.mem_range.mpr (by norm_num))]
  have hcongr : (fun z => (Work.Elliptic.DzdIter 4 (Work.Construction.FK g) z) ^ 2
        * (Work.Spaces.w z) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (Work.Elliptic.Qang g 4 z) ^ 2 * (Work.Spaces.w z) ^ 2) := hcongr'
  refine ⟨hint.congr hcongr.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hcongr]
  refine hbound.trans ?_
  exact mul_le_mul_of_nonneg_right
    Work.FTS.Nonlinear.Pieces.RNP.Ktheta_sq_integral_le
    (Work.FTS.Nonlinear.RadialProd.HkSq_nonneg α 4 g)

end Work.FTS.Nonlinear.Open.Row24Aux
