import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.gammaHonesty
import Submission.Work.FTS.EllipticEst.TT.integrableOn_mixedSummand
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoBnds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

/-- The radial weight `w` is positive for `z > 0`. -/
theorem w_pos_of_pos_sliceHon {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (sq_pos_of_pos (by linarith)) (sq_pos_of_pos hz)

/-- **The per-slice `γ`-honesty of the mixed slot of `z²∂_z²Ψ`** for a level-`2` weak datum: for
a.e. `z > 0` the function `θ ↦ (D_z ∂_θ (z²∂_z²Ψ)(z,θ))² · sin(2θ)^{2-γ}` is integrable on `Iθ`
(in fact this holds for every `z ∈ Iz`).

Route: `slot11_sq_eq`/`gammaHonesty_integrand_eq_slot11` (`TT/gammaHonesty.lean`) identify
`(mixed 1 1 (Aof Ψ) · Wt α)²` with `(Dz (pth (Aof Ψ)))² · sin(2θ)^{2-γ} · (w z)²` on `Iθ`; the
stated integrand is that slot divided by the *constant* `(w z)² > 0` (for `z > 0`), so it is
pointwise `≤` the `(i,j) = (1,1)` summand of the nonnegative `HkIntegrand α 2 (Aof Ψ)`, whose
whole slice-sum is integrable by `h.memA.1`.  A useful existing tool for the domination +
a.e.-strong-measurability bookkeeping is the sibling `i2Mem_sq_of_le` (in the import closure via
`TT.gammaHonesty`); the weight `sin(2θ)^{2-γ}` is `≤ 1` on `Iθ` since `2 - γ = 1 - α/10 > 0`. -/
theorem aslotTwoShift_mixedSliceHon {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz (Work.Spaces.pth (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  -- `Ψ` is `C^∞` on the open quadrant, hence so is `z²∂_z²Ψ`.
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hA : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul (hΨ.pzIter 2)
  -- the claim holds for *every* `z > 0`.
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  have hzpos : 0 < z := hz
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (w_pos_of_pos_sliceHon hzpos))
  -- the `(1,1)`-mixed summand of `HkIntegrand α 2 (Aof Ψ)` is slice-integrable.
  have hslot : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.TT.integrableOn_mixedSummand α 2 hA h.memA 1 1 le_rfl (by norm_num)
      (Set.mem_Ici.mpr (le_of_lt hzpos))
  -- divide the (integrable) slot by the constant `(w z)² > 0`.
  refine MeasureTheory.IntegrableOn.congr_fun
    (MeasureTheory.Integrable.const_mul hslot ((Work.Spaces.w z) ^ 2)⁻¹) ?_ measurableSet_Icc
  intro θ hθ
  have hkey := Work.FTS.EllipticEst.TT.gammaHonesty_integrand_eq_slot11 (z := z) (θ := θ) α
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hα hα4 hθ
  calc ((Work.Spaces.w z) ^ 2)⁻¹
        * (Work.Spaces.mixed 1 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2
      = ((Work.Spaces.w z) ^ 2)⁻¹
        * ((Work.Spaces.Dz (Work.Spaces.pth (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
        rw [← hkey]
    _ = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
        * ((Work.Spaces.Dz (Work.Spaces.pth (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by ring
    _ = (Work.Spaces.Dz (Work.Spaces.pth (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
        rw [inv_mul_cancel₀ hw2, one_mul]

end Work.FTS.EllipticEst.Prop
