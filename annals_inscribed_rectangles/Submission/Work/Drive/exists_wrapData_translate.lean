import Mathlib
import Submission.Work.Drive.planeWrapData
import Submission.Work.Drive.exists_winding_ne_zero
import Submission.Work.Drive.goodC_translate
import Submission.Work.Drive.doubledPositionPoint
import Submission.Work.Drive.translateWinding

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **Some translate of `γ` satisfies the meridian hypothesis.**  Every smooth Jordan curve `γ` has
a translate `fun x => γ x + c` avoiding the origin and satisfying `Work.Drive.WrapData`, i.e.
enclosing the origin non-trivially.

This is what lets the whole chain route be run for a curve to which the plane chart applies: by
`Work.Drive.goodC_translate` (`GoodC (γ + c) = GoodC γ`, hence `Zc (γ + c) = Zc γ`) the translation
does not affect `ParityCore`/`OrderSplitHolds`.

ROUTE: `Work.Drive.exists_winding_ne_zero` gives `q ∉ Set.range γ` with `winding γ _ q ≠ 0`; take
`c := -q`, so `γ x + c ≠ 0` and the position winding of `γ + c` about the origin equals
`winding γ _ q ≠ 0`.  `Work.Drive.WrapData (fun x => γ x + c)` is `m ≠ 0`, i.e. the existence of the
continuous lift `Ψ` of `t ↦ dirC ((γ + c) (Circle.exp t))` with `Ψ (2π) - Ψ 0 ≠ 0`; build `Ψ` from a
polar lift of `γ + c` about the origin (`Submission/Work/Drive/position_angle_lift.lean`) via
`Work.Drive.total_change_of_position_lift` (which computes the total change as `2m`).  The stronger
pieces `Work.Drive.exists_translate_origin_winding_ne_zero`, `Work.Drive.exists_cap_angle_data`
(`Submission/Work/Drive/capAngleOfSmooth.lean`) and `Work.Drive.lift_total_eq_winding`
(`Submission/Work/Drive/reparamWinding.lean`) already contain most of this. -/
theorem exists_wrapData_translate (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∃ c : ℝ × ℝ, (∀ x : Circle, γ x + c ≠ 0) ∧ Work.Drive.WrapData (fun x => γ x + c) := by
  have hγc : Continuous γ := hγ.isEmbedding.continuous
  have hγinj : Function.Injective γ := hγ.isEmbedding.injective
  -- the `UnitAddCircle`-reparametrisation of `γ`, on which the winding API lives
  have hηc : Continuous (fun u : UnitAddCircle => γ (ccirc u)) := hγc.comp ccirc_continuous
  have hηinj : Function.Injective (fun u : UnitAddCircle => γ (ccirc u)) :=
    fun u v huv => ccirc_injective (hγinj huv)
  have hηsm : ContDiff ℝ 1 (fun t : ℝ => γ (ccirc (t : UnitAddCircle))) := by
    have hbase : ContDiff ℝ 1 (fun t : ℝ => γ (Circle.exp t)) :=
      (hγ.contMDiff.comp contMDiff_circleExp).contDiff.of_le (by simp)
    have hcomp : ContDiff ℝ 1 (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t))) :=
      hbase.comp (by fun_prop)
    have hfun : (fun t : ℝ => γ (ccirc (t : UnitAddCircle)))
        = fun t : ℝ => γ (Circle.exp (2 * Real.pi * t)) := by
      funext t
      rw [ccirc_coe_eq_exp t]
    rw [hfun]
    exact hcomp
  -- input A: a translate about which the origin has non-zero winding
  obtain ⟨p, h0, hne⟩ := exists_translate_origin_winding_ne_zero
    (fun u : UnitAddCircle => γ (ccirc u)) hηc hηinj hηsm
  -- the lift of the doubled position direction about `p`, with total the (non-zero) winding
  obtain ⟨Ψ, hΨc, hΨ, hΨtot⟩ := exists_lift_doubled_dir γ hγc p h0
  refine ⟨-p, ?_, Ψ, hΨc, ?_, ?_⟩
  · -- the translate `γ + (-p)` avoids the origin
    intro x hx
    obtain ⟨u, rfl⟩ := ccirc_surjective x
    exact h0 ⟨u, by simpa [sub_eq_add_neg] using hx⟩
  · -- `Ψ` lifts the doubled position direction of the translate
    intro t
    have hpt : (fun x : Circle => γ x + -p) (Circle.exp t) = γ (Circle.exp t) - p := by
      simp [sub_eq_add_neg]
    rw [hΨ t, hpt]
  · -- the total change is the winding number, which is non-zero
    rintro hzero
    exact hne (Int.cast_eq_zero.mp (by rw [← hΨtot]; exact hzero))

end

end Work.Drive
