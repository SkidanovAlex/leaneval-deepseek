import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Compare.neuFrac_fibre_aemeasurable_v2
import Submission.Work.BoseKinLoc.Kinetic.fibre_lift_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.aemeasurable_neuWord_zero_fibre`

**The Neumann word `neuWord ℓ d ε_T 0 ψ_r` is a.e. strongly measurable along the slot-`i`
fibre of a smooth, box-supported `(n+1)`-body state**, at the *fixed* translation parameter
`u = 0`.

FS `eq:DefT`'s first kinetic piece is `neuWord ℓ d ε_T u ψ = ½ε_T(dℓ)⁻² neuFrac ℓ (dℓ)⁻² u (Q_uψ)`,
where `Q_uψ = ψ − m_u(ψ)` is the mean-free part and `neuFrac` is the `sInf` of the
resolvent variational functional over smooth compactly supported trials (see `Defs.lean`).

## Proof

Write `ψ_r := genFibre i Ψ r` for the slot-`i` fibre.  There are two steps.

* The box-mean subtraction is invisible to `neuFrac` (`neuFrac_add_const_of_integrableSq`,
  applicable because `ψ_r` is continuous with compact support — it is supported in `acube L`
  and `L ≥ 0`), so

      `neuWord ℓ d ε_T 0 ψ_r = ½ε_T(dℓ)⁻² · neuFrac ℓ (dℓ)⁻² 0 ψ_r`.

  Here `(dℓ)⁻²` is positive: `d ≠ 0` and `ℓ > 0`.

* `q ↦ neuFrac ℓ (dℓ)⁻² q.1 (genFibreState i Ψ q)` is *measurable* on `ℝ³ × X n`
  (`measurable_neuFrac_genFibreState`, from the `sInf`-description of `neuFrac` as an infimum
  of continuous trial values) — and this is a genuine `Measurable`, not merely an a.e. one.
  Composing it with the measurable injection `r ↦ (0, r)` gives the measurability of
  `r ↦ neuFrac ℓ (dℓ)⁻² 0 ψ_r`, hence a.e. strong measurability, and multiplying by the
  constant `½ε_T(dℓ)⁻²` preserves it.
-/

namespace Work.BoseKinLoc.Sector

open MeasureTheory

theorem aemeasurable_neuWord_zero_fibre {ℓ d εT L : ℝ} (hℓ : 0 < ℓ) (hd : d ≠ 0) (hL : 0 ≤ L)
    {n : ℕ} {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
      MeasureTheory.volume := by
  have hne : d * ℓ ≠ 0 := mul_ne_zero hd (ne_of_gt hℓ)
  have ha2pos : 0 < (d * ℓ) ^ (-2 : ℤ) := by
    have hsq : 0 < (d * ℓ) ^ 2 := by nlinarith [mul_self_pos.mpr hne, sq_nonneg (d * ℓ)]
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
    exact inv_pos.mpr hsq
  obtain ⟨M, hM⟩ :=
    Work.BoseKinLoc.Kinetic.exists_abs_bound_of_tsupport_subset_abox (n := n) hL hΨ hsupp
  -- measurability of the anchored (u = 0) Neumann fraction of the raw fibre
  have hraw : Measurable (fun r : Submission.BoseGases.X n =>
      Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0
        (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)) := by
    have h := (Work.BoseKinLoc.Kinetic.measurable_neuFrac_genFibreState (ℓ := ℓ)
      (a2 := (d * ℓ) ^ (-2 : ℤ)) (M := M) hℓ ha2pos.le hΨ hM i).comp
      (Measurable.prod measurable_const measurable_id :
        Measurable (fun r : Submission.BoseGases.X n => ((0 : ℝ³), r)))
    have hgoal : (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0
          (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
        = (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) ((0 : ℝ³), r).1
          (Work.BoseKinLoc.Kinetic.genFibreState i Ψ ((0 : ℝ³), r))) := by
      funext r
      rfl
    rw [hgoal]
    exact h
  -- strip the box mean and multiply by the constant `½ε_T(dℓ)⁻²`
  refine ((hraw.const_mul ((1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ))).aestronglyMeasurable).congr ?_
  refine Filter.Eventually.of_forall (fun r => ?_)
  have hψmeas : Measurable (Work.BoseKinLoc.Kinetic.genFibre i Ψ r) :=
    (Work.BoseKinLoc.Kinetic.genFibre_contDiff hΨ i r).continuous.measurable
  have hint : Integrable (fun z : ℝ³ => (Work.BoseKinLoc.Kinetic.genFibre i Ψ r z) ^ 2) :=
    Continuous.integrable_of_hasCompactSupport
      ((Work.BoseKinLoc.Kinetic.genFibre_contDiff hΨ i r).continuous.pow 2)
      ((Work.BoseKinLoc.Kinetic.genFibre_hasCompactSupport_of_supp hL hsupp i r).comp_left
        (g := fun t : ℝ => t ^ 2) (by norm_num))
  have hQ : Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)
      = fun z : ℝ³ => Work.BoseKinLoc.Kinetic.genFibre i Ψ r z
          + (-(Work.BoseKinLoc.meanU ℓ 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))) := by
    funext z
    simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, Work.BoseKinLoc.meanU, sub_eq_add_neg]
  simp only [Work.BoseKinLoc.neuWord]
  rw [hQ, Work.BoseKinLoc.NeuFrac.neuFrac_add_const_of_integrableSq ha2pos 0 _ _ hψmeas hint]

end Work.BoseKinLoc.Sector
