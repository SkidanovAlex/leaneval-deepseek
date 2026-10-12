import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Word.integral_prod_erase_mul_indU
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral` — peeling the slot integral

The slot-`i` lifting of a one-body form `q` is defined (`Work.BoseKinLoc.slotForm`) as

    `slotForm N q ℓ u i Φ = ℓ⁻³ ∫_{X N} 1_{Λ(u)}(xᵢ) · q(fibre N i Φ x) d x`,

i.e. symmetrised against the box indicator in the slot `i`.  This module proves that the
`xᵢ`-integration is exactly the *fibre* integration: writing `x = kcInsN n i (y, r)` (insert
the coordinate `y` in slot `i` of `r : X n`, `N = n + 1`), the fibre of `x` is
`z ↦ Φ (kcInsN n i (z, r))`, which does **not** depend on `y`; the `y`-integral therefore
produces `∫ indU ℓ u = ℓ³`, cancelling the `ℓ⁻³` prefactor, and there remains the integral
over the remaining coordinates

    `slotForm (n+1) q ℓ u i Φ = ∫_{X n} q (fun z => Φ (kcInsN n i (z, r))) d r`.

The statement is *unconditional* in `q` and `Φ` (no measurability, no integrability): the
change of variables is `MeasurePreserving.integral_comp'` for the measure preserving
equivalence `kcInsN n i` (unconditional in the integrand), the Fubini step is
`MeasureTheory.integral_prod_mul` (also unconditional — the integrand is a product of a
function of `y` and a function of `r`), and the only analytic input is the volume
normalisation `∫ indU = ℓ³` of `Word.integral_indU_eq`.
-/

namespace Work.BoseKinLoc.Kinetic

open MeasureTheory

theorem slotForm_eq_fibre_integral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (q : (EuclideanSpace ℝ (Fin 3) → ℝ) → ℝ) (u : EuclideanSpace ℝ (Fin 3)) (i : Fin (n + 1))
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) :
    Work.BoseKinLoc.slotForm (n + 1) q ℓ u i Φ
      = ∫ r : Submission.BoseGases.X n,
          q (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN n i (z, r))) := by
  -- the fibre of a re-inserted configuration does not see the inserted coordinate
  have hfib : ∀ (y : EuclideanSpace ℝ (Fin 3)) (r : Submission.BoseGases.X n),
      Work.BoseKinLoc.fibre (n + 1) i Φ (Submission.BoseGases.kcInsN n i (y, r))
        = fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN n i (z, r)) := by
    intro y r
    funext z
    show Φ (Function.update (Submission.BoseGases.kcInsN n i (y, r)) i z) = _
    rw [Submission.BoseGases.update_kcInsN]
  -- the integrand of `slotForm` after the change of variables `kcInsN n i`
  have hpt : (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ u ((Submission.BoseGases.kcInsN n i p) i)
          * q (Work.BoseKinLoc.fibre (n + 1) i Φ (Submission.BoseGases.kcInsN n i p)))
      = fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
          Work.BoseKinLoc.indU ℓ u p.1
            * q (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN n i (z, p.2))) := by
    funext p
    obtain ⟨y, r⟩ := p
    rw [Submission.BoseGases.kc_insN_apply_same n i y r, hfib y r]
  -- the measure preserving change of variables
  have hcomp := (Submission.BoseGases.kc_mp_insN n i).integral_comp'
    (fun x : Submission.BoseGases.X (n + 1) =>
      Work.BoseKinLoc.indU ℓ u (x i) * q (Work.BoseKinLoc.fibre (n + 1) i Φ x))
  rw [Work.BoseKinLoc.slotForm]
  rw [← hcomp, hpt]
  -- Fubini: the integrand is a product of a function of the inserted coordinate and a
  -- function of the remaining coordinates
  rw [MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.integral_prod_mul (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseKinLoc.indU ℓ u z)
      (fun r : Submission.BoseGases.X n =>
        q (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN n i (z, r))))]
  -- the inserted coordinate integrates to the volume `ℓ³` of the moving box
  rw [Work.BoseKinLoc.Word.integral_indU_eq hℓ u]
  -- the `ℓ⁻³` prefactor cancels the volume
  rw [← mul_assoc]
  rw [show ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 from by
        rw [← zpow_natCast ℓ 3, ← zpow_add₀ (ne_of_gt hℓ)]
        norm_num]
  rw [one_mul]

end Work.BoseKinLoc.Kinetic
