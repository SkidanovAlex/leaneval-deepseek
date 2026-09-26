import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.loopIndexTrans

/-!
# Reversing a closed loop negates its index

`loopIndex (p.symm) = -loopIndex p` for a closed path `p` based at `a ≠ 0` avoiding `0`, together
with the immediate corollary that a "there and back" excursion has index `0`
(`loopIndex (p.trans p.symm) = 0`).  These two facts, with `loopIndexTrans`, reduce the index
bookkeeping of a walk that splices in excursions to arithmetic: `1 + 0 + ⋯ + 0 = 1`.
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- The reversed lift `t ↦ Λ (1 - t)`. -/
def revLift (Λ : C(unitInterval, ℂ)) : C(unitInterval, ℂ) :=
  Λ.comp ⟨unitInterval.symm, by fun_prop⟩

/-- **Reversing a closed loop negates the index.** -/
theorem loopIndex_symm {a : ℂ} (p : Path a a) (hp : ∀ t, p t ≠ 0) :
    Work.Smooth.SphereJordan.loopIndex (p.symm : C(unitInterval, ℂ)) =
      -Work.Smooth.SphereJordan.loopIndex (p : C(unitInterval, ℂ)) := by
  have hp' : ∀ t : unitInterval, (p.symm : C(unitInterval, ℂ)) t ≠ 0 := by
    intro t
    show p (unitInterval.symm t) ≠ 0
    exact hp _
  have hloop : (p.symm : C(unitInterval, ℂ)) 0 = (p.symm : C(unitInterval, ℂ)) 1 := by
    show p (unitInterval.symm 0) = p (unitInterval.symm 1)
    rw [unitInterval.symm_zero, unitInterval.symm_one, p.target, p.source]
  -- a lift of `p`
  obtain ⟨Λ, hΛ, -, -⟩ := argChangeLift (p : C(unitInterval, ℂ)) hp
  -- the reversed lift is a lift of `p.symm`
  have hΛ' : ∀ t, Complex.exp (revLift Λ t) = (p.symm : C(unitInterval, ℂ)) t := by
    intro t
    show Complex.exp (Λ (unitInterval.symm t)) = p (unitInterval.symm t)
    exact hΛ _
  have hincr : revLift Λ 1 - revLift Λ 0 = -(Λ 1 - Λ 0) := by
    show Λ (unitInterval.symm 1) - Λ (unitInterval.symm 0) = -(Λ 1 - Λ 0)
    rw [unitInterval.symm_one, unitInterval.symm_zero]
    ring
  have hspec_p := loopIndex_spec (p : C(unitInterval, ℂ)) hp (p.source.trans p.target.symm) Λ hΛ
  have hspec_q := loopIndex_spec (p.symm : C(unitInterval, ℂ)) hp' hloop (revLift Λ) hΛ'
  rw [hincr] at hspec_q
  have h2 : ((Work.Smooth.SphereJordan.loopIndex (p.symm : C(unitInterval, ℂ)) : ℤ) : ℂ) *
      (2 * ↑Real.pi * Complex.I) =
      ((-(Work.Smooth.SphereJordan.loopIndex (p : C(unitInterval, ℂ))) : ℤ) : ℂ) *
        (2 * ↑Real.pi * Complex.I) := by
    rw [← hspec_q, hspec_p, Int.cast_neg]
    ring
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero h2

/-- **A there-and-back excursion has index `0`.** -/
theorem loopIndex_trans_symm {a : ℂ} (ha : a ≠ 0) (p : Path a a) (hp : ∀ t, p t ≠ 0) :
    Work.Smooth.SphereJordan.loopIndex (p.trans p.symm) = 0 := by
  have hp' : ∀ t : unitInterval, (p.symm : C(unitInterval, ℂ)) t ≠ 0 := by
    intro t
    show p (unitInterval.symm t) ≠ 0
    exact hp _
  have h1 := loopIndexTrans (a := a) ha p p.symm hp hp'
  rw [h1, loopIndex_symm (a := a) p hp, add_neg_cancel]

end

end Work.Smooth.SphereJordan
