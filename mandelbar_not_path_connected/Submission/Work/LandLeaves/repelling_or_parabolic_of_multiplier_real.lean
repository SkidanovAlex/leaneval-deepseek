import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.attractingCyclesInner
import Submission.Work.Landing.Land.Landing
import Submission.Work.Landing.Family.deriv_tsq_iterate_odd_real

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Milnor 18.10 without the parity hypothesis, from the realness of the multiplier

`Work.Landing.landsAt_repelling_or_parabolic` proves that the landing point of a ray of **odd**
period `k` is repelling or parabolic, using `deriv_tsq_iterate_odd_real` to obtain the realness of
the second-return multiplier `multiplier2 c k z = deriv ((Tsq c)^[k]) z`.

For **even** periods that realness statement is no longer available, but it can be *hypothesised*:
that is what this file does.  The two ingredients of the argument are the combinatorial one
(`Work.Landing.landsAt_periodic`: the landing point of a periodic ray is a periodic point — for an
antiholomorphic map there is no parity obstruction to this) and the geometric one
(`Work.Landing.AttractingCyclesInner`: an attracting cycle has a neighbourhood disjoint from the
basin of infinity, while a landing point of a ray is never an interior point of the filled Julia
set, `Work.Landing.rayAccum_subset_closure_escaping`).  Consequently the modulus of the multiplier
is `≥ 1`, and since it is a nonnegative real it is either `> 1` (repelling) or `= 1` (parabolic).

This is the "even period" form of Milnor 18.10 used by the endgame of the multiborn argument
(`Work.Landing.EvenPeriodLandingDichotomy`, `Work.LANDCL.../evenPeriodLandingDichotomy_of_snail`).
-/

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar)
open Work.ParamRays (escapingSet)

/-- **Milnor 18.10, real-multiplier form.**  Let the ray of angle `θ` land at `z`, let `θ` be
periodic of period `k > 0`, and assume the second-return multiplier `multiplier2 c k z` is a
nonnegative real number (this is automatic for odd `k`, by `deriv_tsq_iterate_odd_real`, and is
the hypothesis in the even-period case).  Then, given the geometric input that attracting cycles
lie off the basin of infinity, `z` is repelling or parabolic.

The argument is the same as in `Work.Landing.landsAt_repelling_or_parabolic`: `z` is a periodic
point (`landsAt_periodic`), it lies in the closure of the escaping set (it is the landing point of
a ray, `rayAccum_subset_closure_escaping`), hence it cannot be attracting; so the modulus of the
multiplier is `≥ 1`, and being a nonnegative real it is `> 1` or `= 1`. -/
theorem repelling_or_parabolic_of_multiplier_real {c : ℂ} {θ : ℝ} {k : ℕ} {z : ℂ}
    (hland : Work.Landing.landsAt c θ z) (hper : Work.Landing.PeriodicAngle θ k) (hk : 0 < k)
    (hreal : ∃ r : ℝ, 0 ≤ r ∧ Work.Landing.multiplier2 c k z = ↑r)
    (hgeo : Work.Landing.AttractingCyclesInner c) :
    Work.Landing.IsRepelling c k z ∨ Work.Landing.IsParabolic c k z := by
  obtain ⟨r, hr, hr_eq⟩ := hreal
  -- the landing point of a periodic ray is a periodic point
  have hxk : (Tantibar c)^[k] z = z := Work.Landing.landsAt_periodic hland hper
  -- a landing point of a ray lies in the closure of the escaping set
  have hclos : z ∈ closure (escapingSet c) := by
    obtain ⟨φ, hφ, hland'⟩ := hland
    have hz : z ∈ Work.Landing.rayAccum c φ θ := by
      rw [show Work.Landing.rayAccum c φ θ = {z} from hland']
      exact Set.mem_singleton z
    exact Work.Landing.rayAccum_subset_closure_escaping c φ θ hz
  -- hence it is not an attracting periodic point
  have hnotattr : ¬ Work.Landing.IsAttracting c k z := by
    intro hattr
    obtain ⟨ε, hε, hball⟩ := hgeo z ⟨k, hattr⟩
    rw [Metric.mem_closure_iff] at hclos
    obtain ⟨w, hw, hwd⟩ := hclos ε hε
    exact hball w (by simpa only [dist_comm z w, dist_eq_norm] using hwd) hw
  -- so the modulus of the multiplier is at least one, i.e. `1 ≤ r`
  have hge : 1 ≤ r := by
    have h1 : ¬ ‖Work.Landing.multiplier2 c k z‖ < 1 :=
      fun hlt => hnotattr ⟨⟨hk, hxk⟩, hlt⟩
    rw [hr_eq, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hr] at h1
    exact not_lt.mp h1
  rcases lt_or_eq_of_le hge with hlt | heq
  · -- modulus `> 1`: repelling
    refine Or.inl ⟨⟨hk, hxk⟩, ?_⟩
    show 1 < ‖Work.Landing.multiplier2 c k z‖
    rw [hr_eq, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hr]
    exact hlt
  · -- modulus `= 1`: parabolic
    refine Or.inr ⟨⟨hk, hxk⟩, ?_⟩
    show Work.Landing.multiplier2 c k z = 1
    rw [← heq] at hr_eq
    simpa using hr_eq

end Work.LandLeaves
