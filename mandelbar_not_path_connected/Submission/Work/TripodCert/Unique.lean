/-
# TripodCert — uniqueness of the fixed point of `(Tsq c)^[3]` on the disc

Area `Submission/Work/TripodCert/`.  This module combines the numerical certificate
(`UniqueDefs.lean`) with the two analytic lemmas

* `deriv_tsq_three_re_pos` — `Re (deriv ((Tsq c)^[3])) > 1` on the uniqueness disc, and
* `injOn_closedBall_of_re_deriv_pos` — positive real part of the derivative implies injectivity,

into the statement actually used by the seed certificate: on the disc `closedBall z₀ R` the map
`(Tsq c)^[3]` has **at most one** fixed point.
-/
import Mathlib
import Submission.Work.TripodCert.Data
import Submission.Work.TripodCert.Num2
import Submission.Work.TripodCert.Check2
import Submission.Work.TripodCert.Sound
import Submission.Work.TripodCert.inUBall_sound
import Submission.Work.TripodCert.UniqueDefs
import Submission.Work.TripodCert.deriv_tsq_three_re_pos
import Submission.Work.TripodCert.injOn_closedBall_of_re_deriv_pos
import Submission.Work.TripodCert.Chain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.TripodCert

open Work.SeedCertRay
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The periodic boxes of the angle class `0` lie in the uniqueness disc. -/
theorem CT_KT_zero_sub : CT KT 0 ⊆ Metric.closedBall uZ0 uRUr := by
  intro z hz
  obtain ⟨i, hi⟩ := Work.SeedCertRay.mem_diskUnion.mp hz
  have hbox : boxT KT 0 i = Work.SeedCertRay.dskOf perT (0 % 6 * NC + i.val) := by
    simp only [boxT, boxOfT, if_neg (by omega : ¬ KT < KT)]
  have hR := radLeT_sound URmU perT 0 chkRadU_0 i
  have hC := chkUBall_sound Uzx Uzy URmU perT 0 chkUBallU_0 i
  have h := inUBall_sound Uzx Uzy URmU perT (0 % 6) i.val hR hC
  rw [← hbox] at h
  exact h hi

/-- The periodic boxes of the angle class `2` lie in the uniqueness disc. -/
theorem CT_KT_two_sub : CT KT 2 ⊆ Metric.closedBall uZ0 uRUr := by
  intro z hz
  obtain ⟨i, hi⟩ := Work.SeedCertRay.mem_diskUnion.mp hz
  have hbox : boxT KT 2 i = Work.SeedCertRay.dskOf perT (2 % 6 * NC + i.val) := by
    simp only [boxT, boxOfT, if_neg (by omega : ¬ KT < KT)]
  have hR := radLeT_sound URmU perT 2 chkRadU_2 i
  have hC := chkUBall_sound Uzx Uzy URmU perT 2 chkUBallU_2 i
  have h := inUBall_sound Uzx Uzy URmU perT (2 % 6) i.val hR hC
  rw [← hbox] at h
  exact h hi

/-- **Uniqueness of the fixed point of `(Tsq c)^[3]` on the disc.** -/
theorem tsq_three_fixp_unique {c : ℂ} (hc : Xb.mem c) {y y' : ℂ}
    (hy : y ∈ Metric.closedBall uZ0 uRUr) (hy' : y' ∈ Metric.closedBall uZ0 uRUr)
    (h1 : (Work.Landing.Tsq c)^[3] y = y) (h2 : (Work.Landing.Tsq c)^[3] y' = y') : y = y' := by
  have hTsq : Differentiable ℂ (Work.Landing.Tsq c) := by
    have h1' : Differentiable ℂ (fun z : ℂ => z ^ 2 + star c) :=
      (differentiable_id.pow 2).add_const (star c)
    exact ((h1'.pow 2).add_const c)
  have hiter : Differentiable ℂ ((Work.Landing.Tsq c)^[3]) := hTsq.iterate 3
  have hderiv : ∀ z : ℂ, deriv (fun w : ℂ => (Work.Landing.Tsq c)^[3] w - w) z
      = deriv ((Work.Landing.Tsq c)^[3]) z - 1 := by
    intro z
    have h : HasDerivAt (fun w : ℂ => (Work.Landing.Tsq c)^[3] w - w)
        (deriv ((Work.Landing.Tsq c)^[3]) z - 1) z :=
      (((hiter.differentiableAt (x := z)).hasDerivAt).sub (hasDerivAt_id z))
    exact h.deriv
  refine injOn_closedBall_of_re_deriv_pos (z₀ := uZ0) (R := uRUr)
    (f := fun w : ℂ => (Work.Landing.Tsq c)^[3] w - w)
    (fun z _ => (hiter.sub differentiable_id).differentiableAt) (fun z hz => ?_) hy hy' ?_
  · rw [hderiv z]
    have h := deriv_tsq_three_re_pos hc hz
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  · show (Work.Landing.Tsq c)^[3] y - y = (Work.Landing.Tsq c)^[3] y' - y'
    rw [h1, h2]
    ring

end Work.TripodCert
