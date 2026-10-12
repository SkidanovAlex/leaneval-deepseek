import ChallengeDeps
import Submission.PotSupport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `g = v(1−ω)` for a scattering solution (Layer 3)

Throughout the Fournais--Solovej analysis the potential is decomposed as
`g := v(1−ω)` (paper eq. (eq:gdef)).  This module records the basic
integrability fact: if `v` is supported inside `ball 0 R` and `w` is a weak
scattering solution (`IsScatteringSolution w v`, which already gives
`LocallyIntegrable (v(1−w))`), then `g` is *globally* integrable — the
`tsupport` of `v` turns local integrability into global integrability because
`g` vanishes wherever `v` does, hence outside the compact ball `closedBall 0 R`.

No nonnegativity or radiality of `v` is needed; no bound on `w` is needed.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `g := v(1−w)` is (globally) integrable over `ℝ³` whenever `v` is supported
in `ball 0 R` and `w` is a weak scattering solution of `v`. -/
theorem scatG_integrable {v w : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hw : IsScatteringSolution w v) :
    MeasureTheory.Integrable (fun x : ℝ³ => v x * (1 - w x)) := by
  let g : ℝ³ → ℝ := fun x : ℝ³ => v x * (1 - w x)
  have hloc : MeasureTheory.LocallyIntegrable g := by
    have hgdef : g = v * (1 - w) := by
      funext x
      simp [g, Pi.mul_apply, Pi.sub_apply]
    rw [hgdef]
    exact hw.rhs_integrable
  have hsupp : Function.support g ⊆ Metric.closedBall (0 : ℝ³) R := by
    intro x hx
    by_contra hxnot
    have hxge : R ≤ ‖x‖ := by
      have hdist : ¬ dist x 0 ≤ R := by
        simpa [Metric.mem_closedBall] using hxnot
      have habs : ¬ |‖x‖| ≤ R := by
        simpa [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hdist
      exact le_of_not_ge (by
        intro hle
        exact habs (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] using hle))
    have hv0 : v x = 0 := v_eq_zero_of_norm_ge hv_supp hxge
    have hg0 : g x = 0 := by simp [g, hv0]
    exact hx hg0
  have hc : IsCompact (Metric.closedBall (0 : ℝ³) R) :=
    ProperSpace.isCompact_closedBall (0 : ℝ³) R
  have hgon : MeasureTheory.IntegrableOn g (Metric.closedBall (0 : ℝ³) R) := by
    exact hloc.integrableOn_isCompact hc
  exact (MeasureTheory.integrableOn_iff_integrable_of_support_subset (f := g) hsupp).mp hgon

end Submission.BoseGases
