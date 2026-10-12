import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.rungDefs
import Submission.Work.BoseFixB1B.w0_ge_const_on_ball
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.pairMass_pos` — the LHY kernel mass `ĝω(0) = ∫g₀ω₀` is strictly positive

`PairMass h = ∫ z, g₀(z)·ω₀(z)` with `g₀ = v(1−ω₀)` and `ω₀ = Classical.choose h` the chosen
radial scattering solution.  Under the standing hypotheses of FS's dilute regime
(`0 ≤ v` radial `L¹`, `tsupport v ⊆ ball 0 R`, `0 < a v`) this is strictly positive.

## Route (elementary — no Newton representation needed)

* `∫g₀ = 8π·a v > 0` (`g0_integral`, `chosen_scattering_integral`) — this is what `hav` buys.
* `ω₀ ≥ a v/(2R) > 0` a.e. on `ball 0 R` (`Work.BoseFixB1B.w0_ge_const_on_ball`, the quantitative
  concavity bound on the canonical profile).  Note: the corpus had *no* strict form of
  `chosen_gomega_integral_bounds` (only `0 ≤ ∫g₀ω₀`), so the strictness has to come from this
  pointwise lower bound.
* `g₀ ≥ 0` a.e. (`g0_nonneg_ae`) and `g₀` vanishes off `ball 0 R` (`g0_zero_of_norm_ge`), so
  pointwise a.e. `g₀(z)·(a v/(2R)) ≤ g₀(z)·ω₀(z)`: on the ball from the previous point and
  `g₀ ≥ 0`; off the ball because then `g₀ z = 0` and both sides vanish.
* Integrate (`integral_mono_ae`, integrability from `g0_integrable`/`g0w0_integrable`):
  `∫g₀ω₀ ≥ (a v/(2R))·∫g₀ = (a v/(2R))·8π a v > 0`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real

namespace Work.BoseFixB1B

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem pairMass_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    0 < Work.BoseFixB1B.PairMass h := by
  classical
  set c : ℝ := _root_.BoseGases.a v / (2 * R) with hc
  have hcpos : 0 < c := by rw [hc]; exact div_pos hav (by linarith)
  -- the quantitative lower bound on the scattering solution inside the ball
  have hwlow : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      ‖z‖ < R → c ≤ Classical.choose h z := by
    simpa [hc] using
      (Work.BoseFixB1B.w0_ge_const_on_ball (v := v) (R0 := R) hv_supp hR hv hvrad h)
  -- `g₀ ≥ 0` a.e. and `g₀ = 0` off the ball
  have hg0nn : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae (R := R) hR hv hvrad hv_supp h
  -- the pointwise a.e. lower bound `g₀·c ≤ g₀·ω₀`
  have hmono : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      Submission.BoseGases.g0 v h z * c ≤ Submission.BoseGases.g0 v h z * Classical.choose h z := by
    filter_upwards [hwlow, hg0nn] with z hzl hzg
    by_cases hzR : ‖z‖ < R
    · exact mul_le_mul_of_nonneg_left (hzl hzR) hzg
    · have hzero : Submission.BoseGases.g0 v h z = 0 :=
        Submission.BoseGases.g0_zero_of_norm_ge hv_supp (le_of_not_gt hzR) h
      simp [hzero]
  -- integrability of both sides
  have hg0int : MeasureTheory.Integrable
      (fun z : E3 => Submission.BoseGases.g0 v h z) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hprodint : MeasureTheory.Integrable
      (fun z : E3 => Submission.BoseGases.g0 v h z * Classical.choose h z) :=
    Submission.BoseGases.g0w0_integrable hR hv hvrad hv_supp h
  have hle := MeasureTheory.integral_mono_ae (hg0int.mul_const c) hprodint hmono
  -- the left-hand side is `c·∫g₀ = c·(8π a v) > 0`
  have hleft : (∫ z : E3, Submission.BoseGases.g0 v h z * c)
      = (8 * π * _root_.BoseGases.a v) * c := by
    rw [MeasureTheory.integral_mul_const, Submission.BoseGases.g0_integral hR hv_supp h]
  have hpos : 0 < (∫ z : E3, Submission.BoseGases.g0 v h z * c) := by
    rw [hleft]
    exact mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hav) hcpos
  exact lt_of_lt_of_le hpos hle

end Work.BoseFixB1B
