import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxSliding.Assembly
import Submission.Work.SmallBoxSliding.Band
import Submission.Work.SmallBoxSliding.Jensen
import Submission.Work.SmallBoxSliding.boxMass_integral_u
import Submission.Work.SmallBoxSliding.chiSmallB_continuous_joint
import Submission.Work.SmallBoxSliding.integral_chiMass_eq
import Submission.Work.SmallBoxSliding.integral_chiSmallB_sq_u
import Submission.Work.SmallBoxSliding.nBoxInd_integral_u
import Submission.Work.SmallBoxSliding.qLHSwordB_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the volume of the sliding interior `I₋`

`I₋ = interiorSet ℓ d μ = {u : ℝ³ | ∀j, |((ℓd)•u)_j| ≤ ½ℓ(1+d) − 2μ^{-1/3}}`
is the region of the sliding localisation on which the chemical potential is
used as it stands (`m(u) = 1`).  Because `ℓ > 0` and `d > 0`, the scaling
`u ↦ (ℓd)•u` is invertible, so `I₋` is a *bounded* subset of `ℝ³`: each
coordinate `u_j` is bounded by `(|b| + 1)/(ℓd)`, where
`b = ½ℓ(1+d) − 2μ^{-1/3}` is the coordinate half-side (the bound is vacuous —
`I₋ = ∅` — when `b < 0`, which is why no sign hypothesis on `b` is needed).
Lebesgue measure on a finite-dimensional Euclidean space is finite on bounded
sets (`Bornology.IsBounded.measure_lt_top`), whence `volume I₋ ≠ ⊤`.

This is the hypothesis needed to normalise the `u`-integral over `I₋` in the
`R_Ψ`/window layer (cf. `Submission/Work/BoseFixB1/perBoxF_integrated.lean`).
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem volume_interiorSet_ne_top {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    MeasureTheory.volume (Work.SmallBoxSliding.interiorSet ℓ d μ) ≠ ⊤ := by
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  -- the (possibly negative) coordinate half-side and the coordinate bound
  set b : ℝ := (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) with hbdef
  set C : ℝ := (|b| + 1) / (ℓ * d) with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]; positivity
  -- `I₋` is contained in the closed ball of radius `3C`
  have hsub : Work.SmallBoxSliding.interiorSet ℓ d μ ⊆ Metric.closedBall (0 : ℝ³) (3 * C) := by
    intro u hu
    rw [Work.SmallBoxSliding.mem_interiorSet_iff] at hu
    rw [EuclideanSpace.closedBall_zero_eq (3 * C) (by positivity)]
    -- each coordinate of `u` is bounded by `C`
    have hcoord : ∀ j : Fin 3, |u.ofLp j| ≤ C := by
      intro j
      have h1 : (ℓ * d) * |u.ofLp j| ≤ b := by
        have h2 := hu j
        rw [PiLp.smul_apply, smul_eq_mul] at h2
        rw [abs_mul, abs_of_pos hℓd] at h2
        exact h2
      rw [hCdef, le_div_iff₀ hℓd]
      nlinarith [le_abs_self b, h1]
    have hsum : ∑ j : Fin 3, (u.ofLp j) ^ 2 ≤ 3 * C ^ 2 := by
      have h3 : ∑ j : Fin 3, (u.ofLp j) ^ 2 ≤ ∑ _j : Fin 3, C ^ 2 := by
        refine Finset.sum_le_sum (s := Finset.univ) (fun j _ => ?_)
        have hj := hcoord j
        rw [abs_le] at hj
        nlinarith [hj.1, hj.2]
      simpa using h3
    calc ∑ j : Fin 3, u j ^ 2 = ∑ j : Fin 3, (u.ofLp j) ^ 2 := rfl
      _ ≤ 3 * C ^ 2 := hsum
      _ ≤ (3 * C) ^ 2 := by nlinarith [hCnn]
  exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub) (isBounded_closedBall.measure_lt_top))

end Work.BoseFixB1
