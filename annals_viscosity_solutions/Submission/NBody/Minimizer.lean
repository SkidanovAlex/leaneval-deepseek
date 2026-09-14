import Submission.NBody.Tonelli
import Mathlib

/-!
# `h`-minimisers

A curve `γ` is an `h`-**minimiser** on `[a,b]` when its action realises the action potential of its
endpoints: `actionOn m h γ a b = φ_h(γ a, γ b)`.  This chapter collects the elementary structure of
minimisers: additivity of the action over time intervals, the fact that every non-degenerate
sub-curve of a minimiser with finite action is a minimiser, and the two-sided time estimate of the
paper (`lema-time.estim`).
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- A curve is an `h`-minimiser on `[a,b]` if its action on that interval equals the action
potential of the two endpoints. -/
def IsHMinimizer (m : Fin N → ℝ) (h : ℝ) (γ : ℝ → EN E N) (a b : ℝ) : Prop :=
  actionOn m h γ a b = actionPot m h (γ a) (γ b)

/-- **Additivity of the action over time intervals.** -/
theorem actionOn_add {m : Fin N → ℝ} {h : ℝ} (γ : ℝ → EN E N) {a b c : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) : actionOn m h γ a c = actionOn m h γ a b + actionOn m h γ b c := by
  unfold actionOn
  rw [← Set.Ioc_union_Ioc_eq_Ioc hab hbc]
  rw [lintegral_union measurableSet_Ioc]
  exact Set.disjoint_left.mpr fun t ht ht' => absurd ht.2 (not_le_of_gt ht'.1)

/-- Monotonicity of the action in the time interval. -/
theorem actionOn_mono_set {m : Fin N → ℝ} {h : ℝ} (γ : ℝ → EN E N) {a b c : ℝ} (hac : a ≤ c)
    (hcb : c ≤ b) : actionOn m h γ a c ≤ actionOn m h γ a b := by
  rw [actionOn_add γ hac hcb]
  exact le_add_right le_rfl

/-- A sub-curve of an `h`-minimiser (with finite action) is an `h`-minimiser on the initial part
of the interval. -/
theorem IsHMinimizer.sub_left {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b c : ℝ}
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : actionOn m h γ a b < ⊤)
    (hac' : a < c) (hcb : c < b) : IsHMinimizer m h γ a c := by
  have hsum : actionOn m h γ a b = actionOn m h γ a c + actionOn m h γ c b :=
    actionOn_add γ hac'.le hcb.le
  have hYtop : actionOn m h γ c b < ⊤ := by
    rw [hsum] at hfin; exact (ENNReal.add_lt_top.mp hfin).2
  have h1 : actionPot m h (γ a) (γ b)
      ≤ actionPot m h (γ a) (γ c) + actionPot m h (γ c) (γ b) :=
    actionPot_triangle m h (γ a) (γ c) (γ b)
  have h2 : actionPot m h (γ a) (γ c) ≤ actionOn m h γ a c :=
    actionPot_le_of_interval hac' rfl rfl
      (hac.mono (by
        rw [uIcc_of_le hac'.le, uIcc_of_le (hac'.le.trans hcb.le)]
        exact Set.Icc_subset_Icc_right hcb.le))
  have h3 : actionPot m h (γ c) (γ b) ≤ actionOn m h γ c b :=
    actionPot_le_of_interval hcb rfl rfl
      (hac.mono (by
        rw [uIcc_of_le hcb.le, uIcc_of_le (hac'.le.trans hcb.le)]
        exact Set.Icc_subset_Icc_left hac'.le))
  refine le_antisymm ?_ h2
  have hEq : actionOn m h γ a c + actionOn m h γ c b
      = actionPot m h (γ a) (γ c) + actionPot m h (γ c) (γ b) :=
    le_antisymm (by rw [← hsum, hmin]; exact h1) (add_le_add h2 h3)
  have h4 : actionOn m h γ a c + actionOn m h γ c b
      ≤ actionPot m h (γ a) (γ c) + actionOn m h γ c b := by
    rw [hEq]; exact add_le_add le_rfl h3
  exact (ENNReal.add_le_add_iff_right hYtop.ne).mp h4

/-- A sub-curve of an `h`-minimiser (with finite action) is an `h`-minimiser on the final part
of the interval. -/
theorem IsHMinimizer.sub_right {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b c : ℝ}
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : actionOn m h γ a b < ⊤)
    (hac' : a < c) (hcb : c < b) : IsHMinimizer m h γ c b := by
  have hsum : actionOn m h γ a b = actionOn m h γ a c + actionOn m h γ c b :=
    actionOn_add γ hac'.le hcb.le
  have hXtop : actionOn m h γ a c < ⊤ := by
    rw [hsum] at hfin; exact (ENNReal.add_lt_top.mp hfin).1
  have h1 : actionPot m h (γ a) (γ b)
      ≤ actionPot m h (γ a) (γ c) + actionPot m h (γ c) (γ b) :=
    actionPot_triangle m h (γ a) (γ c) (γ b)
  have h2 : actionPot m h (γ a) (γ c) ≤ actionOn m h γ a c :=
    actionPot_le_of_interval hac' rfl rfl
      (hac.mono (by
        rw [uIcc_of_le hac'.le, uIcc_of_le (hac'.le.trans hcb.le)]
        exact Set.Icc_subset_Icc_right hcb.le))
  have h3 : actionPot m h (γ c) (γ b) ≤ actionOn m h γ c b :=
    actionPot_le_of_interval hcb rfl rfl
      (hac.mono (by
        rw [uIcc_of_le hcb.le, uIcc_of_le (hac'.le.trans hcb.le)]
        exact Set.Icc_subset_Icc_left hac'.le))
  refine le_antisymm ?_ h3
  have hEq : actionOn m h γ a c + actionOn m h γ c b
      = actionPot m h (γ a) (γ c) + actionPot m h (γ c) (γ b) :=
    le_antisymm (by rw [← hsum, hmin]; exact h1) (add_le_add h2 h3)
  have h4 : actionOn m h γ a c + actionOn m h γ c b
      ≤ actionOn m h γ a c + actionPot m h (γ c) (γ b) := by
    rw [hEq]; exact add_le_add h2 le_rfl
  exact (ENNReal.add_le_add_iff_left hXtop.ne).mp h4

/-- **Every non-degenerate sub-interval of an `h`-minimiser is an `h`-minimiser.** -/
theorem IsHMinimizer.sub {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b c d : ℝ}
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : actionOn m h γ a b < ⊤)
    (hac' : a < c) (hcd : c < d) (hdb : d < b) : IsHMinimizer m h γ c d := by
  have hfin1 : actionOn m h γ c b < ⊤ := by
    rw [actionOn_add γ hac'.le (hcd.le.trans hdb.le)] at hfin
    exact (ENNReal.add_lt_top.mp hfin).2
  have hac_cb : AbsolutelyContinuousOnInterval γ c b :=
    hac.mono (by
      rw [uIcc_of_le (hcd.le.trans hdb.le),
        uIcc_of_le (hac'.le.trans (hcd.le.trans hdb.le))]
      exact Set.Icc_subset_Icc_left hac'.le)
  exact IsHMinimizer.sub_left hac_cb
    (IsHMinimizer.sub_right hac hmin hfin hac' (hcd.trans hdb)) hfin1 hcd hdb

-- NOTE (deferred): the classical "every sub-curve of an `h`-minimiser is an `h`-minimiser" will be
-- added later, in the reparametrised form that makes the admissibility statements cheap.

/-- The action of an `h`-minimiser is finite when the action potential is. -/
theorem IsHMinimizer.actionOn_lt_top {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b : ℝ}
    (hm : IsHMinimizer m h γ a b) (hfin : actionPot m h (γ a) (γ b) < ⊤) :
    actionOn m h γ a b < ⊤ := hm ▸ hfin

/-- **`lema-time.estim`.**  The time `τ` spent by an `h`-minimiser between two configurations
satisfies the quadratic lower bound `½c‖x-y‖²/τ + hτ ≤ φ_h(x,y)`; equivalently `τ` lies between
the two roots of `P(τ) = 2hτ² - 2φ_h(x,y)τ + ‖x-y‖²`. -/
theorem IsHMinimizer.ofReal_tau_le {m : Fin N → ℝ} {h : ℝ} {x y : EN E N} {τ : ℝ}
    {γ : ℝ → EN E N} (hac : AbsolutelyContinuousOnInterval γ 0 τ) (h0 : γ 0 = x) (h1 : γ τ = y)
    (hm : IsHMinimizer m h γ 0 τ) {c : ℝ} (hc : 0 < c) (hmc : ∀ i, c ≤ m i) (hh : 0 ≤ h)
    (hτ : 0 < τ) :
    ENNReal.ofReal ((1 / 2) * c * ‖x - y‖ ^ 2 / τ + h * τ) ≤ actionPot m h x y := by
  have h := ofReal_chord_sq_div_add_le_actionOn hc hmc hh hτ h0 h1 hac
  rw [← h0, ← h1] at h ⊢
  exact h.trans hm.le

end Submission.NBody
