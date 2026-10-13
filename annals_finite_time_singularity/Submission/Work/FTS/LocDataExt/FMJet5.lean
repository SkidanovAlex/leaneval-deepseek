/-
# `Work.FTS.LocDataExt.FMJet5` — the order-`5` jet bound of the plain profile `FM.Fstar`

`|D_z^j FM.Fstar z| ≤ C/z` for `z ≥ 1` and `j ≤ 5`, where `FM.Fstar z = 2z/(1+z)²` is the
radial factor of the reference profile.  For `j ≤ 4` this follows from the delivered
`Work.FTS.LocData.Phi_w_le` (`|w z · Phi i z| ≤ 2/z`) with `Work.FTS.LocData.PhiZ_eq` and
`w z ≥ 1`; the new case `j = 5` needs one more step of the *general* recursion of
`Work.FTS.LocData.Phi_div_deriv`, which is stated there only for `n ≤ 3`: the normalised fifth
iterate has the explicit form

  `D_z^5 FM.Fstar z = 2z·(1 - 57z + 302z² - 302z³ + 57z⁴ - z⁵)/(1+z)^7`,

and the coefficient bound `|1 - 57z + 302z² - 302z³ + 57z⁴ - z⁵| ≤ 720(1+z)^5` (for `z ≥ 1`:
the sum of the absolute values of the coefficients, which is what an expansion of the numerator
by `abs_le` gives) yields `|D_z^5 FM.Fstar z| ≤ 1440/z`.

This module deliberately avoids `Submission.Work.FTS.LocData.FstarAux` and
`Work.FTS.LocData.DzIter_FM_Fstar_abs_le`: those modules define a *second* copy of
`Work.FTS.LocData.T1`, which cannot be imported together with `Work.FTS.LocData.DzIter_bumpZ_bound`
(the two definitions collide in the environment), and the assembly `LocG5.lean` needs the latter.
The proof here uses only `Phi_w_le`, `PhiZ_eq` and `Phi_div_deriv`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.HkFstarDefs
import Submission.Work.FTS.LocData.Phi_div_deriv
import Submission.Work.FTS.LocData.PhiZ_eq
import Submission.Work.FTS.LocData.Phi_w_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The fifth iterate of `D_z` on `FM.Fstar` -/

/-- One more step of the recursion of `Work.FTS.LocData.Phi_div_deriv` (`n = 4`, where the
fifth normalised iterate is not provided by the delivered `PhiR`). -/
theorem Phi_div_deriv_four {z : ℝ} (hz : z ≠ -1) :
    z * deriv (fun w : ℝ => Work.FTS.LocData.PhiR 4 w / (1 + w) ^ 6) z
      = 2 * z * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5)
          / (1 + z) ^ 7 := by
  have h1 : (1 : ℝ) + z ≠ 0 := by
    intro h
    exact hz (by linarith)
  have hsub2 : (2 : ℕ) - 1 = 1 := by norm_num
  have hsub3 : (3 : ℕ) - 1 = 2 := by norm_num
  have hsub4 : (4 : ℕ) - 1 = 3 := by norm_num
  have hsub6 : (6 : ℕ) - 1 = 5 := by norm_num
  have hp6 : (1 + z) ^ 6 ≠ 0 := pow_ne_zero 6 h1
  have hp62 : ((1 + z) ^ 6) ^ 2 ≠ 0 := pow_ne_zero 2 hp6
  have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
    have h0 : HasDerivAt ((fun x : ℝ => x) ^ 2) (2 * z) z := by
      refine (((hasDerivAt_id' (x := z)).pow 2).congr_deriv ?_)
      simp [hsub2]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hcu : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
    have h0 : HasDerivAt ((fun x : ℝ => x) ^ 3) (3 * z ^ 2) z := by
      refine (((hasDerivAt_id' (x := z)).pow 3).congr_deriv ?_)
      simp [hsub3]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hqu : HasDerivAt (fun w : ℝ => w ^ 4) (4 * z ^ 3) z := by
    have h0 : HasDerivAt ((fun x : ℝ => x) ^ 4) (4 * z ^ 3) z := by
      refine (((hasDerivAt_id' (x := z)).pow 4).congr_deriv ?_)
      simp [hsub4]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hquartic : HasDerivAt (fun w : ℝ => 1 - 26 * w + 66 * w ^ 2 - 26 * w ^ 3 + w ^ 4)
      (-26 + 132 * z - 78 * z ^ 2 + 4 * z ^ 3) z := by
    have h26 : HasDerivAt (fun w : ℝ => 26 * w) 26 z :=
      hasDerivAt_const_mul (c := (26 : ℝ)) (x := z)
    have h66 : HasDerivAt (fun w : ℝ => 66 * w ^ 2) (66 * (2 * z)) z :=
      hsq.const_mul (66 : ℝ)
    have h26c : HasDerivAt (fun w : ℝ => 26 * w ^ 3) (26 * (3 * z ^ 2)) z :=
      hcu.const_mul (26 : ℝ)
    have hlin : HasDerivAt (fun w : ℝ => 1 - 26 * w) (0 - 26) z :=
      (hasDerivAt_const (c := (1 : ℝ)) (x := z)).sub h26
    exact ((((hlin.add h66).sub h26c).add hqu)).congr_deriv (by ring)
  have ha : HasDerivAt (fun w : ℝ => 2 * w) 2 z :=
    hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
  have hnum : HasDerivAt (fun w : ℝ => Work.FTS.LocData.PhiR 4 w)
      (2 * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4)
        + 2 * z * (-26 + 132 * z - 78 * z ^ 2 + 4 * z ^ 3)) z := by
    have h0 : HasDerivAt
        ((fun w : ℝ => 2 * w) * (fun w : ℝ => 1 - 26 * w + 66 * w ^ 2 - 26 * w ^ 3 + w ^ 4))
        (2 * (1 - 26 * z + 66 * z ^ 2 - 26 * z ^ 3 + z ^ 4)
          + 2 * z * (-26 + 132 * z - 78 * z ^ 2 + 4 * z ^ 3)) z :=
      ha.mul hquartic
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp only [Pi.mul_apply, Work.FTS.LocData.PhiR_four]
    · ring
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 6) (6 * (1 + z) ^ 5) z := by
    have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 6) (6 * (1 + z) ^ 5) z := by
      refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 6).congr_deriv ?_)
      simp [hsub6]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hq : HasDerivAt (fun w : ℝ => Work.FTS.LocData.PhiR 4 w / (1 + w) ^ 6)
      (2 * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5)
        / (1 + z) ^ 7) z := by
    refine (hnum.fun_div hden (pow_ne_zero 6 h1)).congr_deriv ?_
    simp only [Work.FTS.LocData.PhiR_four]
    field_simp [h1, hp6, hp62]
    ring
  have hgoal : deriv (fun w : ℝ => Work.FTS.LocData.PhiR 4 w / (1 + w) ^ 6) z
      = 2 * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5)
          / (1 + z) ^ 7 := by
    simpa using hq.deriv
  rw [hgoal]
  ring

/-- **The fifth `D_z`-iterate of the plain profile decays like `1/z`.** -/
theorem DzIter_FM_Fstar_five_le {z : ℝ} (hz : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) z θ| ≤ 1440 / z := by
  have hz1 : z ≠ -1 := by linarith
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hstep : Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) z θ
      = z * deriv (fun w : ℝ => Work.FTS.LocData.PhiR 4 w / (1 + w) ^ 6) z := by
    show Work.Spaces.Dz (Work.Spaces.DzIter 4 (fun z _ => Work.FM.Fstar z)) z θ = _
    rw [Work.Spaces.Dz, Work.Spaces.pz]
    congr 1
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards with w
    rw [Work.FTS.LocData.PhiZ_eq 4 (by norm_num) w θ]
    rfl
  rw [hstep, Phi_div_deriv_four hz1]
  have hR5 : |1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5| ≤ 720 * (1 + z) ^ 5 := by
    have hz0' : (0 : ℝ) ≤ z := le_of_lt hz0
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [hz0', sq_nonneg z, pow_nonneg hz0' 3, pow_nonneg hz0' 4, pow_nonneg hz0' 5]
    · nlinarith [hz0', sq_nonneg z, pow_nonneg hz0' 3, pow_nonneg hz0' 4, pow_nonneg hz0' 5]
  have hnum : |2 * z * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5)|
      ≤ 2 * z * (720 * (1 + z) ^ 5) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hz0]
    exact mul_le_mul_of_nonneg_left hR5 (by positivity)
  calc |2 * z * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5) / (1 + z) ^ 7|
      = |2 * z * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5)|
          / (1 + z) ^ 7 := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ 7)]
    _ ≤ (2 * z * (720 * (1 + z) ^ 5)) / (1 + z) ^ 7 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1440 * z / (1 + z) ^ 2 := by
        field_simp
        ring
    _ ≤ 1440 / z := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2) hz0]
        nlinarith [hz, sq_nonneg z]

/-! ## The order-`5` jet bound of `FM.Fstar` -/

/-- On `z > 0` the radial weight is at least `1`. -/
theorem one_le_w5 {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

/-- The order-`4` decay of the `D_z`-jets of `FM.Fstar`, from the delivered `Phi_w_le`. -/
theorem DzIter_FM_Fstar_le_four5 {b : ℕ} (hb : b ≤ 4) {z : ℝ} (hz : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ| ≤ 2 / z := by
  rw [Work.FTS.LocData.PhiZ_eq b hb z θ]
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have h1 := Work.FTS.LocData.Phi_w_le b hb hz θ
  calc |Work.FTS.LocData.Phi b z θ| = |Work.FTS.LocData.Phi b z θ| * 1 := by ring
    _ ≤ |Work.FTS.LocData.Phi b z θ| * Work.Spaces.w z :=
        mul_le_mul_of_nonneg_left (one_le_w5 hz0) (abs_nonneg _)
    _ = |Work.Spaces.w z * Work.FTS.LocData.Phi b z θ| := by
        rw [abs_mul, abs_of_pos (lt_of_lt_of_le zero_lt_one (one_le_w5 hz0))]
        ring
    _ ≤ 2 / z := h1

/-- **The order-`5` jet bound of the plain profile**: `|D_z^j FM.Fstar z| ≤ C/z` for `z ≥ 1`,
`j ≤ 5`. -/
theorem FM_Fstar_jet_le5 :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, j ≤ 5 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ C / z := by
  refine ⟨1440, by norm_num, fun j hj z hz θ => ?_⟩
  rcases eq_or_lt_of_le hj with h | h
  · subst h
    exact DzIter_FM_Fstar_five_le hz θ
  · have hj4 : j ≤ 4 := by omega
    exact (DzIter_FM_Fstar_le_four5 hj4 hz θ).trans
      (div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 1440) (by linarith))

end Work.FTS.LocDataExt
