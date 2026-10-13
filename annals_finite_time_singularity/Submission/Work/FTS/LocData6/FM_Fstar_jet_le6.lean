/-
# `Submission/Work/FTS/LocData6/FM_Fstar_jet_le6`

The order-`6` jet bound of the plain profile `φ = FM.Fstar`, `φ z = 2z/(1+z)²`:

  `∃ C > 0, ∀ j ≤ 6, ∀ z ≥ 1, ∀ θ, |D_z^j φ(z)| ≤ C/z`,   `D_z = z ∂_z`.

The cases `j ≤ 4` and `j = 5` are the delivered results of
`Submission/Work/FTS/LocDataExt/FMJet5` (constants `2` and `1440`); the new content is `j = 6`,
in the form of the exact formula (`FMFstar_six_eq`, for `z ≠ -1`, the `D_z`-iterates being
`z`-only functions the case `z = -1` is never needed):

  `D_z^6 φ(z) = 2z·(z^6 - 120z^5 + 1191z^4 - 2416z^3 + 1191z^2 - 120z + 1)/(1+z)^8`.

Since the numerator has coefficients of absolute value summing to `5040` and `z ≥ 1`, one gets
`|D_z^6 φ(z)| ≤ 2·5040·z^7/(1+z)^8 ≤ 10080/z`, which is the announced constant.

The derivative in `FMFstar_six_eq` is computed with `HasDerivAt.fun_div` on
`2w·P(w)/(1+w)^7` (`P(w) = 1 - 57w + 302w² - 302w³ + 57w⁴ - w⁵`, whose derivative is
`-57 + 604w - 906w² + 228w³ - 5w⁴`); the resulting rational identity is discharged by
`field_simp` + `ring`.  The pointwise identification of the fifth iterate is
`DzIter_FM_Fstar_five_eq`, which combines the delivered `PhiZ_eq` (at order `4`) with
`Phi_div_deriv_four`.

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
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.FTS.LocDataExt.FMJet5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.LocData6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The fifth `D_z`-iterate of the profile in closed form -/

/-- The pointwise form of the fifth `D_z`-iterate of `FM.Fstar` off the pole `z = -1`,
obtained from the delivered `PhiZ_eq` (at order `4`) and `Phi_div_deriv_four`. -/
theorem DzIter_FM_Fstar_five_eq {w : ℝ} (hw : w ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) w θ
      = 2 * w * (1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5) / (1 + w) ^ 7 := by
  have hstep : Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) w θ
      = w * deriv (fun u : ℝ => Work.FTS.LocData.PhiR 4 u / (1 + u) ^ 6) w := by
    show Work.Spaces.Dz (Work.Spaces.DzIter 4 (fun z _ => Work.FM.Fstar z)) w θ = _
    rw [Work.Spaces.Dz, Work.Spaces.pz]
    congr 1
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards with u
    rw [Work.FTS.LocData.PhiZ_eq 4 (by norm_num) u θ]
    rfl
  rw [hstep, Work.FTS.LocDataExt.Phi_div_deriv_four hw]

/-! ## The derivative of the closed form -/

/-- The derivative of the rational function of `DzIter_FM_Fstar_five_eq`. -/
theorem FMFstar_six_deriv {z : ℝ} (hz1 : z ≠ -1) :
    deriv (fun w : ℝ => 2 * w * (1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5)
        / (1 + w) ^ 7) z
      = 2 * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1)
          / (1 + z) ^ 8 := by
  have h1 : (1 : ℝ) + z ≠ 0 := by
    intro h
    exact hz1 (by linarith)
  have hp7 : (1 + z) ^ 7 ≠ 0 := pow_ne_zero 7 h1
  have hp72 : ((1 + z) ^ 7) ^ 2 ≠ 0 := pow_ne_zero 2 hp7
  have hsub2 : (2 : ℕ) - 1 = 1 := by norm_num
  have hsub3 : (3 : ℕ) - 1 = 2 := by norm_num
  have hsub4 : (4 : ℕ) - 1 = 3 := by norm_num
  have hsub5 : (5 : ℕ) - 1 = 4 := by norm_num
  have hsub7 : (7 : ℕ) - 1 = 6 := by norm_num
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
  have hfif : HasDerivAt (fun w : ℝ => w ^ 5) (5 * z ^ 4) z := by
    have h0 : HasDerivAt ((fun x : ℝ => x) ^ 5) (5 * z ^ 4) z := by
      refine (((hasDerivAt_id' (x := z)).pow 5).congr_deriv ?_)
      simp [hsub5]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hQ : HasDerivAt (fun w : ℝ => 1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5)
      (-57 + 604 * z - 906 * z ^ 2 + 228 * z ^ 3 - 5 * z ^ 4) z := by
    have h57 : HasDerivAt (fun w : ℝ => 57 * w) 57 z :=
      hasDerivAt_const_mul (c := (57 : ℝ)) (x := z)
    have h302a : HasDerivAt (fun w : ℝ => 302 * w ^ 2) (302 * (2 * z)) z := hsq.const_mul (302 : ℝ)
    have h302b : HasDerivAt (fun w : ℝ => 302 * w ^ 3) (302 * (3 * z ^ 2)) z := hcu.const_mul (302 : ℝ)
    have h57b : HasDerivAt (fun w : ℝ => 57 * w ^ 4) (57 * (4 * z ^ 3)) z := hqu.const_mul (57 : ℝ)
    have hlin : HasDerivAt (fun w : ℝ => 1 - 57 * w) (0 - 57) z :=
      (hasDerivAt_const (c := (1 : ℝ)) (x := z)).sub h57
    exact ((((hlin.add h302a).sub h302b).add h57b).sub hfif).congr_deriv (by ring)
  have hden : HasDerivAt (fun w : ℝ => (1 + w) ^ 7) (7 * (1 + z) ^ 6) z := by
    have h0 : HasDerivAt ((fun w : ℝ => 1 + w) ^ 7) (7 * (1 + z) ^ 6) z := by
      refine ((((hasDerivAt_id' (x := z)).const_add (1 : ℝ)).pow 7).congr_deriv ?_)
      simp [hsub7]
    refine (h0.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with w
      simp
    · ring
  have hnum : HasDerivAt (fun w : ℝ => 2 * w * (1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5)) (2 * (1 - 57 * z + 302 * z ^ 2 - 302 * z ^ 3 + 57 * z ^ 4 - z ^ 5) + 2 * z * (-57 + 604 * z - 906 * z ^ 2 + 228 * z ^ 3 - 5 * z ^ 4)) z := by
    have h2w : HasDerivAt (fun w : ℝ => 2 * w) 2 z := hasDerivAt_const_mul (c := (2 : ℝ)) (x := z)
    exact h2w.mul hQ
  have hq : HasDerivAt (fun w : ℝ => 2 * w * (1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5) / (1 + w) ^ 7) (2 * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1) / (1 + z) ^ 8) z := by
    refine (hnum.fun_div hden hp7).congr_deriv ?_
    field_simp [h1, hp7, hp72]
    ring
  exact hq.deriv

/-! ## The sixth `D_z`-iterate of the profile -/

/-- The closed form of the sixth `D_z`-iterate of `FM.Fstar` at `z ≠ -1`. -/
theorem FMFstar_six_eq {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 6 (fun z _ => Work.FM.Fstar z) z θ
      = 2 * z * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1)
          / (1 + z) ^ 8 := by
  have hstep : Work.Spaces.DzIter 6 (fun z _ => Work.FM.Fstar z) z θ
      = z * deriv (fun w : ℝ => Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) w θ) z := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  rw [hstep]
  have hfun : (fun w : ℝ => Work.Spaces.DzIter 5 (fun z _ => Work.FM.Fstar z) w θ) =ᶠ[𝓝 z]
      (fun w : ℝ => 2 * w * (1 - 57 * w + 302 * w ^ 2 - 302 * w ^ 3 + 57 * w ^ 4 - w ^ 5)
        / (1 + w) ^ 7) := by
    filter_upwards [(isOpen_ne (x := (-1 : ℝ))).mem_nhds hz] with w hw
    exact DzIter_FM_Fstar_five_eq hw θ
  rw [Filter.EventuallyEq.deriv_eq hfun, FMFstar_six_deriv hz]
  ring

/-! ## The order-`6` decay -/

/-- **The sixth `D_z`-iterate of the plain profile decays like `1/z`.** -/
theorem DzIter_FM_Fstar_six_le {z : ℝ} (hz : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.DzIter 6 (fun z _ => Work.FM.Fstar z) z θ| ≤ 10080 / z := by
  rw [FMFstar_six_eq (by linarith : z ≠ -1) θ]
  have hz0 : (0 : ℝ) < z := by linarith
  have hz0' : (0 : ℝ) ≤ z := by linarith
  have hNUM :
      |z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1| ≤ 5040 * z ^ 6 := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [pow_nonneg hz0' 2, pow_nonneg hz0' 3, pow_nonneg hz0' 4, pow_nonneg hz0' 5, pow_nonneg hz0' 6, hz]
    · nlinarith [pow_nonneg hz0' 2, pow_nonneg hz0' 3, pow_nonneg hz0' 4, pow_nonneg hz0' 5, pow_nonneg hz0' 6, hz]
  have hnum2 : |2 * z * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1)|
      ≤ 2 * z * (5040 * z ^ 6) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hz0]
    exact mul_le_mul_of_nonneg_left hNUM (by positivity)
  calc |2 * z * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1)
        / (1 + z) ^ 8|
      = |2 * z * (z ^ 6 - 120 * z ^ 5 + 1191 * z ^ 4 - 2416 * z ^ 3 + 1191 * z ^ 2 - 120 * z + 1)|
          / (1 + z) ^ 8 := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ 8)]
    _ ≤ (2 * z * (5040 * z ^ 6)) / (1 + z) ^ 8 :=
        div_le_div_of_nonneg_right hnum2 (by positivity)
    _ = 10080 * z ^ 7 / (1 + z) ^ 8 := by ring
    _ ≤ 10080 / z := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 8) hz0]
        have h8 : z ^ 8 ≤ (1 + z) ^ 8 := by
          have h := pow_le_pow_left₀ hz0' (by linarith : z ≤ 1 + z) 8
          simpa using h
        nlinarith [h8]

/-! ## The order-`6` jet bound -/

theorem FM_Fstar_jet_le6 :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ C / z := by
  refine ⟨10080, by norm_num, fun j hj z hz θ => ?_⟩
  rcases eq_or_lt_of_le hj with h | h
  · subst h
    exact DzIter_FM_Fstar_six_le hz θ
  · have hj5 : j ≤ 5 := by omega
    rcases eq_or_lt_of_le hj5 with h5 | h5
    · subst h5
      exact (Work.FTS.LocDataExt.DzIter_FM_Fstar_five_le hz θ).trans
        (div_le_div_of_nonneg_right (by norm_num : (1440 : ℝ) ≤ 10080) (by linarith))
    · have hj4 : j ≤ 4 := by omega
      exact (Work.FTS.LocDataExt.DzIter_FM_Fstar_le_four5 hj4 hz θ).trans
        (div_le_div_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 10080) (by linarith))

end Work.FTS.LocData6
