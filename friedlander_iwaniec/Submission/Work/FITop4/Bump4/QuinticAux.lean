/-
# `Submission.Work.FITop4.Bump4.QuinticAux` — the analytic facts about the clamped quintic step

`Work.FITop4.quinticStep` is the clamped quintic Hermite step

  `quinticStep t = 0` for `t ≤ 0`, `= 1` for `1 ≤ t`, `= t³(10 − 15t + 6t²)` on `[0,1]`.

This file proves, from the piecewise definition and the explicit polynomial identities,
* `quinticStep` is `C²` (`ContDiff ℝ 2`);
* its first and second derivatives are the *clamped* polynomials
  `qstep1 t = if t ≤ 0 then 0 else if 1 ≤ t then 0 else 30t²(1−t)²` and
  `qstep2 t = if t ≤ 0 then 0 else if 1 ≤ t then 0 else 60t(1−t)(1−2t)`;
* the pointwise bounds `|qstep1| ≤ 2`, `|qstep2| ≤ 6`, and `0 ≤ quinticStep ≤ 1`, with
  `quinticStep = 0` on `(-∞,0]`, `= 1` on `[1,∞)` and `> 0` on `(0,∞)`.

The differentiability of the clamped functions is proved by the one-dimensional gluing lemma
`HasDerivWithinAt.union` across the two points `0` and `1` where the polynomial pieces are joined,
using that all the relevant derivatives (`qpoly`, `qpoly1`, `qpoly2`) match the constants there.
-/
import Mathlib
import Submission.Work.FITop4.Bump4

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FITop4.Bump4

noncomputable section

open scoped Topology

/-! ## The polynomials underlying the clamped quintic step -/

/-- The quintic polynomial `t³(10 − 15t + 6t²)` that is the middle branch of `quinticStep`. -/
def qpoly (t : ℝ) : ℝ := t ^ 3 * (10 - 15 * t + 6 * t ^ 2)

/-- The derivative `30t²(1 − t)²` of `qpoly`. -/
def qpoly1 (t : ℝ) : ℝ := 30 * t ^ 2 * (1 - t) ^ 2

/-- The second derivative `60t(1 − t)(1 − 2t)` of `qpoly`. -/
def qpoly2 (t : ℝ) : ℝ := 60 * t * (1 - t) * (1 - 2 * t)

/-- The clamped first derivative of `quinticStep`. -/
def qstep1 (t : ℝ) : ℝ := if t ≤ 0 then 0 else if 1 ≤ t then 0 else qpoly1 t

/-- The clamped second derivative of `quinticStep`. -/
def qstep2 (t : ℝ) : ℝ := if t ≤ 0 then 0 else if 1 ≤ t then 0 else qpoly2 t

/-! ## The gluing lemma for functions clamped at `0` and `1` -/

/-- **Differentiability of a clamped `C¹` function.**  If `p` is differentiable with derivative
`p'` and `p, p'` take the prescribed values `c0, c1` (resp. `0`) at `0` and `1`, then the function
`t ↦ p t` clamped by the constants `c0` on `(-∞,0]` and `c1` on `[1,∞)` is differentiable, with
derivative the `0`-clamped version of `p'`.

The two junction points are handled by gluing the two one-sided derivatives with
`HasDerivWithinAt.union` across `Iic 0 ∪ Ici 0 = univ` (and likewise at `1`); the hypotheses
`p' 0 = 0`, `p' 1 = 0` are exactly the matching conditions that make the two one-sided values
agree. -/
lemma hasDerivAt_clamp {p p' : ℝ → ℝ} {c0 c1 : ℝ}
    (hp : ∀ x, HasDerivAt p (p' x) x)
    (h0 : p 0 = c0) (h1 : p 1 = c1) (hp'0 : p' 0 = 0) (hp'1 : p' 1 = 0) :
    ∀ x, HasDerivAt (fun t => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t)
      ((fun t => if t ≤ 0 then 0 else if 1 ≤ t then 0 else p' t) x) x := by
  intro x
  have hIcc : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (fun t => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t) t = p t := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    show (if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t) = p t
    by_cases h : t ≤ 0
    · rw [if_pos h]
      have : t = 0 := le_antisymm h ht0
      subst this; exact h0.symm
    · rw [if_neg h]
      by_cases h' : 1 ≤ t
      · rw [if_pos h']
        have : t = 1 := le_antisymm ht1 h'
        subst this; exact h1.symm
      · rw [if_neg h']
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hev : (fun t => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t) =ᶠ[𝓝 x]
        (fun _ => c0) := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      rw [Set.mem_Iio] at hy
      show (if y ≤ 0 then c0 else if 1 ≤ y then c1 else p y) = c0
      rw [if_pos hy.le]
    have hval : (fun t => if t ≤ 0 then 0 else if 1 ≤ t then 0 else p' t) x = 0 := by
      show (if x ≤ 0 then 0 else if 1 ≤ x then 0 else p' x) = 0
      rw [if_pos hx.le]
    rw [hval]
    exact (hasDerivAt_const x c0).congr_of_eventuallyEq hev
  · subst hx
    have hL : HasDerivWithinAt (fun t => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t)
        0 (Set.Iic 0) 0 := by
      refine (hasDerivWithinAt_const (0:ℝ) (Set.Iic (0:ℝ)) c0).congr ?_ ?_
      · intro y hy
        rw [Set.mem_Iic] at hy
        show (if y ≤ 0 then c0 else if 1 ≤ y then c1 else p y) = c0
        rw [if_pos hy]
      · show (if (0:ℝ) ≤ 0 then c0 else if 1 ≤ 0 then c1 else p 0) = c0
        rw [if_pos le_rfl]
    have hR : HasDerivWithinAt (fun t => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t)
        (p' 0) (Set.Ici 0) 0 := by
      have hev : (fun t => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t)
          =ᶠ[𝓝[Set.Ici 0] 0] p := by
        filter_upwards [Icc_mem_nhdsGE (show (0:ℝ) < 1 by norm_num)] with y hy
        exact hIcc y hy
      exact ((hp 0).hasDerivWithinAt).congr_of_eventuallyEq hev (hIcc 0 ⟨le_rfl, zero_le_one⟩)
    rw [hp'0] at hR
    have hun := hL.union hR
    rw [Set.Iic_union_Ici] at hun
    have hval : (fun t => if t ≤ 0 then 0 else if 1 ≤ t then 0 else p' t) 0 = 0 := by
      show (if (0:ℝ) ≤ 0 then 0 else if 1 ≤ 0 then 0 else p' 0) = 0
      rw [if_pos le_rfl]
    rw [hval]
    exact hasDerivWithinAt_univ.mp hun
  · rcases lt_trichotomy x 1 with hx1 | hx1 | hx1
    · have hev : (fun t => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t) =ᶠ[𝓝 x] p := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨hx, hx1⟩] with y hy
        rw [Set.mem_Ioo] at hy
        show (if y ≤ 0 then c0 else if 1 ≤ y then c1 else p y) = p y
        rw [if_neg (not_le.mpr hy.1), if_neg (not_le.mpr hy.2)]
      have hval : (fun t => if t ≤ 0 then 0 else if 1 ≤ t then 0 else p' t) x = p' x := by
        show (if x ≤ 0 then 0 else if 1 ≤ x then 0 else p' x) = p' x
        rw [if_neg (not_le.mpr hx), if_neg (not_le.mpr hx1)]
      rw [hval]
      exact (hp x).congr_of_eventuallyEq hev
    · subst hx1
      have hR : HasDerivWithinAt (fun t => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t)
          0 (Set.Ici 1) 1 := by
        refine (hasDerivWithinAt_const (1:ℝ) (Set.Ici (1:ℝ)) c1).congr ?_ ?_
        · intro y hy
          rw [Set.mem_Ici] at hy
          show (if y ≤ 0 then c0 else if 1 ≤ y then c1 else p y) = c1
          rw [if_neg (by linarith : ¬ y ≤ 0), if_pos hy]
        · show (if (1:ℝ) ≤ 0 then c0 else if 1 ≤ 1 then c1 else p 1) = c1
          rw [if_neg (by norm_num : ¬ (1:ℝ) ≤ 0), if_pos le_rfl]
      have hL : HasDerivWithinAt (fun t => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t)
          (p' 1) (Set.Iic 1) 1 := by
        have hev : (fun t => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t)
            =ᶠ[𝓝[Set.Iic 1] 1] p := by
          filter_upwards [Icc_mem_nhdsLE (show (0:ℝ) < 1 by norm_num)] with y hy
          exact hIcc y hy
        exact ((hp 1).hasDerivWithinAt).congr_of_eventuallyEq hev (hIcc 1 ⟨zero_le_one, le_rfl⟩)
      rw [hp'1] at hL
      have hun := hL.union hR
      rw [Set.Iic_union_Ici] at hun
      have hval : (fun t => if t ≤ 0 then 0 else if 1 ≤ t then 0 else p' t) 1 = 0 := by
        show (if (1:ℝ) ≤ 0 then 0 else if 1 ≤ 1 then 0 else p' 1) = 0
        rw [if_neg (by norm_num : ¬ (1:ℝ) ≤ 0), if_pos le_rfl]
      rw [hval]
      exact hasDerivWithinAt_univ.mp hun
    · have hev : (fun t => if t ≤ 0 then c0 else if 1 ≤ t then c1 else p t) =ᶠ[𝓝 x]
          (fun _ => c1) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx1] with y hy
        rw [Set.mem_Ioi] at hy
        show (if y ≤ 0 then c0 else if 1 ≤ y then c1 else p y) = c1
        rw [if_neg (by linarith : ¬ y ≤ 0), if_pos hy.le]
      have hval : (fun t => if t ≤ 0 then 0 else if 1 ≤ t then 0 else p' t) x = 0 := by
        show (if x ≤ 0 then 0 else if 1 ≤ x then 0 else p' x) = 0
        rw [if_neg (by linarith : ¬ x ≤ 0), if_pos hx1.le]
      rw [hval]
      exact (hasDerivAt_const x c1).congr_of_eventuallyEq hev

/-! ## Derivatives of the polynomials -/

lemma qpoly_hasDerivAt (x : ℝ) : HasDerivAt qpoly (qpoly1 x) x := by
  have h0 : HasDerivAt (fun t : ℝ => 10 * t^3) (10 * (3 * x^2)) x := by
    simpa using (hasDerivAt_pow 3 x).const_mul 10
  have h1 : HasDerivAt (fun t : ℝ => -15 * t^4) (-15 * (4 * x^3)) x := by
    simpa using (hasDerivAt_pow 4 x).const_mul (-15)
  have h2 : HasDerivAt (fun t : ℝ => 6 * t^5) (6 * (5 * x^4)) x := by
    simpa using (hasDerivAt_pow 5 x).const_mul 6
  have h012 := (h0.add h1).add h2
  have hfun : ((fun t : ℝ => 10 * t^3) + (fun t : ℝ => -15 * t^4) + (fun t : ℝ => 6 * t^5))
      = qpoly := by
    funext t; simp only [Pi.add_apply]; unfold qpoly; ring
  have hval : 10 * (3 * x^2) + (-15) * (4 * x^3) + 6 * (5 * x^4) = qpoly1 x := by
    unfold qpoly1; ring
  rw [hfun, hval] at h012
  exact h012

lemma qpoly1_hasDerivAt (x : ℝ) : HasDerivAt qpoly1 (qpoly2 x) x := by
  have h0 : HasDerivAt (fun t : ℝ => 30 * t^2) (30 * (2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul 30
  have h1 : HasDerivAt (fun t : ℝ => -60 * t^3) (-60 * (3 * x^2)) x := by
    simpa using (hasDerivAt_pow 3 x).const_mul (-60)
  have h2 : HasDerivAt (fun t : ℝ => 30 * t^4) (30 * (4 * x^3)) x := by
    simpa using (hasDerivAt_pow 4 x).const_mul 30
  have h012 := (h0.add h1).add h2
  have hfun : ((fun t : ℝ => 30 * t^2) + (fun t : ℝ => -60 * t^3) + (fun t : ℝ => 30 * t^4))
      = qpoly1 := by
    funext t; simp only [Pi.add_apply]; unfold qpoly1; ring
  have hval : 30 * (2 * x) + (-60) * (3 * x^2) + 30 * (4 * x^3) = qpoly2 x := by
    unfold qpoly2; ring
  rw [hfun, hval] at h012
  exact h012

lemma qpoly_zero : qpoly 0 = 0 := by unfold qpoly; norm_num
lemma qpoly_one : qpoly 1 = 1 := by unfold qpoly; norm_num
lemma qpoly1_zero : qpoly1 0 = 0 := by unfold qpoly1; norm_num
lemma qpoly1_one : qpoly1 1 = 0 := by unfold qpoly1; norm_num
lemma qpoly2_zero : qpoly2 0 = 0 := by unfold qpoly2; norm_num
lemma qpoly2_one : qpoly2 1 = 0 := by unfold qpoly2; norm_num

/-! ## Derivatives of the clamped step -/

/-- The first derivative of the clamped quintic step is the clamped polynomial `qstep1`. -/
lemma quinticStep_hasDerivAt (x : ℝ) : HasDerivAt quinticStep (qstep1 x) x := by
  have hq : quinticStep = (fun t : ℝ => if t ≤ 0 then 0 else if 1 ≤ t then 1 else qpoly t) := by
    funext t; unfold quinticStep qpoly; rfl
  rw [hq]
  exact hasDerivAt_clamp (p := qpoly) (p' := qpoly1) (c0 := 0) (c1 := 1)
    qpoly_hasDerivAt qpoly_zero qpoly_one qpoly1_zero qpoly1_one x

/-- The second derivative of the clamped quintic step is the clamped polynomial `qstep2`. -/
lemma qstep1_hasDerivAt (x : ℝ) : HasDerivAt qstep1 (qstep2 x) x :=
  hasDerivAt_clamp (p := qpoly1) (p' := qpoly2) (c0 := 0) (c1 := 0)
    qpoly1_hasDerivAt qpoly1_zero qpoly1_one qpoly2_zero qpoly2_one x

/-! ## Continuity of the clamped second derivative -/

lemma continuous_qstep2 : Continuous qstep2 := by
  have hc : Continuous qpoly2 := by unfold qpoly2; fun_prop
  have hIcc : ContinuousOn qstep2 (Set.Icc (0:ℝ) 1) := by
    apply ContinuousOn.congr hc.continuousOn
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    show qstep2 t = qpoly2 t
    unfold qstep2
    by_cases h : t ≤ 0
    · rw [if_pos h]
      have ht' : t = 0 := le_antisymm h ht0
      subst ht'; unfold qpoly2; norm_num
    · rw [if_neg h]
      by_cases h' : 1 ≤ t
      · rw [if_pos h']
        have ht' : t = 1 := le_antisymm ht1 h'
        subst ht'; unfold qpoly2; norm_num
      · rw [if_neg h']
  have hIci1 : ContinuousOn qstep2 (Set.Ici (1:ℝ)) := by
    refine ContinuousOn.congr (f := fun _ : ℝ => (0:ℝ)) continuousOn_const ?_
    intro t ht
    rw [Set.mem_Ici] at ht
    show qstep2 t = 0
    unfold qstep2
    rw [if_neg (by linarith : ¬ t ≤ 0), if_pos ht]
  have hIic0 : ContinuousOn qstep2 (Set.Iic (0:ℝ)) := by
    refine ContinuousOn.congr (f := fun _ : ℝ => (0:ℝ)) continuousOn_const ?_
    intro t ht
    rw [Set.mem_Iic] at ht
    show qstep2 t = 0
    unfold qstep2
    rw [if_pos ht]
  have hIci0 : ContinuousOn qstep2 (Set.Ici (0:ℝ)) := by
    have hun := ContinuousOn.union_of_isClosed hIcc hIci1 isClosed_Icc isClosed_Ici
    rwa [Set.Icc_union_Ici (a := (0:ℝ)) (b := 1) (c := 1) (by norm_num),
      min_eq_left (by norm_num)] at hun
  have hun := ContinuousOn.union_of_isClosed hIic0 hIci0 isClosed_Iic isClosed_Ici
  rw [Set.Iic_union_Ici (a := (0:ℝ))] at hun
  exact continuousOn_univ.mp hun

/-! ## `C²`-regularity -/

lemma contDiff_quinticStep : ContDiff ℝ 2 quinticStep := by
  have hd1 : Differentiable ℝ quinticStep := fun x => (quinticStep_hasDerivAt x).differentiableAt
  have hderiv : deriv quinticStep = qstep1 :=
    funext (fun x => (quinticStep_hasDerivAt x).deriv)
  have hd2 : Differentiable ℝ qstep1 := fun x => (qstep1_hasDerivAt x).differentiableAt
  have hderiv2 : deriv qstep1 = qstep2 :=
    funext (fun x => (qstep1_hasDerivAt x).deriv)
  have hi1 : iteratedDeriv 1 quinticStep = qstep1 := by
    rw [iteratedDeriv_one]; exact hderiv
  have hi2 : iteratedDeriv 2 quinticStep = qstep2 := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hderiv, hderiv2]
  refine (contDiff_nat_iff_iteratedDeriv (𝕜 := ℝ) (n := 2) (f := quinticStep)).mpr ⟨?_, ?_⟩
  · intro m hm
    interval_cases m
    · rw [iteratedDeriv_zero]; exact hd1.continuous
    · rw [hi1]; exact hd2.continuous
    · rw [hi2]; exact continuous_qstep2
  · intro m hm
    interval_cases m
    · rw [iteratedDeriv_zero]; exact hd1
    · rw [hi1]; exact hd2

/-! ## Values of the step -/

lemma quinticStep_nonneg (t : ℝ) : 0 ≤ quinticStep t := by
  unfold quinticStep
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · have h0 : 0 < t := not_le.mp h1
    have hqn : 0 < 10 - 15 * t + 6 * t ^ 2 := by nlinarith [sq_nonneg (4 * t - 5)]
    exact le_of_lt (mul_pos (pow_pos h0 3) hqn)

lemma quinticStep_le_one (t : ℝ) : quinticStep t ≤ 1 := by
  unfold quinticStep
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · have h0 : 0 < t := not_le.mp h1
    have ht1 : t < 1 := not_le.mp h2
    have hfac : 1 - t ^ 3 * (10 - 15 * t + 6 * t ^ 2) = (1 - t) ^ 3 * (6 * t ^ 2 + 3 * t + 1) := by
      ring
    have hnn : 0 ≤ (1 - t) ^ 3 * (6 * t ^ 2 + 3 * t + 1) :=
      mul_nonneg (pow_nonneg (by linarith) 3) (by nlinarith [sq_nonneg t])
    linarith [hfac, hnn]

lemma quinticStep_eq_zero_of_nonpos (t : ℝ) (ht : t ≤ 0) : quinticStep t = 0 := by
  unfold quinticStep; rw [if_pos ht]

lemma quinticStep_eq_one_of_one_le (t : ℝ) (ht : 1 ≤ t) : quinticStep t = 1 := by
  unfold quinticStep
  rw [if_neg (by linarith : ¬ t ≤ 0), if_pos ht]

lemma quinticStep_pos (t : ℝ) (ht : 0 < t) : 0 < quinticStep t := by
  unfold quinticStep
  split_ifs with h1 h2
  · exact absurd h1 (not_le.mpr ht)
  · norm_num
  · have hqn : 0 < 10 - 15 * t + 6 * t ^ 2 := by nlinarith [sq_nonneg (4 * t - 5)]
    exact mul_pos (pow_pos ht 3) hqn

/-! ## Bounds for the clamped derivatives -/

lemma abs_qstep1_le (t : ℝ) : |qstep1 t| ≤ 2 := by
  unfold qstep1
  by_cases h : t ≤ 0
  · rw [if_pos h]; norm_num
  · rw [if_neg h]
    by_cases h' : 1 ≤ t
    · rw [if_pos h']; norm_num
    · rw [if_neg h']
      have ht0 : 0 < t := not_le.mp h
      have ht1 : t < 1 := not_le.mp h'
      have h1 : 0 ≤ t * (1 - t) := by nlinarith
      have h2 : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
      have h3 : (t * (1 - t)) * (t * (1 - t)) ≤ (1 / 4) * (1 / 4) := mul_self_le_mul_self h1 h2
      unfold qpoly1
      rw [abs_of_nonneg (by positivity)]
      nlinarith [h3]

lemma abs_qstep2_le (t : ℝ) : |qstep2 t| ≤ 6 := by
  unfold qstep2
  by_cases h : t ≤ 0
  · rw [if_pos h]; norm_num
  · rw [if_neg h]
    by_cases h' : 1 ≤ t
    · rw [if_pos h']; norm_num
    · rw [if_neg h']
      unfold qpoly2
      have ht0 : 0 < t := not_le.mp h
      have ht1 : t < 1 := not_le.mp h'
      have h1 : 0 ≤ t * (1 - t) := by nlinarith
      have hfac : (t * (1 - t) - 1 / 6) ^ 2 * (432 * (t * (1 - t)) + 36) ≥ 0 := by
        apply mul_nonneg (sq_nonneg _); nlinarith [h1]
      have hkey2 : 108 * (t * (1 - t)) ^ 2 * (1 - 4 * (t * (1 - t))) ≤ 1 := by nlinarith [hfac]
      have hsq : (60 * t * (1 - t) * (1 - 2 * t)) ^ 2 ≤ 36 := by
        have he : (60 * t * (1 - t) * (1 - 2 * t)) ^ 2
            = 3600 * ((t * (1 - t)) ^ 2 * (1 - 4 * (t * (1 - t)))) := by ring
        rw [he]; nlinarith [hkey2]
      apply abs_le.mpr
      constructor <;> nlinarith [hsq]

end

end Work.FITop4.Bump4
