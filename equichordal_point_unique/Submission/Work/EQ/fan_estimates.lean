import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.germCHelpers
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.fan_invBranch_step

set_option maxHeartbeats 2000000

/-! # Uniform fan estimates (Rychlik Thm 7(1), extreme property, Lemma 14)

This file proves `Work.EQ.fan_estimates`: on one disc `B(0,δ)`, uniformly in the branch word
`ε`, the stable fan `fan a h ε` is analytic, its centre `fan a h ε 0` lies on the axis at
`-1/2 + 2ℤ`, and in semi-projective coordinates (`x`, `w = y/(x - a/2)`) the fan stays within
`1/4` of its centre.

The organisation follows Rychlik's majorant induction (pp. 34–36, Lemma 14):

* along a branch word the fan centres are axis points of the coset `-1/2 + 2ℤ`
  (`fan_centres`);
* going one step towards the germ the semi-projective coordinate satisfies the *exact* identity
  `w (invBranch a s Q) = Q.2 / (Q.1 + a/2)`, which turns the branch step into a contraction;
  `fan_invBranch_step` records the resulting two estimates;
* a single radius `δ` works for all words (`fan_induction`), and `fan_estimates` is the final
  assembly.
-/

namespace Work.EQ

open Complex Metric Filter _root_.Topology

noncomputable section

lemma norm_ofReal_complex (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-! ## The branch `invBranch` on the axis -/

/-- The backward branch of the relation at an axis point stays on the axis; the new abscissa is
`-x ± 1` (the sign being the sign of `x + a/2` times the branch sign `s`). -/
theorem invBranch_axis {a : ℝ} {s : Bool} {x : ℝ} (hx : x + a / 2 ≠ 0) :
    invBranch a s ((x : ℂ), (0 : ℂ)) =
      (-(x : ℂ) + (if s then (1 : ℂ) else -1) * (if 0 < x + a / 2 then (1 : ℂ) else -1),
        (0 : ℂ)) := by
  set sg : ℂ := if 0 < x + a / 2 then (1 : ℂ) else -1 with hsg
  have hbase : (x : ℂ) + ((a / 2 : ℝ) : ℂ) = ((x + a / 2 : ℝ) : ℂ) := by push_cast; ring
  have hx0 : (((x + a / 2 : ℝ)) : ℂ) ≠ 0 := by
    rw [← hbase]; exact_mod_cast hx
  have hsgn : sg * sg = 1 := by
    rw [hsg]; split_ifs <;> norm_num
  have hroot : ((((x + a / 2 : ℝ) : ℂ) ^ 2 + (0 : ℂ) ^ 2) ^ (1 / 2 : ℂ))
      = (((x + a / 2 : ℝ)) : ℂ) * sg := by
    have hsq : ((((x + a / 2 : ℝ) : ℂ) ^ 2 + (0 : ℂ) ^ 2)) = ((((x + a / 2) ^ 2 : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_pow]; norm_num
    rw [hsq, ofReal_cpow_half (sq_nonneg _), Real.sqrt_sq_eq_abs, hsg]
    rcases lt_or_gt_of_ne hx with h | h
    · rw [abs_of_neg h, if_neg (not_lt.mpr h.le)]
      push_cast; ring
    · rw [abs_of_pos h, if_pos h]
      push_cast; ring
  have hq : (((x + a / 2 : ℝ)) : ℂ)
      / ((((x + a / 2 : ℝ) : ℂ) ^ 2 + (0 : ℂ) ^ 2) ^ (1 / 2 : ℂ)) = sg := by
    rw [hroot]
    rw [div_eq_iff (mul_ne_zero hx0 (by rw [hsg]; split_ifs <;> norm_num))]
    calc ((x + a / 2 : ℝ) : ℂ) = sg * sg * ((x + a / 2 : ℝ) : ℂ) := by rw [hsgn, one_mul]
      _ = sg * (((x + a / 2 : ℝ) : ℂ) * sg) := by ring
  simp only [invBranch, Prod.mk.injEq]
  refine ⟨?_, by simp⟩
  rw [hbase, mul_div_assoc, hq]

/-- Arithmetic of the fan centres: for `x = -1/2 + 2ℤ` and `0 < a < 1`, with `b = a/2` and
`λ = eqLam a = (1-a)/(1+a)`: `x ± b` do not vanish, `|x + b| ≥ (1-a)/2`, `|x - b| ≥ 1/2`, and
`λ|x ∓ b| ≤ |x ± b|` (the extreme property; equality in the first holds at `x = -1/2` only). -/
theorem fan_centre_arithmetic {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {x : ℝ} {k : ℤ}
    (hx : x = -1 / 2 + 2 * k) :
    x + a / 2 ≠ 0 ∧ x - a / 2 ≠ 0 ∧ (1 - a) / 2 ≤ |x + a / 2| ∧ 1 / 2 ≤ |x - a / 2| ∧
      |x - a / 2| ≤ (1 / eqLam a) * |x + a / 2| ∧
      |x + a / 2| ≤ (1 / eqLam a) * |x - a / 2| := by
  have hkR : x = -1 / 2 + 2 * (k : ℝ) := by rw [hx]
  have hu : x + a / 2 = 2 * (k : ℝ) - (1 - a) / 2 := by rw [hkR]; ring
  have hv : x - a / 2 = 2 * (k : ℝ) - (1 + a) / 2 := by rw [hkR]; ring
  have hlam : 1 / eqLam a = (1 + a) / (1 - a) := by simp only [eqLam, one_div_div]
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1ap : (0 : ℝ) < 1 + a := by linarith
  rcases le_or_gt k 0 with hk | hk
  · have hk0 : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    have hu_neg : x + a / 2 < 0 := by rw [hu]; linarith
    have hv_neg : x - a / 2 < 0 := by rw [hv]; linarith
    refine ⟨ne_of_lt hu_neg, ne_of_lt hv_neg, ?_, ?_, ?_, ?_⟩
    · rw [abs_of_neg hu_neg, hu]; linarith
    · rw [abs_of_neg hv_neg, hv]; linarith
    · rw [abs_of_neg hv_neg, abs_of_neg hu_neg, hlam, hu, hv, div_mul_eq_mul_div,
        le_div_iff₀ h1a]
      nlinarith [hk0]
    · rw [abs_of_neg hv_neg, abs_of_neg hu_neg, hlam, hu, hv, div_mul_eq_mul_div,
        le_div_iff₀ h1a]
      nlinarith [hk0]
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have : (1 : ℤ) ≤ k := by omega
      exact_mod_cast this
    have hu_pos : 0 < x + a / 2 := by rw [hu]; linarith
    have hv_pos : 0 < x - a / 2 := by rw [hv]; linarith
    refine ⟨ne_of_gt hu_pos, ne_of_gt hv_pos, ?_, ?_, ?_, ?_⟩
    · rw [abs_of_pos hu_pos, hu]; linarith
    · rw [abs_of_pos hv_pos, hv]; linarith
    · rw [abs_of_pos hv_pos, abs_of_pos hu_pos, hlam, hu, hv, div_mul_eq_mul_div,
        le_div_iff₀ h1a]
      nlinarith [hk1]
    · rw [abs_of_pos hv_pos, abs_of_pos hu_pos, hlam, hu, hv, div_mul_eq_mul_div,
        le_div_iff₀ h1a]
      nlinarith [hk1]

/-! ## Analyticity of the branch -/

/-- `invBranch a s` is analytic where the radicand `(x + a/2)^2 + y^2` lies in the slit plane. -/
theorem analyticAt_invBranch {a : ℝ} {s : Bool} {Q : ℂ × ℂ}
    (hΔ : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (invBranch a s) Q := by
  have hD : AnalyticAt ℂ (fun Q : ℂ × ℂ => (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) Q :=
    (((analyticAt_fst : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.1) Q).add
      analyticAt_const).pow 2).add
      ((analyticAt_snd : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.2) Q).pow 2)
  have hroot : AnalyticAt ℂ
      (fun Q : ℂ × ℂ => ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) Q :=
    hD.cpow analyticAt_const hΔ
  have hne : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ≠ 0 := Complex.slitPlane_ne_zero hΔ
  have hrootne : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h
    have h2 := cpow_half_sq ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2)
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h2
    exact hne h2.symm
  have hfst : AnalyticAt ℂ (fun Q : ℂ × ℂ =>
      -Q.1 + (if s then (1 : ℂ) else -1) * (Q.1 + ((a / 2 : ℝ) : ℂ))
        / ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) Q :=
    ((analyticAt_fst : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.1) Q).neg).add
      ((analyticAt_const.mul
        (((analyticAt_fst : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.1) Q).add
          analyticAt_const))).div hroot hrootne)
  have hsnd : AnalyticAt ℂ (fun Q : ℂ × ℂ =>
      -Q.2 + (if s then (1 : ℂ) else -1) * Q.2
        / ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) Q :=
    ((analyticAt_snd : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.2) Q).neg).add
      ((analyticAt_const.mul
        ((analyticAt_snd : AnalyticAt ℂ (fun Q : ℂ × ℂ => Q.2) Q))).div hroot hrootne)
  exact hfst.prod hsnd

/-! ## The centres of the fan -/

/-- Parity of the centres: `-(x) ± 1` is again of the form `-1/2 + 2ℤ`. -/
lemma centre_parity {xr : ℝ} {k : ℤ} (hk : xr = -1 / 2 + 2 * (k : ℝ)) {e : ℂ}
    (he : e = 1 ∨ e = -1) :
    ∃ k' : ℤ, -((xr : ℂ)) + e = (((-1 / 2 + 2 * (k' : ℝ)) : ℝ) : ℂ) := by
  rcases he with rfl | rfl
  · refine ⟨1 - k, ?_⟩
    rw [hk]; push_cast; ring
  · refine ⟨-k, ?_⟩
    rw [hk]; push_cast; ring

/-- The fan centres: `fan a h ε 0` lies on the axis, at a point of the coset `-1/2 + 2ℤ`. -/
theorem fan_centres {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∀ ε : List Bool, (fan a h ε 0).2 = 0 ∧
      ∃ k : ℤ, (fan a h ε 0).1 = ((-1 / 2 + 2 * k : ℝ) : ℂ) := by
  intro ε
  induction ε with
  | nil =>
      rw [fan, germC_value ha0 ha1 hh]
      exact ⟨rfl, ⟨0, by norm_num⟩⟩
  | cons s ε ih =>
      obtain ⟨hzs, k, hk⟩ := ih
      have hxk : fan a h ε 0 = ((((-1 / 2 + 2 * (k : ℝ)) : ℝ) : ℂ), (0 : ℂ)) := by
        rw [Prod.ext_iff]; exact ⟨hk, hzs⟩
      have hxp : (-1 / 2 + 2 * (k : ℝ)) + a / 2 ≠ 0 :=
        (fan_centre_arithmetic ha0 ha1 (x := (-1 / 2 + 2 * (k : ℝ))) (k := k) rfl).1
      have hval : fan a h (s :: ε) 0 =
          (-(((-1 / 2 + 2 * (k : ℝ)) : ℝ) : ℂ)
              + (if s then (1 : ℂ) else -1)
                * (if 0 < (-1 / 2 + 2 * (k : ℝ)) + a / 2 then (1 : ℂ) else -1),
            (0 : ℂ)) := by
        rw [fan]
        simp only [mul_zero]
        rw [hxk, invBranch_axis hxp]
      rw [hval]
      refine ⟨rfl, ?_⟩
      have hε : (if s then (1 : ℂ) else -1) * (if s then (1 : ℂ) else -1) = 1 := by
        cases s <;> norm_num
      have hσ2 : (if 0 < (-1 / 2 + 2 * (k : ℝ)) + a / 2 then (1 : ℂ) else -1)
          * (if 0 < (-1 / 2 + 2 * (k : ℝ)) + a / 2 then (1 : ℂ) else -1) = 1 := by
        split_ifs <;> norm_num
      have hprod : ((if s then (1 : ℂ) else -1)
            * (if 0 < (-1 / 2 + 2 * (k : ℝ)) + a / 2 then (1 : ℂ) else -1))
          * ((if s then (1 : ℂ) else -1)
            * (if 0 < (-1 / 2 + 2 * (k : ℝ)) + a / 2 then (1 : ℂ) else -1)) = 1 := by
        rw [mul_mul_mul_comm, hε, hσ2, one_mul]
      have he := (mul_self_eq_one_iff.mp hprod)
      exact centre_parity (xr := (-1 / 2 + 2 * (k : ℝ))) rfl he

/-! ## The germ end: analyticity and size bounds -/

/-- Local data of the germ: `germC a h` is analytic near `0`, and there are `K, δ > 0` such that
on `B(0,δ)` the abscissa moves at most `K‖v‖`, the semi-projective coordinate `y/(x - a/2)` is at
most `K‖v‖(1 + K‖v‖)`, `x - a/2 ≠ 0` and `(x + a/2)^2 + y^2` has positive real part. -/
theorem fan_germC_local {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 δ) ∧
      ∀ v ∈ Metric.ball (0 : ℂ) δ,
        (germC a h v).1 - (a / 2 : ℂ) ≠ 0 ∧
        0 < (((germC a h v).1 + (a / 2 : ℂ)) ^ 2 + (germC a h v).2 ^ 2).re ∧
        ‖(germC a h v).1 - (germC a h 0).1‖ ≤ K * ‖v‖ ∧
        ‖(germC a h v).2 / ((germC a h v).1 - (a / 2 : ℂ))‖ ≤ K * ‖v‖ * (1 + K * ‖v‖) := by
  obtain ⟨hr, han, h0, hderiv, hreal, hFE⟩ := hh
  have hmem : (0 : ℂ) ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, dist_self]; exact hr
  have hAn : AnalyticAt ℂ h 0 := han 0 hmem
  have hd : HasDerivAt h (-1) 0 := by
    have := hAn.differentiableAt.hasDerivAt
    rwa [hderiv] at this
  have hc : HasDerivAt (fun v : ℂ => (eqLam a : ℂ) * v) ((eqLam a : ℂ) * 1) 0 :=
    (hasDerivAt_id (0 : ℂ)).const_mul (eqLam a : ℂ)
  have hcomp : HasDerivAt (fun v : ℂ => h ((eqLam a : ℂ) * v)) ((eqLam a : ℂ) * (-1)) 0 := by
    have hcc := HasDerivAt.comp (0 : ℂ)
      (show HasDerivAt h (-1) ((eqLam a : ℂ) * 0) by simpa using hd) hc
    convert hcc using 1
    · ext v; rfl
    · ring
  have hsub : HasDerivAt (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v)
      ((eqLam a : ℂ) * (-1) - (-1)) 0 := hcomp.sub hd
  have e2 : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 0
      = 1 - ((eqLam a : ℝ) : ℂ) := by
    rw [dslope_same, hsub.deriv]; ring
  have he2nz : (1 : ℂ) - ((eqLam a : ℝ) : ℂ) ≠ 0 := by
    have hl : (0:ℝ) < 1 - eqLam a := by
      have := eqLam_lt_one' ha0 ha1; linarith
    have := Complex.ofReal_ne_zero.mpr (ne_of_gt hl)
    simpa using this
  have hnz : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 0 ≠ 0 := by
    rw [e2]; exact he2nz
  -- analyticity at `0`
  have hgAn : AnalyticAt ℂ (germC a h) 0 := by
    have hB := analyticAt_dslope hAn (a := (0 : ℂ))
    have hlin : AnalyticAt ℂ (fun v : ℂ => (eqLam a : ℂ) * v) 0 :=
      analyticAt_const.mul analyticAt_id
    have hfl : AnalyticAt ℂ (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 :=
      AnalyticAt.comp_of_eq (f := fun v : ℂ => (eqLam a : ℂ) * v) (x := (0 : ℂ)) (y := (0 : ℂ))
        hAn hlin (by ring)
    have hdiff : AnalyticAt ℂ (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 := hfl.sub hAn
    have hA := analyticAt_dslope hfl (a := (0 : ℂ))
    have hAB := analyticAt_dslope hdiff (a := (0 : ℂ))
    have hnum : AnalyticAt ℂ (fun u => a * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 u
        / dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u - a / 2) 0 :=
      ((analyticAt_const.mul hA).div hAB hnz).sub analyticAt_const
    have hsnd : AnalyticAt ℂ (fun u => a * u * dslope h 0 u
        * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 u
        / dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u) 0 :=
      ((((analyticAt_const.mul analyticAt_id).mul hB).mul hA).div hAB hnz)
    exact hnum.prod hsnd
  -- analyticity around `0`, giving a ball
  have hev := hgAn.eventually_analyticAt
  obtain ⟨δ0, hδ0, hA0⟩ := Metric.eventually_nhds_iff.mp hev
  -- continuity at `0`
  have hcont : ContinuousAt (germC a h) 0 := hgAn.continuousAt
  have hval0 := germC_value ha0 ha1 (⟨hr, han, h0, hderiv, hreal, hFE⟩ : IsStableGerm a h r)
  have hgAn1 : AnalyticAt ℂ (fun v => (germC a h v).1) 0 :=
    AnalyticAt.comp (f := germC a h) (x := (0 : ℂ)) (analyticAt_fst (p := (germC a h) 0)) hgAn
  have hgAn2 : AnalyticAt ℂ (fun v => (germC a h v).2) 0 :=
    AnalyticAt.comp (f := germC a h) (x := (0 : ℂ)) (analyticAt_snd (p := (germC a h) 0)) hgAn
  -- the first coordinate moves at most linearly
  have hfx0 : (fun v => (germC a h v).1 - (germC a h 0).1) 0 = 0 := by simp
  have hfxAn : AnalyticAt ℂ (fun v => (germC a h v).1 - (germC a h 0).1) 0 :=
    hgAn1.sub analyticAt_const
  have hfxds : AnalyticAt ℂ (dslope (fun v => (germC a h v).1 - (germC a h 0).1) 0) 0 :=
    analyticAt_dslope hfxAn (a := (0 : ℂ))
  have hfxev : ∀ᶠ v in 𝓝 (0 : ℂ), ‖dslope (fun v => (germC a h v).1 - (germC a h 0).1) 0 v‖
      ≤ ‖dslope (fun v => (germC a h v).1 - (germC a h 0).1) 0 0‖ + 1 := by
    have hε : ∀ᶠ v in 𝓝 (0 : ℂ), dist (dslope (fun v => (germC a h v).1
        - (germC a h 0).1) 0 v) (dslope (fun v => (germC a h v).1 - (germC a h 0).1) 0 0) < 1 :=
      hfxds.continuousAt (Metric.ball_mem_nhds _ zero_lt_one)
    filter_upwards [hε] with v hv
    rw [Complex.dist_eq] at hv
    have h2 := (abs_lt.mp (lt_of_le_of_lt (abs_norm_sub_norm_le _ _) hv)).2
    linarith
  obtain ⟨δ1, hδ1, hb1⟩ := Metric.mem_nhds_iff.mp hfxev
  -- the semi-projective coordinate moves at most linearly
  have hden0 : (germC a h 0).1 - (a / 2 : ℂ) ≠ 0 := by
    rw [hval0]
    intro hcon
    have h2 : ((((-1 : ℝ) / 2 - a / 2 : ℝ)) : ℂ) = 0 := by push_cast; simpa using hcon
    have h3 : ((-1 : ℝ) / 2 - a / 2 : ℝ) = 0 := by exact_mod_cast h2
    linarith [ha1]
  have hgfun : AnalyticAt ℂ (fun v => (germC a h v).2 / ((germC a h v).1 - (a/2:ℂ))) 0 :=
    hgAn2.div (hgAn1.sub analyticAt_const) hden0
  have hgy0 : (fun v => (germC a h v).2 / ((germC a h v).1 - (a/2:ℂ))) 0 = 0 := by
    simp [hval0]
  have hgds : AnalyticAt ℂ (dslope (fun v => (germC a h v).2
      / ((germC a h v).1 - (a/2:ℂ))) 0) 0 := analyticAt_dslope hgfun (a := (0:ℂ))
  have hgyev : ∀ᶠ v in 𝓝 (0 : ℂ),
      ‖dslope (fun v => (germC a h v).2 / ((germC a h v).1 - (a/2:ℂ))) 0 v‖
        ≤ ‖dslope (fun v => (germC a h v).2 / ((germC a h v).1 - (a/2:ℂ))) 0 0‖ + 1 := by
    have hε : ∀ᶠ v in 𝓝 (0 : ℂ), dist (dslope (fun v => (germC a h v).2
        / ((germC a h v).1 - (a/2:ℂ))) 0 v)
        (dslope (fun v => (germC a h v).2 / ((germC a h v).1 - (a/2:ℂ))) 0 0) < 1 :=
      hgds.continuousAt (Metric.ball_mem_nhds _ zero_lt_one)
    filter_upwards [hε] with v hv
    rw [Complex.dist_eq] at hv
    have h2 := (abs_lt.mp (lt_of_le_of_lt (abs_norm_sub_norm_le _ _) hv)).2
    linarith
  obtain ⟨δ2, hδ2, hb2⟩ := Metric.mem_nhds_iff.mp hgyev
  -- the radicand stays in the right half plane
  have hFcont : ContinuousAt (fun v : ℂ =>
      ((germC a h v).1 + (a / 2 : ℂ)) ^ 2 + (germC a h v).2 ^ 2) 0 :=
    (((hgAn1.add analyticAt_const).pow 2).add (hgAn2.pow 2)).continuousAt
  have hF0 : 0 < (((germC a h 0).1 + (a / 2 : ℂ)) ^ 2 + (germC a h 0).2 ^ 2).re := by
    rw [hval0]
    have hval : (((-1 / 2 : ℂ) + (a / 2 : ℂ)) ^ 2 + (0 : ℂ) ^ 2)
        = (((((1 - a) / 2) ^ 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [hval]
    rw [Complex.ofReal_re]
    exact pow_pos (by linarith : (0:ℝ) < (1 - a)/2) 2
  have hFev : ∀ᶠ v in 𝓝 (0 : ℂ),
      0 < (((germC a h v).1 + (a / 2 : ℂ)) ^ 2 + (germC a h v).2 ^ 2).re := by
    have hFre : ContinuousAt (fun v : ℂ =>
        (((germC a h v).1 + (a / 2 : ℂ)) ^ 2 + (germC a h v).2 ^ 2).re) 0 :=
      Complex.continuous_re.continuousAt.comp hFcont
    exact hFre (isOpen_Ioi.mem_nhds hF0)
  obtain ⟨δ3, hδ3, hb3⟩ := Metric.mem_nhds_iff.mp hFev
  -- collect the constants
  set M1 : ℝ := ‖dslope (fun v => (germC a h v).1 - (germC a h 0).1) 0 0‖ + 1 with hM1
  set M2 : ℝ := ‖dslope (fun v => (germC a h v).2 / ((germC a h v).1 - (a/2:ℂ))) 0 0‖ + 1
    with hM2
  set K : ℝ := max M1 M2 + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hKM1 : M1 ≤ K := by rw [hK]; exact le_add_of_le_of_nonneg (le_max_left _ _) zero_le_one
  have hKM2 : M2 ≤ K := by rw [hK]; exact le_add_of_le_of_nonneg (le_max_right _ _) zero_le_one
  set δ : ℝ := min (min (min δ0 δ1) (min δ2 δ3)) (1/(2*K)) with hδdef
  have hle0 : δ ≤ δ0 := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hle1 : δ ≤ δ1 := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hle2 : δ ≤ δ2 := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hle3 : δ ≤ δ3 := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hleK : δ ≤ 1/(2*K) := by
    rw [hδdef]
    exact min_le_right _ _
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (lt_min hδ0 hδ1) (lt_min hδ2 hδ3)) (by positivity)
  refine ⟨K, δ, hKpos, hδpos, ?_, ?_⟩
  · intro v hv
    rw [Metric.mem_ball] at hv
    exact hA0 (lt_of_lt_of_le hv hle0)
  · intro v hv
    rw [Metric.mem_ball] at hv
    have hv0 : dist v 0 < δ0 := lt_of_lt_of_le hv hle0
    have hv1 : dist v 0 < δ1 := lt_of_lt_of_le hv hle1
    have hv2 : dist v 0 < δ2 := lt_of_lt_of_le hv hle2
    have hv3 : dist v 0 < δ3 := lt_of_lt_of_le hv hle3
    have hvK : K * ‖v‖ < 1/2 := by
      have hlt : dist v 0 < 1/(2*K) := lt_of_lt_of_le hv hleK
      have h2 : ‖v‖ < 1/(2*K) := by simpa [dist_eq_norm] using hlt
      have h3 := (lt_div_iff₀ (by positivity : (0:ℝ) < 2*K)).mp h2
      linarith
    -- the first coordinate
    have hdev1 : ‖(germC a h v).1 - (germC a h 0).1‖ ≤ K * ‖v‖ := by
      have hb := hb1 (Metric.mem_ball.mpr hv1)
      have hb' : ‖dslope (fun v => (germC a h v).1 - (germC a h 0).1) 0 v‖ ≤ M1 :=
        hb.trans (le_of_eq hM1.symm)
      rw [← mul_dslope_eq (f := fun v : ℂ => (germC a h v).1 - (germC a h 0).1) (v := v)
        hfx0, norm_mul]
      calc ‖v‖ * ‖dslope (fun v => (germC a h v).1 - (germC a h 0).1) 0 v‖
          ≤ ‖v‖ * M1 := mul_le_mul_of_nonneg_left hb' (norm_nonneg v)
        _ ≤ ‖v‖ * K := mul_le_mul_of_nonneg_left hKM1 (norm_nonneg v)
        _ = K * ‖v‖ := by ring
    have hb0val : ‖(germC a h 0).1 - (a / 2 : ℂ)‖ = (1 + a) / 2 := by
      rw [hval0]
      have hz : ((-1 / 2 : ℂ) - (a / 2 : ℂ)) = (((-(1 + a) / 2 : ℝ)) : ℂ) := by
        push_cast; ring
      rw [hz, Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs,
        abs_of_neg (by linarith : (-(1 + a) / 2 : ℝ) < 0)]
      ring
    -- the semi-projective coordinate
    have hdev2 : ‖(germC a h v).2 / ((germC a h v).1 - (a/2:ℂ))‖ ≤ K * ‖v‖ * (1 + K * ‖v‖) := by
      have hb := hb2 (Metric.mem_ball.mpr hv2)
      have hb' : ‖dslope (fun v => (germC a h v).2 / ((germC a h v).1 - (a/2:ℂ))) 0 v‖ ≤ M2 :=
        hb.trans (le_of_eq hM2.symm)
      rw [← mul_dslope_eq (f := fun v : ℂ => (germC a h v).2 / ((germC a h v).1 - (a/2:ℂ)))
        (v := v) hgy0, norm_mul]
      calc ‖v‖ * ‖dslope (fun v => (germC a h v).2 / ((germC a h v).1 - (a/2:ℂ))) 0 v‖
          ≤ ‖v‖ * M2 := mul_le_mul_of_nonneg_left hb' (norm_nonneg v)
        _ ≤ ‖v‖ * K := mul_le_mul_of_nonneg_left hKM2 (norm_nonneg v)
        _ = K * ‖v‖ := by ring
        _ ≤ K * ‖v‖ * (1 + K * ‖v‖) := by
            nlinarith [norm_nonneg v, hKpos, mul_nonneg hKpos.le (norm_nonneg v)]
    refine ⟨?_, ?_, hdev1, hdev2⟩
    · -- nonvanishing of the denominator
      intro hcon
      have h4 : ‖(germC a h 0).1 - (a / 2 : ℂ)‖
          ≤ ‖(germC a h v).1 - (a / 2 : ℂ)‖ + ‖(germC a h v).1 - (germC a h 0).1‖ := by
        have hsub : (germC a h 0).1 - (a / 2 : ℂ)
            = ((germC a h v).1 - (a / 2 : ℂ)) - ((germC a h v).1 - (germC a h 0).1) := by
          ring
        rw [hsub]
        exact norm_sub_le _ _
      rw [hcon, norm_zero, zero_add] at h4
      have h5 : (1 + a) / 2 ≤ K * ‖v‖ := by
        rw [← hb0val]
        exact h4.trans hdev1
      linarith [hvK, ha0]
    · exact hb3 (Metric.mem_ball.mpr hv3)

/-! ## The induction invariant -/

/-- The invariant of the majorant induction, for one branch word `ε` and one parameter `v`:
analyticity of the fan, its abscissa deviation, its semi-projective coordinate `y/(x - a/2)`,
nonvanishing of `x - a/2` and positivity of the real part of `(x + a/2)^2 + y^2`. -/
def FanGood (a : ℝ) (h : ℂ → ℂ) (Ke Lam Q : ℝ) (ε : List Bool) (v : ℂ) : Prop :=
  AnalyticAt ℂ (fan a h ε) v ∧
    ‖(fan a h ε v).1 - (fan a h ε 0).1‖ ≤ Ke * ‖v‖ ∧
    ‖(fan a h ε v).2 / ((fan a h ε v).1 - (a / 2 : ℂ))‖ ≤ Lam * ‖v‖ * (1 + Q * ‖v‖) ∧
    (fan a h ε v).1 - (a / 2 : ℂ) ≠ 0 ∧
    0 < (((fan a h ε v).1 + (a / 2 : ℂ)) ^ 2 + (fan a h ε v).2 ^ 2).re

/-! ## The two closure inequalities -/

lemma fan_closure_x {Ke Lam g lam w ρ τ : ℝ} (hKe : 0 < Ke) (hLam : 0 < Lam)
    (hg : 0 < g) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hw : 0 ≤ w)
    (hτ0 : 0 ≤ τ) (hρ : ρ = Ke * lam * w) (hτ : τ ≤ 2 * Lam * lam * w)
    (hδe : 64 * (Ke ^ 2 + 4 * Lam ^ 2) * w ≤ Ke * (1 - lam) * g ^ 2) :
    ρ + 64 * (ρ ^ 2 + τ ^ 2) / (lam ^ 2 * g ^ 2) ≤ Ke * w := by
  have h2 : ρ ^ 2 + τ ^ 2 ≤ lam ^ 2 * w ^ 2 * (Ke ^ 2 + 4 * Lam ^ 2) := by
    have hρ2 : ρ ^ 2 = Ke ^ 2 * lam ^ 2 * w ^ 2 := by rw [hρ]; ring
    have h0 : (0:ℝ) ≤ 2 * Lam * lam * w := by positivity
    have hτ2 : τ ^ 2 ≤ (2 * Lam * lam * w) ^ 2 := by
      have h := mul_le_mul hτ hτ hτ0 h0
      nlinarith [h]
    rw [hρ2]; nlinarith [hτ2]
  have h3 : 64 * (ρ ^ 2 + τ ^ 2) / (lam ^ 2 * g ^ 2) ≤ Ke * (1 - lam) * w := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < lam ^ 2 * g ^ 2)]
    have hprod : 64 * (Ke ^ 2 + 4 * Lam ^ 2) * w * (lam ^ 2 * w) ≤ (Ke * (1 - lam) * g ^ 2) * (lam ^ 2 * w) :=
      mul_le_mul_of_nonneg_right hδe (by positivity : (0:ℝ) ≤ lam ^ 2 * w)
    nlinarith [h2, hprod, hlam0, hw, hKe, hg]
  linarith [h3, hρ]

lemma fan_closure_w {Ke Lam Q g lam w ρ τ : ℝ} (hKe : 0 < Ke) (hLam : 0 < Lam) (hQ : 0 < Q)
    (hg : 0 < g) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hw : 0 ≤ w)
    (hρ : ρ = Ke * lam * w) (hτ : τ ≤ Lam * lam * w * (1 + Q * lam * w))
    (hτ0 : 0 ≤ τ)
    (hQbig : 16 * Ke * lam ≤ Q * (1 - lam) * g)
    (hδw : 16 * Ke * lam * w ≤ (1 - lam) * g) :
    (1 / lam) * τ * (1 + 8 * ρ / g) ≤ Lam * w * (1 + Q * w) := by
  have h1 : (1 / lam) * τ ≤ Lam * w * (1 + Q * lam * w) := by
    have h := mul_le_mul_of_nonneg_left hτ (show (0:ℝ) ≤ 1/lam by positivity)
    have he : (1/lam) * (Lam * lam * w * (1 + Q * lam * w)) = Lam * w * (1 + Q * lam * w) := by
      field_simp
    linarith [h, he]
  have h2 : 8 * ρ / g = 8 * Ke * lam * w / g := by rw [hρ]; ring
  have hb1 : 8 * Ke * lam * w / g ≤ (1 - lam) / 2 := by
    rw [div_le_iff₀ hg]
    nlinarith [hδw]
  have hb2 : 8 * Ke * lam / g ≤ Q * (1 - lam) / 2 := by
    rw [div_le_iff₀ hg]
    nlinarith [hQbig]
  have hkey : (1 + Q * lam * w) * (1 + 8 * Ke * lam * w / g) ≤ 1 + Q * w := by
    have hA : 8 * Ke * lam * w / g ≤ Q * (1 - lam) * w / 2 := by
      have h := mul_le_mul_of_nonneg_right hb2 hw
      have he1 : 8 * Ke * lam / g * w = 8 * Ke * lam * w / g := by ring
      have he2 : Q * (1 - lam) / 2 * w = Q * (1 - lam) * w / 2 := by ring
      linarith [h, he1, he2]
    have hB : Q * lam * w * (8 * Ke * lam * w / g) ≤ Q * lam * w * ((1 - lam) / 2) :=
      mul_le_mul_of_nonneg_left hb1 (by positivity)
    have hQw0 : (0:ℝ) ≤ Q * w := by positivity
    have hE : Q * lam * w ≤ Q * w * (1 + lam ^ 2) / 2 := by
      have hsq : (0:ℝ) ≤ (1 - lam)^2 := sq_nonneg _
      have h2l : 2 * lam ≤ 1 + lam^2 := by nlinarith [hsq]
      have hQw2 : (0:ℝ) ≤ Q * w / 2 := by positivity
      have h := mul_le_mul_of_nonneg_right h2l hQw2
      nlinarith [h]
    nlinarith [hA, hB, hE, hQ, hw, hlam0, hlam1]
  calc (1 / lam) * τ * (1 + 8 * ρ / g) = (1 / lam) * τ * (1 + 8 * Ke * lam * w / g) := by rw [h2]
    _ ≤ (Lam * w * (1 + Q * lam * w)) * (1 + 8 * Ke * lam * w / g) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ Lam * w * (1 + Q * w) := by
        have h := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ Lam * w)
        linarith [h]

/-! ## The majorant induction -/

/-- **The uniform estimate, inductively.**  There are constants `Ke, Λ, Q` and a radius `δ` such
that `FanGood a h Ke Λ Q ε v` holds for every branch word `ε` and every `‖v‖ < δ`. -/
theorem fan_induction {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ Ke Lam Q δ : ℝ, 0 < Ke ∧ 0 < Lam ∧ 0 < Q ∧ 0 < δ ∧
      ∀ ε : List Bool, ∀ v ∈ Metric.ball (0 : ℂ) δ, FanGood a h Ke Lam Q ε v := by
  obtain ⟨Kg, δg, hKg, hδg, hgan, hgb⟩ := fan_germC_local ha0 ha1 hh
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have h1mlam : (0 : ℝ) < 1 - eqLam a := by linarith
  set g : ℝ := (1 - a) / 2 with hgdef
  have hg0 : 0 < g := by rw [hgdef]; linarith
  -- the constants
  set Ke : ℝ := Kg + 1 + 1 / g ^ 2 + 1 with hKedef
  have hKe0 : 0 < Ke := by rw [hKedef]; positivity
  have hKeKg : Kg ≤ Ke := by
    rw [hKedef]
    have h1 : (0 : ℝ) ≤ 1 / g ^ 2 := by positivity
    linarith
  set Lam : ℝ := Kg + 1 + 1 with hLamdef
  have hLam0 : 0 < Lam := by rw [hLamdef]; linarith
  have hLamKg : Kg ≤ Lam := by rw [hLamdef]; linarith
  set Q : ℝ := 32 * Ke * eqLam a / (g * (1 - eqLam a)) + Kg + 1 with hQdef
  have hQ0 : 0 < Q := by
    rw [hQdef]
    have : 0 ≤ 32 * Ke * eqLam a / (g * (1 - eqLam a)) := by positivity
    linarith
  have hQKg : Kg ≤ Q := by
    rw [hQdef]
    have : 0 ≤ 32 * Ke * eqLam a / (g * (1 - eqLam a)) := by positivity
    linarith
  have hQbig : 16 * Ke * eqLam a ≤ Q * (1 - eqLam a) * g := by
    have h1 : (32 * Ke * eqLam a / (g * (1 - eqLam a)) + Kg + 1) * (1 - eqLam a) * g
        = 32 * Ke * eqLam a + (Kg + 1) * (1 - eqLam a) * g := by
      field_simp
      ring
    rw [hQdef, h1]
    have h2 : 0 ≤ (Kg + 1) * (1 - eqLam a) * g := by positivity
    have h3 : 0 ≤ 16 * Ke * eqLam a := by positivity
    linarith
  -- the radius
  set δ : ℝ := min (min (min δg (g / (16 * Ke * eqLam a)))
      (min (g / (32 * Lam * eqLam a)) (eqLam a / (16 * Lam))))
    (min (min (1 / (Q * eqLam a)) (Ke * (1 - eqLam a) * g ^ 2 / (64 * (Ke ^ 2 + 4 * Lam ^ 2))))
      ((1 - eqLam a) * g / (16 * Ke * eqLam a))) with hδdef
  have hδg' : δ ≤ δg :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδρ : δ ≤ g / (16 * Ke * eqLam a) :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδτ1 : δ ≤ g / (32 * Lam * eqLam a) :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδτ2 : δ ≤ eqLam a / (16 * Lam) :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδQ1 : δ ≤ 1 / (Q * eqLam a) :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδe : δ ≤ Ke * (1 - eqLam a) * g ^ 2 / (64 * (Ke ^ 2 + 4 * Lam ^ 2)) :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδw : δ ≤ (1 - eqLam a) * g / (16 * Ke * eqLam a) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hδpos : 0 < δ := by
    rw [hδdef]
    refine lt_min (lt_min (lt_min hδg (by positivity)) (lt_min (by positivity) (by positivity)))
      (lt_min (lt_min (by positivity) (by positivity)) (by positivity))
  refine ⟨Ke, Lam, Q, δ, hKe0, hLam0, hQ0, hδpos, ?_⟩
  intro ε
  induction ε with
  | nil =>
      intro v hv
      rw [Metric.mem_ball] at hv
      have hv' : ‖v‖ < δg := by
        simpa [dist_eq_norm] using lt_of_lt_of_le hv hδg'
      have hmem : v ∈ Metric.ball (0 : ℂ) δg := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hv'
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hgb v hmem
      have hw0 : fan a h [] v = germC a h v := rfl
      have hc0 : fan a h [] 0 = germC a h 0 := rfl
      refine ⟨hgan v hmem, ?_, ?_, hb1, hb2⟩
      · rw [hw0, hc0]
        exact le_trans hb3 (mul_le_mul_of_nonneg_right hKeKg (norm_nonneg v))
      · rw [hw0]
        have h1 : Kg * ‖v‖ ≤ Lam * ‖v‖ :=
          mul_le_mul_of_nonneg_right hLamKg (norm_nonneg v)
        have h2 : 1 + Kg * ‖v‖ ≤ 1 + Q * ‖v‖ := by
          have : Kg * ‖v‖ ≤ Q * ‖v‖ := mul_le_mul_of_nonneg_right hQKg (norm_nonneg v)
          linarith
        have h3 : 0 ≤ 1 + Kg * ‖v‖ := by positivity
        calc ‖(germC a h v).2 / ((germC a h v).1 - (a / 2 : ℂ))‖
            ≤ Kg * ‖v‖ * (1 + Kg * ‖v‖) := hb4
          _ ≤ Lam * ‖v‖ * (1 + Kg * ‖v‖) := mul_le_mul_of_nonneg_right h1 h3
          _ ≤ Lam * ‖v‖ * (1 + Q * ‖v‖) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
  | cons s ε ih =>
      intro v hv
      rw [Metric.mem_ball] at hv
      set w : ℝ := ‖v‖ with hwdef
      have hw0 : 0 ≤ w := by rw [hwdef]; positivity
      have hwlt : w < δ := by rw [hwdef]; simpa [dist_eq_norm] using hv
      have hlamv : ‖(eqLam a : ℂ) * v‖ = eqLam a * w := by
        rw [norm_mul, norm_ofReal_complex, abs_of_pos hlam0, hwdef]
      have hwlt' : ‖v‖ < δ := by rw [hwdef] at hwlt; exact hwlt
      have hwlv : ‖(eqLam a : ℂ) * v‖ < δ := norm_mul_lt_of_lt hlam0 hlam1 hδpos hwlt'
      obtain ⟨hcan, hcx, hcw, hcb, hcs⟩ := ih ((eqLam a : ℂ) * v)
        (Metric.mem_ball.mpr (by simpa [dist_eq_norm] using hwlv))
      -- the child's centre
      obtain ⟨hzsc, k, hkc⟩ := fan_centres ha0 ha1 hh ε
      have hcc : fan a h ε 0 = ((((-1 / 2 + 2 * (k : ℝ)) : ℝ) : ℂ), (0 : ℂ)) := by
        rw [Prod.ext_iff]; exact ⟨hkc, hzsc⟩
      set x1 : ℝ := -1 / 2 + 2 * (k : ℝ) with hx1def
      have hx1 : x1 = -1 / 2 + 2 * k := by rw [hx1def]
      obtain ⟨hxa, hxb, hxc, hxd, hxe, hxf⟩ := fan_centre_arithmetic ha0 ha1 hx1
      -- the parent's centre
      have hpar : (fan a h (s :: ε) 0).1 =
          (((-x1 + (if s then (1 : ℝ) else -1) * (if 0 < x1 + a / 2 then (1 : ℝ) else -1)) : ℝ) : ℂ) := by
        show (invBranch a s (fan a h ε ((eqLam a : ℂ) * 0))).1 = _
        rw [mul_zero, hcc, invBranch_axis hxa]
        split_ifs <;> push_cast <;> ring
      -- the step
      set ρ : ℝ := Ke * (eqLam a * w) with hρdef
      set τ : ℝ := Lam * (eqLam a * w) * (1 + Q * (eqLam a * w)) with hτdef
      have hρ0 : 0 ≤ ρ := by rw [hρdef]; positivity
      have hτ0 : 0 ≤ τ := by rw [hτdef]; positivity
      have hρg : ρ ≤ (1 - a) / 16 := by
        have h1 : Ke * (eqLam a * w) ≤ Ke * (eqLam a * δ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwlt.le hlam0.le) hKe0.le
        have h2 : Ke * (eqLam a * (g / (16 * Ke * eqLam a))) = g / 16 := by
          field_simp
        have h3 : δ ≤ g / (16 * Ke * eqLam a) := hδρ
        have h4 : Ke * (eqLam a * δ) ≤ Ke * (eqLam a * (g / (16 * Ke * eqLam a))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hlam0.le) hKe0.le
        rw [hgdef] at h2
        linarith [h1, h2, h4]
      have hτg : τ ≤ (1 - a) / 16 := by
        have hQlw : Q * (eqLam a * w) ≤ 1 := by
          have h1 : (Q * eqLam a) * w ≤ (Q * eqLam a) * δ := mul_le_mul_of_nonneg_left hwlt.le (by positivity)
          have h2 : (Q * eqLam a) * (1 / (Q * eqLam a)) = 1 := by field_simp
          have h3 : δ ≤ 1 / (Q * eqLam a) := hδQ1
          have h4 : (Q * eqLam a) * δ ≤ (Q * eqLam a) * (1 / (Q * eqLam a)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
          nlinarith [h1, h2, h4]
        have h1 : 1 + Q * (eqLam a * w) ≤ 2 := by linarith
        have h2 : τ ≤ Lam * (eqLam a * w) * 2 := by
          rw [hτdef]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : Lam * (eqLam a * w) * 2 ≤ Lam * (eqLam a * δ) * 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwlt.le hlam0.le) hLam0.le) (by norm_num)
        have h4 : Lam * (eqLam a * (g / (32 * Lam * eqLam a))) * 2 = g / 16 := by
          field_simp
          ring
        have h5 : δ ≤ g / (32 * Lam * eqLam a) := hδτ1
        have h6 : Lam * (eqLam a * δ) * 2 ≤ Lam * (eqLam a * (g / (32 * Lam * eqLam a))) * 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hlam0.le) hLam0.le) (by norm_num)
        have hτg' : τ ≤ g / 16 := by linarith [h2, h3, h4, h6]
        rw [show (1 - a) = 2 * g by rw [hgdef]; ring]
        linarith [hτg', hg0]
      have hτl : τ ≤ eqLam a ^ 2 / 8 := by
        have hQlw : Q * (eqLam a * w) ≤ 1 := by
          have h1 : (Q * eqLam a) * w ≤ (Q * eqLam a) * δ := mul_le_mul_of_nonneg_left hwlt.le (by positivity)
          have h2 : (Q * eqLam a) * (1 / (Q * eqLam a)) = 1 := by field_simp
          have h3 : δ ≤ 1 / (Q * eqLam a) := hδQ1
          have h4 : (Q * eqLam a) * δ ≤ (Q * eqLam a) * (1 / (Q * eqLam a)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
          nlinarith [h1, h2, h4]
        have h1 : 1 + Q * (eqLam a * w) ≤ 2 := by linarith
        have h2 : τ ≤ Lam * (eqLam a * w) * 2 := by
          rw [hτdef]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : Lam * (eqLam a * w) * 2 ≤ Lam * (eqLam a * δ) * 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwlt.le hlam0.le) hLam0.le) (by norm_num)
        have h4 : Lam * (eqLam a * (eqLam a / (16 * Lam))) * 2 = eqLam a ^ 2 / 8 := by
          field_simp
          ring
        have h5 : δ ≤ eqLam a / (16 * Lam) := hδτ2
        have h6 : Lam * (eqLam a * δ) * 2 ≤ Lam * (eqLam a * (eqLam a / (16 * Lam))) * 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hlam0.le) hLam0.le) (by norm_num)
        linarith [h2, h3, h4, h6]
      have hQlw : Q * (eqLam a * w) ≤ 1 := by
        have h1 : (Q * eqLam a) * w ≤ (Q * eqLam a) * δ :=
          mul_le_mul_of_nonneg_left hwlt.le (by positivity)
        have h2 : (Q * eqLam a) * (1 / (Q * eqLam a)) = 1 := by
          rw [mul_one_div_cancel (by positivity : (Q * eqLam a) ≠ 0)]
        have h4 : (Q * eqLam a) * δ ≤ (Q * eqLam a) * (1 / (Q * eqLam a)) :=
          mul_le_mul_of_nonneg_left hδQ1 (by positivity)
        nlinarith [h1, h2, h4]
      have hstep := fan_invBranch_step (s := s) ha0 ha1 hx1 hρ0 hτ0 hρg hτg hτl
        (Q := fan a h ε ((eqLam a : ℂ) * v))
        (by
          have h : ‖(fan a h ε ((eqLam a : ℂ) * v)).1 - (fan a h ε 0).1‖
              ≤ Ke * ‖(eqLam a : ℂ) * v‖ := hcx
          rw [hlamv] at h
          rw [hcc] at h
          rw [hρdef]
          exact h)
        hcb
        (by
          have h : ‖(fan a h ε ((eqLam a : ℂ) * v)).2
              / ((fan a h ε ((eqLam a : ℂ) * v)).1 - (a / 2 : ℂ))‖
              ≤ Lam * ‖(eqLam a : ℂ) * v‖ * (1 + Q * ‖(eqLam a : ℂ) * v‖) := hcw
          rw [hlamv] at h
          rw [hτdef]
          exact h)
      obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hstep
      -- the analyticity clause
      have han' : AnalyticAt ℂ (fan a h (s :: ε)) v := by
        show AnalyticAt ℂ (fun u => invBranch a s (fan a h ε ((eqLam a : ℂ) * u))) v
        have hcs' : 0 < ((((fan a h ε ((eqLam a : ℂ) * v)).1 + ((a / 2 : ℝ) : ℂ)) ^ 2
            + (fan a h ε ((eqLam a : ℂ) * v)).2 ^ 2)).re := by
          have hcast : ((a / 2 : ℝ) : ℂ) = (a / 2 : ℂ) := by push_cast; ring
          rw [hcast]; exact hcs
        have hcomp : AnalyticAt ℂ (fun u => fan a h ε ((eqLam a : ℂ) * u)) v :=
          AnalyticAt.comp (f := fun u => (eqLam a : ℂ) * u) (x := v) hcan
            (analyticAt_const.mul analyticAt_id)
        exact AnalyticAt.comp (f := fun u => fan a h ε ((eqLam a : ℂ) * u)) (x := v)
          (analyticAt_invBranch (s := s) (Or.inl hcs')) hcomp
      -- the abscissa clause
      have hfin1 : ‖(fan a h (s :: ε) v).1 - (fan a h (s :: ε) 0).1‖ ≤ Ke * w := by
        have h1 : (fan a h (s :: ε) v).1
            = (invBranch a s (fan a h ε ((eqLam a : ℂ) * v))).1 := rfl
        rw [h1, hpar]
        have hτ2 : τ ≤ 2 * Lam * eqLam a * w := by
          rw [hτdef]
          have h1 : 1 + Q * (eqLam a * w) ≤ 2 := by linarith
          have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ Lam * (eqLam a * w))
          linarith [h2]
        have hδe' : 64 * (Ke ^ 2 + 4 * Lam ^ 2) * w ≤ Ke * (1 - eqLam a) * g ^ 2 := by
          have h := mul_le_mul_of_nonneg_right (le_trans hwlt.le hδe)
            (by positivity : (0:ℝ) ≤ 64 * (Ke ^ 2 + 4 * Lam ^ 2))
          rw [div_mul_cancel₀ _ (by positivity : (64 * (Ke ^ 2 + 4 * Lam ^ 2)) ≠ 0)] at h
          linarith [h]
        have hρ' : ρ = Ke * eqLam a * w := by rw [hρdef]; ring
        have hclos := fan_closure_x hKe0 hLam0 hg0 hlam0 hlam1 hw0 hτ0 hρ' hτ2 hδe'
        exact le_trans hs1 hclos
      -- the semi-projective clause
      have hfin2 : ‖(fan a h (s :: ε) v).2 / ((fan a h (s :: ε) v).1 - (a / 2 : ℂ))‖
          ≤ Lam * w * (1 + Q * w) := by
        have h1 : (fan a h (s :: ε) v)
            = invBranch a s (fan a h ε ((eqLam a : ℂ) * v)) := rfl
        rw [h1]
        have hτsharp : τ ≤ Lam * eqLam a * w * (1 + Q * eqLam a * w) := by
          rw [hτdef]
          exact le_of_eq (by ring)
        have hδw' : 16 * Ke * eqLam a * w ≤ (1 - eqLam a) * g := by
          have h := mul_le_mul_of_nonneg_right (le_trans hwlt.le hδw)
            (by positivity : (0:ℝ) ≤ 16 * Ke * eqLam a)
          rw [div_mul_cancel₀ _ (by positivity : (16 * Ke * eqLam a) ≠ 0)] at h
          linarith [h]
        have hρ' : ρ = Ke * eqLam a * w := by rw [hρdef]; ring
        have hclos := fan_closure_w hKe0 hLam0 hQ0 hg0 hlam0 hlam1 hw0 hρ'
          hτsharp hτ0 hQbig hδw'
        exact le_trans hs2 hclos
      exact ⟨han', hfin1, hfin2, hs4, hs5⟩

/-! ## The final statement -/

/-- **Uniform fan estimates (Rychlik Thm 7(1), extreme property, Lemma 14).** On one disc,
every fan map is analytic, its centre lies on the axis at `-1/2 + 2ℤ`, and in semi-projective
terms (`x`, `w = y/(x - a/2)`) it stays within `1/4` of its centre. -/
theorem fan_estimates {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : List Bool,
      AnalyticOnNhd ℂ (fan a h ε) (Metric.ball 0 δ) ∧ (fan a h ε 0).2 = 0 ∧
      (∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k) ∧
      ∀ u ∈ Metric.ball (0 : ℂ) δ, ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ 1 / 4 ∧
        ‖(fan a h ε u).2‖ ≤ ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ / 4 := by
  obtain ⟨Ke, Lam, Q, δ0, hKe0, hLam0, hQ0, hδ0, hind⟩ := fan_induction ha0 ha1 hh
  set δ : ℝ := min δ0 (min (1 / (4 * Ke)) (min (1 / (8 * Lam)) (min (1 / (2 * Q)) 1)))
    with hδdef
  have hδle0 : δ ≤ δ0 := by
    rw [hδdef]; exact min_le_left _ _
  have hδleKe : δ ≤ 1 / (4 * Ke) := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδleLam : δ ≤ 1 / (8 * Lam) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδleQ : δ ≤ 1 / (2 * Q) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδle1 : δ ≤ 1 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min hδ0 (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) one_pos)))
  refine ⟨δ, hδpos, ?_⟩
  intro ε
  obtain ⟨hzc, k, hkc⟩ := fan_centres ha0 ha1 hh ε
  refine ⟨?_, hzc, ⟨k, ?_⟩, ?_⟩
  · -- analyticity
    intro v hv
    refine (hind ε v ?_).1
    rw [Metric.mem_ball] at hv ⊢
    exact lt_of_lt_of_le hv hδle0
  · -- the centre is at `-1/2 + 2ℤ`
    rw [hkc]; push_cast; ring
  · intro u hu
    rw [Metric.mem_ball] at hu
    have huw : ‖u‖ < δ := by simpa [dist_eq_norm] using hu
    have hu0 : u ∈ Metric.ball (0 : ℂ) δ0 := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      exact lt_of_lt_of_le huw hδle0
    obtain ⟨han, hx, hw, hb, hsl⟩ := hind ε u hu0
    have hcast : ((a / 2 : ℝ) : ℂ) = (a / 2 : ℂ) := by push_cast; ring
    refine ⟨?_, ?_⟩
    · -- the abscissa
      refine le_trans hx ?_
      have h2 : Ke * ‖u‖ ≤ Ke * (1 / (4 * Ke)) :=
        mul_le_mul_of_nonneg_left (le_trans huw.le hδleKe) hKe0.le
      have h3 : Ke * (1 / (4 * Ke)) = 1 / 4 := by
        field_simp
      linarith [h2, h3]
    · -- the semi-projective bound
      have hw' : ‖(fan a h ε u).2 / ((fan a h ε u).1 - ((a / 2 : ℝ) : ℂ))‖ ≤ 1 / 4 := by
        rw [hcast]
        refine le_trans hw ?_
        have h1 : Q * ‖u‖ ≤ 1 / 2 := by
          have h2 : ‖u‖ ≤ 1 / (2 * Q) := le_trans huw.le hδleQ
          have h3 : ‖u‖ * (2 * Q) ≤ 1 := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * Q)).mp h2
          nlinarith [h3, hQ0]
        have h4 : 1 + Q * ‖u‖ ≤ 2 := by linarith
        have h5 : Lam * ‖u‖ ≤ 1 / 8 := by
          have h6 : ‖u‖ ≤ 1 / (8 * Lam) := le_trans huw.le hδleLam
          have h7 : ‖u‖ * (8 * Lam) ≤ 1 := (le_div_iff₀ (by positivity : (0:ℝ) < 8 * Lam)).mp h6
          nlinarith [h7, hLam0]
        calc Lam * ‖u‖ * (1 + Q * ‖u‖) ≤ (1 / 8) * 2 :=
              mul_le_mul h5 h4 (by positivity) (by norm_num)
          _ = 1 / 4 := by norm_num
      have hb' : (fan a h ε u).1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by
        rw [hcast]; exact hb
      calc ‖(fan a h ε u).2‖
          = ‖((fan a h ε u).2 / ((fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)))
              * ((fan a h ε u).1 - ((a / 2 : ℝ) : ℂ))‖ := by
            rw [div_mul_cancel₀ _ hb']
        _ = ‖(fan a h ε u).2 / ((fan a h ε u).1 - ((a / 2 : ℝ) : ℂ))‖
              * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ := norm_mul _ _
        _ ≤ (1 / 4) * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
            mul_le_mul_of_nonneg_right hw' (norm_nonneg _)
        _ = ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ / 4 := by ring

end

end Work.EQ
