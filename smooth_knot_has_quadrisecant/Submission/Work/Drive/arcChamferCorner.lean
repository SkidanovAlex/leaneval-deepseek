import Mathlib
import Submission.Work.Drive.chordFrame
import Submission.Work.Drive.transverse_structure_local

set_option maxHeartbeats 800000

/-!
# The arc–chamfer corner of the sweep is never a `π`-corner (pointwise form)

**This file was restored under a new path.**  Its content was written and verified at
`Submission/Work/Drive/arcChamferNoPiCorner.lean`; that path is now occupied by a *different*
(ongoing) development of the same corner by the Taylor expansion of the transverse component, so the
two theorems here have been renamed (`arcChamferCorner_pair`, `arcChamferCorner_noOpposite`) and
moved to this file.  The uniform-on-a-window form is `Work.Drive.arcChamfer_no_piCorner_window`
(`Submission/Work/Drive/arcChamferWindow.lean`), which imports *this* file.

At the corner where the retained arc of a chord sweep meets the first chamfer, the chamfer direction
`Q - P` (`P = r (b - lam*(b - a))` the last retained arc point, `Q = r b - lam • (r b - r a)` the
chord point at fraction `1 - lam`) is never a *negative* multiple of the tangent at `P`: this is the
"no `π` corner" input of the box-average step of the regularity pin `sweepFamVelNz`.

**Proof.**  Write `T := velocity r b`, `dv := r b - r a`, `dv = dvp + μ • T` with `dvp ⊥ T`.

* If `dvp ≠ 0`, pair the opposition with `T` and with `dvp/‖dvp‖`: the `T`-pairing and the
  mean-value estimates `‖(r b - r (b-h)) - h • T‖ ≤ C h²/2`, `‖velocity r (b-h) - T‖ ≤ C h` give
  `c = O(lam)`, and the second pairing then gives `‖dvp‖ = O(lam)` — a contradiction for small
  `lam`.  No `havoid`, no Taylor expansion.
* If `dvp = 0` (*fold*: the chord lies on the tangent line at `b`), pair the opposition with the
  normal `n` of `Work.Drive.transverse_structure_local` at `b`: the chord then lies in the tangent
  hyperplane at `b`, so the left side is `> 0` by the one-sidedness and the right side is
  `-c ⟪n, ·⟫ ≤ 0` by the one-sided monotonicity.  Analyticity enters only through
  `transverse_structure_local`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-- **Pairing the opposition equation with a fixed vector.** -/
lemma arcChamferCorner_pair {r : ℝ → Space} {b lam c θ : ℝ} {dv y : Space}
    (heq : (r b - lam • dv) - r θ = -c • velocity r θ) :
    inner ℝ y (r b) - lam * inner ℝ y dv - inner ℝ y (r θ)
      = -c * inner ℝ y (velocity r θ) := by
  have h := congrArg (fun x : Space => inner ℝ y x) heq
  rw [inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right] at h
  linarith [h]

/-- **The arc–chamfer corner is not a `π`-corner, pointwise.** -/
theorem arcChamferCorner_noOpposite {r : ℝ → Space} (hr : IsSmoothKnot r) {a b : ℝ}
    (hab : a < b) :
    ∃ L : ℝ, 0 < L ∧ ∀ lam : ℝ, 0 < lam → lam ≤ L →
      ¬ ∃ c : ℝ, 0 < c ∧
        (r b - lam • (r b - r a)) - r (b - lam * (b - a))
          = -c • velocity r (b - lam * (b - a)) := by
  obtain ⟨m, M, C, hm, hM, hC, hmin, hmax, hlip⟩ := exists_knot_c2_bounds (r := r) hr
  have hvelcont : Continuous (velocity r) := by
    have h : Continuous (deriv r) :=
      hr.smooth.continuous_deriv (by simp : (1 : WithTop ℕ∞) ≤ ⊤)
    rw [show velocity r = deriv r from rfl]
    exact h
  have hderiv : ∀ x : ℝ, HasDerivAt r (velocity r x) x :=
    fun x => ((hr.smooth.differentiable (by simp)) x).hasDerivAt
  have hftc : ∀ u v : ℝ, r v - r u = ∫ x in u..v, velocity r x := by
    intro u v
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) (hvelcont.intervalIntegrable _ _)).symm
  -- ### the two mean-value estimates
  have hE1 : ∀ h : ℝ, 0 < h →
      ‖(r b - r (b - h)) - h • velocity r b‖ ≤ C * h ^ 2 / 2 := by
    intro h hh
    have hsub : b - h ≤ b := by linarith
    have hkey : (∫ x in (b - h)..b, (velocity r x - velocity r b))
        = (r b - r (b - h)) - h • velocity r b := by
      rw [intervalIntegral.integral_sub (hvelcont.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _), hftc (b - h) b,
        intervalIntegral.integral_const]
      rw [show b - (b - h) = h by ring]
    have h2 : (∫ x in (b - h)..b, C * (b - x)) = C * h ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul]
      have hsplit : (∫ x in (b - h)..b, (b - x))
          = (∫ x in (b - h)..b, b) - (∫ x in (b - h)..b, x) := by
        rw [← intervalIntegral.integral_sub (f := fun _ : ℝ => b) (g := fun x : ℝ => x)
          (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
      have h3 : (∫ x in (b - h)..b, (b - x)) = h ^ 2 / 2 := by
        rw [hsplit, intervalIntegral.integral_const, integral_id,
          show b - (b - h) = h by ring]
        ring
      rw [h3]
      ring
    have hbound : ‖∫ x in (b - h)..b, (velocity r x - velocity r b)‖
        ≤ ∫ x in (b - h)..b, C * (b - x) := by
      refine intervalIntegral.norm_integral_le_of_norm_le
        (f := fun x : ℝ => velocity r x - velocity r b) (g := fun x : ℝ => C * (b - x))
        (μ := MeasureTheory.volume) hsub ?_ ?_
      · filter_upwards with x hx
        have h1 : ‖velocity r x - velocity r b‖ ≤ C * (b - x) := by
          have := hlip x b
          rwa [abs_of_nonneg (by linarith [hx.2])] at this
        exact h1
      · exact (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
    rw [hkey, h2] at hbound
    exact hbound
  have hE2 : ∀ h : ℝ, 0 < h → ‖velocity r (b - h) - velocity r b‖ ≤ C * h := by
    intro h hh
    have := hlip (b - h) b
    rwa [show |b - (b - h)| = h by
      rw [show b - (b - h) = h by ring, abs_of_pos hh]] at this
  -- ### the transverse structure at `b`
  obtain ⟨n, hn_ne, hnT, δ, hδ, hside, hmono⟩ := transverse_structure_local hr b
  have hn_deriv : ∀ θ ∈ Set.Ioo (b - δ) b, 0 ≤ inner ℝ n (velocity r θ) := by
    intro θ hθ
    have hdθ : HasDerivAt (fun x : ℝ => inner ℝ n (r x)) (inner ℝ n (velocity r θ)) θ := by
      have hd : HasDerivAt r (velocity r θ) θ := hderiv θ
      have h := (innerSL ℝ n).hasFDerivAt.comp θ hd.hasFDerivAt
      simpa [Function.comp_def, innerSL_apply_apply] using h.hasDerivAt
    have hmonoOn : MonotoneOn (fun x : ℝ => inner ℝ n (r x)) (Set.Ioo (b - δ) b) := by
      intro x hx y hy hxy
      have h := hmono x y hx.1 hxy hy.2
      rw [inner_sub_right, inner_sub_right] at h
      linarith [h]
    have h1 : 0 ≤ derivWithin (fun x : ℝ => inner ℝ n (r x)) (Set.Ioo (b - δ) b) θ :=
      hmonoOn.derivWithin_nonneg
    have h2 : derivWithin (fun x : ℝ => inner ℝ n (r x)) (Set.Ioo (b - δ) b) θ
        = deriv (fun x : ℝ => inner ℝ n (r x)) θ :=
      derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hθ)
    rw [h2, hdθ.deriv] at h1
    exact h1
  -- ### the setup of the chord
  set W : ℝ := b - a with hW
  have hWpos : 0 < W := sub_pos.mpr hab
  set T : Space := velocity r b with hTdef
  have hTpos : 0 < ‖T‖ := norm_pos_iff.mpr (hr.regular b)
  have hT2pos : 0 < ‖T‖ ^ 2 := by positivity
  set dv : Space := r b - r a with hdvdef
  set μ : ℝ := inner ℝ dv T / ‖T‖ ^ 2 with hμdef
  set dvp : Space := dv - μ • T with hdvpdef
  have hTdv : inner ℝ T dv = μ * ‖T‖ ^ 2 := by
    rw [hμdef, real_inner_comm]
    field_simp
  have hdvp_orth : inner ℝ dvp T = 0 := by
    have hne : ‖T‖ ≠ 0 := ne_of_gt hTpos
    have h1 : inner ℝ dvp T = inner ℝ dv T - μ * inner ℝ T T := by
      rw [hdvpdef, inner_sub_left, inner_smul_left]
      simp
    rw [h1, hμdef, real_inner_self_eq_norm_sq]
    have h2 : inner ℝ dv T = (inner ℝ dv T / ‖T‖ ^ 2) * ‖T‖ ^ 2 := by field_simp
    linarith [h2]
  have hdv_eq : dv = dvp + μ • T := by
    rw [hdvpdef]; abel
  -- ### the constants
  set K : ℝ := 2 * |μ - W| + C * W ^ 2 / ‖T‖ + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have h1 : 0 ≤ 2 * |μ - W| := by positivity
    have h2 : 0 ≤ C * W ^ 2 / ‖T‖ := by positivity
    linarith
  set K₂ : ℝ := C * (W ^ 2 / 2 + K * W) with hK2def
  have hK2pos : 0 < K₂ := by
    rw [hK2def]
    have h3 : 0 < W ^ 2 / 2 + K * W := by nlinarith [hWpos, hKpos]
    positivity
  set L : ℝ := min 1 (min (δ / (2 * W)) (min (‖T‖ / (2 * C * W))
      (if dvp = 0 then 1 else ‖dvp‖ / (2 * K₂)))) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    refine lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) ?_))
    split_ifs with h
    · norm_num
    · positivity
  have hL1 : L ≤ δ / (2 * W) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hL2 : L ≤ ‖T‖ / (2 * C * W) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hL3 : L ≤ 1 := min_le_left _ _
  have hL4 : L ≤ (if dvp = 0 then 1 else ‖dvp‖ / (2 * K₂)) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨L, hLpos, fun lam hlam0 hlamL => ?_⟩
  have hlam1 : lam ≤ 1 := le_trans hlamL hL3
  set h : ℝ := lam * W with hh
  have hhpos : 0 < h := mul_pos hlam0 hWpos
  have hhδ : h < δ := by
    have h1 : lam * W ≤ (δ / (2 * W)) * W :=
      mul_le_mul_of_nonneg_right (le_trans hlamL hL1) hWpos.le
    have h2 : (δ / (2 * W)) * W = δ / 2 := by field_simp
    rw [hh]
    linarith [h1, h2]
  have hhC : C * h ≤ ‖T‖ / 2 := by
    have h1 : lam * W ≤ (‖T‖ / (2 * C * W)) * W :=
      mul_le_mul_of_nonneg_right (le_trans hlamL hL2) hWpos.le
    have h2 : (‖T‖ / (2 * C * W)) * W = ‖T‖ / (2 * C) := by field_simp
    have h3 : C * (lam * W) ≤ C * (‖T‖ / (2 * C)) := by
      rw [← h2]
      exact mul_le_mul_of_nonneg_left h1 hC.le
    have h4 : C * (‖T‖ / (2 * C)) = ‖T‖ / 2 := by field_simp
    rw [hh]
    linarith [h3, h4]
  -- the assumed opposition
  rintro ⟨c, hc, heq⟩
  have hbha : b - h = b - lam * (b - a) := by rw [hh, hW]
  -- ### the `T`-pairing
  have hTpair : c * inner ℝ T (velocity r (b - h))
      = lam * (μ * ‖T‖ ^ 2) - inner ℝ T (r b - r (b - h)) := by
    have hpair := arcChamferCorner_pair (r := r) (b := b) (lam := lam) (c := c) (θ := b - h)
      (dv := dv) (y := T) (by rw [hbha]; exact heq)
    rw [hTdv] at hpair
    rw [inner_sub_right]
    linarith [hpair]
  -- ### the `T`-estimate: `c ≤ lam * K`
  have hTv : ‖T‖ ^ 2 - ‖T‖ * (C * h) ≤ inner ℝ T (velocity r (b - h)) := by
    have hsplit : inner ℝ T (velocity r (b - h))
        = inner ℝ T T + inner ℝ T (velocity r (b - h) - T) := by
      rw [inner_sub_right]; ring
    have hbd : -(‖T‖ * (C * h)) ≤ inner ℝ T (velocity r (b - h) - T) := by
      have h1 : |inner ℝ T (velocity r (b - h) - T)| ≤ ‖T‖ * (C * h) :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hE2 h hhpos) (norm_nonneg T))
      linarith [neg_le_of_abs_le h1]
    have hTn : inner ℝ T T = ‖T‖ ^ 2 := real_inner_self_eq_norm_sq T
    rw [hsplit, hTn]
    linarith [hbd]
  have hTE : h * ‖T‖ ^ 2 - ‖T‖ * (C * h ^ 2 / 2) ≤ inner ℝ T (r b - r (b - h)) := by
    have hsplit : inner ℝ T ((r b - r (b - h)) - h • T)
        = inner ℝ T (r b - r (b - h)) - h * ‖T‖ ^ 2 := by
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hbd : -(‖T‖ * (C * h ^ 2 / 2)) ≤ inner ℝ T ((r b - r (b - h)) - h • T) := by
      have h1 : |inner ℝ T ((r b - r (b - h)) - h • T)| ≤ ‖T‖ * (C * h ^ 2 / 2) :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hE1 h hhpos) (norm_nonneg T))
      linarith [neg_le_of_abs_le h1]
    linarith [hsplit, hbd]
  have hcK : c ≤ lam * K := by
    have hstep1 : c * (‖T‖ ^ 2 / 2) ≤ c * (‖T‖ ^ 2 - ‖T‖ * (C * h)) := by
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      nlinarith [hTpos, hhC]
    have hstep2 : c * (‖T‖ ^ 2 - ‖T‖ * (C * h))
        ≤ c * inner ℝ T (velocity r (b - h)) := mul_le_mul_of_nonneg_left hTv hc.le
    have hstep3 : c * inner ℝ T (velocity r (b - h))
        ≤ lam * (μ * ‖T‖ ^ 2) - h * ‖T‖ ^ 2 + ‖T‖ * (C * h ^ 2 / 2) := by
      rw [hTpair]
      linarith [hTE]
    have hmain : c * (‖T‖ ^ 2 / 2)
        ≤ lam * (μ - W) * ‖T‖ ^ 2 + ‖T‖ * (C * h ^ 2 / 2) := by
      have hrw : lam * (μ * ‖T‖ ^ 2) - h * ‖T‖ ^ 2 = lam * (μ - W) * ‖T‖ ^ 2 := by
        rw [hh]; ring
      linarith [hstep1, hstep2, hstep3, hrw.le, hrw.ge]
    have hμW : lam * (μ - W) * ‖T‖ ^ 2 ≤ lam * |μ - W| * ‖T‖ ^ 2 := by
      have h2 : (0:ℝ) ≤ lam * ‖T‖ ^ 2 := mul_nonneg hlam0.le (sq_nonneg _)
      nlinarith [le_abs_self (μ - W), h2]
    have hrest : ‖T‖ * (C * h ^ 2 / 2) ≤ lam * (C * W ^ 2 / ‖T‖) * (‖T‖ ^ 2 / 2) := by
      have h2 : h ^ 2 = lam * (W ^ 2 * lam) := by rw [hh]; ring
      have heq1 : ‖T‖ * (C * h ^ 2 / 2) = lam * (C * W ^ 2 * lam / 2) * ‖T‖ := by
        rw [h2]; ring
      rw [heq1]
      have h4 : lam * (C * W ^ 2 * lam / 2) * ‖T‖ ≤ lam * (C * W ^ 2 / 2) * ‖T‖ := by
        have h5 : C * W ^ 2 * lam / 2 ≤ C * W ^ 2 / 2 := by
          have h6 : C * W ^ 2 * lam ≤ C * W ^ 2 := by
            have h7 := mul_le_mul_of_nonneg_left hlam1 (mul_nonneg hC.le (sq_nonneg W))
            simpa using h7
          linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hlam0.le) hTpos.le
      refine h4.trans (le_of_eq ?_)
      field_simp
    have hKexp : lam * K * (‖T‖ ^ 2 / 2)
        = lam * |μ - W| * ‖T‖ ^ 2 + lam * (C * W ^ 2 / ‖T‖) * (‖T‖ ^ 2 / 2)
          + lam * 1 * (‖T‖ ^ 2 / 2) := by
      rw [hKdef]; ring
    have hfin : lam * (μ - W) * ‖T‖ ^ 2 + ‖T‖ * (C * h ^ 2 / 2)
        ≤ lam * K * (‖T‖ ^ 2 / 2) := by
      have hlast : (0:ℝ) ≤ lam * 1 * (‖T‖ ^ 2 / 2) := by positivity
      rw [hKexp]
      linarith [hμW, hrest, hlast]
    have hres := le_trans hmain hfin
    have hpos2 : (0:ℝ) < ‖T‖ ^ 2 / 2 := by positivity
    exact (mul_le_mul_iff_left₀ hpos2).mp hres
  -- ### the two cases
  by_cases hfold : dvp = 0
  · -- fold: pair with the one-sided normal `n`
    have hnpair : inner ℝ n (r b) - lam * inner ℝ n dv - inner ℝ n (r (b - h))
        = -c * inner ℝ n (velocity r (b - h)) :=
      arcChamferCorner_pair (r := r) (b := b) (lam := lam) (c := c) (θ := b - h)
        (dv := dv) (y := n) (by rw [hbha]; exact heq)
    have hndv : inner ℝ n dv = 0 := by
      have hdv' : dv = μ • T := by rw [hdv_eq, hfold, zero_add]
      rw [hdv', inner_smul_right, show inner ℝ n T = 0 from by rw [hTdef]; exact hnT]
      ring
    have hleft : 0 < inner ℝ n (r b) - inner ℝ n (r (b - h)) := by
      have h1 : 0 < inner ℝ n (r b - r (b - h)) := by
        have h2 := hside (b - h) (by linarith [hhδ]) (by linarith)
        rwa [hbha] at h2
      rwa [inner_sub_right] at h1
    have hright : 0 ≤ inner ℝ n (velocity r (b - h)) :=
      hn_deriv (b - h) ⟨by linarith [hhδ], by linarith⟩
    rw [hndv] at hnpair
    nlinarith [hnpair, hleft, hright, hc]
  · -- non-fold: pair with the unit vector in the direction of `dvp`
    set np : Space := ‖dvp‖⁻¹ • dvp with hnpdef
    have hdvp_pos : 0 < ‖dvp‖ := norm_pos_iff.mpr hfold
    have hnp_norm : ‖np‖ = 1 := by
      rw [hnpdef, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hdvp_pos,
        inv_mul_cancel₀ (ne_of_gt hdvp_pos)]
    have hnp_dvp : inner ℝ np dvp = ‖dvp‖ := by
      have hne : ‖dvp‖ ≠ 0 := ne_of_gt hdvp_pos
      have h1 : inner ℝ np dvp = ‖dvp‖⁻¹ * inner ℝ dvp dvp := by
        rw [hnpdef, inner_smul_left]
        simp
      rw [h1, real_inner_self_eq_norm_sq]
      field_simp
    have hnp_T : inner ℝ np T = 0 := by
      rw [hnpdef, inner_smul_left, hdvp_orth]
      simp
    have hnpair : inner ℝ np (r b) - lam * inner ℝ np dv - inner ℝ np (r (b - h))
        = -c * inner ℝ np (velocity r (b - h)) :=
      arcChamferCorner_pair (r := r) (b := b) (lam := lam) (c := c) (θ := b - h)
        (dv := dv) (y := np) (by rw [hbha]; exact heq)
    have hnpdv : inner ℝ np dv = ‖dvp‖ := by
      have h1 : dv = dvp + μ • T := hdv_eq
      calc inner ℝ np dv = inner ℝ np (dvp + μ • T) := by rw [h1]
        _ = inner ℝ np dvp + μ * inner ℝ np T := by rw [inner_add_right, inner_smul_right]
        _ = ‖dvp‖ := by rw [hnp_T, hnp_dvp]; ring
    rw [hnpdv] at hnpair
    have hb1 : inner ℝ np (r b) - inner ℝ np (r (b - h)) ≤ C * h ^ 2 / 2 := by
      have hsplit : inner ℝ np ((r b - r (b - h)) - h • T)
          = inner ℝ np (r b - r (b - h)) - h * inner ℝ np T := by
        rw [inner_sub_right, inner_smul_right]
      have hsplit2 : inner ℝ np (r b - r (b - h))
          = inner ℝ np (r b) - inner ℝ np (r (b - h)) := inner_sub_right _ _ _
      have hbd : inner ℝ np ((r b - r (b - h)) - h • T) ≤ C * h ^ 2 / 2 :=
        (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
          (by rw [hnp_norm]; simpa using hE1 h hhpos))
      rw [hsplit, hnp_T, mul_zero, sub_zero] at hbd
      linarith [hbd, hsplit2.le, hsplit2.ge]
    have hb2 : inner ℝ np (velocity r (b - h)) ≤ C * h := by
      have hsplit : inner ℝ np (velocity r (b - h))
          = inner ℝ np (velocity r (b - h) - T) := by
        rw [inner_sub_right, hnp_T]; ring
      rw [hsplit]
      exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
        (by rw [hnp_norm]; simpa using hE2 h hhpos))
    have hbound : lam * ‖dvp‖ ≤ C * h ^ 2 / 2 + (lam * K) * (C * h) := by
      have h1 : lam * ‖dvp‖ = (inner ℝ np (r b) - inner ℝ np (r (b - h)))
          + c * inner ℝ np (velocity r (b - h)) := by linarith [hnpair]
      have h2 : c * inner ℝ np (velocity r (b - h)) ≤ c * (C * h) :=
        mul_le_mul_of_nonneg_left hb2 hc.le
      have h3 : c * (C * h) ≤ (lam * K) * (C * h) :=
        mul_le_mul_of_nonneg_right hcK (by positivity)
      linarith [h1, hb1, h2, h3]
    have hK₂ : lam * ‖dvp‖ ≤ lam * (lam * K₂) := by
      have heq2 : C * h ^ 2 / 2 + (lam * K) * (C * h) = lam * (lam * K₂) := by
        rw [hK2def, hh]
        ring
      rw [← heq2]
      exact hbound
    have hL5 : lam ≤ ‖dvp‖ / (2 * K₂) := by
      have := le_trans hlamL hL4
      rwa [if_neg hfold] at this
    have hstep : lam * K₂ ≤ ‖dvp‖ / 2 := by
      have h1 : K₂ * lam ≤ K₂ * (‖dvp‖ / (2 * K₂)) :=
        mul_le_mul_of_nonneg_left hL5 hK2pos.le
      have h2 : K₂ * (‖dvp‖ / (2 * K₂)) = ‖dvp‖ / 2 := by field_simp
      linarith [h1, h2]
    have hnvp : ‖dvp‖ ≤ lam * K₂ := (mul_le_mul_iff_right₀ hlam0).mp hK₂
    linarith [hnvp, hstep, hdvp_pos]

end Work.Drive
