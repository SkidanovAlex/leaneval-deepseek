/-
# The real slice: escape above `1/4`, and the real behaviour of `Φ`

This file collects the elementary facts about the restriction of the parameter theory to the
real axis which are used by the analysis of the parameter ray of angle `0`:

* for real `x > 1/4` the critical orbit of `T_x` is the real orbit of `t ↦ t² + x`, which
  increases by at least `x - 1/4` at every step, hence escapes; so `(x : ℂ) ∉ Mb`;
* `Φ` is continuous on the exterior of the mandelbar, because there it agrees with Nakane's
  homeomorphism;
* the asymptotic `Φ c / c → 1` restricts to the real axis, in both directions;
* for real `x` the value `Φ (x : ℂ)` is real, by conjugation equivariance.

## Main results

* `Work.ParamRays.real_not_mem_Mb_of_one_fourth_lt` : `1/4 < x → (x : ℂ) ∉ Mb`.
* `Work.ParamRays.continuousOn_Phi_compl` : `ContinuousOn Φ Mbᶜ`.
* `Work.ParamRays.Phi_tendsto_div_atTop`, `..._atBot` : `Φ x / x → 1` along the real axis.
* `Work.ParamRays.Phi_ofReal_eq_re` : `Φ (x : ℂ)` is fixed by conjugation.
* `Work.ParamRays.eventually_re_Phi_ofReal_pos`, `..._tendsto_norm_Phi_ofReal_atTop`.
-/
import Mathlib
import Submission.Work.ParamRays.Interface
import Submission.Work.ParamRays.continuous_potential

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The real orbit of `t ↦ t² + x` -/

/-- The orbit of `0` under the real quadratic map `t ↦ t² + x`. -/
noncomputable def realOrbit (x : ℝ) (n : ℕ) : ℝ := (fun t : ℝ => t ^ 2 + x)^[n] 0

theorem realOrbit_zero (x : ℝ) : realOrbit x 0 = 0 := rfl

theorem realOrbit_succ (x : ℝ) (n : ℕ) : realOrbit x (n + 1) = realOrbit x n ^ 2 + x := by
  simp only [realOrbit]
  rw [Function.iterate_succ_apply']

/-- For real `x` the critical orbit of `T_x` is the real orbit of `t ↦ t² + x`. -/
theorem critOrbit_ofReal_eq (x : ℝ) (n : ℕ) : critOrbit (x : ℂ) n = (realOrbit x n : ℂ) := by
  induction n with
  | zero => simp [realOrbit_zero, critOrbit]
  | succ n ih =>
      rw [show critOrbit (x : ℂ) (n + 1) = Tantibar (x : ℂ) (critOrbit (x : ℂ) n) from
        orbit_succ _ 0 n, ih, realOrbit_succ]
      simp only [Tantibar, Complex.conj_ofReal]
      push_cast
      ring

/-- Above `1/4` the real orbit increases by at least `x - 1/4` at every step. -/
theorem natCast_mul_le_realOrbit (x : ℝ) (n : ℕ) :
    (n : ℝ) * (x - 1 / 4) ≤ realOrbit x n := by
  induction n with
  | zero => simp [realOrbit_zero]
  | succ n ih =>
      rw [realOrbit_succ]
      have hring : realOrbit x n ^ 2 + x =
          realOrbit x n + (x - 1 / 4) + (realOrbit x n - 1 / 2) ^ 2 := by ring
      rw [hring]
      push_cast
      nlinarith [sq_nonneg (realOrbit x n - 1 / 2)]

/-- **Escape above the root point.**  For real `x > 1/4` the parameter `x` lies outside the
mandelbar. -/
theorem real_not_mem_Mb_of_one_fourth_lt {x : ℝ} (hx : 1 / 4 < x) : (x : ℂ) ∉ Mb := by
  intro hmem
  have hb : BoundedOrbit (x : ℂ) 0 := (mem_mandelbar_iff_bounded (x : ℂ)).mp hmem
  obtain ⟨M, hM⟩ := hb
  have hδ : 0 < x - 1 / 4 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (max M 0 / (x - 1 / 4))
  have hn' : max M 0 < (n : ℝ) * (x - 1 / 4) := by
    rw [div_lt_iff₀ hδ] at hn
    exact hn
  have hlt : M < realOrbit x n :=
    lt_of_le_of_lt (le_max_left M 0) (lt_of_lt_of_le hn' (natCast_mul_le_realOrbit x n))
  have hle : |realOrbit x n| ≤ M := by
    have h := hM n
    change ‖critOrbit (x : ℂ) n‖ ≤ M at h
    rw [critOrbit_ofReal_eq] at h
    simpa using h
  have : realOrbit x n ≤ M := le_trans (le_abs_self _) hle
  linarith

/-! ## `Φ` on the exterior of the mandelbar -/

/-- `Φ` is continuous on the exterior of the mandelbar, where it agrees with Nakane's
homeomorphism onto `‖w‖ > 1`. -/
theorem continuousOn_Phi_compl (hN : NakaneInput) : ContinuousOn Phi Mbᶜ := by
  obtain ⟨e, he⟩ := Phi_homeo hN
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : Mbᶜ.domRestrict Phi = fun c : ↥(Mbᶜ) => (e c : ℂ) := by
    funext c
    rw [Set.domRestrict_apply, ← he c]
  rw [hfun]
  exact continuous_subtype_val.comp e.continuous

/-! ## The asymptotic `Φ c / c → 1` along the real axis -/

theorem tendsto_ofReal_atTop_cocompact :
    Tendsto (fun x : ℝ => (x : ℂ)) atTop (Filter.cocompact ℂ) := by
  rw [hasBasis_cocompact.tendsto_right_iff]
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  filter_upwards [eventually_gt_atTop (max r 0)] with x hx
  simp only [Set.mem_compl_iff]
  intro hxK
  have h1 : (x : ℂ) ∈ Metric.closedBall (0 : ℂ) r := hr hxK
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : ‖(x : ℂ)‖ = x := by
    rw [show ‖(x : ℂ)‖ = |x| from by simp]
    exact abs_of_pos (by linarith [le_max_right r 0])
  rw [h2] at h1
  linarith [le_max_left r 0]

theorem tendsto_ofReal_atBot_cocompact :
    Tendsto (fun x : ℝ => (x : ℂ)) atBot (Filter.cocompact ℂ) := by
  rw [hasBasis_cocompact.tendsto_right_iff]
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  filter_upwards [eventually_lt_atBot (min (-r) 0)] with x hx
  simp only [Set.mem_compl_iff]
  intro hxK
  have h1 : (x : ℂ) ∈ Metric.closedBall (0 : ℂ) r := hr hxK
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : ‖(x : ℂ)‖ = -x := by
    rw [show ‖(x : ℂ)‖ = |x| from by simp]
    exact abs_of_neg (by linarith [le_min_iff.mp (le_refl (min (-r) 0))])
  rw [h2] at h1
  have : -x ≤ r := by linarith
  linarith [le_min_iff.mp (le_refl (min (-r) 0))]

/-- The asymptotic `Φ c / c → 1` restricted to the real axis, at `+ ∞`. -/
theorem Phi_tendsto_div_atTop (hN : NakaneInput) :
    Tendsto (fun x : ℝ => Phi (x : ℂ) / (x : ℂ)) atTop (nhds 1) :=
  (Phi_isBigO_atTop hN).comp tendsto_ofReal_atTop_cocompact

/-- The asymptotic `Φ c / c → 1` restricted to the real axis, at `- ∞`. -/
theorem Phi_tendsto_div_atBot (hN : NakaneInput) :
    Tendsto (fun x : ℝ => Phi (x : ℂ) / (x : ℂ)) atBot (nhds 1) :=
  (Phi_isBigO_atTop hN).comp tendsto_ofReal_atBot_cocompact

/-! ## `Φ` is real on the real axis -/

/-- Conjugation equivariance makes `Φ` real on the real axis. -/
theorem Phi_ofReal_conj_self (hconj : ∀ c : ℂ, Phi ((starRingEnd ℂ) c) =
    (starRingEnd ℂ) (Phi c)) (x : ℝ) : Phi (x : ℂ) = (starRingEnd ℂ) (Phi (x : ℂ)) := by
  simpa [Complex.conj_ofReal] using hconj (x : ℂ)

theorem Phi_ofReal_im_zero (hconj : ∀ c : ℂ, Phi ((starRingEnd ℂ) c) =
    (starRingEnd ℂ) (Phi c)) (x : ℝ) : (Phi (x : ℂ)).im = 0 :=
  Complex.conj_eq_iff_im.mp (Phi_ofReal_conj_self hconj x).symm

/-- A complex number with vanishing imaginary part is the real number of its real part. -/
theorem complex_eq_ofReal_re_of_im_zero {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp
  · simpa using h

/-- `Φ` of a real parameter is the real number given by its real part. -/
theorem Phi_ofReal_eq_re (hconj : ∀ c : ℂ, Phi ((starRingEnd ℂ) c) =
    (starRingEnd ℂ) (Phi c)) (x : ℝ) : Phi (x : ℂ) = ((Phi (x : ℂ)).re : ℂ) :=
  complex_eq_ofReal_re_of_im_zero (Phi_ofReal_im_zero hconj x)

/-! ## Consequences of the asymptotic for the real axis -/

/-- For large real `x` the real value `Φ (x : ℂ)` is positive. -/
theorem eventually_re_Phi_ofReal_pos (hN : NakaneInput) :
    ∀ᶠ x : ℝ in atTop, 0 < (Phi (x : ℂ)).re := by
  have h := Phi_tendsto_div_atTop hN
  filter_upwards [h.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0:ℝ) < 1/2)),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  rw [dist_eq_norm] at hx
  have h2 : ‖Phi (x : ℂ) / (x : ℂ) - 1‖ < 1 / 2 := hx
  have h3 : |(Phi (x : ℂ) / (x : ℂ)).re - 1| ≤ ‖Phi (x : ℂ) / (x : ℂ) - 1‖ := by
    have h4 : (Phi (x : ℂ) / (x : ℂ) - 1).re = (Phi (x : ℂ) / (x : ℂ)).re - 1 := by simp
    rw [← h4]
    exact Complex.abs_re_le_norm _
  have h4 : (Phi (x : ℂ) / (x : ℂ)).re = (Phi (x : ℂ)).re / x := by
    rw [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
    field_simp
    ring
  rw [h4] at h3
  have h5 : (Phi (x : ℂ)).re / x > 1 / 2 := by
    have h6 := abs_lt.mp (lt_of_le_of_lt h3 h2)
    linarith [h6.1]
  have h7 : 0 < (Phi (x : ℂ)).re / x := by linarith
  have h8 : 0 < (Phi (x : ℂ)).re / x * x := mul_pos h7 hx0
  rwa [div_mul_cancel₀ _ (ne_of_gt hx0)] at h8

/-- The modulus of `Φ` along the real axis tends to infinity. -/
theorem tendsto_norm_Phi_ofReal_atTop (hN : NakaneInput) :
    Tendsto (fun x : ℝ => ‖Phi (x : ℂ)‖) atTop atTop := by
  have h := Phi_tendsto_div_atTop hN
  have hev : ∀ᶠ x : ℝ in atTop, 1 / 2 < ‖Phi (x : ℂ) / (x : ℂ)‖ := by
    filter_upwards
      [h.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0:ℝ) < 1/2))] with x hx
    rw [dist_eq_norm] at hx
    have h4 : 1 - ‖Phi (x : ℂ) / (x : ℂ) - 1‖ ≤ ‖Phi (x : ℂ) / (x : ℂ)‖ := by
      have h5 := abs_norm_sub_norm_le (Phi (x : ℂ) / (x : ℂ)) 1
      rw [norm_one] at h5
      linarith [(abs_le.mp h5).1]
    linarith
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨i, hi⟩ := eventually_atTop.mp hev
  refine ⟨max (2 * (max b 0 + 1)) i, fun x hx => ?_⟩
  have hx2 : 2 * (max b 0 + 1) ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : i ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith [le_max_right b 0]
  have h3 : 1 / 2 < ‖Phi (x : ℂ) / (x : ℂ)‖ := hi x hx1
  have h5 : ‖Phi (x : ℂ)‖ = ‖Phi (x : ℂ) / (x : ℂ)‖ * x := by
    rw [norm_div, show ‖(x : ℂ)‖ = x from by
      rw [show ‖(x : ℂ)‖ = |x| from by simp]; exact abs_of_pos hx0]
    field_simp
  rw [h5]
  have h6 : x / 2 < ‖Phi (x : ℂ) / (x : ℂ)‖ * x := by nlinarith [h3, hx0]
  have h7 : max b 0 + 1 ≤ x / 2 := by linarith
  have h8 : b < max b 0 + 1 := lt_of_le_of_lt (le_max_left b 0) (by linarith)
  linarith

end Work.ParamRays
