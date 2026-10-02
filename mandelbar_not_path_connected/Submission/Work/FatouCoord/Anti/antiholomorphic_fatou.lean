import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.coordError_bound
import Submission.Work.FatouCoord.Estimate.summable_coordError
import Submission.Work.FatouCoord.Estimate.iterate_re_growth
import Submission.Work.FatouCoord.Estimate.wMap_re_growth
import Submission.Work.FatouCoord.Exist.fatouCoordW_abel
import Submission.Work.FatouCoord.Exist.fatouCoordW_differentiable
import Submission.Work.FatouCoord.Exist.fatouCoordW_injOn
import Submission.Work.FatouCoord.Petal.petal_mapsTo
import Submission.Work.FatouCoord.Anti.g_second_order_limit
import Submission.Work.FatouCoord.Anti.fatouCoordW_eq_lim
import Submission.Work.FatouCoord.Anti.gW_sub_tend
import Submission.Work.FatouCoord.Anti.gW_log_tend

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Anti

open Work.FatouCoord Metric Set Filter
open scoped Topology

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

variable {f h g : ℂ → ℂ} {a : ℂ} {r A A' G : ℝ}

/-- The chart-conjugate of `g`: `gW g w = -1 / g (-1/w)`. -/
def gW (g : ℂ → ℂ) (w : ℂ) : ℂ := chart (g (chart w))

theorem chart_chart' (z : ℂ) : chart (chart z) = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · exact chart_chart hz

theorem star_ofReal' (t : ℝ) : star (t : ℂ) = (t : ℂ) := by
  rw [← starRingEnd_apply, Complex.conj_ofReal]

theorem gW_apply (w : ℂ) : gW g w = chart (g (chart w)) := rfl

theorem gW_chart {z : ℂ} (hz : z ≠ 0) : gW g (chart z) = chart (g z) := by
  rw [gW_apply, chart_chart hz]

theorem gW_wMap (hgg : ∀ z ∈ ball 0 r, g (g z) = f z)
    {w : ℂ} (hζ : chart w ∈ ball 0 r) (hgζ : g (chart w) ∈ ball 0 r) :
    gW g (wMap f w) = wMap f (gW g w) := by
  have h1 : g (f (chart w)) = f (g (chart w)) := by
    rw [← hgg (chart w) hζ, hgg (g (chart w)) hgζ]
  simp only [gW_apply, wMap, chart_chart']
  rw [h1]

theorem gW_gW (hgg : ∀ z ∈ ball 0 r, g (g z) = f z)
    {w : ℂ} (hζ : chart w ∈ ball 0 r) (hgζ : g (chart w) ∈ ball 0 r) :
    gW g (gW g w) = wMap f w := by
  simp only [gW_apply, wMap, chart_chart']
  rw [hgg (chart w) hζ]

/-- Membership in `comap Complex.re atTop`, spelled out with an explicit bound. -/
theorem eventually_comap_re {P : ℂ → Prop} :
    (∀ᶠ w in comap Complex.re atTop, P w) ↔ ∃ R : ℝ, ∀ w : ℂ, R ≤ w.re → P w := by
  rw [Filter.eventually_iff, Filter.mem_comap]
  constructor
  · rintro ⟨t, ht, hts⟩
    rw [Filter.mem_atTop_sets] at ht
    obtain ⟨x₀, hx₀⟩ := ht
    exact ⟨x₀, fun w hw => hts (hx₀ (w.re) hw)⟩
  · rintro ⟨R, hR⟩
    exact ⟨Set.Ici R, Filter.mem_atTop_sets.mpr ⟨R, fun _ hy => hy⟩, fun w hw => hR w hw⟩

/-- `star (Complex.log x) = Complex.log (star x)` for `x` in the right half-plane. -/
theorem star_log_of_re_pos {x : ℂ} (hx : 0 < x.re) :
    star (Complex.log x) = Complex.log (star x) := by
  have harg : x.arg ≠ Real.pi := by
    have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
    rw [abs_lt] at h
    intro hc
    rw [hc] at h
    linarith [Real.pi_pos]
  have h := Complex.log_conj x harg
  rw [starRingEnd_apply, starRingEnd_apply] at h
  exact h.symm

/-! ## The main computation in the chart -/

/-- The heart of the antiholomorphic Fatou-coordinate statement: the chart-coordinate
`ψ (gW w) - star (ψ w)` is the constant `star b`, and `b + star b = 1`. -/
theorem gamma_eq {f h g : ℂ → ℂ} {a : ℂ} {r A A' G : ℝ} {b : ℂ} {Nlim Nabel : ℝ}
    (hb : ParabolicBounds f h a r A A') (hgg : ∀ z ∈ ball 0 r, g (g z) = f z)
    (hg_lin : ∀ z ∈ ball 0 r, ‖g z - star z‖ ≤ G * ‖z‖ ^ 2)
    (hc : star (1 - a) = 1 - a)
    (hlim : ∀ x : ℂ, Nlim < x.re →
      Tendsto (fun n : ℕ => approxCoord (1 - a) ((wMap f)^[n] x) - (n : ℂ)) atTop
        (nhds (fatouCoordW f (1 - a) x)))
    (habel : ∀ x : ℂ, Nabel < x.re →
      fatouCoordW f (1 - a) (wMap f x) = fatouCoordW f (1 - a) x + 1)
    (hgW_tend : Tendsto (fun w : ℂ => gW g w - star w) (comap Complex.re atTop) (nhds (star b)))
    (hlog_tend : Tendsto (fun w : ℂ => Complex.log (gW g w) - Complex.log (star w))
      (comap Complex.re atTop) (nhds 0)) :
    ∃ M : ℝ, 0 < M ∧ (∀ w : ℂ, M < w.re → fatouCoordW f (1 - a) (gW g w)
        - star (fatouCoordW f (1 - a) w) = star b) ∧ b + star b = 1 := by
  obtain ⟨Ngr, hNgrpos, hrNgr, hgr⟩ := Estimate.wMap_re_growth hb
  obtain ⟨R1, hR1⟩ : ∃ R : ℝ, ∀ w : ℂ, R ≤ w.re → ‖gW g w - star w - star b‖ < 1 := by
    have hev : ∀ᶠ w in comap Complex.re atTop, gW g w - star w ∈ Metric.ball (star b) 1 :=
      hgW_tend.eventually (Metric.ball_mem_nhds _ one_pos)
    rw [eventually_comap_re] at hev
    obtain ⟨R, hR⟩ := hev
    refine ⟨R, fun w hw => ?_⟩
    have h := hR w hw
    rw [Metric.mem_ball, dist_eq_norm] at h
    simpa [sub_sub] using h
  -- the "good point" threshold
  let sΘ : Finset ℝ := {Ngr, 1 / r, 2 / r, 2 * |G| / r + 2, |G| + 1, 2, Nlim, Nabel}
  set Θ : ℝ := sΘ.max' (by simp [sΘ]) + 1 with hΘdef
  have hΘlt : ∀ x ∈ sΘ, x < Θ := fun x hx => by
    have := Finset.le_max' sΘ x hx
    rw [hΘdef]; linarith
  have hΘpos : 0 < Θ := by have := hΘlt 2 (by simp [sΘ]); linarith
  have hΘNgr : Ngr < Θ := hΘlt Ngr (by simp [sΘ])
  have hΘ2r : 2 / r < Θ := hΘlt (2 / r) (by simp [sΘ])
  have hΘG : 2 * |G| / r + 2 < Θ := hΘlt (2 * |G| / r + 2) (by simp [sΘ])
  have hΘG1 : |G| + 1 < Θ := hΘlt (|G| + 1) (by simp [sΘ])
  have hΘNlim : Nlim < Θ := hΘlt Nlim (by simp [sΘ])
  have hΘNabel : Nabel < Θ := hΘlt Nabel (by simp [sΘ])
  -- auxiliary real bounds
  have hΘinv : 1 / Θ < r / 2 := by
    rw [div_lt_iff₀ hΘpos]
    have h2 : 2 < r * Θ := by
      have := (div_lt_iff₀ hb.hr).mp hΘ2r
      linarith
    linarith
  have hΘGinv : |G| / Θ ^ 2 < r / 2 := by
    rw [div_lt_iff₀ (pow_pos hΘpos 2)]
    have h1 : |G| < r * Θ / 2 := by
      have h2 : 2 * |G| / r < Θ := by linarith [hΘG]
      have h3 : 2 * |G| < r * Θ := by
        have := (div_lt_iff₀ hb.hr).mp h2
        linarith
      linarith
    have h2 : r * Θ / 2 ≤ r / 2 * Θ ^ 2 := by
      have hA : r * Θ / 2 * 1 ≤ r * Θ / 2 * Θ :=
        mul_le_mul_of_nonneg_left (by linarith [hΘG1, abs_nonneg G])
          (by nlinarith [hb.hr, hΘpos])
      have hB : r * Θ / 2 * Θ = r / 2 * Θ ^ 2 := by ring
      linarith [hA, hB]
    linarith [h1, h2]
  -- the "good" level
  have hgood : ∀ x : ℂ, Θ < x.re →
      chart x ∈ ball 0 r ∧ g (chart x) ∈ ball 0 r ∧ chart x ≠ 0 ∧ g (chart x) ≠ 0 := by
    intro x hx
    have hxne : x ≠ 0 := by
      intro h0; rw [h0] at hx; simp at hx; linarith [hΘpos]
    have hcx : chart x ≠ 0 := chart_ne_zero hxne
    have hcn : ‖chart x‖ = 1 / ‖x‖ := by rw [norm_chart hxne, one_div]
    have hxn : Θ < ‖x‖ := lt_of_lt_of_le hx (Complex.re_le_norm x)
    have hxnp : 0 < ‖x‖ := lt_trans hΘpos hxn
    have hinv : 1 / ‖x‖ < 1 / Θ :=
      (div_lt_div_iff_of_pos_left one_pos hxnp hΘpos).mpr hxn
    have ha1 : ‖chart x‖ < r / 2 := by rw [hcn]; linarith [hinv, hΘinv]
    have ha : ‖chart x‖ < r := by linarith [hb.hr]
    refine ⟨mem_ball_zero_iff.mpr ha, ?_, hcx, ?_⟩
    · have hy : chart x ∈ ball 0 r := mem_ball_zero_iff.mpr ha
      have hb1 := hg_lin (chart x) hy
      have hgn : ‖g (chart x)‖ ≤ ‖chart x‖ + G * ‖chart x‖ ^ 2 := by
        have h1 : ‖g (chart x)‖ ≤ ‖g (chart x) - star (chart x)‖ + ‖star (chart x)‖ := by
          have := norm_add_le (g (chart x) - star (chart x)) (star (chart x))
          rwa [sub_add_cancel] at this
        rw [norm_star] at h1
        linarith [h1, hb1]
      have hG2 : G * ‖chart x‖ ^ 2 < r / 2 := by
        have hn2 : ‖chart x‖ ^ 2 = 1 / ‖x‖ ^ 2 := by rw [hcn, one_div, inv_pow, one_div]
        have h2 : G * ‖chart x‖ ^ 2 ≤ |G| * ‖chart x‖ ^ 2 := by
          have := le_abs_self G; nlinarith [sq_nonneg ‖chart x‖]
        have h3 : |G| * ‖chart x‖ ^ 2 < r / 2 := by
          rw [hn2, mul_one_div, div_lt_div_iff₀ (pow_pos hxnp 2) (by norm_num : (0:ℝ) < 2)]
          have h4 : 2 * |G| < r * ‖x‖ ^ 2 := by
            have h5 : 2 * |G| < r * Θ := by
              have h6 : 2 * |G| / r < Θ := by linarith [hΘG]
              have := (div_lt_iff₀ hb.hr).mp h6
              linarith
            have h7 : Θ ≤ ‖x‖ ^ 2 := by nlinarith [hxn, hΘG1, abs_nonneg G, hΘpos]
            nlinarith [h5, h7, hb.hr]
          linarith [h4]
        linarith [h2, h3]
      have hglt : ‖g (chart x)‖ < r := by linarith [hgn, hG2, ha1]
      exact mem_ball_zero_iff.mpr hglt
    · intro hgz
      have hy : chart x ∈ ball 0 r := mem_ball_zero_iff.mpr ha
      have hb1 := hg_lin (chart x) hy
      have hgn : ‖chart x‖ - G * ‖chart x‖ ^ 2 ≤ ‖g (chart x)‖ := by
        have h1 : ‖star (chart x)‖ ≤ ‖g (chart x) - star (chart x)‖ + ‖g (chart x)‖ := by
          have := norm_add_le (star (chart x) - g (chart x)) (g (chart x))
          rw [sub_add_cancel] at this
          rwa [norm_sub_rev] at this
        rw [norm_star] at h1
        linarith [h1, hb1]
      have hpos : 0 < ‖chart x‖ - G * ‖chart x‖ ^ 2 := by
        have hn2 : ‖chart x‖ ^ 2 = 1 / ‖x‖ ^ 2 := by rw [hcn, one_div, inv_pow, one_div]
        have h3 : G * ‖chart x‖ ^ 2 ≤ |G| * ‖chart x‖ ^ 2 := by
          have := le_abs_self G; nlinarith [sq_nonneg ‖chart x‖]
        have h4 : |G| * ‖chart x‖ ^ 2 < ‖chart x‖ := by
          rw [hn2, mul_one_div, hcn, div_lt_div_iff₀ (pow_pos hxnp 2) hxnp]
          have h5 : |G| * ‖x‖ < ‖x‖ ^ 2 := by
            have h6 : |G| < Θ := by linarith [hΘG1]
            nlinarith [h6, hxnp, hxn]
          linarith [h5]
        linarith [h3, h4]
      rw [hgz, norm_zero] at hgn
      linarith [hpos, hgn]
  let sM : Finset ℝ := {Θ + ‖star b‖ + 3, R1 + ‖star b‖ + 3, 0}
  set M : ℝ := sM.max' (by simp [sM]) + 1 with hMdef
  have hMlt : ∀ x ∈ sM, x < M := fun x hx => by
    have := Finset.le_max' sM x hx
    rw [hMdef]; linarith
  have hMpos : 0 < M := by have := hMlt 0 (by simp [sM]); linarith
  have hMΘ : Θ + ‖star b‖ + 3 < M := hMlt _ (by simp [sM])
  have hMR1 : R1 + ‖star b‖ + 3 < M := hMlt _ (by simp [sM])
  have hmain : ∀ w : ℂ, M < w.re → fatouCoordW f (1 - a) (gW g w)
      - star (fatouCoordW f (1 - a) w) = star b := by
    intro w hw
    have hwΘ : Θ < w.re := by linarith [hMΘ, norm_nonneg (star b)]
    have hwNlim : Nlim < w.re := lt_trans hΘNlim hwΘ
    have hvgrow : ∀ n : ℕ, w.re + (n : ℝ) / 2 ≤ ((wMap f)^[n] w).re := hgr w (lt_trans hΘNgr hwΘ)
    have hvΘ : ∀ n : ℕ, Θ < ((wMap f)^[n] w).re := by
      intro n
      have h1 := hvgrow n
      have h2 : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
      linarith [hMΘ, norm_nonneg (star b)]
    have hvgood : ∀ n : ℕ, chart ((wMap f)^[n] w) ∈ ball 0 r ∧
        g (chart ((wMap f)^[n] w)) ∈ ball 0 r :=
      fun n => ⟨(hgood _ (hvΘ n)).1, (hgood _ (hvΘ n)).2.1⟩
    have hvst : Tendsto (fun n : ℕ => ((wMap f)^[n] w).re) atTop atTop := by
      have hf1 : Tendsto (fun n : ℕ => (n : ℝ) / 2) atTop atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num)
      have hf2 : Tendsto (fun n : ℕ => w.re + (n : ℝ) / 2) atTop atTop :=
        tendsto_atTop_mono (fun n => by linarith) hf1
      exact tendsto_atTop_mono (fun n => hvgrow n) hf2
    have hvfilter : Tendsto (fun n : ℕ => (wMap f)^[n] w) atTop (comap Complex.re atTop) :=
      Filter.tendsto_comap_iff.mpr hvst
    have huΘ : Θ < (gW g w).re := by
      have hbn := hR1 w (le_of_lt (by linarith [hMR1, norm_nonneg (star b)] : R1 < w.re))
      have hsplit : gW g w = star w + (gW g w - star w - star b) + star b := by ring
      have h1 : (gW g w).re
          = (star w).re + (gW g w - star w - star b).re + (star b).re := by
        conv_lhs => rw [hsplit]
        simp only [Complex.add_re, Complex.sub_re]
      have h2 : -(‖gW g w - star w - star b‖) ≤ (gW g w - star w - star b).re := by
        have := Complex.abs_re_le_norm (gW g w - star w - star b)
        rw [abs_le] at this; linarith [this.1]
      have h3 : -(‖star b‖) ≤ (star b).re := by
        have := Complex.abs_re_le_norm (star b)
        rw [abs_le] at this; linarith [this.1]
      have h4 : (star w).re = w.re := by simp
      rw [h4] at h1
      linarith [h1, h2, h3, hbn, norm_nonneg (star b), hMΘ]
    have huNlim : Nlim < (gW g w).re := lt_trans hΘNlim huΘ
    have hiter : ∀ n : ℕ, (wMap f)^[n] (gW g w) = gW g ((wMap f)^[n] w) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        exact (gW_wMap hgg (hvgood n).1 (hvgood n).2).symm
    have h1 : Tendsto (fun n : ℕ => approxCoord (1 - a) ((wMap f)^[n] w) - (n : ℂ)) atTop
        (nhds (fatouCoordW f (1 - a) w)) := hlim w hwNlim
    have h2 : Tendsto (fun n : ℕ => approxCoord (1 - a) ((wMap f)^[n] (gW g w)) - (n : ℂ))
        atTop (nhds (fatouCoordW f (1 - a) (gW g w))) := hlim (gW g w) huNlim
    have h2' : Tendsto (fun n : ℕ => approxCoord (1 - a) (gW g ((wMap f)^[n] w)) - (n : ℂ))
        atTop (nhds (fatouCoordW f (1 - a) (gW g w))) :=
      Tendsto.congr' (Eventually.of_forall (fun n => by rw [hiter n])) h2
    have h3 : Tendsto (fun n : ℕ => (approxCoord (1 - a) (gW g ((wMap f)^[n] w)) - (n : ℂ))
        - star (approxCoord (1 - a) ((wMap f)^[n] w) - (n : ℂ))) atTop
        (nhds (fatouCoordW f (1 - a) (gW g w) - star (fatouCoordW f (1 - a) w))) :=
      h2'.sub h1.star
    have h3' : Tendsto (fun n : ℕ => approxCoord (1 - a) (gW g ((wMap f)^[n] w))
        - star (approxCoord (1 - a) ((wMap f)^[n] w))) atTop
        (nhds (fatouCoordW f (1 - a) (gW g w) - star (fatouCoordW f (1 - a) w))) := by
      refine Tendsto.congr' (Eventually.of_forall (fun n => ?_)) h3
      rw [star_sub, star_natCast]
      ring
    have h4 : Tendsto (fun n : ℕ => (gW g ((wMap f)^[n] w) - star ((wMap f)^[n] w))
        - (1 - a) * (Complex.log (gW g ((wMap f)^[n] w))
          - Complex.log (star ((wMap f)^[n] w)))) atTop (nhds (star b)) := by
      have haux := (hgW_tend.comp hvfilter).sub ((hlog_tend.comp hvfilter).const_mul (1 - a))
      simpa using haux
    have hEq : ∀ᶠ n in atTop, (gW g ((wMap f)^[n] w) - star ((wMap f)^[n] w))
        - (1 - a) * (Complex.log (gW g ((wMap f)^[n] w))
          - Complex.log (star ((wMap f)^[n] w)))
        = approxCoord (1 - a) (gW g ((wMap f)^[n] w))
          - star (approxCoord (1 - a) ((wMap f)^[n] w)) := by
      refine Eventually.of_forall (fun n => ?_)
      have hxre : 0 < ((wMap f)^[n] w).re := lt_trans hΘpos (hvΘ n)
      have hlog : star (Complex.log ((wMap f)^[n] w)) = Complex.log (star ((wMap f)^[n] w)) :=
        star_log_of_re_pos hxre
      have hstar : star (approxCoord (1 - a) ((wMap f)^[n] w))
          = star ((wMap f)^[n] w) - (1 - a) * Complex.log (star ((wMap f)^[n] w)) := by
        rw [approxCoord_apply, star_sub, star_mul, hc, hlog]
        ring
      rw [hstar, approxCoord_apply]
      ring
    have h3'' : Tendsto (fun n : ℕ => approxCoord (1 - a) (gW g ((wMap f)^[n] w))
        - star (approxCoord (1 - a) ((wMap f)^[n] w))) atTop (nhds (star b)) :=
      Tendsto.congr' hEq h4
    exact tendsto_nhds_unique h3' h3''
  refine ⟨M, hMpos, hmain, ?_⟩
  -- deduce `b + star b = 1`
  set w₀ : ℂ := ((M + ‖star b‖ + 3 : ℝ) : ℂ) with hw₀def
  have hw₀re : w₀.re = M + ‖star b‖ + 3 := by simp [hw₀def]
  have hw₀M : M < w₀.re := by rw [hw₀re]; linarith [norm_nonneg (star b)]
  have hw₀Θ : Θ < w₀.re := by linarith [hMΘ, norm_nonneg (star b)]
  have hu₀M : M < (gW g w₀).re := by
    have hbn := hR1 w₀ (le_of_lt (by rw [hw₀re]; linarith [norm_nonneg (star b)]))
    have hsplit : gW g w₀ = star w₀ + (gW g w₀ - star w₀ - star b) + star b := by ring
    have h1 : (gW g w₀).re
        = (star w₀).re + (gW g w₀ - star w₀ - star b).re + (star b).re := by
      conv_lhs => rw [hsplit]
      simp only [Complex.add_re, Complex.sub_re]
    have h2 : -(‖gW g w₀ - star w₀ - star b‖) ≤ (gW g w₀ - star w₀ - star b).re := by
      have := Complex.abs_re_le_norm (gW g w₀ - star w₀ - star b)
      rw [abs_le] at this; linarith [this.1]
    have h3 : -(‖star b‖) ≤ (star b).re := by
      have := Complex.abs_re_le_norm (star b)
      rw [abs_le] at this; linarith [this.1]
    have h4 : (star w₀).re = w₀.re := by simp
    rw [h4, hw₀re] at h1
    linarith [h1, h2, h3, hbn, norm_nonneg (star b)]
  have hγ₀ := hmain w₀ hw₀M
  have hγ₁ := hmain (gW g w₀) hu₀M
  have hgg₀ : gW g (gW g w₀) = wMap f w₀ :=
    gW_gW hgg (hgood w₀ hw₀Θ).1 (hgood w₀ hw₀Θ).2.1
  rw [hgg₀] at hγ₁
  have hab : fatouCoordW f (1 - a) (wMap f w₀) = fatouCoordW f (1 - a) w₀ + 1 :=
    habel w₀ (lt_trans hΘNabel hw₀Θ)
  rw [hab] at hγ₁
  have hstar : star (fatouCoordW f (1 - a) (gW g w₀)) = fatouCoordW f (1 - a) w₀ + b := by
    have := congrArg star hγ₀
    simp only [star_sub, star_star] at this
    linear_combination this
  rw [hstar] at hγ₁
  have hfin : (1 : ℂ) - b = star b := by rw [← hγ₁]; ring
  linear_combination -hfin

/-! ## The main theorem -/

theorem antiholomorphic_fatou {f h g : ℂ → ℂ} {a : ℂ} {r A A' G : ℝ} (hb : ParabolicBounds f h a r A A') (hreal : ∀ z ∈ ball 0 r, f (star z) = star (f z)) (hg_anti : ∀ z ∈ ball 0 r, DifferentiableAt ℂ (fun z => star (g z)) z) (hgg : ∀ z ∈ ball 0 r, g (g z) = f z) (hg0 : g 0 = 0) (hg_lin : ∀ z ∈ ball 0 r, ‖g z - star z‖ ≤ G * ‖z‖ ^ 2) : ∃ (M : ℝ) (s : ℂ), 0 < M ∧ IsAntiholomorphicFatouOn g (fun z => fatouCoord f (1 - a) z + s) (Petal r M) ∧ Set.InjOn (fun z => fatouCoord f (1 - a) z + s) (Petal r M) := by
  have hr : 0 < r := hb.hr
  -- `h 0 = 1`
  have h00 : h 0 = 1 := by
    have hcl := hb.h_close 0 (mem_ball_zero_iff.mpr (show ‖(0:ℂ)‖ < r by simpa using hr))
    have h1 : ‖h 0 - 1‖ ≤ 0 := by simpa using hcl
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
  -- `a` is real
  have ha_real : star a = a := by
    have hsym : ∀ t : ℝ, |t| < r → h (t : ℂ) = star (h (t : ℂ)) := by
      intro t ht
      rcases eq_or_ne t 0 with rfl | htne
      · simp [h00]
      · have htball : (t : ℂ) ∈ ball 0 r := by
          rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ht
        have h2 : f (t : ℂ) = star (f (t : ℂ)) := by
          have hh := hreal (t : ℂ) htball
          rwa [star_ofReal'] at hh
        have h3 : (t : ℂ) + (t : ℂ) ^ 2 * h (t : ℂ)
            = (t : ℂ) + (t : ℂ) ^ 2 * star (h (t : ℂ)) := by
          calc (t : ℂ) + (t : ℂ) ^ 2 * h (t : ℂ) = f (t : ℂ) := (hb.f_eq (t : ℂ) htball).symm
            _ = star (f (t : ℂ)) := h2
            _ = star ((t : ℂ) + (t : ℂ) ^ 2 * h (t : ℂ)) := by rw [hb.f_eq (t : ℂ) htball]
            _ = (t : ℂ) + (t : ℂ) ^ 2 * star (h (t : ℂ)) := by
                simp only [star_add, star_mul, star_pow, star_ofReal']
                ring
        have ht2 : (t : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast htne)
        exact mul_left_cancel₀ ht2 (add_left_cancel h3)
    have hlimR : Tendsto (fun t : ℝ => (h (t : ℂ) - 1) / (t : ℂ))
        (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds a) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hbound : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
          ‖(h (t : ℂ) - 1) / (t : ℂ) - a‖ ≤ A * |t| := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t htr htne
        rw [mem_ball_zero_iff, Real.norm_eq_abs] at htr
        have htball : (t : ℂ) ∈ ball 0 r := by
          rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact htr
        have hc := hb.h_close (t : ℂ) htball
        have htn : ‖(t : ℂ)‖ = |t| := by rw [Complex.norm_real, Real.norm_eq_abs]
        have htne0 : t ≠ 0 := by simpa using htne
        have htne' : (t : ℂ) ≠ 0 := by exact_mod_cast htne0
        have heq : (h (t : ℂ) - 1) / (t : ℂ) - a
            = (h (t : ℂ) - 1 - a * (t : ℂ)) / (t : ℂ) := by
          field_simp [htne']
        rw [heq, norm_div, htn]
        rw [div_le_iff₀ (abs_pos.mpr htne)]
        have hb2 : ‖h (t : ℂ) - 1 - a * (t : ℂ)‖ ≤ A * |t| ^ 2 := by
          have := hc; rwa [htn] at this
        calc ‖h (t : ℂ) - 1 - a * (t : ℂ)‖ ≤ A * |t| ^ 2 := hb2
          _ = A * |t| * |t| := by ring
      refine squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) hbound ?_
      have h1 : Tendsto (fun t : ℝ => |t|) (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) := by
        simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ) (a := (0 : ℝ)))
      simpa using h1.const_mul A
    have h2 : Tendsto (fun t : ℝ => (h (t : ℂ) - 1) / (t : ℂ))
        (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (star a)) := by
      have hev : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
          star ((h (t : ℂ) - 1) / (t : ℂ)) = (h (t : ℂ) - 1) / (t : ℂ) := by
        rw [eventually_nhdsWithin_iff]
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t htr htne
        rw [mem_ball_zero_iff, Real.norm_eq_abs] at htr
        have hsymt := hsym t htr
        rw [star_div₀, star_sub, star_one, ← hsymt, star_ofReal']
      exact Tendsto.congr' hev hlimR.star
    exact (tendsto_nhds_unique hlimR h2).symm
  have hc : star (1 - a) = 1 - a := by rw [star_sub, star_one, ha_real]
  -- collect the pieces
  obtain ⟨N1, hN1pos, hrN1, hdiff⟩ := Exist.fatouCoordW_differentiable hb
  obtain ⟨N2, hN2pos, hrN2, habel⟩ := Exist.fatouCoordW_abel hb
  obtain ⟨N3, hN3pos, hrN3, hlim3⟩ := Work.FatouCoord.Anti.fatouCoordW_eq_lim hb
  obtain ⟨N4, hN4pos, hrN4, hinj⟩ := Exist.fatouCoordW_injOn hb
  obtain ⟨b, hb_tend⟩ := Work.FatouCoord.Anti.g_second_order_limit hr hg_anti hg0 hg_lin
  have hgW_tend : Tendsto (fun w : ℂ => gW g w - star w) (comap Complex.re atTop)
      (nhds (star b)) := gW_sub_tend hr hg_lin hb_tend
  have hlog_tend : Tendsto (fun w : ℂ => Complex.log (gW g w) - Complex.log (star w))
      (comap Complex.re atTop) (nhds 0) := gW_log_tend hr hg_lin hb_tend
  obtain ⟨M1, hM1pos, hgamma, hbb⟩ := gamma_eq hb hgg hg_lin hc hlim3 habel hgW_tend hlog_tend
  set s : ℂ := (1 / 2 - star b) / 2 with hsdef
  set MF : ℝ := max M1 (max N1 N4) + 1 with hMFdef
  have hM1MF : M1 < MF := by
    rw [hMFdef]; have := le_max_left M1 (max N1 N4); linarith
  have hN1MF : N1 < MF := by
    rw [hMFdef]; have h := le_max_left N1 N4
    have h2 := le_max_right M1 (max N1 N4); linarith
  have hN4MF : N4 < MF := by
    rw [hMFdef]; have h := le_max_right N1 N4
    have h2 := le_max_right M1 (max N1 N4); linarith
  have hMFpos : 0 < MF := by
    rw [hMFdef]; have := le_max_left M1 (max N1 N4); linarith
  refine ⟨MF, s, hMFpos, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact (hg_anti z (Petal_subset_ball hz)).differentiableWithinAt
    · have hmaps : MapsTo chart (Petal r MF) {w : ℂ | N1 < w.re} := by
        intro z hz
        show N1 < (chart z).re
        have hz0 := ne_zero_of_mem_Petal hz
        have hns : 0 < Complex.normSq z := normSq_pos_of_mem_Petal hz
        rw [re_chart hz0, lt_div_iff₀ hns]
        nlinarith [hz.2, hns, hN1MF]
      have hchart : DifferentiableOn ℂ chart (Petal r MF) :=
        (differentiableOn_const (c := (-1 : ℂ))).div differentiableOn_id
          (fun z hz => ne_zero_of_mem_Petal hz)
      have hbase : DifferentiableOn ℂ (fun z => fatouCoord f (1 - a) z) (Petal r MF) :=
        hdiff.comp hchart hmaps
      exact hbase.add_const s
    · intro z hz
      have hz0 := ne_zero_of_mem_Petal hz
      have hns : 0 < Complex.normSq z := normSq_pos_of_mem_Petal hz
      have hzM1 : M1 < (chart z).re := by
        rw [re_chart hz0, lt_div_iff₀ hns]
        nlinarith [hz.2, hns, hM1MF]
      have hγ := hgamma (chart z) hzM1
      rw [gW_chart hz0] at hγ
      have h1 : fatouCoord f (1 - a) (g z) = star (fatouCoord f (1 - a) z) + star b := by
        rw [fatouCoord_eq, fatouCoord_eq]
        linear_combination hγ
      have hs : star b + s = star s + 1 / 2 := by
        have hs' : star s = (1 / 2 - b) / 2 := by
          rw [hsdef]
          simp only [star_div₀, star_sub, star_star]
          norm_num
        rw [hs', hsdef]
        linear_combination (1 / 2 : ℂ) * hbb
      show fatouCoord f (1 - a) (g z) + s = star (fatouCoord f (1 - a) z + s) + 1 / 2
      rw [h1, star_add]
      linear_combination hs
  · intro z1 hz1 z2 hz2 heq
    have hz10 := ne_zero_of_mem_Petal hz1
    have hz20 := ne_zero_of_mem_Petal hz2
    have hns1 : 0 < Complex.normSq z1 := normSq_pos_of_mem_Petal hz1
    have hns2 : 0 < Complex.normSq z2 := normSq_pos_of_mem_Petal hz2
    have hc1 : N4 < (chart z1).re := by
      rw [re_chart hz10, lt_div_iff₀ hns1]
      nlinarith [hz1.2, hns1, hN4MF]
    have hc2 : N4 < (chart z2).re := by
      rw [re_chart hz20, lt_div_iff₀ hns2]
      nlinarith [hz2.2, hns2, hN4MF]
    have heq' : fatouCoordW f (1 - a) (chart z1) = fatouCoordW f (1 - a) (chart z2) := by
      have h := heq
      simp only at h
      rw [fatouCoord_eq, fatouCoord_eq] at h
      exact add_right_cancel h
    exact chart_injective (hinj hc1 hc2 heq')

end

end Work.FatouCoord.Anti
