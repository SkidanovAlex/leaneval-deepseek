import Mathlib
import Submission.Work.A14.defs

/-!
# `log`-structured vanishing (`Work.A14D.log_structured_vanishes`)

If `G` is holomorphic on the disc `ball ninth δ` (`ninth = 1/9`) and `B` is holomorphic on the
punctured disc `ball ninth δ \ {ninth}`, and `G z · log (z − ninth) + B z = 0` for every `z` in
the disc with `z.im ≠ 0`, then `G` vanishes on the whole disc.

The point is the branch cut of the principal logarithm along the negative real axis: for real
`x < 1/9` inside the disc, `x − ninth` is a negative real number, so approaching `x` from above
and from below gives the two one–sided limits `Real.log ‖x − ninth‖ ± π·I`, which differ by
`2π·I ≠ 0`.  Continuity of `G` and `B` at `x` produces the two relations

  `G x · (Real.log ‖x − ninth‖ + π·I) + B x = 0`,   `G x · (Real.log ‖x − ninth‖ − π·I) + B x = 0`,

whence `G x = 0` on the interval `(1/9 − δ, 1/9)`.  That interval accumulates at `ninth`, which
lies in the (connected, open) disc, so the identity theorem for analytic functions gives `G ≡ 0`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

private theorem log_structured_vanishes_aux {δ : ℝ} (hδ : 0 < δ) {G B : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball ninth δ))
    (hB : DifferentiableOn ℂ B (ball ninth δ \ {ninth}))
    (hid : ∀ z ∈ ball ninth δ, z.im ≠ 0 → G z * Complex.log (z - ninth) + B z = 0) :
    ∀ z ∈ ball ninth δ, G z = 0 := by
  have hnin : ninth = ((1 / 9 : ℝ) : ℂ) := by rw [ninth]; norm_num
  have hnorm : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := by
    intro r
    have h2 : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_sq_eq_abs]
  -- The two one-sided relations at a real point `x < 1/9` of the disc give `G x = 0`.
  have hInterval : ∀ x : ℝ, 1 / 9 - δ < x → x < 1 / 9 → G (x : ℂ) = 0 := by
    intro x hxa hxb
    set w : ℂ := (x : ℂ) - ninth with hw
    have hwre : w.re < 0 := by rw [hw, hnin]; simp; linarith
    have hwim : w.im = 0 := by rw [hw, hnin]; simp
    have hxball : (x : ℂ) ∈ ball ninth δ := by
      rw [mem_ball, dist_eq_norm]
      have hweq : (x : ℂ) - ninth = ((x - 1 / 9 : ℝ) : ℂ) := by rw [hnin]; push_cast; ring
      rw [hweq, hnorm, abs_of_neg (by linarith : x - 1 / 9 < 0)]
      linarith
    have hxne : (x : ℂ) ≠ ninth := by
      intro h
      have h9 : x = 1 / 9 := by
        apply Complex.ofReal_inj.mp
        rw [hnin] at h; simpa using h
      linarith
    have hGcont : ContinuousAt G (x : ℂ) :=
      (hG.differentiableAt (isOpen_ball.mem_nhds hxball)).continuousAt
    have hBmem : (ball ninth δ \ {ninth}) ∈ 𝓝 (x : ℂ) :=
      Filter.inter_mem (isOpen_ball.mem_nhds hxball)
        ((isClosed_singleton (x := ninth)).isOpen_compl.mem_nhds (by simpa using hxne))
    have hBcont : ContinuousAt B (x : ℂ) :=
      (hB.differentiableAt hBmem).continuousAt
    have hp_tend : Tendsto (fun ε : ℝ => (x : ℂ) + ε * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have h : ContinuousAt (fun ε : ℝ => (x : ℂ) + ε * Complex.I) 0 := by fun_prop
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    have hp_tend2 : Tendsto (fun ε : ℝ => (x : ℂ) - ε * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have h : ContinuousAt (fun ε : ℝ => (x : ℂ) - ε * Complex.I) 0 := by fun_prop
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    -- one-sided limits of `log (z - ninth)` for `z → x` from above / below
    have hlog_up : Tendsto (fun ε : ℝ => Complex.log ((x : ℂ) + ε * Complex.I - ninth)) (𝓝[>] 0)
        (𝓝 (Real.log ‖w‖ + Real.pi * Complex.I)) := by
      have hbase := Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hwre hwim
      have hmem : Tendsto (fun ε : ℝ => ((x : ℂ) + ε * Complex.I) - ninth) (𝓝[>] 0) (𝓝 w) := by
        have h : ContinuousAt (fun ε : ℝ => ((x : ℂ) + ε * Complex.I) - ninth) 0 := by fun_prop
        simpa [hw] using h.tendsto.mono_left nhdsWithin_le_nhds
      have hwith : Tendsto (fun ε : ℝ => ((x : ℂ) + ε * Complex.I) - ninth) (𝓝[>] 0)
          (𝓝[{z : ℂ | 0 ≤ z.im}] w) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hmem, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have hεim : (((x : ℂ) + ε * Complex.I) - ninth).im = ε := by rw [hnin]; simp
        rw [hεim]; exact le_of_lt hε
      exact hbase.comp hwith
    have hlog_dn : Tendsto (fun ε : ℝ => Complex.log ((x : ℂ) - ε * Complex.I - ninth)) (𝓝[>] 0)
        (𝓝 (Real.log ‖w‖ - Real.pi * Complex.I)) := by
      have hbase := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hwre hwim
      have hmem : Tendsto (fun ε : ℝ => ((x : ℂ) - ε * Complex.I) - ninth) (𝓝[>] 0) (𝓝 w) := by
        have h : ContinuousAt (fun ε : ℝ => ((x : ℂ) - ε * Complex.I) - ninth) 0 := by fun_prop
        simpa [hw] using h.tendsto.mono_left nhdsWithin_le_nhds
      have hwith : Tendsto (fun ε : ℝ => ((x : ℂ) - ε * Complex.I) - ninth) (𝓝[>] 0)
          (𝓝[{z : ℂ | z.im < 0}] w) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hmem, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have hεim : (((x : ℂ) - ε * Complex.I) - ninth).im = -ε := by rw [hnin]; simp
        rw [hεim]; exact neg_lt_zero.mpr hε
      exact hbase.comp hwith
    have hGt : Tendsto (fun ε : ℝ => G ((x : ℂ) + ε * Complex.I)) (𝓝[>] 0) (𝓝 (G (x : ℂ))) :=
      hGcont.tendsto.comp hp_tend
    have hBt : Tendsto (fun ε : ℝ => B ((x : ℂ) + ε * Complex.I)) (𝓝[>] 0) (𝓝 (B (x : ℂ))) :=
      hBcont.tendsto.comp hp_tend
    have hGt2 : Tendsto (fun ε : ℝ => G ((x : ℂ) - ε * Complex.I)) (𝓝[>] 0) (𝓝 (G (x : ℂ))) :=
      hGcont.tendsto.comp hp_tend2
    have hBt2 : Tendsto (fun ε : ℝ => B ((x : ℂ) - ε * Complex.I)) (𝓝[>] 0) (𝓝 (B (x : ℂ))) :=
      hBcont.tendsto.comp hp_tend2
    have hev_ball : ∀ᶠ ε : ℝ in 𝓝[>] 0, (x : ℂ) + ε * Complex.I ∈ ball ninth δ :=
      hp_tend (isOpen_ball.mem_nhds hxball)
    have hev_ball2 : ∀ᶠ ε : ℝ in 𝓝[>] 0, (x : ℂ) - ε * Complex.I ∈ ball ninth δ :=
      hp_tend2 (isOpen_ball.mem_nhds hxball)
    have hev_zero : (fun ε : ℝ => G ((x : ℂ) + ε * Complex.I)
        * Complex.log (((x : ℂ) + ε * Complex.I) - ninth) + B ((x : ℂ) + ε * Complex.I))
        =ᶠ[𝓝[>] 0] 0 := by
      filter_upwards [hev_ball, self_mem_nhdsWithin] with ε hbal hε
      have him : (((x : ℂ) + ε * Complex.I)).im ≠ 0 := by
        rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
          Complex.ofReal_re, Complex.ofReal_im]
        simp only [mul_one, mul_zero, add_zero, zero_add]
        exact ne_of_gt hε
      exact hid _ hbal him
    have hev_zero2 : (fun ε : ℝ => G ((x : ℂ) - ε * Complex.I)
        * Complex.log (((x : ℂ) - ε * Complex.I) - ninth) + B ((x : ℂ) - ε * Complex.I))
        =ᶠ[𝓝[>] 0] 0 := by
      filter_upwards [hev_ball2, self_mem_nhdsWithin] with ε hbal hε
      have him : (((x : ℂ) - ε * Complex.I)).im ≠ 0 := by
        rw [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
          Complex.ofReal_re, Complex.ofReal_im]
        simp only [mul_one, mul_zero, add_zero, zero_sub]
        exact ne_of_lt (neg_lt_zero.mpr hε)
      exact hid _ hbal him
    have hup : G (x : ℂ) * (Real.log ‖w‖ + Real.pi * Complex.I) + B (x : ℂ) = 0 := by
      have hcomb : Tendsto (fun ε : ℝ => G ((x : ℂ) + ε * Complex.I)
          * Complex.log (((x : ℂ) + ε * Complex.I) - ninth) + B ((x : ℂ) + ε * Complex.I))
          (𝓝[>] 0) (𝓝 (G (x : ℂ) * (Real.log ‖w‖ + Real.pi * Complex.I) + B (x : ℂ))) :=
        (hGt.mul hlog_up).add hBt
      have hzero : Tendsto (fun ε : ℝ => G ((x : ℂ) + ε * Complex.I)
          * Complex.log (((x : ℂ) + ε * Complex.I) - ninth) + B ((x : ℂ) + ε * Complex.I))
          (𝓝[>] 0) (𝓝 0) :=
        Filter.Tendsto.congr' hev_zero.symm tendsto_const_nhds
      exact tendsto_nhds_unique hcomb hzero
    have hdn : G (x : ℂ) * (Real.log ‖w‖ - Real.pi * Complex.I) + B (x : ℂ) = 0 := by
      have hcomb : Tendsto (fun ε : ℝ => G ((x : ℂ) - ε * Complex.I)
          * Complex.log (((x : ℂ) - ε * Complex.I) - ninth) + B ((x : ℂ) - ε * Complex.I))
          (𝓝[>] 0) (𝓝 (G (x : ℂ) * (Real.log ‖w‖ - Real.pi * Complex.I) + B (x : ℂ))) :=
        (hGt2.mul hlog_dn).add hBt2
      have hzero : Tendsto (fun ε : ℝ => G ((x : ℂ) - ε * Complex.I)
          * Complex.log (((x : ℂ) - ε * Complex.I) - ninth) + B ((x : ℂ) - ε * Complex.I))
          (𝓝[>] 0) (𝓝 0) :=
        Filter.Tendsto.congr' hev_zero2.symm tendsto_const_nhds
      exact tendsto_nhds_unique hcomb hzero
    have h1 : G (x : ℂ) * (Real.log ‖w‖ + Real.pi * Complex.I) = - B (x : ℂ) :=
      eq_neg_of_add_eq_zero_left hup
    have h2 : G (x : ℂ) * (Real.log ‖w‖ - Real.pi * Complex.I) = - B (x : ℂ) :=
      eq_neg_of_add_eq_zero_left hdn
    have key : G (x : ℂ)
        * ((Real.log ‖w‖ + Real.pi * Complex.I) - (Real.log ‖w‖ - Real.pi * Complex.I)) = 0 := by
      rw [mul_sub, h1, h2, sub_self]
    have hne : (Real.log ‖w‖ + Real.pi * Complex.I) - (Real.log ‖w‖ - Real.pi * Complex.I) ≠ 0 := by
      have hrw : (Real.log ‖w‖ + Real.pi * Complex.I) - (Real.log ‖w‖ - Real.pi * Complex.I)
          = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hrw]
      exact mul_ne_zero (by norm_num [Real.pi_ne_zero]) Complex.I_ne_zero
    exact (mul_eq_zero.mp key).resolve_right hne
  -- The interval `(1/9 − δ, 1/9)` accumulates at `ninth`, so the identity theorem applies.
  have hAnal : AnalyticOnNhd ℂ G (ball ninth δ) := hG.analyticOnNhd isOpen_ball
  have hpre : IsPreconnected (ball ninth δ) := (convex_ball ninth δ).isPreconnected
  have hmem : ninth ∈ ball ninth δ := mem_ball_self hδ
  have hclos : ninth ∈ closure ({z : ℂ | G z = 0} \ {ninth}) := by
    have hsub : ((fun x : ℝ => (x : ℂ)) '' (Set.Ioo (1 / 9 - δ) (1 / 9)))
        ⊆ ({z : ℂ | G z = 0} \ {ninth}) := by
      rintro z ⟨x, hx, rfl⟩
      refine ⟨hInterval x hx.1 hx.2, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro h
      have h9 : x = 1 / 9 := by
        apply Complex.ofReal_inj.mp
        rw [hnin] at h; simpa using h
      exact absurd h9 (ne_of_lt hx.2)
    refine closure_mono hsub ?_
    have h1 : (1 / 9 : ℝ) ∈ closure (Set.Ioo (1 / 9 - δ) (1 / 9)) := by
      rw [closure_Ioo (by linarith : (1 / 9 - δ) ≠ 1 / 9)]
      exact ⟨by linarith, le_refl _⟩
    have h3 : (((1 / 9 : ℝ)) : ℂ)
        ∈ ((fun x : ℝ => (x : ℂ)) '' closure (Set.Ioo (1 / 9 - δ) (1 / 9))) := ⟨1 / 9, h1, rfl⟩
    have h4 : (((1 / 9 : ℝ)) : ℂ) = ninth := hnin.symm
    rw [h4] at h3
    exact image_closure_subset_closure_image Complex.continuous_ofReal h3
  intro z hz
  exact hAnal.eqOn_zero_of_preconnected_of_mem_closure hpre hmem hclos hz

/-- If `G` is holomorphic on the disc `ball ninth δ`, `B` is holomorphic on the punctured disc,
and `G z · log (z − ninth) + B z = 0` off the real axis, then `G ≡ 0` on the disc. -/
theorem log_structured_vanishes {δ : ℝ} (hδ : 0 < δ) {G B : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball ninth δ))
    (hB : DifferentiableOn ℂ B (ball ninth δ \ {ninth}))
    (hid : ∀ z ∈ ball ninth δ, z.im ≠ 0 → G z * Complex.log (z - ninth) + B z = 0) :
    ∀ z ∈ ball ninth δ, G z = 0 :=
  log_structured_vanishes_aux hδ hG hB hid

namespace Work.A14D

/-- The same statement under the doubled-namespace name `Work.A14D.Work.A14D.log_structured_vanishes`
(the name under which the seeded file originally declared it). -/
theorem log_structured_vanishes {δ : ℝ} (hδ : 0 < δ) {G B : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball ninth δ))
    (hB : DifferentiableOn ℂ B (ball ninth δ \ {ninth}))
    (hid : ∀ z ∈ ball ninth δ, z.im ≠ 0 → G z * Complex.log (z - ninth) + B z = 0) :
    ∀ z ∈ ball ninth δ, G z = 0 :=
  log_structured_vanishes_aux hδ hG hB hid

end Work.A14D

end Work.A14D
