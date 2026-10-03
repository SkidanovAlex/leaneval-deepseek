import Mathlib

/-!
# Extending a holomorphic function across a point from `exp (-f) = g`

`Work.Potential.extend_of_exp_neg_eq`: if `f` is holomorphic on the punctured disc
`0 < ‖z‖ < ρ`, if `g` is holomorphic and nowhere vanishing on the disc `‖z‖ < ρ`, and if
`exp (-(f z)) = g z` off the origin, then `f` extends holomorphically across the origin
(without changing its values off the origin).

The proof has three ingredients, each isolated below.

* `isPreconnected_punctured_ball`: a punctured disc in `ℂ` is preconnected.
* `exists_local_log`: a nowhere-vanishing holomorphic function on a disc admits a holomorphic
  logarithm on a (possibly smaller) disc; the construction is principal-branch `Complex.log`
  of `g z / g 0`, valid as long as `g z / g 0` stays in the slit plane, which holds on a
  neighbourhood of `0` by continuity of `g` at `0`.
* `exists_eq_const_of_exp_eq_one`: a holomorphic function on a punctured disc whose exponential
  is identically `1` is constant there (differentiate and use that a function with vanishing
  derivative on an open preconnected set is constant).

Then, writing `L` for the local logarithm of `g`, the function `f + L` is holomorphic on a
punctured disc with `exp (f + L) = 1`, hence `f + L` is constant there; so `f` agrees on a
punctured neighbourhood of `0` with the holomorphic function `a - L`, which extends it.
-/

open Complex Metric Filter
open scoped Topology

noncomputable section

namespace Work.Potential

/-- **A punctured disc in `ℂ` is preconnected.**  For `δ > 0` the set `{z | 0 < ‖z‖ < δ}` is the
image of the punctured plane under the open partial homeomorphism `univBall 0 δ : ℂ → ball 0 δ`,
and the punctured plane is preconnected because `ℂ` has real dimension `> 1`. -/
theorem isPreconnected_punctured_ball {δ : ℝ} (hδ : 0 < δ) :
    IsPreconnected {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < δ} := by
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have h0 : IsPreconnected ({0}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank hrank 0).isPreconnected
  have hinj : Function.Injective (OpenPartialHomeomorph.univBall (0 : ℂ) δ) :=
    fun x y h => (OpenPartialHomeomorph.univBall (0 : ℂ) δ).injOn
      (by simp [OpenPartialHomeomorph.univBall_source])
      (by simp [OpenPartialHomeomorph.univBall_source]) h
  have himg : OpenPartialHomeomorph.univBall (0 : ℂ) δ '' ({0}ᶜ : Set ℂ)
      = Metric.ball (0 : ℂ) δ \ {0} := by
    rw [Set.compl_eq_univ_sdiff, Set.image_sdiff hinj,
      ← OpenPartialHomeomorph.univBall_source (0 : ℂ) δ,
      OpenPartialHomeomorph.image_source_eq_target,
      OpenPartialHomeomorph.univBall_target (0 : ℂ) hδ,
      Set.image_singleton, OpenPartialHomeomorph.univBall_apply_zero]
  have hset : Metric.ball (0 : ℂ) δ \ {0} = {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < δ} := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨norm_pos_iff.mpr h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, norm_ne_zero_iff.mp (ne_of_gt h1)⟩
  rw [hset] at himg
  rw [← himg]
  exact h0.image _
    ((OpenPartialHomeomorph.continuous_univBall (0 : ℂ) δ).continuousOn.mono (Set.subset_univ _))

/-- **Local holomorphic logarithm.**  If `g` is holomorphic and nowhere vanishing on the disc
`‖z‖ < ρ`, then on some disc `‖z‖ < δ` with `0 < δ ≤ ρ` there is a holomorphic `L` with
`exp (L z) = g z`.

The proof takes `L z = log (g 0) + log (g z / g 0)`; by continuity of `g` at `0` and
`g 0 ≠ 0`, the quotient `g z / g 0` lies in the slit plane for `‖z‖` small enough, where the
principal branch `Complex.log` is holomorphic. -/
theorem exists_local_log {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : ∀ z : ℂ, ‖z‖ < ρ → AnalyticAt ℂ g z)
    (hg0 : ∀ z : ℂ, ‖z‖ < ρ → g z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∃ L : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ < δ → AnalyticAt ℂ L z) ∧
      ∀ z : ℂ, ‖z‖ < δ → Complex.exp (L z) = g z := by
  have hc : g 0 ≠ 0 := hg0 0 (by simpa using hρ)
  have hcont : ContinuousAt g 0 := (hg 0 (by simpa using hρ)).continuousAt
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), ‖g z - g 0‖ < ‖g 0‖ / 2 := by
    have h1 : ContinuousAt (fun z : ℂ => ‖g z - g 0‖) 0 := (hcont.sub continuousAt_const).norm
    have h2 := (Metric.continuousAt_iff'.mp h1) (‖g 0‖ / 2) (by positivity)
    simpa [Real.dist_eq, sub_self, norm_zero, abs_of_nonneg (norm_nonneg _)] using h2
  obtain ⟨ε, hεpos, hεball⟩ := Metric.mem_nhds_iff.mp hev
  set δ : ℝ := min ε ρ with hδdef
  have hδpos : 0 < δ := lt_min hεpos hρ
  have hδε : δ ≤ ε := min_le_left _ _
  have hδρ : δ ≤ ρ := min_le_right _ _
  have hmem : ∀ z : ℂ, ‖z‖ < δ → g z / g 0 ∈ Complex.slitPlane := by
    intro z hz
    have hzin : z ∈ Metric.ball (0 : ℂ) ε := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hz hδε
    have h1 : ‖g z - g 0‖ < ‖g 0‖ / 2 := hεball hzin
    have h2 : ‖g z / g 0 - 1‖ < 1 := by
      have he : g z / g 0 - 1 = (g z - g 0) / g 0 := by field_simp
      rw [he, norm_div, div_lt_one (norm_pos_iff.mpr hc)]
      linarith [h1, norm_nonneg (g 0), norm_nonneg (g z - g 0)]
    simpa using Complex.mem_slitPlane_of_norm_lt_one h2
  refine ⟨δ, hδpos, hδρ, fun z => Complex.log (g 0) + Complex.log (g z / g 0), ?_, ?_⟩
  · intro z hz
    exact (analyticAt_const (v := Complex.log (g 0))).add
      (((hg z (lt_of_lt_of_le hz hδρ)).div analyticAt_const hc).clog (hmem z hz))
  · intro z hz
    have hne : g z / g 0 ≠ 0 := Complex.slitPlane_ne_zero (hmem z hz)
    rw [Complex.exp_add, Complex.exp_log hc, Complex.exp_log hne]
    field_simp

/-- **A holomorphic function on a punctured disc whose exponential is `1` is constant there.**
Differentiating the identity `exp (F ·) = 1` shows `deriv F = 0` on the punctured disc; a function
with vanishing derivative on an open preconnected set is constant. -/
theorem exists_eq_const_of_exp_eq_one {F : ℂ → ℂ} {δ : ℝ} (_hδ : 0 < δ)
    (hpre : IsPreconnected {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < δ})
    (hF : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ → AnalyticAt ℂ F z)
    (hexp : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ → Complex.exp (F z) = 1) :
    ∃ a : ℂ, ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ → F z = a := by
  have hUopen : IsOpen {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < δ} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hdiff : DifferentiableOn ℂ F {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < δ} :=
    fun z hz => (hF z hz.1 hz.2).differentiableAt.differentiableWithinAt
  have hfderiv : Set.EqOn (fderiv ℂ F) 0 {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < δ} := by
    intro z hz
    have heq : (fun w : ℂ => Complex.exp (F w)) =ᶠ[𝓝 z] (fun _ : ℂ => (1 : ℂ)) := by
      filter_upwards [hUopen.mem_nhds hz] with w hw
      exact hexp w hw.1 hw.2
    have hconst : HasDerivAt (fun w : ℂ => Complex.exp (F w)) 0 z :=
      (hasDerivAt_const z (1 : ℂ)).congr_of_eventuallyEq heq
    have hder : HasDerivAt (fun w : ℂ => Complex.exp (F w))
        (Complex.exp (F z) * deriv F z) z :=
      (Complex.hasDerivAt_exp (F z)).comp z ((hF z hz.1 hz.2).differentiableAt.hasDerivAt)
    have h0 : Complex.exp (F z) * deriv F z = 0 := hder.unique hconst
    have hder0 : deriv F z = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (Complex.exp_ne_zero _)
      · exact h
    refine ContinuousLinearMap.ext fun y => ?_
    simp [fderiv_eq_smul_deriv, hder0]
  obtain ⟨a, ha⟩ := hUopen.exists_is_const_of_fderiv_eq_zero hpre hdiff hfderiv
  exact ⟨a, fun z h1 h2 => ha z ⟨h1, h2⟩⟩

theorem extend_of_exp_neg_eq {f g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → AnalyticAt ℂ f z)
    (hg : ∀ z : ℂ, ‖z‖ < ρ → AnalyticAt ℂ g z)
    (hg0 : ∀ z : ℂ, ‖z‖ < ρ → g z ≠ 0)
    (hfg : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → Complex.exp (-(f z)) = g z) :
    ∃ G : ℂ → ℂ, (∀ z : ℂ, ‖z‖ < ρ → AnalyticAt ℂ G z) ∧
      ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → G z = f z := by
  obtain ⟨δ, hδpos, hδρ, L, hLana, hLexp⟩ := exists_local_log hρ hg hg0
  have hexpF : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ → Complex.exp (f z + L z) = 1 := by
    intro z h1 h2
    have hg_eq : Complex.exp (-(f z)) = g z := hfg z h1 (lt_of_lt_of_le h2 hδρ)
    have hLz : Complex.exp (L z) = g z := hLexp z h2
    have hgz : g z ≠ 0 := hg0 z (lt_of_lt_of_le h2 hδρ)
    have hfe : Complex.exp (f z) = (g z)⁻¹ := by
      have h := Complex.exp_neg (f z)
      rw [hg_eq] at h
      rw [h, inv_inv]
    rw [Complex.exp_add, hfe, hLz, inv_mul_cancel₀ hgz]
  obtain ⟨a, ha⟩ := exists_eq_const_of_exp_eq_one hδpos (isPreconnected_punctured_ball hδpos)
    (fun z h1 h2 => (hf z h1 (lt_of_lt_of_le h2 hδρ)).add (hLana z h2)) hexpF
  refine ⟨fun z => if z = 0 then a - L 0 else f z, ?_, ?_⟩
  · intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      have hev : (fun w : ℂ => a - L w) =ᶠ[𝓝 (0 : ℂ)]
          (fun w : ℂ => if w = 0 then a - L 0 else f w) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδpos] with w hw
        have hwn : ‖w‖ < δ := by rwa [Metric.mem_ball, dist_zero_right] at hw
        by_cases hw0 : w = 0
        · simp only [hw0, if_true]
        · have h1 : 0 < ‖w‖ := norm_pos_iff.mpr hw0
          have hw' : f w + L w = a := ha w h1 hwn
          simp only [hw0, if_false]
          rw [← hw']
          ring
      exact ((analyticAt_const (v := a) (x := (0 : ℂ))).sub
        (hLana 0 (by simpa using hδpos))).congr hev
    · have hev : f =ᶠ[𝓝 z] (fun w : ℂ => if w = 0 then a - L 0 else f w) := by
        filter_upwards [(isOpen_ne (x := (0 : ℂ))).mem_nhds hz0] with w hw
        simp only [hw, if_false]
      exact (hf z (norm_pos_iff.mpr hz0) hz).congr hev
  · intro z h1 h2
    show (if z = 0 then a - L 0 else f z) = f z
    rw [if_neg (norm_ne_zero_iff.mp (ne_of_gt h1))]

end Work.Potential
