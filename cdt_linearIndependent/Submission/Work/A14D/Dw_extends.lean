import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.exists_sol_LZ_convex
import Submission.Work.A14D.eqOn_of_sol_LZ

/-!
# `Work.A14D.Dw_extends`: the `w`-pullback of a solution of `LZ y = 0` extends across `1/9`

Let `LZ y = P y'' + P' y' + R y` (`P = x(1−x)(1−9x)`) be Zagier's operator and
`wC z = z/(z−1)` the deck involution.  Every solution `D` of `LZ y = 0` on the slit plane
`Om1 = ℂ ∖ (−∞,1]` has a `w`-pullback `D ∘ wC` which is a solution of the conjugated operator
`LZw` on `Om1`; in particular `D ∘ wC` solves a linear ODE on the open upper half of the disc
`ball (1/9) δ` (`δ ≤ 1/20`).  The only singularities of `LZw` are `0, −1/8, 1` and

  `wC(1/9) = −1/8`,   `wC (ball (1/9) δ) ⊆ ball (−1/8) (1/10)`,

so the theorem below states the (true) fact that `D ∘ wC` continues holomorphically to the *whole*
disc `ball (1/9) δ`.

The proof avoids the conjugated operator altogether by pulling the geometry back to the `w`-side:
`ball (−1/8) (1/10)` is an **open convex** set on which `PZ` does not vanish, so the second order
equation `LZ y = 0` has a solution `E` there with prescribed Cauchy data (`exists_sol_LZ_convex`),
and any two solutions agree on the (open preconnected) lower half of that disc
(`eqOn_of_sol_LZ`).  Taking the Cauchy data of `D` itself at the point `−1/8 − i/100` therefore
gives a solution `E` of `LZ y = 0` on `ball (−1/8) (1/10)` which equals `D` on the lower half of
that disc.  Since `wC` maps `ball (1/9) δ` into `ball (−1/8) (1/10)`, and maps the upper half of
`ball (1/9) δ` into the lower half plane, the composite `E ∘ wC` is the required extension of
`D ∘ wC`; this is exactly the analytic continuation of `D` across the cut, as seen in the chart
`w` centered at `−1/8`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-! ## 1. The Möbius map `w(z) = z/(z−1)` near `1/9` -/

/-- The basic algebraic identity behind all the estimates: `w(z) + 1/8 = 9(z−1/9)/(8(z−1))`. -/
lemma wC_add_eighth {z : ℂ} (hz : z ≠ 1) : wC z + 1 / 8 = 9 * (z - ninth) / (8 * (z - 1)) := by
  rw [wC, ninth]
  field_simp
  ring

/-- `w` maps the disc `ball (1/9) δ` (`δ ≤ 1/20`) into the disc `ball (−1/8) (1/10)`: this is the
quantitative form of `w(1/9) = −1/8`. -/
lemma norm_wC_add_eighth_lt {δ : ℝ} (hδ20 : δ ≤ 1 / 20) {z : ℂ} (hz : z ∈ Metric.ball ninth δ) :
    ‖wC z + 1 / 8‖ < 1 / 10 := by
  have hzn : ‖z - ninth‖ < δ := by
    rw [Metric.mem_ball, Complex.dist_eq] at hz; exact hz
  by_cases hδ0 : 0 < δ
  · have hN : ‖(1 : ℂ) - ninth‖ = 8 / 9 := by
      rw [ninth]; norm_num [Complex.normSq_apply, Complex.norm_def]
    have hz1 : z ≠ 1 := by
      intro h; rw [h] at hzn; rw [hN] at hzn; linarith
    have hden : 8 / 9 - δ ≤ ‖z - 1‖ := by
      calc 8 / 9 - δ ≤ 8 / 9 - ‖z - ninth‖ := by linarith
        _ = ‖(1 : ℂ) - ninth‖ - ‖z - ninth‖ := by rw [hN]
        _ ≤ ‖((1 : ℂ) - ninth) - (z - ninth)‖ := norm_sub_norm_le _ _
        _ = ‖z - 1‖ := by rw [norm_sub_rev]; congr 1; ring
    have hid := wC_add_eighth hz1
    rw [hid, norm_div, norm_mul, norm_mul]
    have h9 : ‖(9 : ℂ)‖ = 9 := by norm_num [Complex.normSq_apply, Complex.norm_def]
    have h8 : ‖(8 : ℂ)‖ = 8 := by norm_num [Complex.normSq_apply, Complex.norm_def]
    rw [h9, h8]
    have hpos : 0 < 8 * ‖z - 1‖ := by
      have : 0 < 8 / 9 - δ := by linarith
      nlinarith [hden]
    rw [div_lt_iff₀ hpos]
    nlinarith [hzn, hden, hδ20]
  · have := norm_nonneg (z - ninth)
    linarith

/-- `w` maps the open upper half plane into the open lower half plane: for `z = x + iy` with
`y > 0` one has `Im w(z) = −y/‖z−1‖² < 0`.  (In particular it maps the upper half of the disc
`ball (1/9) δ` into the slit plane `Om1`.) -/
lemma wC_im_neg_of_pos {z : ℂ} (hz : 0 < z.im) : (wC z).im < 0 := by
  rw [wC, Complex.div_im]
  have h1 : (z - 1).im = z.im := by simp
  have h2 : (z - 1).re = z.re - 1 := by simp
  rw [h1, h2]
  have hN : 0 < Complex.normSq (z - 1) := by
    rw [Complex.normSq_pos]
    intro hc
    have : (z - 1).im = 0 := by rw [hc]; simp
    simp at this
    linarith
  have hnum : z.im * (z.re - 1) - z.re * z.im = -z.im := by ring
  rw [← sub_div, hnum]
  exact div_neg_of_neg_of_pos (by linarith) hN

/-- `PZ = z(1−z)(1−9z)` does not vanish on the disc `ball (−1/8) (1/10)`, so the operator `LZ` has
no singularity there.  (The ball lies in the half plane `Re z < −1/40`.) -/
lemma PZ_ne_zero_near_neg_eighth {z : ℂ} (hz : z ∈ Metric.ball (-(1 / 8) : ℂ) (1 / 10)) :
    PZ z ≠ 0 := by
  rw [Metric.mem_ball, Complex.dist_eq] at hz
  intro h
  rw [PZ] at h
  have hre : z.re < -(1 / 40) := by
    have h1 : |(z - (-(1 / 8) : ℂ)).re| ≤ ‖z - (-(1 / 8) : ℂ)‖ := Complex.abs_re_le_norm _
    have h2 : |(z - (-(1 / 8) : ℂ)).re| < 1 / 10 := lt_of_le_of_lt h1 hz
    have h3 : (z - (-(1 / 8) : ℂ)).re = z.re + 1 / 8 := by rw [Complex.sub_re]; norm_num
    rw [h3, abs_lt] at h2
    linarith [h2.2]
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · rw [h2] at hre; norm_num at hre
    · have hz1 : z = 1 := by linear_combination -h2
      rw [hz1] at hre; norm_num at hre
  · have h3 : 9 * z = 1 := by linear_combination -h1
    have hz9 : z = 1 / 9 := by
      rw [eq_div_iff (by norm_num : (9 : ℂ) ≠ 0)]
      linear_combination h3
    rw [hz9] at hre; norm_num at hre

/-- `w` is holomorphic on `ball (1/9) δ` as soon as `δ ≤ 1/20` (the pole `z = 1` is at distance
`8/9` from the centre). -/
lemma differentiableOn_wC_ball {δ : ℝ} (hδ20 : δ ≤ 1 / 20) :
    DifferentiableOn ℂ wC (Metric.ball ninth δ) := by
  unfold wC
  refine DifferentiableOn.div differentiableOn_id
    (differentiableOn_id.sub (differentiableOn_const 1)) ?_
  intro z hz h
  rw [sub_eq_zero] at h
  rw [h] at hz
  rw [Metric.mem_ball, Complex.dist_eq, ninth] at hz
  norm_num [Complex.normSq_apply, Complex.norm_def] at hz
  linarith

/-! ## 2. The extension -/

/-- The disc `ball (−1/8) (1/10)` around `wC(1/9) = −1/8` on which `LZ` is regular. -/
def discW : Set ℂ := Metric.ball (-(1 / 8) : ℂ) (1 / 10)

/-- **Extension of the `w`-pullback across the cut.**  Let `D` be a holomorphic solution of
`LZ y = 0` on the slit plane `Om1 = ℂ ∖ (−∞,1]`.  Then for every `0 < δ ≤ 1/20` the function
`z ↦ D (wC z)`, which is holomorphic on the upper half `halfU δ` of the disc `ball (1/9) δ`
(`wC` sends it into the lower half plane, where `D` is defined), extends holomorphically to the
whole disc `ball (1/9) δ`.

The extension is obtained by continuing `D` across the cut in the `w`-chart: the disc
`discW = ball (−1/8) (1/10)` is convex and free of singularities of `LZ`, `D` is defined on its
lower half (which lies in `Om1`), and a solution of `LZ y = 0` on that half continues uniquely to
`discW`; composing with `wC` gives the extension. -/
theorem Dw_extends {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1)
    (hDL : ∀ z ∈ Om1, LZ D z = 0) {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) :
    ∃ De : ℂ → ℂ, DifferentiableOn ℂ De (Metric.ball ninth δ) ∧
      ∀ z ∈ halfU δ, De z = D (wC z) := by
  -- `0 < δ` is not needed below (for `δ ≤ 0` the disc `ball (1/9) δ` is empty)
  have _ : (0 : ℝ) < δ := hδ
  have hΩo : IsOpen discW := by rw [discW]; exact Metric.isOpen_ball
  have hΩc : Convex ℝ discW := by rw [discW]; exact convex_ball (-(1 / 8) : ℂ) (1 / 10)
  have hPZ : ∀ z ∈ discW, PZ z ≠ 0 := by
    intro z hz
    rw [discW] at hz
    exact PZ_ne_zero_near_neg_eighth hz
  have hz₀W : ((-(1 / 8) : ℂ) - (1 / 100 : ℝ) * Complex.I) ∈ discW := by
    rw [discW, Metric.mem_ball, Complex.dist_eq]
    norm_num [Complex.normSq_apply, Complex.norm_def]
  -- Cauchy data at the point `z₀ = −1/8 − i/100` of the lower half of `discW`
  obtain ⟨E, hEdiff, hEz₀, hEd, -, hEL⟩ :=
    exists_sol_LZ_convex hΩo hΩc hPZ hz₀W
      (D ((-(1 / 8) : ℂ) - (1 / 100 : ℝ) * Complex.I))
      (deriv D ((-(1 / 8) : ℂ) - (1 / 100 : ℝ) * Complex.I))
  -- `D` and `E` agree on the (open, convex, hence preconnected) lower half of `discW`
  have hUo : IsOpen (discW ∩ {z : ℂ | z.im < 0}) := by
    rw [discW]
    exact Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_im continuous_const)
  have hUpc : IsPreconnected (discW ∩ {z : ℂ | z.im < 0}) := by
    rw [discW]
    exact ((convex_ball (-(1 / 8) : ℂ) (1 / 10)).inter
      (convex_halfSpace_im_lt 0)).isPreconnected
  have hUOm1 : (discW ∩ {z : ℂ | z.im < 0}) ⊆ Om1 := fun z hz => Or.inl (ne_of_lt hz.2)
  have hz₀U : ((-(1 / 8) : ℂ) - (1 / 100 : ℝ) * Complex.I) ∈ discW ∩ {z : ℂ | z.im < 0} :=
    ⟨hz₀W, by simp⟩
  have hEqUD : Set.EqOn E D (discW ∩ {z : ℂ | z.im < 0}) :=
    eqOn_of_sol_LZ hUo hUpc (fun z hz => hPZ z hz.1)
      (hEdiff.mono Set.inter_subset_left) (hD.mono hUOm1)
      (fun z hz => hEL z hz.1) (fun z hz => hDL z (hUOm1 hz))
      hz₀U hEz₀ hEd
  -- assembly: the extension is the `w`-pullback of `E`
  have hmaps : Set.MapsTo wC (Metric.ball ninth δ) discW := by
    intro z hz
    rw [discW, Metric.mem_ball, Complex.dist_eq]
    have hdist : wC z - (-(1 / 8) : ℂ) = wC z + 1 / 8 := by ring
    rw [hdist]
    exact norm_wC_add_eighth_lt hδ20 hz
  refine ⟨fun z => E (wC z), hEdiff.comp (differentiableOn_wC_ball hδ20) hmaps, ?_⟩
  intro z hz
  exact hEqUD ⟨hmaps hz.1, wC_im_neg_of_pos hz.2⟩

end

end Work.A14D
