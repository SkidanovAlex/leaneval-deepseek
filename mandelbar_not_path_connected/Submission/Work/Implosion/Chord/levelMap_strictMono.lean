/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The level map of the chord foliation is strictly monotone and onto

Let `Φ = modelDisp a h` be the displacement of the Écalle coordinate in one
iterate (see `Disp.lean`) and let `transitMap a h u = u + Φ u` be the induced
map.  On a vertical line `{u : ℂ | u.re = x}` — every point of which is of the
form `x + i y` — consider the **level map**

  `F y = (transitMap a h (x + i y)).im = y + (Φ (x + i y)).im`.

If `Φ` is complex differentiable at every point of that line and its derivative
is bounded by `δ < 1` there, then `Φ` is `δ`-Lipschitz along the line (mean
value inequality on the convex set `{u | u.re = x}`, whose points are exactly
the `x + i y`), so

  `F y₂ - F y₁ ≥ (1 - δ) (y₂ - y₁)`   for `y₁ ≤ y₂`.

Since `δ < 1`, `F` is strictly increasing, and the growth bound together with
the continuity of `F` (which follows from differentiability of `Φ` along the
line) shows `F` is unbounded above and below, hence — by the intermediate value
theorem — surjective onto `ℝ`.

Note that `hM`/`hbound` are not needed for the conclusion; they are kept because
they are part of the statement.  The hypothesis `hdiff` is essential: where `Φ`
fails to be complex differentiable, `deriv Φ` vanishes and no longer controls
the behaviour of `Φ`.
-/
import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Disp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Chord

open Complex
open scoped Topology

set_option linter.unusedVariables false

theorem levelMap_strictMono (a : ℂ) (h : ℂ → ℂ) (x δ M : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hM : 0 ≤ M)
    (hdiff : ∀ y : ℝ, DifferentiableAt ℂ (modelDisp a h) (x + y * I))
    (hderiv : ∀ y : ℝ, ‖deriv (modelDisp a h) (x + y * I)‖ ≤ δ)
    (hbound : ∀ y : ℝ, ‖modelDisp a h (x + y * I)‖ ≤ M) :
    StrictMono (fun y : ℝ => (transitMap a h (x + y * I)).im)
      ∧ Set.SurjOn (fun y : ℝ => (transitMap a h (x + y * I)).im) Set.univ Set.univ := by
  -- The level map written out: it is the level plus the imaginary part of the displacement.
  have hfun : ∀ y : ℝ, (transitMap a h (x + y * I)).im
      = y + (modelDisp a h (x + y * I)).im := by
    intro y
    rw [transitMap_apply, Complex.add_im]
    simp
  -- The vertical line is convex.
  have hconv : Convex ℝ {u : ℂ | u.re = x} := by
    intro u hu v hv r s _ _ hrs
    change u.re = x at hu
    change v.re = x at hv
    change (r • u + s • v).re = x
    rw [Complex.add_re, Complex.smul_re, Complex.smul_re, hu, hv]
    simp only [smul_eq_mul]
    linear_combination (x) * hrs
  -- The hypotheses hold at every point of the line.
  have hdmem : ∀ u ∈ {u : ℂ | u.re = x}, DifferentiableAt ℂ (modelDisp a h) u := by
    intro u hu
    have hx : (x : ℂ) = (u.re : ℂ) := by rw [hu]
    have hu' : (x : ℂ) + u.im * I = u := by rw [hx, Complex.re_add_im]
    rw [← hu']
    exact hdiff u.im
  have hbmem : ∀ u ∈ {u : ℂ | u.re = x}, ‖deriv (modelDisp a h) u‖ ≤ δ := by
    intro u hu
    have hx : (x : ℂ) = (u.re : ℂ) := by rw [hu]
    have hu' : (x : ℂ) + u.im * I = u := by rw [hx, Complex.re_add_im]
    rw [← hu']
    exact hderiv u.im
  -- Mean value inequality for `Φ` along the line.
  have hlip : ∀ y₁ y₂ : ℝ,
      ‖modelDisp a h (x + y₂ * I) - modelDisp a h (x + y₁ * I)‖ ≤ δ * |y₂ - y₁| := by
    intro y₁ y₂
    have hmvt := hconv.norm_image_sub_le_of_norm_deriv_le hdmem hbmem
      (show x + y₁ * I ∈ {u : ℂ | u.re = x} by simp)
      (show x + y₂ * I ∈ {u : ℂ | u.re = x} by simp)
    rwa [show x + y₂ * I - (x + y₁ * I) = ((y₂ - y₁ : ℝ) : ℂ) * I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hmvt
  -- Growth of the level map.
  have hgrowth : ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ →
      (1 - δ) * (y₂ - y₁) ≤ (transitMap a h (x + y₂ * I)).im
        - (transitMap a h (x + y₁ * I)).im := by
    intro y₁ y₂ hy
    have hk := hlip y₁ y₂
    rw [abs_of_nonneg (sub_nonneg.mpr hy)] at hk
    have him : -(‖modelDisp a h (x + y₂ * I) - modelDisp a h (x + y₁ * I)‖)
        ≤ (modelDisp a h (x + y₂ * I)).im - (modelDisp a h (x + y₁ * I)).im := by
      have h := Complex.im_le_norm
        (-(modelDisp a h (x + y₂ * I) - modelDisp a h (x + y₁ * I)))
      simp only [Complex.neg_im, norm_neg, Complex.sub_im] at h
      linarith
    rw [hfun y₂, hfun y₁]
    linarith
  -- Strict monotonicity.
  have hstrict : StrictMono (fun y : ℝ => (transitMap a h (x + y * I)).im) := by
    intro y₁ y₂ hy
    have h := hgrowth y₁ y₂ (le_of_lt hy)
    have hp : 0 < (1 - δ) * (y₂ - y₁) := mul_pos (by linarith) (by linarith)
    linarith
  -- Continuity of the level map.
  have hcont : Continuous (fun y : ℝ => (transitMap a h (x + y * I)).im) := by
    rw [continuous_iff_continuousAt]
    intro y₀
    have hline : ContinuousAt (fun y : ℝ => (x : ℂ) + y * I) y₀ :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    have hproj : ContinuousAt (fun u : ℂ => (transitMap a h u).im) ((x : ℂ) + y₀ * I) := by
      have hd' : ContinuousAt (transitMap a h) ((x : ℂ) + y₀ * I) := by
        change ContinuousAt (fun u : ℂ => u + modelDisp a h u) ((x : ℂ) + y₀ * I)
        exact continuousAt_id.add (hdiff y₀).continuousAt
      exact Complex.continuous_im.continuousAt.comp hd'
    simpa [Function.comp_def] using
      hproj.comp (f := fun y : ℝ => (x : ℂ) + y * I) hline
  refine ⟨hstrict, ?_⟩
  -- Surjectivity: the level map is unbounded above and below.
  intro b _
  set F : ℝ → ℝ := fun y => (transitMap a h (x + y * I)).im with hFs
  have keyF : ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ → (1 - δ) * (y₂ - y₁) ≤ F y₂ - F y₁ := by
    intro y₁ y₂ hy
    rw [hFs]
    exact hgrowth y₁ y₂ hy
  have hcontF : Continuous F := by
    rw [hFs]
    exact hcont
  have hcd : 0 < 1 - δ := by linarith
  set d : ℝ := (b - F 0) / (1 - δ) with hd
  have hdc : (1 - δ) * d = b - F 0 := by
    rw [hd]
    exact mul_div_cancel₀ _ (ne_of_gt hcd)
  have hUp : b < F (|d| + 1) := by
    have h := keyF 0 (|d| + 1) (by positivity)
    simp only [sub_zero] at h
    have h1 : (1 - δ) * (d + 1) ≤ (1 - δ) * (|d| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self d]) hcd.le
    have h2 : (1 - δ) * (d + 1) = b - F 0 + (1 - δ) := by rw [mul_add, mul_one, hdc]
    linarith
  have hDn : F (-(|d| + 1)) < b := by
    have h := keyF (-(|d| + 1)) 0 (by linarith [abs_nonneg d])
    have h0 : (0 : ℝ) - (-(|d| + 1)) = |d| + 1 := by ring
    rw [h0] at h
    have h1 : (1 - δ) * (-(|d| + 1)) ≤ (1 - δ) * (d - 1) :=
      mul_le_mul_of_nonneg_left (by linarith [neg_abs_le d]) hcd.le
    have h2 : (1 - δ) * (d - 1) = b - F 0 - (1 - δ) := by rw [mul_sub, mul_one, hdc]
    have h3 : (1 - δ) * (-(|d| + 1)) = -((1 - δ) * (|d| + 1)) := mul_neg ..
    linarith
  have hy12 : -(|d| + 1) < |d| + 1 := by linarith [abs_nonneg d]
  have hmem : b ∈ Set.Icc (F (-(|d| + 1))) (F (|d| + 1)) := ⟨le_of_lt hDn, le_of_lt hUp⟩
  obtain ⟨y, -, hyeq⟩ := intermediate_value_Icc (le_of_lt hy12) hcontF.continuousOn hmem
  exact ⟨y, trivial, hyeq⟩

end Work.Implosion.Chord
