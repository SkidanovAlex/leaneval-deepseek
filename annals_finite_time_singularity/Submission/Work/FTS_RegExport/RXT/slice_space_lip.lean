import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT.loc_sup4
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.STBounds2
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.slice_space_lip`

**S2 of the RegExport plan**: the space-time Lipschitz bound for the jets of the strong solution.

For a family `g` satisfying `DynOK' (pExp α) C₀ Φs E g` and any box `[a,b] × [c,d]` of the open
quadrant (`0 < a ≤ b`, `0 < c ≤ d < π/2`), every mixed jet
`D_z^j D_θ^i (slice g τ)` of order `j + i ≤ 3` is, uniformly on `[0,T]` and on the box, Lipschitz
in both `z` and `θ` (with a *single* constant).

Route (the same one as `RXT.loc_sup4`): `DynOK'` gives the class-`C` approximants `gn` of the
solution with a uniform `ℋ⁶`-bound `Xn6 α (slice (gn n) τ) ≤ B` and `C⁴`-jet convergence on the
open quadrant, and `DynOK` gives the `C⁴`-regularity of the solution itself.  Each approximant
slice is `SmoothOpen`, hence:

* the derivative of `D_z^jD_θ^i f` in `z` is `D_z^{j+1}D_θ^i f / z` (definitional);
* the derivative in `θ` is `D_z^jD_θ^{i+1} f / sin(2θ)` (`Dth_mixed_eq_C4` of
  `RegExport/C4/Dth_mixed_eq_C4.lean`);
* both are bounded on the box by `classC_mixed_sup_le_four`, giving the mean-value bounds
  `K/a` (in `z`) and `K/σ` (in `θ`), where `K = C₁/√(γ-1)·B` and `σ = (4/π)·min c (π/2-d)`.

Passing to the limit in `n` (the `C⁴`-jet convergence of `LimApprox`) gives the same bounds for
`g` itself.  The single constant is `K/a + K/σ`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

/-! ## Two mean-value/Lipschitz engines -/

/-- If `φ` is differentiable on the closed interval `[lo,hi]` and its derivative is bounded by
`C` there, then `φ` is `C`-Lipschitz on that interval.  (The `ℝ → ℝ` form of
`Convex.norm_image_sub_le_of_norm_deriv_le`.) -/
private lemma abs_sub_le_of_deriv_le {φ : ℝ → ℝ} {C lo hi : ℝ}
    (hdiff : ∀ x ∈ Set.Icc lo hi, DifferentiableAt ℝ φ x)
    (hbd : ∀ x ∈ Set.Icc lo hi, |deriv φ x| ≤ C) :
    ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi, |φ x - φ y| ≤ C * |x - y| := by
  intro x hx y hy
  have h : ‖φ y - φ x‖ ≤ C * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff
      (fun x hx => by rw [Real.norm_eq_abs]; exact hbd x hx) (convex_Icc lo hi) hx hy
  have h2 : |φ x - φ y| = ‖φ y - φ x‖ := by rw [Real.norm_eq_abs, abs_sub_comm]
  have h3 : |x - y| = ‖y - x‖ := by rw [Real.norm_eq_abs, abs_sub_comm]
  rw [h2, h3]
  exact h

/-- **The `z`-Lipschitz bound for the mixed slots.**  If `f` is smooth on the open quadrant and
every mixed slot of order `≤ 4` is bounded by `K` on the box `[a,b] × [c,d]`, then every mixed
slot `D_z^j D_θ^i f` with `j + i ≤ 3` is `K/a`-Lipschitz in `z` on the box. -/
private lemma mixed_lipschitz_z {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    {a b c d K : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2) (hKnn : 0 ≤ K)
    (hK : ∀ p q : ℕ, p + q ≤ 4 → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |Work.Spaces.mixed p q f z θ| ≤ K)
    {j i : ℕ} (hji : j + i ≤ 3) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ z' ∈ Set.Icc a b,
      |Work.Spaces.mixed j i f z θ - Work.Spaces.mixed j i f z' θ| ≤ (K / a) * |z - z'| := by
  intro z hz θ hθ z' hz'
  have hθIoo : θ ∈ Set.Ioo 0 (π / 2) := ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun x : ℝ => Work.Spaces.mixed j i f x θ) (Set.Ioi 0) :=
    (hF.mixed j i).curry_z hθIoo
  have hdiff : ∀ x ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun x : ℝ => Work.Spaces.mixed j i f x θ) x := by
    intro x hx
    exact (hslice.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds (lt_of_lt_of_le ha hx.1))
  have hbd : ∀ x ∈ Set.Icc a b,
      |deriv (fun x : ℝ => Work.Spaces.mixed j i f x θ) x| ≤ K / a := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hkey : x * Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        = Work.Spaces.mixed (j + 1) i f x θ := rfl
    have hdiv : Work.Spaces.pz (Work.Spaces.mixed j i f) x θ
        = Work.Spaces.mixed (j + 1) i f x θ / x := by
      rw [eq_div_iff (ne_of_gt hxpos), mul_comm]
      exact hkey
    have hderiv : deriv (fun x : ℝ => Work.Spaces.mixed j i f x θ) x
        = Work.Spaces.mixed (j + 1) i f x θ / x := by
      rw [show deriv (fun x : ℝ => Work.Spaces.mixed j i f x θ) x
            = Work.Spaces.pz (Work.Spaces.mixed j i f) x θ from rfl, hdiv]
    calc |deriv (fun x : ℝ => Work.Spaces.mixed j i f x θ) x|
        = |Work.Spaces.mixed (j + 1) i f x θ| / x := by
          rw [hderiv, abs_div, abs_of_pos hxpos]
      _ ≤ K / x := div_le_div_of_nonneg_right (hK (j + 1) i (by omega) x hx θ hθ) hxpos.le
      _ ≤ K / a := div_le_div_of_nonneg_left hKnn ha hx.1
  exact abs_sub_le_of_deriv_le hdiff hbd z hz z' hz'

/-- **The `θ`-Lipschitz bound for the mixed slots.**  If `f` is smooth on the open quadrant, every
mixed slot of order `≤ 4` is bounded by `K` on the box, and `σ > 0` bounds `sin(2θ)` from below on
`[c,d]`, then every mixed slot `D_z^j D_θ^i f` with `j + i ≤ 3` is `K/σ`-Lipschitz in `θ` on the
box. -/
private lemma mixed_lipschitz_theta {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    {a b c d K σ : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2) (hKnn : 0 ≤ K)
    (hσpos : 0 < σ) (hσ : ∀ θ ∈ Set.Icc c d, σ ≤ Real.sin (2 * θ))
    (hK : ∀ p q : ℕ, p + q ≤ 4 → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |Work.Spaces.mixed p q f z θ| ≤ K)
    {j i : ℕ} (hji : j + i ≤ 3) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ θ' ∈ Set.Icc c d,
      |Work.Spaces.mixed j i f z θ - Work.Spaces.mixed j i f z θ'| ≤ (K / σ) * |θ - θ'| := by
  intro z hz θ hθ θ' hθ'
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun x : ℝ => Work.Spaces.mixed j i f z x) (Set.Ioo 0 (π / 2)) :=
    (hF.mixed j i).curry_θ hzpos
  have hdiff : ∀ x ∈ Set.Icc c d,
      DifferentiableAt ℝ (fun x : ℝ => Work.Spaces.mixed j i f z x) x := by
    intro x hx
    exact (hslice.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨lt_of_lt_of_le hc hx.1, lt_of_le_of_lt hx.2 hd⟩)
  have hbd : ∀ x ∈ Set.Icc c d,
      |deriv (fun x : ℝ => Work.Spaces.mixed j i f z x) x| ≤ K / σ := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo 0 (π / 2) := ⟨lt_of_lt_of_le hc hx.1, lt_of_le_of_lt hx.2 hd⟩
    have hsin : 0 < Real.sin (2 * x) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hxIoo.1]) (by linarith [hxIoo.2, Real.pi_pos])
    have hDth := Work.FTS_RegExport.C4.Dth_mixed_eq_C4 (hF.forall 4) j i (by omega) hzpos hxIoo
    have hkey : Real.sin (2 * x) * Work.Spaces.pth (Work.Spaces.mixed j i f) z x
        = Work.Spaces.mixed j (i + 1) f z x := by
      simpa only [Work.Spaces.Dth] using hDth
    have hdiv : Work.Spaces.pth (Work.Spaces.mixed j i f) z x
        = Work.Spaces.mixed j (i + 1) f z x / Real.sin (2 * x) := by
      rw [eq_div_iff (ne_of_gt hsin), mul_comm]
      exact hkey
    have hderiv : deriv (fun x : ℝ => Work.Spaces.mixed j i f z x) x
        = Work.Spaces.mixed j (i + 1) f z x / Real.sin (2 * x) := by
      rw [show deriv (fun x : ℝ => Work.Spaces.mixed j i f z x) x
            = Work.Spaces.pth (Work.Spaces.mixed j i f) z x from rfl, hdiv]
    calc |deriv (fun x : ℝ => Work.Spaces.mixed j i f z x) x|
        = |Work.Spaces.mixed j (i + 1) f z x| / Real.sin (2 * x) := by
          rw [hderiv, abs_div, abs_of_pos hsin]
      _ ≤ K / Real.sin (2 * x) :=
          div_le_div_of_nonneg_right (hK j (i + 1) (by omega) z hz x hx) hsin.le
      _ ≤ K / σ := div_le_div_of_nonneg_left hKnn hσpos (hσ x hx)
  exact abs_sub_le_of_deriv_le hdiff hbd θ hθ θ' hθ'

/-! ## The target -/

theorem slice_space_lip {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ j i : ℕ, j + i ≤ 3 →
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ z' ∈ Set.Icc a b,
        |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z' θ| ≤ C * |z - z'|) ∧
      (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, ∀ θ' ∈ Set.Icc c d,
        |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ'| ≤ C * |θ - θ'|) := by
  -- the exponent `β = pExp α = 3α` is a positive exponent `≤ 1`
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the class-`C` interior `L^∞`–`ℋ⁶` trade-off
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  -- the approximating class-C families, the uniform `ℋ⁶`-bound `B`, and the jet convergence
  obtain ⟨gn, B, _L, h1, _h2, h3, _h4⟩ := hOK.2 (T + 1) (by linarith)
  have hBnn : 0 ≤ B := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨le_rfl, by linarith⟩
    have hx : 0 ≤ Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn 0) 0) := Work.Spaces.HkNorm_nonneg _ 6 _
    linarith [(h1 0 0 h0).2.2]
  -- the universal constant of the sup bounds
  set K : ℝ := C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (div_nonneg hC₁pos.le (Real.sqrt_nonneg _)) hBnn
  -- the angular lower bound on `[c,d]`
  set σ : ℝ := (4 / π) * min c (π / 2 - d) with hσdef
  have hσpos : 0 < σ := by
    rw [hσdef]
    have h1' : 0 < min c (π / 2 - d) := lt_min hc (by linarith)
    positivity
  have hσle : ∀ θ ∈ Set.Icc c d, σ ≤ Real.sin (2 * θ) := by
    intro θ hθ
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨by linarith [hθ.1, hc], by linarith [hθ.2, hd]⟩
    have hmin : min c (π / 2 - d) ≤ min θ (π / 2 - θ) :=
      le_min (le_trans (min_le_left _ _) hθ.1) (le_trans (min_le_right _ _) (by linarith [hθ.2]))
    have h4π : (0 : ℝ) ≤ 4 / π := div_nonneg (by norm_num) Real.pi_pos.le
    have h1' : (4 / π) * min θ (π / 2 - θ) ≤ Real.sin (2 * θ) := by
      have hms := mul_le_mul_of_nonneg_left (Work.FTS.H2.min_le_sin θ hθIθ) h4π
      have h4 : (4 / π) * ((π / 4) * Real.sin (2 * θ)) = Real.sin (2 * θ) := by
        rw [← mul_assoc, show (4 : ℝ) / π * (π / 4) = 1 by field_simp, one_mul]
      linarith [hms, h4]
    calc σ = (4 / π) * min c (π / 2 - d) := hσdef
      _ ≤ (4 / π) * min θ (π / 2 - θ) := mul_le_mul_of_nonneg_left hmin h4π
      _ ≤ Real.sin (2 * θ) := h1'
  refine ⟨K / a + K / σ, add_nonneg (div_nonneg hKnn ha.le) (div_nonneg hKnn hσpos.le), ?_⟩
  intro τ hτ j i hji
  have hτT : τ ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨hτ.1, by linarith [hτ.2]⟩
  -- the uniform sup bound on the mixed slots of order `≤ 4`, for every approximant
  have hKn : ∀ n : ℕ, ∀ p q : ℕ, p + q ≤ 4 → ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d,
      |Work.Spaces.mixed p q (Work.FTS.Galerkin.slice (gn n) τ) x y| ≤ K := by
    intro n p q hpq x hx y hy
    have hCn : Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) := (h1 n τ hτT).1
    have hn6 : Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) ≤ B := (h1 n τ hτT).2.2
    have hxy : (x, y) ∈ Work.Construction.Qd :=
      ⟨lt_of_lt_of_le ha hx.1, lt_of_lt_of_le hc hy.1, lt_of_le_of_lt hy.2 hd⟩
    have hb := hC₁ (Work.FTS.Regularity.pExp α) ⟨hβ, hβ1⟩ hCn p q (by omega) hxy
    calc |Work.Spaces.mixed p q (Work.FTS.Galerkin.slice (gn n) τ) x y|
        ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
            * Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ) := hb
      _ ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B :=
          mul_le_mul_of_nonneg_left hn6 (div_nonneg hC₁pos.le (Real.sqrt_nonneg _))
      _ = K := hKdef.symm
  -- the box lies in the open quadrant
  have hbox : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, (x, y) ∈ Work.Construction.Qd :=
    fun x hx y hy => ⟨lt_of_lt_of_le ha hx.1, lt_of_lt_of_le hc hy.1, lt_of_le_of_lt hy.2 hd⟩
  constructor
  · -- Lipschitz in `z`
    intro z hz θ hθ z' hz'
    have hbnd : ∀ n : ℕ,
        |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z' θ| ≤ (K / a) * |z - z'| :=
      fun n => mixed_lipschitz_z ((h1 n τ hτT).1).reg ha hc hd hKnn (hKn n) hji z hz θ hθ z' hz'
    have htend := ((h3 τ hτT j i (by omega) z θ (hbox z hz θ hθ)).sub
      (h3 τ hτT j i (by omega) z' θ (hbox z' hz' θ hθ))).abs
    have hlim := le_of_tendsto htend (Filter.Eventually.of_forall hbnd)
    calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z' θ|
        ≤ (K / a) * |z - z'| := hlim
      _ ≤ (K / a + K / σ) * |z - z'| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact le_add_of_nonneg_right (div_nonneg hKnn hσpos.le)
  · -- Lipschitz in `θ`
    intro z hz θ hθ θ' hθ'
    have hbnd : ∀ n : ℕ,
        |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ'| ≤ (K / σ) * |θ - θ'| :=
      fun n => mixed_lipschitz_theta ((h1 n τ hτT).1).reg ha hc hd hKnn hσpos hσle (hKn n) hji
        z hz θ hθ θ' hθ'
    have htend := ((h3 τ hτT j i (by omega) z θ (hbox z hz θ hθ)).sub
      (h3 τ hτT j i (by omega) z θ' (hbox z hz θ' hθ'))).abs
    have hlim := le_of_tendsto htend (Filter.Eventually.of_forall hbnd)
    calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ
          - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ'|
        ≤ (K / σ) * |θ - θ'| := hlim
      _ ≤ (K / a + K / σ) * |θ - θ'| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact le_add_of_nonneg_left (div_nonneg hKnn ha.le)

end Work.FTS_RegExport.RXT
