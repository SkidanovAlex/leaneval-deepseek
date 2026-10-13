/-
# `Work.FTS.PhiStar.Series.exists_eFam_bounds`

Pointwise bounds for the angular Dirichlet eigenfunctions
`eFam m θ = cos θ · gC (2m+1) (sin θ)` of `Lzero` (`Gegenbauer/Defs.lean`), needed by the
series construction of the self-similar profile.

Since `gC (2m+1)` is an odd *polynomial*, `gC (2m+1)` vanishes at `0` and is Lipschitz on
`[-1,1]`; the statements

* `|eFam m θ| ≤ A cos θ` and `|eFam m θ · cos θ| ≤ A sin θ cos²θ` on `Iθ = [0,π/2]`,

both follow from the mean value bound `|gC (2m+1) (sin θ)| ≤ D · sin θ` with `D` a bound for
`|deriv (gC (2m+1))|` on `[-1,1]` (and `gC (2m+1) 0 = 0`).  The third statement,

* `|deriv (fun t => eFam m t · cos t) θ| ≤ B` for all real `θ`,

uses in addition that `t ↦ eFam m t · cos t = (1 - sin²t) · gC (2m+1) (sin t)` is the
composition of a polynomial with `sin`, so that its derivative at `θ` is
`(0 - 2 sin θ cos θ) · gC (2m+1)(sin θ) + cos²θ · deriv (gC (2m+1))(sin θ)`, a combination of
values on `[-1,1]` of `gC (2m+1)` and of `deriv (gC (2m+1))`, both bounded there.

The two uniform bounds `M`, `D` on `[-1,1]` come from compactness of `[-1,1]` and continuity
of `gC (2m+1)` (a `C³` function, `Gegenbauer.gC_ode.contDiff_gC`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-! ## Auxiliary bounds on the compact interval `[-1,1]` -/

/-- A continuous real function on `[-1,1]` is bounded there in absolute value. -/
lemma exists_abs_le_on_Icc {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1) 1)) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := f) hf
  exact ⟨C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩

/-- The value and the derivative of the Gegenbauer polynomial `gC (2m+1)` are both bounded on
the interval `[-1,1]` (the two constants `M`, `D` are nonnegative). -/
lemma exists_gC_bound_and_deriv_bound (m : ℕ) : ∃ M D : ℝ, 0 ≤ M ∧ 0 ≤ D ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) x| ≤ M) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) x| ≤ D) := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1))).continuous).continuousOn
  obtain ⟨D, hD⟩ := exists_abs_le_on_Icc
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1))).continuous_deriv
      (by norm_num)).continuousOn
  exact ⟨M, D, le_trans (abs_nonneg _) (hM 0 (by norm_num)),
    le_trans (abs_nonneg _) (hD 0 (by norm_num)), hM, hD⟩

/-- Mean value bound for the odd Gegenbauer polynomial: for `θ ∈ Iθ`,
`|gC (2m+1) (sin θ)| ≤ D · sin θ`, where `D` bounds `|deriv (gC (2m+1))|` on `[-1,1]`. -/
lemma abs_gC_sin_le (m : ℕ) {D : ℝ}
    (hD : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) x| ≤ D) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| ≤ D * Real.sin θ := by
  intro θ hθ
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (s := Set.Icc (0 : ℝ) 1) (C := D)
    (x := (0 : ℝ)) (y := Real.sin θ)
    (fun x _ => ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).differentiable
      (by norm_num)).differentiableAt)
    (fun x hx => hD x ⟨by linarith [hx.1], hx.2⟩)
    (convex_Icc (0 : ℝ) 1) ⟨le_rfl, zero_le_one⟩ ⟨hsin0, hsin1⟩
  rw [gC_odd_zero m] at h
  simpa [Real.norm_eq_abs, abs_of_nonneg hsin0] using h

/-! ## The derivative of `eFam m · cos` -/

/-- Explicit form of the derivative of `θ ↦ eFam m θ · cos θ`: since
`eFam m t · cos t = (1 - sin²t) · gC (2m+1) (sin t)` (as `cos² = 1 - sin²`), the product and
chain rules give the displayed combination of `gC (2m+1)` and its derivative at `sin θ`. -/
lemma deriv_eFam_mul_cos (m : ℕ) (θ : ℝ) :
    deriv (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t * Real.cos t) θ
      = (0 - 2 * Real.sin θ * Real.cos θ)
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
        + (1 - Real.sin θ ^ 2)
          * (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ) * Real.cos θ) := by
  have hgc : HasDerivAt (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1))
      (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ)) (Real.sin θ) :=
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).differentiable
      (by norm_num)).differentiableAt).hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t))
      (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ) * Real.cos θ) θ :=
    hgc.comp θ (Real.hasDerivAt_sin θ)
  have h1 : HasDerivAt (fun t : ℝ => 1 - Real.sin t ^ 2)
      (0 - 2 * Real.sin θ * Real.cos θ) θ := by
    have hs : HasDerivAt (fun t : ℝ => Real.sin t ^ 2)
        (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) θ := (Real.hasDerivAt_sin θ).pow 2
    have h := (hasDerivAt_const (x := θ) (c := (1 : ℝ))).sub hs
    convert h using 1
    ring
  have hprod := h1.mul h2
  rw [show (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t * Real.cos t)
      = fun t : ℝ => (1 - Real.sin t ^ 2)
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t) from ?_]
  · exact hprod.deriv
  · funext t
    rw [Work.FTS.PhiStar.Gegenbauer.eFam]
    rw [show Real.cos t * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t) * Real.cos t
        = Real.cos t ^ 2 * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t) from by ring]
    rw [Real.cos_sq']

/-! ## The main bounds -/

theorem exists_eFam_bounds (m : ℕ) : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
    (∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ A * Real.cos θ) ∧
    (∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤ A * Real.sin θ * Real.cos θ ^ 2) ∧
    (∀ θ : ℝ,
      |deriv (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t * Real.cos t) θ| ≤ B) := by
  obtain ⟨M, D, hMnn, hDnn, hM, hD⟩ := exists_gC_bound_and_deriv_bound m
  have hmvt := abs_gC_sin_le m hD
  refine ⟨D + 1, 2 * M + D + 1, by linarith, by linarith, ?_, ?_, ?_⟩
  · intro θ hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hsin0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        = Real.cos θ * |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| := by
          rw [Work.FTS.PhiStar.Gegenbauer.eFam, abs_mul, abs_of_nonneg hcos]
      _ ≤ Real.cos θ * (D * Real.sin θ) := mul_le_mul_of_nonneg_left (hmvt θ hθ) hcos
      _ = D * Real.cos θ * Real.sin θ := by ring
      _ ≤ D * Real.cos θ * 1 := mul_le_mul_of_nonneg_left hsin1 (mul_nonneg hDnn hcos)
      _ = D * Real.cos θ := by ring
      _ ≤ (D + 1) * Real.cos θ := mul_le_mul_of_nonneg_right (by linarith) hcos
  · intro θ hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hsin0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
        = Real.cos θ ^ 2 * |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| := by
          rw [Work.FTS.PhiStar.Gegenbauer.eFam, abs_mul, abs_mul, abs_of_nonneg hcos]
          ring
      _ ≤ Real.cos θ ^ 2 * (D * Real.sin θ) :=
          mul_le_mul_of_nonneg_left (hmvt θ hθ) (by positivity)
      _ = (D * Real.sin θ) * Real.cos θ ^ 2 := by ring
      _ ≤ ((D + 1) * Real.sin θ) * Real.cos θ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hsin0)
            (by positivity)
      _ = (D + 1) * Real.sin θ * Real.cos θ ^ 2 := by ring
  · intro θ
    have hsin_abs : |Real.sin θ| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    have hcos_abs : |Real.cos θ| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have hsin_mem : Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    have hP : |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| ≤ M := hM _ hsin_mem
    have hP' : |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ)| ≤ D :=
      hD _ hsin_mem
    have hsq_abs : |1 - Real.sin θ ^ 2| ≤ 1 := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · nlinarith [sq_nonneg (Real.sin θ), Real.sin_le_one θ, Real.neg_one_le_sin θ]
      · nlinarith [sq_nonneg (Real.sin θ)]
    have hfirst : |0 - 2 * Real.sin θ * Real.cos θ| ≤ 2 := by
      have hprod : |Real.sin θ| * |Real.cos θ| ≤ 1 := by
        have h := mul_le_mul hsin_abs hcos_abs (abs_nonneg (Real.cos θ))
          (by norm_num : (0 : ℝ) ≤ 1)
        simpa using h
      have h1 : |0 - 2 * Real.sin θ * Real.cos θ| = 2 * (|Real.sin θ| * |Real.cos θ|) := by
        rw [show (0 : ℝ) - 2 * Real.sin θ * Real.cos θ = -(2 * Real.sin θ * Real.cos θ) from
            by ring,
          abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      rw [h1]
      linarith
    rw [deriv_eFam_mul_cos m θ]
    calc |(0 - 2 * Real.sin θ * Real.cos θ)
            * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
          + (1 - Real.sin θ ^ 2)
            * (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ) * Real.cos θ)|
        ≤ |(0 - 2 * Real.sin θ * Real.cos θ)
            * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)|
          + |(1 - Real.sin θ ^ 2)
            * (deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ) * Real.cos θ)| :=
          abs_add_le _ _
      _ ≤ 2 * M + 1 * (D * 1) := by
          rw [abs_mul, abs_mul, abs_mul]
          have hA : |0 - 2 * Real.sin θ * Real.cos θ|
              * |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| ≤ 2 * M :=
            mul_le_mul hfirst hP (abs_nonneg _) (by norm_num)
          have hB : |1 - Real.sin θ ^ 2|
              * (|deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ)|
                * |Real.cos θ|) ≤ 1 * (D * 1) := by
            have hbd : |deriv (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) (Real.sin θ)|
                * |Real.cos θ| ≤ D * 1 :=
              mul_le_mul hP' hcos_abs (abs_nonneg _) hDnn
            exact mul_le_mul hsq_abs hbd (by positivity) (by norm_num)
          linarith
      _ = 2 * M + D := by ring
      _ ≤ 2 * M + D + 1 := by linarith

end Work.FTS.PhiStar.Series
