/-
Copyright: work module for the Elgindi finite-time singularity project.

# Smoothness and endpoint vanishing of the iterated angular derivatives `D_θ^i u`

For a slice `u` that is `C^∞` on the open neighbourhood `U = (-1, π/2 + 1)` of the closed
angular interval `[0, π/2]` (this is exactly `Work.Elliptic.SmoothSlice u`), this module proves

* every iterate `D_θ^i u` of `D_θ = sin(2θ) ∂_θ` (`i ∈ ℕ`) is again `C^∞` on `U`;
* for `i ≥ 1` there is `K ≥ 0` with `|D_θ^i u θ| ≤ K sin(2θ)` for `θ ∈ (0, π/2)`.

The second statement needs no product-rule induction: by definition

  `D_θ^i u = sin(2θ) · ∂_θ (D_θ^{i-1} u)`   (`θ` arbitrary, `i ≥ 1`),

and the first statement applied to `i - 1` says that `w := ∂_θ (D_θ^{i-1} u)` is `C^∞` on the
open set `U`; being continuous on the compact `[0, π/2] ⊆ U` it is bounded there, say by `C`,
and then `|D_θ^i u θ| ≤ C sin(2θ)` because `sin(2θ) > 0` on `(0, π/2)`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

local notation "U" => Set.Ioo (-1) (Real.pi / 2 + 1)

/-- `D_θ = sin(2θ) ∂_θ` preserves `C^∞` on an open set (the derivative of a smooth function is
smooth on an open set, and `θ ↦ sin(2θ)` is smooth). -/
private lemma contDiffOn_Dth1 {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ f s) : ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1 f) s :=
  ((show ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) s by fun_prop)).mul
    (hf.deriv_of_isOpen hs le_top)

/-- Iterates of `D_θ` preserve `C^∞` on an open set. -/
private lemma contDiffOn_Dth1Iter {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ f s) : ∀ m : ℕ, ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1Iter m f) s
  | 0 => by simpa using hf
  | (m + 1) => by
      have h : ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1Iter m f) s := contDiffOn_Dth1Iter hs hf m
      simpa only [Work.Elliptic.Dth1Iter_succ] using contDiffOn_Dth1 hs h

/-- **Smoothness and `O(sin 2θ)` vanishing of the angular iterates.**  For `u` smooth on a
neighbourhood `(-1, π/2+1)` of `[0, π/2]`: every `D_θ^i u` is `C^∞` there, and for `i ≥ 1` the
iterate vanishes at both endpoints at least as fast as `sin(2θ)`. -/
theorem dth1Iter_smooth_bound (u : ℝ → ℝ) (hu : Work.Elliptic.SmoothSlice u) :
    (∀ i : ℕ, ContDiffOn ℝ ⊤ (Work.Elliptic.Dth1Iter i u) (Set.Ioo (-1) (Real.pi / 2 + 1))) ∧
    (∀ i : ℕ, 1 ≤ i → ∃ K : ℝ, 0 ≤ K ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |Work.Elliptic.Dth1Iter i u θ| ≤ K * Real.sin (2 * θ)) := by
  refine ⟨fun i => contDiffOn_Dth1Iter isOpen_Ioo hu i, ?_⟩
  intro i hi
  -- write `i = k + 1` so that `Dth1Iter_succ` applies literally: `D_θ^{k+1} u = Dth1 (D_θ^k u)`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, i = k + 1 := ⟨i - 1, (Nat.sub_add_cancel hi).symm⟩
  rw [hk]
  clear hk
  -- The witness of the factorisation: `w = ∂_θ (D_θ^k u)`, smooth on `U`.
  have hw : ContDiffOn ℝ ⊤ (deriv (Work.Elliptic.Dth1Iter k u)) U :=
    (contDiffOn_Dth1Iter isOpen_Ioo hu k).deriv_of_isOpen isOpen_Ioo le_top
  -- `D_θ^{k+1} u = sin(2θ) · w` holds *everywhere* (no restriction to `(0, π/2)`).
  have hid : ∀ θ : ℝ, Work.Elliptic.Dth1Iter (k + 1) u θ
      = Real.sin (2 * θ) * deriv (Work.Elliptic.Dth1Iter k u) θ := by
    intro θ
    rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1]
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ U := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hw.continuousOn.mono hsub)
  have hC' : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |deriv (Work.Elliptic.Dth1Iter k u) θ| ≤ C := fun θ hθ => by
    have h := hC θ hθ
    rwa [Real.norm_eq_abs] at h
  have hCnn : 0 ≤ C := by
    have h := hC' 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩
    linarith [abs_nonneg (deriv (Work.Elliptic.Dth1Iter k u) 0)]
  refine ⟨C, hCnn, ?_⟩
  intro θ hθ
  have hsp : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [hid θ, abs_mul, abs_of_pos hsp]
  calc Real.sin (2 * θ) * |deriv (Work.Elliptic.Dth1Iter k u) θ|
      ≤ Real.sin (2 * θ) * C :=
        mul_le_mul_of_nonneg_left (hC' θ ⟨hθ.1.le, hθ.2.le⟩) hsp.le
    _ = C * Real.sin (2 * θ) := by ring

end Work.FTS.EllipticEst.TT
