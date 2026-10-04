import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The slice-jet estimate, proved from scratch

Let `u : ℝ × E → Z` and let `Φ_k u` be the `k`-th time derivative of `u`, i.e. the function
`q ↦ (D^k u q) ((1,0), …, (1,0))`.  This file proves

`‖D^m (Φ_k u) p‖ ≤ C ‖D^{k+m} u p‖`

with the explicit constant `C = 1`.

The proof avoids the (universe-sensitive) induction on `k` by using the *unconditional* identity

`‖D^m (fun q => D^k u q) p‖ = ‖D^{k+m} u p‖`

which is proved by induction on `m` (`norm_iteratedFDeriv_jet`): the step rewrites the
`(k+1)`-st derivative as the derivative of the `k`-th one (`filp`), uses that postcomposition
with a linear isometry equivalence does not change the norm of an iterated derivative, and applies
the induction hypothesis at `k+1`.

The estimate for `Φ_k u` then follows by composing on the left with the evaluation functional
`T ↦ T ((1,0), …, (1,0))`, whose operator norm is at most `1`.
-/

namespace Work.Diff.EXT.Phi

open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **The norm of the jets of the `k`-th iterated derivative.**  For a function `u : ℝ × E → Z`
and every `m`, the norm of the `m`-th jet of `q ↦ D^k u q` equals the norm of the `(k+m)`-th jet
of `u`.  No smoothness is needed. -/
theorem norm_iteratedFDeriv_jet (u : ℝ × E → Z) (p : ℝ × E) :
    ∀ (m k : ℕ), ‖iteratedFDeriv ℝ m (fun q : ℝ × E => iteratedFDeriv ℝ k u q) p‖
      = ‖iteratedFDeriv ℝ (k + m) u p‖ := by
  intro m
  induction m with
  | zero =>
    intro k
    rw [norm_iteratedFDeriv_zero, Nat.add_zero]
  | succ m ih =>
    intro k
    have h1 : ‖iteratedFDeriv ℝ (m + 1) (fun q : ℝ × E => iteratedFDeriv ℝ k u q) p‖
        = ‖iteratedFDeriv ℝ m (fderiv ℝ (fun q : ℝ × E => iteratedFDeriv ℝ k u q)) p‖ := by
      rw [iteratedFDeriv_succ_eq_comp_right]
      exact LinearIsometryEquiv.norm_map _ _
    have h2 : ‖iteratedFDeriv ℝ m (fderiv ℝ (fun q : ℝ × E => iteratedFDeriv ℝ k u q)) p‖
        = ‖iteratedFDeriv ℝ m (fun q : ℝ × E => iteratedFDeriv ℝ (k + 1) u q) p‖ := by
      have hfd : fderiv ℝ (fun q : ℝ × E => iteratedFDeriv ℝ k u q)
          = ⇑(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => ℝ × E) Z)
              ∘ (fun q : ℝ × E => iteratedFDeriv ℝ (k + 1) u q) :=
        fderiv_iteratedFDeriv
      rw [hfd, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    have h3 : ‖iteratedFDeriv ℝ m (fun q : ℝ × E => iteratedFDeriv ℝ (k + 1) u q) p‖
        = ‖iteratedFDeriv ℝ ((k + 1) + m) u p‖ := ih (k + 1)
    have h4 : ‖iteratedFDeriv ℝ ((k + 1) + m) u p‖
        = ‖iteratedFDeriv ℝ (k + (m + 1)) u p‖ := by
      rw [show (k + 1) + m = k + (m + 1) from by omega]
    exact h1.trans (h2.trans (h3.trans h4))

/-- **The slice-jet estimate.**  With the constant `C = 1`: for every `C^∞` function
`u : ℝ × E → Z` at `p` and all `k, m`, the norm of the `m`-th jet at `p` of the `k`-th time
derivative `q ↦ (D^k u q) ((1,0),…,(1,0))` is at most the norm of the `(k+m)`-th jet of `u` at
`p`. -/
theorem norm_iteratedFDeriv_Phi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (u : ℝ × E → Z) (p : ℝ × E), ContDiffAt ℝ (⊤ : ℕ∞) u p →
      ‖iteratedFDeriv ℝ m
        (fun q : ℝ × E => (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0))) p‖
        ≤ C * ‖iteratedFDeriv ℝ (k + m) u p‖ := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Z _ _ u p hu
  set L : (ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × E) Z) →L[ℝ] Z :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × E) Z
      (fun _ : Fin k => ((1 : ℝ), 0)) with hL
  have hfun : (fun q : ℝ × E => (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0)))
      = ⇑L ∘ (fun q : ℝ × E => iteratedFDeriv ℝ k u q) := by
    funext q
    simp only [Function.comp_apply, hL]
    rfl
  have hnormL : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun T => ?_)
    rw [hL]
    calc ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × E) Z
            (fun _ : Fin k => ((1 : ℝ), 0)) T‖
        = ‖T (fun _ : Fin k => ((1 : ℝ), 0))‖ := rfl
      _ ≤ ‖T‖ * ∏ i : Fin k, ‖(fun _ : Fin k => ((1 : ℝ), 0)) i‖ :=
          ContinuousMultilinearMap.le_opNorm T _
      _ = ‖T‖ * 1 := by simp
      _ = 1 * ‖T‖ := by ring
  have hJ : ContDiffAt ℝ (((m : ℕ)) : ℕ∞ω)
      (fun q : ℝ × E => iteratedFDeriv ℝ k u q) p := by
    have h1 : ContDiffAt ℝ (((m + k : ℕ)) : ℕ∞ω) u p :=
      (contDiffAt_infty.mp hu) (m + k)
    refine h1.iteratedFDeriv_right (i := k) (m := ((m : ℕ) : ℕ∞ω)) ?_
    push_cast
    exact le_rfl
  have hcomp := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) L hJ
    (show ((m : ℕ) : ℕ∞ω) ≤ ((m : ℕ) : ℕ∞ω) from le_rfl)
  have hjet := norm_iteratedFDeriv_jet (Z := Z) u p m k
  calc ‖iteratedFDeriv ℝ m
        (fun q : ℝ × E => (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0))) p‖
      = ‖iteratedFDeriv ℝ m (⇑L ∘ (fun q : ℝ × E => iteratedFDeriv ℝ k u q)) p‖ := by
        rw [hfun]
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m (fun q : ℝ × E => iteratedFDeriv ℝ k u q) p‖ := hcomp
    _ ≤ 1 * ‖iteratedFDeriv ℝ m (fun q : ℝ × E => iteratedFDeriv ℝ k u q) p‖ :=
        mul_le_mul_of_nonneg_right hnormL (norm_nonneg _)
    _ = 1 * ‖iteratedFDeriv ℝ (k + m) u p‖ := by rw [hjet]

end Work.Diff.EXT.Phi
