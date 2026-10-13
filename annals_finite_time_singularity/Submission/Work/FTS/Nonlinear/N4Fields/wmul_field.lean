/-
# The `𝒲^{4,∞}`-product rule of the N4 interface

This file proves the field `Work.FTS.Nonlin.N4Norm.wmul` of
`Submission/Work/FTS/Nonlinear/Interface.lean` (design §3.3):

for `0 < α ≤ α₂ ≤ 1` and `f, g : Fn` smooth on the open quadrant, in `𝒲^{4,∞}`, with
*flat vanishing of all `z`-derivatives up to order `4` of the `θ = 0` and `θ = π/2`
slices of `g`*, the product `f·g` is again in `𝒲^{4,∞}` and
`|f g|_{𝒲^{4,∞}} ≤ C |f|_{𝒲^{4,∞}} |g|_{𝒲^{4,∞}}` with `C` universal.

The estimate splits in two.

* **Interior** (`Work.FTS.H2.prodW_interior_bound`, already in the tree): on the *open*
  quadrant the `z`- and `θ`-Leibniz expansions are available (`Work.FTS.H2.Q.pzIter_mul_local_sm`,
  `Work.FTS.LocData.DthIter_mul_smoothQuad`), the pointwise factor bounds are
  `Work.Spaces.factor_bound` and `Work.Spaces.psi_mw_le`, and the angular weight is shared
  between the two factors; this gives the pointwise bound with constant `C₀` (universal) for
  every weighted derivative of the product.

* **From the open quadrant to the closed domain** (the content of this file).  `supAbs`
  takes its supremum over `z ∈ [0,∞)`, `θ ∈ [0,π/2]`, so the two boundary lines need care:
  * the radial terms `(z+1)^k ∂_z^k (f g)` at `θ = 0, π/2` vanish identically, because the
    corresponding slice of `g` is the zero function (this is the hypothesis, used at `k = 0`)
    and hence so is the slice of the product;
  * the mixed terms carry the factor `sin(2θ)^{-α/5}/(α + sin 2θ)`, which vanishes at
    `θ = 0, π/2` for `α > 0`, so no boundary information about `f g` is needed there.

  The pointwise bounds on the *closed* domain then give `WlInfMem α 4 (f g)` and
  `WlInf α 4 (f g) ≤ 30 (C₀ |f| |g|)` through the counting lemma
  `Work.FTS.Nonlinear.N4Fields.wlInf_of_pointwise_bounds` (`5` radial summands and `10`
  mixed ones); the universal constant is `50 C₀`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.H2.prodW_interior_bound
import Submission.Work.FTS.Nonlinear.N4Fields.wlInf_of_pointwise_bounds
import Submission.Work.Spaces.ProductRuleInW

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.Nonlinear.N4Fields

theorem wmul_field {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.LocData.SmoothQuad f → Work.FTS.LocData.SmoothQuad g → Work.Spaces.WlInfMem α 4 f → Work.Spaces.WlInfMem α 4 g → (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) → Work.Spaces.WlInfMem α 4 (fun z θ => f z θ * g z θ) ∧ Work.Spaces.WlInf α 4 (fun z θ => f z θ * g z θ) ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g := by
  obtain ⟨C₀, hC₀pos, hC₀b⟩ := Work.FTS.H2.prodW_interior_bound
  refine ⟨50 * C₀, by positivity, ?_⟩
  intro α hα f g hfS hgS hfm hgm hbdy
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂1
  -- the pointwise estimate on the open quadrant
  obtain ⟨hrad, hang⟩ := hC₀b α f g hα.1 hα1 hfS hgS hfm hgm
  set Wf := Work.Spaces.WlInf α 4 f with hWf
  set Wg := Work.Spaces.WlInf α 4 g with hWg
  have hWfnn : 0 ≤ Wf := by rw [hWf]; exact Work.Spaces.WlInf_nonneg α 4 f hfm
  have hWgnn : 0 ≤ Wg := by rw [hWg]; exact Work.Spaces.WlInf_nonneg α 4 g hgm
  have hB : 0 ≤ C₀ * Wf * Wg := mul_nonneg (mul_nonneg hC₀pos.le hWfnn) hWgnn
  -- the slice of `g` at `θ = 0` (resp. `π/2`) is the zero function, hence so is the slice of `f g`
  have hslice : ∀ (θ₀ : ℝ), (∀ z : ℝ, g z θ₀ = 0) → ∀ k : ℕ, ∀ z : ℝ,
      Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ₀ = 0 := by
    intro θ₀ hg k z
    rw [Work.Spaces.pzIter_eq_iteratedDeriv]
    have hs : (fun z' => (fun z θ => f z θ * g z θ) z' θ₀) = fun _ => (0 : ℝ) := by
      funext z'; simp [hg z']
    rw [hs, iteratedDeriv_const]
    simp
  have hg0 : ∀ z : ℝ, g z 0 = 0 := fun z => (hbdy 0 (by norm_num) z).1
  have hgpi : ∀ z : ℝ, g z (π / 2) = 0 := fun z => (hbdy 0 (by norm_num) z).2
  -- the pointwise bound for the radial terms of the product, on the *closed* domain
  have hPZ : ∀ k : ℕ, k ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => f z θ * g z θ) z θ| ≤ C₀ * Wf * Wg := by
    intro k hk z hz θ hθ
    rcases eq_or_ne θ 0 with h0 | h0
    · subst h0
      rw [hslice 0 hg0 k z, mul_zero, abs_zero]
      exact hB
    · rcases eq_or_ne θ (π / 2) with hpi | hpi
      · subst hpi
        rw [hslice (π / 2) hgpi k z, mul_zero, abs_zero]
        exact hB
      · exact hrad k hk z hz θ ⟨lt_of_le_of_ne hθ.1 (Ne.symm h0),
          lt_of_le_of_ne hθ.2 hpi⟩
  -- the pointwise bound for the mixed terms; the angular weight is zero at the boundary
  have hPT : ∀ j k : ℕ, 1 ≤ j → k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k
            (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C₀ * Wf * Wg := by
    intro j k hj hkj z hz θ hθ
    have hα5 : α / 5 ≠ 0 := ne_of_gt (by linarith [hα.1] : (0 : ℝ) < α / 5)
    rcases eq_or_ne θ 0 with h0 | h0
    · subst h0
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by rw [show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero],
        Real.zero_rpow (neg_ne_zero.mpr hα5), mul_div_assoc]
      simp
      exact hB
    · rcases eq_or_ne θ (π / 2) with hpi | hpi
      · subst hpi
        rw [show Real.sin (2 * (π / 2)) = 0 by
            rw [show 2 * (π / 2) = π by ring, Real.sin_pi],
          Real.zero_rpow (neg_ne_zero.mpr hα5), mul_div_assoc]
        simp
        exact hB
      · exact hang j k hj hkj z hz θ ⟨lt_of_le_of_ne hθ.1 (Ne.symm h0),
          lt_of_le_of_ne hθ.2 hpi⟩
  -- the supremum and the counting of the `15` summands of the norm
  have hcount := wlInf_of_pointwise_bounds (α := α) (B := C₀ * Wf * Wg) hB hPZ hPT
  refine ⟨hcount.1, ?_⟩
  calc Work.Spaces.WlInf α 4 (fun z θ => f z θ * g z θ)
      ≤ 30 * (C₀ * Wf * Wg) := hcount.2
    _ ≤ 50 * C₀ * Wf * Wg := by nlinarith [hB]

end Work.FTS.Nonlinear.N4Fields
