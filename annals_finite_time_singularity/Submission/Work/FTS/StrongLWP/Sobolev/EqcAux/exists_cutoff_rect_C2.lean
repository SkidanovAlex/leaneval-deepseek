/-
Copyright: work module for the Elgindi finite-time singularity project.

# A smooth rectangular cut-off with bounded first and second derivatives

`Work.FTS.StrongLWP.Sobolev.EqcAux.exists_cutoff_rect_C2`: for rectangles
`[a,b] × [c,d] ⊆ [a',b'] × [c',d'] ⊆ ℝ × ℝ` there is a `C^∞` function `χ : ℝ × ℝ → ℝ` with

* `0 ≤ χ ≤ 1`, `χ = 1` on `[a,b] × [c,d]` and `χ = 0` outside `[a',b'] × [c',d']`,
* compact support (indeed `tsupport χ ⊆ [a',b'] × [c',d']`),
* and one constant `M > 0` bounding both `‖fderiv χ‖` and `‖fderiv (fderiv χ)‖`
  everywhere.

## How it is built

The one-dimensional input is the separate (independently proved) asset
`Work.FTS.StrongLWP.Sobolev.EqcAux.smoothIntervalCutoff`
(`Submission/Work/FTS/StrongLWP/Sobolev/EqcAux/smoothIntervalCutoff.lean`): for nested
intervals `[q,r] ⊆ [p,s]` there is a `C^∞` function `g : ℝ → ℝ` with `0 ≤ g ≤ 1`, `g = 1`
on `[q,r]` and `g = 0` outside `[p,s]`.  Instantiating it for the two coordinates and
forming the product

`χ (z,θ) = g z · v θ`

gives the two-dimensional cut-off.  The remaining work here is the assembly:

* smoothness is `ContDiff.mul` of the two compositions with the projections;
* `0 ≤ χ ≤ 1` and `χ = 1` on the inner rectangle are pointwise (the target rectangle is a
  product, so each of `z`, `θ` is in the corresponding inner interval);
* `χ = 0` off the outer rectangle: a point outside a product of intervals has a coordinate
  outside the corresponding interval, and the corresponding factor vanishes;
* compact support reduces to the general fact (`hasCompactSupport_prodMul`) that a product
  `(z,θ) ↦ f z * g θ` of two one-variable functions has compact support, and the topological
  support of such a product is contained in `tsupport f ×ˢ tsupport g` — the support of the
  product is contained in the product of the supports and the closure of a product of sets is
  the product of the closures;
* the two derivative bounds come from `exists_bound_fderiv_fderiv`: a `C²` function with
  compact support has both `fderiv` and `fderiv ∘ fderiv` bounded in norm (each is continuous
  by the `C²` hypothesis and compactly supported, since `tsupport (fderiv f) ⊆ tsupport f`).

Everything rests on Mathlib plus the one-dimensional cut-off module.  The hypotheses
`0 < a'`, `0 < c'` and `d' < π / 2` of the request are inherited from the geometric setting
(`(0,∞) × (0,π/2)`) and are not used by the construction.  (`open scoped Real` is needed so
that the `π` of the statement means `Real.pi`: the workspace is compiled with
`autoImplicit = false`, under which a bare `π` is not an identifier.)
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongLWP.Sobolev.EqcAux.smoothIntervalCutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongLWP.Sobolev.EqcAux

set_option autoImplicit false

/-! ## Two general tools for compact support -/

/-- The support of a product `(z,θ) ↦ f z * g θ` of two one-variable functions is contained
in `support f ×ˢ support g`; taking closures gives
`tsupport (·) ⊆ tsupport f ×ˢ tsupport g`. -/
lemma tsupport_prodMul_subset {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → ℝ} {g : β → ℝ} :
    tsupport (fun p : α × β => f p.1 * g p.2) ⊆ tsupport f ×ˢ tsupport g := by
  show closure (Function.support (fun p : α × β => f p.1 * g p.2)) ⊆
    closure (Function.support f) ×ˢ closure (Function.support g)
  rw [← closure_prod_eq]
  apply closure_mono
  intro p hp
  rw [Set.mem_prod]
  exact mul_ne_zero_iff.mp hp

/-- **Compact support is preserved by forming the product of two one-variable functions.** -/
lemma hasCompactSupport_prodMul {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → ℝ} {g : β → ℝ} (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (fun p : α × β => f p.1 * g p.2) :=
  IsCompact.of_isClosed_subset (hf.prod hg) (isClosed_tsupport _)
    (tsupport_prodMul_subset (f := f) (g := g))

/-- **A `C²` function with compact support has bounded first and second derivatives.**
`fderiv f` is continuous (`ContDiff.continuous_fderiv`) and compactly supported
(`HasCompactSupport.fderiv`), hence bounded in norm; the same argument, one order up, gives
the bound on the second derivative.  The constant `M` is chosen positive. -/
lemma exists_bound_fderiv_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (h2 : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    ∃ M : ℝ, 0 < M ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ M) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) := by
  have hcf : HasCompactSupport (fderiv ℝ f) := HasCompactSupport.fderiv (𝕜 := ℝ) hc
  have h1 : ContDiff ℝ (1 : WithTop ℕ∞) f := h2.of_le (by norm_num)
  obtain ⟨M₁, hM₁⟩ := (h1.continuous_fderiv (by norm_num)).bounded_above_of_compact_support hcf
  have hd : ContDiff ℝ (1 : WithTop ℕ∞) (fderiv ℝ f) := h2.fderiv_right (by norm_num)
  have hcf2 : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) hcf
  obtain ⟨M₂, hM₂⟩ := (hd.continuous_fderiv (by norm_num)).bounded_above_of_compact_support hcf2
  exact ⟨|M₁| + |M₂| + 1, by positivity,
    fun x => by linarith [hM₁ x, le_abs_self M₁, abs_nonneg M₂],
    fun x => by linarith [hM₂ x, le_abs_self M₂, abs_nonneg M₁]⟩

/-! ## The target -/

/-- **A `C^∞` rectangular cut-off with a uniform bound on the first two derivatives.**
The two one-dimensional factors come from `smoothIntervalCutoff`; their product is the
cut-off `χ`.  All the clauses are immediate from the defining properties of the factors,
except the two derivative bounds, which come from `exists_bound_fderiv_fderiv` and compact
support.

The hypotheses `0 < a'`, `0 < c'` and `d' < π / 2` are not used: the construction works for
arbitrary nested rectangles. -/
theorem exists_cutoff_rect_C2 {a b c d a' b' c' d' : ℝ}
    (ha' : 0 < a') (h1 : a' < a) (h2 : a ≤ b) (h3 : b < b')
    (hc' : 0 < c') (h4 : c' < c) (h5 : c ≤ d) (h6 : d < d') (h7 : d' < π / 2) :
    ∃ (χ : ℝ × ℝ → ℝ) (M : ℝ), 0 < M ∧ (∀ n : ℕ, ContDiff ℝ n χ) ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ z, z ∈ Set.Icc a b → ∀ θ, θ ∈ Set.Icc c d → χ (z, θ) = 1) ∧
      (∀ x, x ∉ Set.Icc a' b' ×ˢ Set.Icc c' d' → χ x = 0) ∧
      (∀ x, ‖fderiv ℝ χ x‖ ≤ M) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ M) := by
  obtain ⟨g, hgsm, hgcs, hgnn, hgle, hgone, hgzero⟩ := smoothIntervalCutoff h1 h3
  obtain ⟨v, hvsm, hvcs, hvnn, hvle, hvone, hvzero⟩ := smoothIntervalCutoff h4 h6
  have hsm : ∀ n : ℕ, ContDiff ℝ n (fun p : ℝ × ℝ => g p.1 * v p.2) := fun n =>
    ((hgsm n).comp contDiff_fst).mul ((hvsm n).comp contDiff_snd)
  have hcs : HasCompactSupport (fun p : ℝ × ℝ => g p.1 * v p.2) :=
    hasCompactSupport_prodMul hgcs hvcs
  obtain ⟨M, hMpos, hMn1, hMn2⟩ := exists_bound_fderiv_fderiv (hsm 2) hcs
  exact ⟨fun p : ℝ × ℝ => g p.1 * v p.2, M, hMpos, hsm, hcs,
    fun x => mul_nonneg (hgnn x.1) (hvnn x.2),
    fun x => by
      calc g x.1 * v x.2 ≤ 1 * 1 := mul_le_mul (hgle x.1) (hvle x.2) (hvnn x.2) zero_le_one
        _ = 1 := by ring,
    fun z hz θ hθ => by
      show g z * v θ = 1
      rw [hgone z hz, hvone θ hθ, mul_one],
    fun x hx => by
      obtain ⟨z, θ⟩ := x
      show g z * v θ = 0
      by_cases hz : z ∈ Set.Icc a' b'
      · have hθ : θ ∉ Set.Icc c' d' := fun hθ => hx (Set.mem_prod.mpr ⟨hz, hθ⟩)
        rw [hvzero θ hθ, mul_zero]
      · rw [hgzero z hz, zero_mul],
    hMn1, hMn2⟩

end Work.FTS.StrongLWP.Sobolev.EqcAux
