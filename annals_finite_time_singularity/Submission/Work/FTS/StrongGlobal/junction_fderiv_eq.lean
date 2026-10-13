import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongGlobal.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongGlobal

open Work.FTS.Galerkin (Fam)

/-! ## Coordinates of the Fréchet derivative of a curried family

For a family `F : Fam = ℝ → ℝ → ℝ → ℝ` the uncurried map `uncurry3 F : P3 → ℝ`,
`p ↦ F p.1 p.2.1 p.2.2`, has at a point `(z,θ,τ)` at which it is differentiable the Fréchet
derivative whose value on `v = (v₁, v₂, v₃)` is the linear combination of the three partial
derivatives with coefficients `v₁`, `v₂`, `v₃`.  The three lemmas below compute the three
coordinate directions, and `fderiv_uncurry3_apply` packages them.

The proof of each coordinate direction is the chain rule along the (affine) curve
`s ↦ (s,θ,τ)` / `s ↦ (z,s,τ)` / `s ↦ (z,θ,s)`, whose derivative is the corresponding basis
vector; this is `HasFDerivAt.comp_hasDerivAt`. -/

/-- The first coordinate direction of the Fréchet derivative of `uncurry3 F` is the `z`-partial
derivative of `F`. -/
theorem fderiv_uncurry3_apply_fst {F : Fam} {z θ τ : ℝ}
    (hF : DifferentiableAt ℝ (uncurry3 F) (z, θ, τ)) :
    fderiv ℝ (uncurry3 F) (z, θ, τ) ((1 : ℝ), 0, 0) = deriv (fun s => F s θ τ) z := by
  have hc : HasDerivAt (fun s : ℝ => (s, θ, τ)) ((1 : ℝ), (0 : ℝ), (0 : ℝ)) z :=
    (hasDerivAt_id z).prodMk
      ((hasDerivAt_const (c := θ) (x := z)).prodMk (hasDerivAt_const (c := τ) (x := z)))
  have h := HasFDerivAt.comp_hasDerivAt (x := z) hF.hasFDerivAt hc
  rw [← h.deriv]
  simp [Function.comp_def]

/-- The second coordinate direction of the Fréchet derivative of `uncurry3 F` is the `θ`-partial
derivative of `F`. -/
theorem fderiv_uncurry3_apply_snd {F : Fam} {z θ τ : ℝ}
    (hF : DifferentiableAt ℝ (uncurry3 F) (z, θ, τ)) :
    fderiv ℝ (uncurry3 F) (z, θ, τ) ((0 : ℝ), 1, 0) = deriv (fun s => F z s τ) θ := by
  have hc : HasDerivAt (fun s : ℝ => (z, s, τ)) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_const (c := z) (x := θ)).prodMk
      ((hasDerivAt_id θ).prodMk (hasDerivAt_const (c := τ) (x := θ)))
  have h := HasFDerivAt.comp_hasDerivAt (x := θ) hF.hasFDerivAt hc
  rw [← h.deriv]
  simp [Function.comp_def]

/-- The third coordinate direction of the Fréchet derivative of `uncurry3 F` is the `τ`-partial
derivative of `F`. -/
theorem fderiv_uncurry3_apply_thd {F : Fam} {z θ τ : ℝ}
    (hF : DifferentiableAt ℝ (uncurry3 F) (z, θ, τ)) :
    fderiv ℝ (uncurry3 F) (z, θ, τ) ((0 : ℝ), 0, 1) = deriv (fun s => F z θ s) τ := by
  have hc : HasDerivAt (fun s : ℝ => (z, θ, s)) ((0 : ℝ), (0 : ℝ), (1 : ℝ)) τ :=
    (hasDerivAt_const (c := z) (x := τ)).prodMk
      ((hasDerivAt_const (c := θ) (x := τ)).prodMk (hasDerivAt_id τ))
  have h := HasFDerivAt.comp_hasDerivAt (x := τ) hF.hasFDerivAt hc
  rw [← h.deriv]
  simp [Function.comp_def]

/-- **The Fréchet derivative of a curried family, in coordinates.**  If `uncurry3 F` is
differentiable at `(z,θ,τ)` then its derivative there is the linear combination of the three
partial derivatives. -/
theorem fderiv_uncurry3_apply {F : Fam} {z θ τ : ℝ}
    (hF : DifferentiableAt ℝ (uncurry3 F) (z, θ, τ)) (v : P3) :
    fderiv ℝ (uncurry3 F) (z, θ, τ) v =
      v.1 * deriv (fun s => F s θ τ) z + v.2.1 * deriv (fun s => F z s τ) θ
        + v.2.2 * deriv (fun s => F z θ s) τ := by
  have h1 := fderiv_uncurry3_apply_fst (F := F) hF
  have h2 := fderiv_uncurry3_apply_snd (F := F) hF
  have h3 := fderiv_uncurry3_apply_thd (F := F) hF
  have hv : v = v.1 • (((1 : ℝ), 0, 0) : P3) + v.2.1 • (((0 : ℝ), 1, 0) : P3)
      + v.2.2 • (((0 : ℝ), 0, 1) : P3) := by
    ext <;> simp
  conv_lhs => rw [hv]
  rw [map_add, map_add, map_smul, map_smul, map_smul, h1, h2, h3]
  simp only [smul_eq_mul]

/-- **The junction lemma for the joint `C¹`-regularity of a concatenation of two pieces.**

If two families `G` and `H` agree on the open quadrant `(0,∞) × (0,π/2)` at the fake time `τ₀`
(`hval`), and their fake-time derivatives agree there as well (`hder`), and both are jointly
differentiable at `(z,θ,τ₀)` with `(z,θ)` in that quadrant, then the Fréchet derivatives of the
two uncurried families at `(z,θ,τ₀)` are equal.

Indeed, `hval` makes the two families agree on a *neighbourhood* of `(z,θ)` inside the hyperplane
`{τ = τ₀}`, so their `z`- and `θ`-partial derivatives at `(z,θ,τ₀)` coincide, while `hder` gives
the equality of the `τ`-partials; the derivative is the linear combination of the three partials
(`fderiv_uncurry3_apply`). -/
theorem junction_fderiv_eq {G H : Work.FTS.Galerkin.Fam} {τ₀ z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hGd : DifferentiableAt ℝ (Work.FTS.StrongGlobal.uncurry3 G) (z, θ, τ₀))
    (hHd : DifferentiableAt ℝ (Work.FTS.StrongGlobal.uncurry3 H) (z, θ, τ₀))
    (hval : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 → G z' θ' τ₀ = H z' θ' τ₀)
    (hder : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      deriv (fun s => G z' θ' s) τ₀ = deriv (fun s => H z' θ' s) τ₀) :
    fderiv ℝ (Work.FTS.StrongGlobal.uncurry3 G) (z, θ, τ₀) =
      fderiv ℝ (Work.FTS.StrongGlobal.uncurry3 H) (z, θ, τ₀) := by
  -- the `z`-partials agree: `G` and `H` agree on the neighbourhood `(0,∞)` of `z`
  have hz_eq : deriv (fun s : ℝ => G s θ τ₀) z = deriv (fun s : ℝ => H s θ τ₀) z := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
    exact hval s θ hs hθ0 hθ1
  -- the `θ`-partials agree: `G` and `H` agree on the neighbourhood `(0,π/2)` of `θ`
  have hθ_eq : deriv (fun s : ℝ => G z s τ₀) θ = deriv (fun s : ℝ => H z s τ₀) θ := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩] with s hs
    exact hval z s hz hs.1 hs.2
  -- (the product-`ext` lemma of `ContinuousLinearMap` fires first and is not what we want here,
  -- hence the explicit `ContinuousLinearMap.ext`)
  refine ContinuousLinearMap.ext fun v => ?_
  rw [fderiv_uncurry3_apply hGd v, fderiv_uncurry3_apply hHd v, hz_eq, hθ_eq,
    hder z θ hz hθ0 hθ1]

end Work.FTS.StrongGlobal
