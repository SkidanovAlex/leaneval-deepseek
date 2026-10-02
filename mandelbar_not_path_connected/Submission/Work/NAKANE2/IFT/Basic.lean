/-
# `Work.NAKANE2` — the inverse-function-theorem layer

This file contains the pure-analysis ingredients of the route to `Work.NAKANE.PhiLocalHomeo`
which do not use anything about the tricorn.

* `Work.NAKANE2.surjective_of_lipschitzSection` **(D2)**: if `f` is differentiable at `x` with
  derivative `L`, `h` is differentiable at `0` with *surjective* derivative `H`, and there is a
  Lipschitz section of `h` through `f` near `x` (`f (c v) = h v` and `‖c v − x‖ ≤ K‖v‖` for small
  `v`), then `L` is surjective.  This is the mechanism by which the Shishikura surgery forces
  `DΦ(c₀)` to be invertible.
* `Work.NAKANE2.equivOfSurjective` **(D2, II)**: a surjective `ℝ`-linear endomorphism of `ℂ` is a
  `ContinuousLinearEquiv`.
* `Work.NAKANE2.localHomeoAt_of_strict` **(D3)**: Mathlib's inverse function theorem
  `HasStrictFDerivAt.toOpenPartialHomeomorph`, packaged as the witness required by
  `IsLocalHomeomorphOn`.
* `Work.NAKANE2.hasStrictFDerivAt_tsum_of_isPreconnected` (real and complex forms): a series of
  functions on a preconnected open set, each differentiable with a uniformly summable bound on
  the derivatives and with *continuous* sum of derivatives, is strictly differentiable, with the
  sum of the derivatives as derivative.

The last item is the substitute for the "Osgood lemma" of the design note: it replaces
"continuous + separately holomorphic ⟹ strictly differentiable" by the elementary
observation that uniform convergence of the term-wise derivatives is enough.  Only this
form is used below (there is no `osgood3` definition in this area).
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Function Asymptotics
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace Work.NAKANE2

/-! ## (D2): a Lipschitz section forces surjectivity of the derivative -/

/-- The ray `t ↦ (t : ℂ) * u` tends to `0` along `t → 0⁺`. -/
theorem tendsto_ofReal_mul (u : ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ) * u) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  have h2 : Tendsto (fun t : ℝ => (t : ℂ) * u) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℂ) * u)) :=
    ((Complex.continuous_ofReal.mul continuous_const).continuousAt).tendsto
  simpa using h2.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))

theorem ofReal_mul_eq_smul (t : ℝ) (z : ℂ) : (t : ℂ) * z = t • z := by
  rw [Complex.real_smul]

theorem smul_eq_ofReal_mul (t : ℝ) (z : ℂ) : t • z = (t : ℂ) * z := by
  rw [Complex.real_smul]

/-- **(D2).**  A differentiable map with a Lipschitz section through a differentiable map with
surjective derivative has surjective derivative. -/
theorem surjective_of_lipschitzSection {f h : ℂ → ℂ} {L H : ℂ →L[ℝ] ℂ} {x : ℂ} {r K : ℝ}
    (hf : HasFDerivAt f L x) (hh : HasFDerivAt h H 0) (hH : Function.Surjective H)
    (hr : 0 < r) (h0 : h 0 = f x)
    (hsec : ∀ v : ℂ, ‖v‖ < r → ∃ c : ℂ, f c = h v ∧ ‖c - x‖ ≤ K * ‖v‖) :
    Function.Surjective L := by
  classical
  intro y
  obtain ⟨u, hu⟩ := hH y
  set cfun : ℝ → ℂ := fun t =>
    if ht : ‖(t : ℂ) * u‖ < r then Classical.choose (hsec ((t : ℂ) * u) ht) else x with hcfundef
  have hcfun_spec : ∀ t : ℝ, ‖(t : ℂ) * u‖ < r →
      f (cfun t) = h ((t : ℂ) * u) ∧ ‖cfun t - x‖ ≤ K * ‖(t : ℂ) * u‖ := by
    intro t ht
    have hval : cfun t = Classical.choose (hsec ((t : ℂ) * u) ht) := by
      rw [hcfundef]; exact dif_pos ht
    rw [hval]
    exact Classical.choose_spec (hsec ((t : ℂ) * u) ht)
  have hnorm : Tendsto (fun t : ℝ => ‖(t : ℂ) * u‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_ofReal_mul u).norm
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ‖(t : ℂ) * u‖ < r := by
    have hmem := Metric.tendsto_nhds.mp hnorm r hr
    filter_upwards [hmem] with t ht
    rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at ht
  have hlip : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ‖cfun t - x‖ ≤ (max K 0) * ‖(t : ℂ) * u‖ := by
    filter_upwards [hsmall] with t ht
    exact ((hcfun_spec t ht).2).trans
      (mul_le_mul_of_nonneg_right (le_max_left K 0) (norm_nonneg _))
  -- the section points tend to `x`
  have hcx : Tendsto cfun (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hden : 0 < max K 0 + 1 := by positivity
    have hmem := Metric.tendsto_nhds.mp hnorm (ε / (max K 0 + 1)) (div_pos hε hden)
    have hthr : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ‖(t : ℂ) * u‖ < ε / (max K 0 + 1) := by
      filter_upwards [hmem] with t ht
      rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at ht
    filter_upwards [hlip, hthr] with t hl ht
    rw [dist_eq_norm]
    calc ‖cfun t - x‖ ≤ max K 0 * ‖(t : ℂ) * u‖ := hl
      _ ≤ (max K 0 + 1) * ‖(t : ℂ) * u‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (max K 0 + 1) * (ε / (max K 0 + 1)) := mul_lt_mul_of_pos_left ht hden
      _ = ε := by rw [mul_comm]; exact div_mul_cancel₀ ε hden.ne' 
  have herr : ∀ ε > 0, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ‖f (cfun t) - f x - L (cfun t - x)‖ ≤ ε * ‖cfun t - x‖ := by
    intro ε hε
    have hlit : (fun c : ℂ => f c - f x - L (c - x)) =o[𝓝 x] (fun c : ℂ => c - x) := hf.isLittleO
    exact hcx.eventually (hlit.bound hε)
  -- the "nonlinear" part of the quotient tends to `0`
  have h2 : Tendsto (fun t : ℝ => (f (cfun t) - f x - L (cfun t - x)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hM : 0 ≤ max K 0 * ‖u‖ := mul_nonneg (le_max_right K 0) (norm_nonneg u)
    have hden : 0 < max K 0 * ‖u‖ + 1 := by linarith
    have hε' : 0 < ε / (max K 0 * ‖u‖ + 1) := div_pos hε hden
    filter_upwards [herr _ hε', hlip, self_mem_nhdsWithin] with t hterr hl htpos
    have htn : (0 : ℝ) < t := htpos
    have htC : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htn]
    have hvn : ‖(t : ℂ) * u‖ = t * ‖u‖ := by rw [norm_mul, htC]
    have hbd : ‖cfun t - x‖ ≤ (max K 0 * ‖u‖) * t := by
      calc ‖cfun t - x‖ ≤ max K 0 * ‖(t : ℂ) * u‖ := hl
        _ = (max K 0 * ‖u‖) * t := by rw [hvn]; ring
    have hbd' : ‖cfun t - x‖ / t ≤ max K 0 * ‖u‖ := by
      rw [div_le_iff₀ htn]; exact hbd
    rw [dist_eq_norm, sub_zero, norm_div, htC]
    calc ‖f (cfun t) - f x - L (cfun t - x)‖ / t
        ≤ (ε / (max K 0 * ‖u‖ + 1)) * ‖cfun t - x‖ / t :=
          div_le_div_of_nonneg_right hterr (le_of_lt htn)
      _ = (ε / (max K 0 * ‖u‖ + 1)) * (‖cfun t - x‖ / t) := by ring
      _ ≤ (ε / (max K 0 * ‖u‖ + 1)) * (max K 0 * ‖u‖) :=
          mul_le_mul_of_nonneg_left hbd' (by positivity)
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
          nlinarith [hM, hε]
  -- the differential part of the quotient tends to `y`
  have h1 : Tendsto (fun t : ℝ => (f (cfun t) - f x) / t) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    have heq : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        (h ((t : ℂ) * u) - h 0) / t = (f (cfun t) - f x) / t := by
      filter_upwards [hsmall] with t ht
      rw [(hcfun_spec t ht).1, h0]
    refine Tendsto.congr' heq ?_
    have hlit : (fun v : ℂ => h v - h 0 - H v) =o[𝓝 (0 : ℂ)] (fun v : ℂ => v) := by
      simpa using hh.isLittleO
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hden : 0 < ‖u‖ + 1 := by positivity
    have hε' : 0 < ε / (‖u‖ + 1) := div_pos hε hden
    filter_upwards [(tendsto_ofReal_mul u).eventually (hlit.bound hε'), self_mem_nhdsWithin]
      with t hbnd htpos
    have htn : (0 : ℝ) < t := htpos
    have htn' : t ≠ 0 := ne_of_gt htn
    have htC : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htn]
    have hvn : ‖(t : ℂ) * u‖ = t * ‖u‖ := by rw [norm_mul, htC]
    have hHv : H ((t : ℂ) * u) = (t : ℂ) * y := by
      conv_lhs => rw [ofReal_mul_eq_smul]
      rw [map_smul, hu]
      exact smul_eq_ofReal_mul t y
    have htCne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htn'
    have hHv' : H ((t : ℂ) * u) / (t : ℂ) = y := by
      rw [hHv, mul_div_cancel_left₀ y htCne]
    have hkey : (h ((t : ℂ) * u) - h 0) / t - y
        = (h ((t : ℂ) * u) - h 0 - H ((t : ℂ) * u)) / t := by
      rw [← hHv', ← sub_div]
    rw [dist_eq_norm, hkey, norm_div, htC]
    calc ‖h ((t : ℂ) * u) - h 0 - H ((t : ℂ) * u)‖ / t
        ≤ (ε / (‖u‖ + 1)) * ‖(t : ℂ) * u‖ / t :=
          div_le_div_of_nonneg_right hbnd (le_of_lt htn)
      _ = (ε / (‖u‖ + 1)) * (‖(t : ℂ) * u‖ / t) := by ring
      _ = (ε / (‖u‖ + 1)) * ‖u‖ := by
          rw [hvn, mul_div_cancel_left₀ ‖u‖ htn']
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
          nlinarith [norm_nonneg u, hε]
  -- hence `y` is a limit of points of `range L`, which is closed in finite dimension
  have h3 : Tendsto (fun t : ℝ => L ((cfun t - x) / t)) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    have hsub := h1.sub h2
    rw [sub_zero] at hsub
    refine Tendsto.congr' (Eventually.of_forall fun t => ?_) hsub
    show (f (cfun t) - f x) / (t : ℂ) - (f (cfun t) - f x - L (cfun t - x)) / (t : ℂ)
      = L ((cfun t - x) / (t : ℂ))
    have hL : L ((cfun t - x) / (t : ℂ)) = L (cfun t - x) / (t : ℂ) := by
      have h1 : (cfun t - x) / (t : ℂ) = (t⁻¹ : ℝ) • (cfun t - x) := by
        rw [div_eq_inv_mul, ← Complex.ofReal_inv, ofReal_mul_eq_smul]
      have h2 : L (cfun t - x) / (t : ℂ) = (t⁻¹ : ℝ) • L (cfun t - x) := by
        rw [div_eq_inv_mul, ← Complex.ofReal_inv, ofReal_mul_eq_smul]
      rw [h1, h2, map_smul]
    rw [← sub_div, show (f (cfun t) - f x) - (f (cfun t) - f x - L (cfun t - x))
      = L (cfun t - x) from by ring, ← hL]
  have hclosed : IsClosed (Set.range L) := by
    have : IsClosed ((L.toLinearMap.range : Submodule ℝ ℂ) : Set ℂ) :=
      Submodule.closed_of_finiteDimensional _
    simpa [LinearMap.coe_range] using this
  exact Set.mem_range.mp
    (hclosed.mem_of_tendsto h3 (Eventually.of_forall fun _ => Set.mem_range_self _))

/-! ## (D2, II): a surjective real-linear endomorphism of `ℂ` is a linear equivalence -/

/-- A surjective `ℝ`-linear endomorphism of the finite-dimensional space `ℂ` is a
`ContinuousLinearEquiv`. -/
theorem equivOfSurjective (L : ℂ →L[ℝ] ℂ) (hL : Function.Surjective L) :
    ∃ e : ℂ ≃L[ℝ] ℂ, (e : ℂ →L[ℝ] ℂ) = L := by
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr
    ((LinearMap.injective_iff_surjective (f := L.toLinearMap)).mpr hL)
  have hrange : L.range = ⊤ := LinearMap.range_eq_top.mpr hL
  exact ⟨ContinuousLinearEquiv.ofBijective L hker hrange,
    ContinuousLinearEquiv.coe_ofBijective L hker hrange⟩

/-! ## (D3): the inverse function theorem -/

/-- **(D3).**  A strict derivative at `c₀` which is invertible produces the witness of
`IsLocalHomeomorphOn`: an `OpenPartialHomeomorph` whose source contains `c₀` and which *is* the
function `f`. -/
theorem localHomeoAt_of_strict {f : ℂ → ℂ} {c₀ : ℂ} {e : ℂ ≃L[ℝ] ℂ}
    (h : HasStrictFDerivAt f (e : ℂ →L[ℝ] ℂ) c₀) :
    ∃ E : OpenPartialHomeomorph ℂ ℂ, c₀ ∈ E.source ∧ f = E :=
  ⟨h.toOpenPartialHomeomorph f, h.mem_toOpenPartialHomeomorph_source,
    (HasStrictFDerivAt.toOpenPartialHomeomorph_coe h).symm⟩

/-! ## Strict differentiability of a series -/

/-- A series of functions on a preconnected open set, each differentiable with a uniformly
summable bound on the derivatives and with a *continuous* sum of derivatives, is strictly
differentiable at every point of the set, with derivative the sum of the derivatives.

This is Mathlib's `hasFDerivAt_tsum_of_isPreconnected` upgraded to a strict derivative via
`hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt`. -/
theorem hasStrictFDerivAt_tsum_of_isPreconnected_real {α E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {u : α → ℝ}
    {f : α → E → F} {f' : α → E → E →L[ℝ] F} {s : Set E} {x₀ x : E}
    (hu : Summable u) (hs : IsOpen s) (h's : IsPreconnected s)
    (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, x ∈ s → ‖f' n x‖ ≤ u n)
    (hcont : ContinuousOn (fun x => ∑' n, f' n x) s)
    (hx₀ : x₀ ∈ s) (hf0 : Summable fun n => f n x₀) (hx : x ∈ s) :
    HasStrictFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x := by
  haveI : IsRCLikeNormedField ℝ := inferInstance
  refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (f' := fun y => ∑' n, f' n y) ?_ ?_
  · filter_upwards [hs.mem_nhds hx] with y hy
    exact hasFDerivAt_tsum_of_isPreconnected hu hs h's hf hf' hx₀ hf0 hy
  · exact hcont.continuousAt (hs.mem_nhds hx)

/-- The complex form of `hasStrictFDerivAt_tsum_of_isPreconnected_real`. -/
theorem hasStrictFDerivAt_tsum_of_isPreconnected_complex {α E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {u : α → ℝ}
    {f : α → E → F} {f' : α → E → E →L[ℂ] F} {s : Set E} {x₀ x : E}
    (hu : Summable u) (hs : IsOpen s) (h's : IsPreconnected s)
    (hf : ∀ n x, x ∈ s → HasFDerivAt (f n) (f' n x) x)
    (hf' : ∀ n x, x ∈ s → ‖f' n x‖ ≤ u n)
    (hcont : ContinuousOn (fun x => ∑' n, f' n x) s)
    (hx₀ : x₀ ∈ s) (hf0 : Summable fun n => f n x₀) (hx : x ∈ s) :
    HasStrictFDerivAt (fun y => ∑' n, f n y) (∑' n, f' n x) x := by
  haveI : IsRCLikeNormedField ℂ := inferInstance
  refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (f' := fun y => ∑' n, f' n y) ?_ ?_
  · filter_upwards [hs.mem_nhds hx] with y hy
    exact hasFDerivAt_tsum_of_isPreconnected hu hs h's hf hf' hx₀ hf0 hy
  · exact hcont.continuousAt (hs.mem_nhds hx)

end Work.NAKANE2
