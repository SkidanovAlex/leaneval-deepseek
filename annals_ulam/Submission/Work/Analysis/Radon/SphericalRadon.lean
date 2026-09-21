import Mathlib
import Submission.Commons.Analysis.Radon.sphericalRadon_rot
import Submission.Commons.Analysis.InnerProductSpace.orthogonal_transitive_level_sets

/-!
# The spherical Radon transform

For a finite-dimensional real inner product space `E` and `f : E → ℝ`, the *spherical Radon
transform* of `f` at a unit vector `ξ` is the integral of `f` over the unit sphere of the
orthogonal complement `ξᗮ`, i.e. over the equator `S^{d-1} ∩ ξ^⊥`:

`sphericalRadon f ξ = ∫_{S(ξᗮ)} f`.

This is the operator `𝓡` used in §4 of Ryabogin, *A negative answer to Ulam's Problem 19 from
the Scottish Book*, Ann. of Math. **195** (2022), where

`𝓡 g(ξ) = ∫_{S^{d-1} ∩ ξ^⊥} g(w) dw`.

We normalise the measure on the equator as the intrinsic surface measure
`MeasureTheory.Measure.toSphere` of the orthogonal complement.

## Main definitions

* `radonOver s f`: the integral of `f` over the unit sphere of a submodule `s` (this is the
  type-correct primitive, allowing transport along equalities of submodules).
* `sphericalRadon f ξ`: `radonOver ξᗮ f`.

## Main results

* `radonOver_congr`: `radonOver` depends only on the submodule.
* `sphericalRadon_neg_arg`: `sphericalRadon` is even in `ξ` (`ξ` and `-ξ` share an equator).
* `toSphere_neg` / `toSphere_instIsNegInvariant`: the sphere measure is invariant under
  negation, hence the antipodal map is measure preserving on the equator.
* `sphericalRadon_odd`: `sphericalRadon` kills odd functions.  This is the analytic content
  of the paper's condition `𝓡(w_j ρ_K^d)(ξ) = 0` (eq. (mihalna2)).
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Commons.Analysis.Radon

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The integral of `f` over the unit sphere of a submodule `s`, with respect to the intrinsic
surface measure `MeasureTheory.Measure.toSphere` of `s`. -/
noncomputable def radonOver (s : Submodule ℝ E) (f : E → ℝ) : ℝ :=
  ∫ ω : Metric.sphere (0 : s) 1, f ((ω : s) : E)
    ∂(MeasureTheory.Measure.toSphere (volume : Measure s))

/-- `radonOver` only depends on the submodule (transport along an equality of submodules). -/
lemma radonOver_congr {s t : Submodule ℝ E} (h : s = t) (f : E → ℝ) :
    radonOver s f = radonOver t f := by
  subst h; rfl

/-- The equator of `ξ`: the unit sphere of the orthogonal complement `(ℝ ∙ ξ)ᗮ`. -/
abbrev equator (ξ : E) : Set ((ℝ ∙ ξ)ᗮ) := Metric.sphere (0 : (ℝ ∙ ξ)ᗮ) 1

/-- The surface measure on the equator of `ξ`. -/
noncomputable def equatorMeasure (ξ : E) : Measure (equator ξ) :=
  MeasureTheory.Measure.toSphere (volume : Measure ((ℝ ∙ ξ)ᗮ))

/-- The spherical Radon transform of `f` at `ξ`: the integral of `f` over the equator of `ξ`. -/
noncomputable def sphericalRadon (f : E → ℝ) (ξ : Metric.sphere (0 : E) 1) : ℝ :=
  radonOver (ℝ ∙ ξ.1)ᗮ f

/-- `sphericalRadon f ξ` agrees with the "equator" description. -/
lemma sphericalRadon_eq_integral (f : E → ℝ) (ξ : Metric.sphere (0 : E) 1) :
    sphericalRadon f ξ = ∫ ω : equator ξ.1, f ((ω : (ℝ ∙ ξ.1)ᗮ) : E) ∂(equatorMeasure ξ.1) :=
  rfl

/-- Negating `ξ` does not change its orthogonal complement. -/
lemma orthogonal_span_neg (v : E) : (ℝ ∙ (-v))ᗮ = (ℝ ∙ v)ᗮ := by
  have h : (ℝ ∙ (-v)) = (ℝ ∙ v) := by
    rw [show (-v : E) = (-1 : ℝ) • v by simp,
      Submodule.span_singleton_smul_eq (R := ℝ) (isUnit_iff_ne_zero.mpr (by norm_num)) v]
  rw [h]

/-- The negated unit vector. -/
def sphereNeg (ξ : Metric.sphere (0 : E) 1) : Metric.sphere (0 : E) 1 :=
  ⟨-ξ.1, by simpa [Metric.mem_sphere, norm_neg] using ξ.2⟩

@[simp] lemma sphereNeg_coe (ξ : Metric.sphere (0 : E) 1) : (sphereNeg ξ).1 = -ξ.1 := rfl

/-- `sphereNeg` is an involution. -/
@[simp] lemma sphereNeg_sphereNeg (ξ : Metric.sphere (0 : E) 1) :
    sphereNeg (sphereNeg ξ) = ξ := by
  ext; simp [sphereNeg]

/-- The Radon transform is even as a function of `ξ`, since `ξ` and `-ξ` have the same equator. -/
lemma sphericalRadon_neg_arg (f : E → ℝ) (ξ : Metric.sphere (0 : E) 1) :
    sphericalRadon f (sphereNeg ξ) = sphericalRadon f ξ := by
  unfold sphericalRadon sphereNeg
  exact radonOver_congr (orthogonal_span_neg ξ.1) f

/-! ### Negation invariance of the sphere measure

`toSphere_neg` (negation-invariance of `volume.toSphere`) is in the commons as
`Commons.Analysis.Radon.toSphere_neg`; here we record the two instance-level consequences used
below, together with the `MeasurableNeg`/`InvolutiveNeg` instances on the unit sphere. -/

section NegInvariant

variable (μ : Measure E) [μ.IsNegInvariant]

/-- The sphere inherits measurability of negation. -/
instance instMeasurableNegSphere : MeasurableNeg (Metric.sphere (0 : E) 1) where
  measurable_neg := by fun_prop

/-- The sphere inherits an involutive negation. -/
instance instInvolutiveNegSphere : InvolutiveNeg (Metric.sphere (0 : E) 1) where
  neg_neg := fun x => Subtype.ext (by simp)

/-- The sphere measure of a negation-invariant measure is itself negation-invariant. -/
instance toSphere_instIsNegInvariant : (μ.toSphere).IsNegInvariant where
  neg_eq_self := by
    rw [MeasureTheory.Measure.neg_def]
    refine MeasureTheory.Measure.ext fun s hs => ?_
    rw [MeasureTheory.Measure.map_apply measurable_neg hs]
    have hpre : Neg.neg ⁻¹' s = -s := by ext x; simp [Set.mem_neg]
    rw [hpre, Commons.Analysis.Radon.toSphere_neg μ s hs]

end NegInvariant

/-- The equator measure is negation-invariant. -/
instance equatorMeasure_instIsNegInvariant (ξ : E) : (equatorMeasure ξ).IsNegInvariant :=
  toSphere_instIsNegInvariant (volume : Measure ((ℝ ∙ ξ)ᗮ))

/-- The antipodal map is measure preserving on the equator. -/
lemma measurePreserving_neg_equator (ξ : E) :
    MeasurePreserving (fun ω : equator ξ => -ω) (equatorMeasure ξ) (equatorMeasure ξ) :=
  Measure.measurePreserving_neg _

/-- `radonOver` is invariant under precomposing with negation. -/
lemma radonOver_neg (s : Submodule ℝ E) (f : E → ℝ) :
    radonOver s (fun x => f (-x)) = radonOver s f := by
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.neg (Metric.sphere (0 : s) 1)))
      (MeasureTheory.Measure.toSphere (volume : Measure s))
      (MeasureTheory.Measure.toSphere (volume : Measure s)) := by
    simpa [MeasurableEquiv.neg_apply] using
      (Measure.measurePreserving_neg (MeasureTheory.Measure.toSphere (volume : Measure s)))
  have h := hmp.integral_comp' (fun y : Metric.sphere (0 : s) 1 => f ((y : s) : E))
  simpa [radonOver, MeasurableEquiv.neg_apply, Function.comp_def] using h

/-- **The Radon transform kills odd functions.**  If `f (-x) = - f x` then `𝓡 f ξ = 0` for
every unit vector `ξ`.  This is the analytic content of the paper's condition
`𝓡(w_j ρ_K^d)(ξ) = 0` (eq. (mihalna2)). -/
theorem sphericalRadon_odd (f : E → ℝ) (hf : ∀ x, f (-x) = - f x) (ξ : Metric.sphere (0 : E) 1) :
    sphericalRadon f ξ = 0 := by
  have hfun : (fun x : E => f (-x)) = fun x => - f x := by funext x; exact hf x
  have hstep : radonOver ((ℝ ∙ ξ.1)ᗮ) (fun x => - f x)
      = - radonOver ((ℝ ∙ ξ.1)ᗮ) f := by
    rw [radonOver, radonOver, ← MeasureTheory.integral_neg]
  have key : radonOver ((ℝ ∙ ξ.1)ᗮ) f = - radonOver ((ℝ ∙ ξ.1)ᗮ) f :=
    (radonOver_neg ((ℝ ∙ ξ.1)ᗮ) f).symm.trans
      ((congrArg (radonOver ((ℝ ∙ ξ.1)ᗮ)) hfun).trans hstep)
  have hzero : radonOver ((ℝ ∙ ξ.1)ᗮ) f = 0 := by linarith [key]
  simpa [sphericalRadon] using hzero

/-- **`𝓡 f` factors through the coordinate `ξ ↦ ⟪ξ, e⟫`.**

If `f` is invariant under the stabiliser of `e` in `E ≃ₗᵢ[ℝ] E`, then the spherical Radon
transform of `f` depends on `ξ` only through `⟪ξ.1, e⟫`.  (Corollary of
`Commons.Analysis.Radon.sphericalRadon_rot` and
`Commons.Analysis.InnerProductSpace.orthogonal_transitive_level_sets`.)  For a body of
revolution this is what turns `𝓡` into a function of the single angle `α` with
`|ξ_1| = cos α`. -/
theorem sphericalRadon_factors_coord (e : E) (f : E → ℝ)
    (hf : ∀ k : E ≃ₗᵢ[ℝ] E, k e = e → ∀ x, f (k x) = f x)
    {ξ η : Metric.sphere (0 : E) 1} (h : ⟪ξ.1, e⟫ = ⟪η.1, e⟫) :
    sphericalRadon f ξ = sphericalRadon f η := by
  have hξ1 : ‖ξ.1‖ = 1 := by simpa [Metric.mem_sphere] using ξ.2
  have hη1 : ‖η.1‖ = 1 := by simpa [Metric.mem_sphere] using η.2
  have hnorm : ‖η.1‖ = ‖ξ.1‖ := by rw [hη1, hξ1]
  obtain ⟨k, hke, hk⟩ :=
    Commons.Analysis.InnerProductSpace.orthogonal_transitive_level_sets e η.1 ξ.1 hnorm h.symm
  have hsphere : (⟨k η.1, by rw [Metric.mem_sphere, dist_zero_right, k.norm_map, hη1]⟩
      : Metric.sphere (0 : E) 1) = ξ := Subtype.ext hk
  have hrot := Commons.Analysis.Radon.sphericalRadon_rot k f (hf k hke) η
  rw [← hsphere]
  simpa [sphericalRadon, radonOver] using hrot

/-- **A stabiliser-invariant function depends only on `(‖·‖, ⟪·, e⟫)`.**

If `g` is invariant under every orthogonal `k` with `k e = e`, then `g v = g w` as soon as
`‖v‖ = ‖w‖` and `⟪v, e⟫ = ⟪w, e⟫`.  Equivalently, such a `g` is `w ↦ γ (‖w‖, ⟪w, e⟫)` for some
`γ : ℝ × ℝ → ℝ`.  (This is the "radial profile" of a body of revolution, and the input to the
1-dimensional reduction of the spherical Radon transform.) -/
theorem invariant_apply_eq_of_norm_inner_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (e : E) (g : E → ℝ)
    (hg : ∀ k : E ≃ₗᵢ[ℝ] E, k e = e → ∀ x, g (k x) = g x)
    {v w : E} (hv : ‖v‖ = ‖w‖) (hw : ⟪v, e⟫ = ⟪w, e⟫) : g v = g w := by
  obtain ⟨k, hke, hk⟩ :=
    Commons.Analysis.InnerProductSpace.orthogonal_transitive_level_sets e v w hv hw
  rw [← hk]
  exact (hg k hke v).symm

end Commons.Analysis.Radon



/-- **Substitution step: the 1-dimensional Radon integral is an Abel-type integral.**

In even dimension `d = 2n`, the radial reduction produces the integral
`∫_{-1}^{1} γ (a s) (1-s²)^{n-2} ds` with `a = √(1-t²)`.  Substituting `u = a s` identifies it
with the Abel-type transform with *polynomial* kernel,

  `a^{2n-3} ∫_{-1}^{1} γ (a s) (1-s²)^{n-2} ds = ∫_{-a}^{a} γ u (a²-u²)^{n-2} du`

(for `a > 0`).  The right-hand side is `F_{n-2}(a)` of `abel_differentiation_recursion`, whose
inversion is the `(n-1)`-fold differentiation in `A = a²`. -/
theorem pow_mul_integral_sqrt_eq_abelIntegral (n : ℕ) (hn : 2 ≤ n) (γ : ℝ → ℝ) {a : ℝ}
    (ha : 0 < a) :
    a ^ (2 * n - 3) * (∫ s in (-1 : ℝ)..1, γ (a * s) * (1 - s ^ 2) ^ (n - 2))
      = ∫ u in (-a)..a, γ u * (a ^ 2 - u ^ 2) ^ (n - 2) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hcv : (∫ s in (-1 : ℝ)..1, γ (a * s) * (1 - s ^ 2) ^ (n - 2))
      = a⁻¹ * ∫ u in (-a)..a, γ u * (1 - (u / a) ^ 2) ^ (n - 2) := by
    have h := intervalIntegral.integral_comp_mul_left
      (f := fun u : ℝ => γ u * (1 - (u / a) ^ 2) ^ (n - 2)) (a := (-1 : ℝ)) (b := 1) ha0
    simpa [mul_neg, mul_one, smul_eq_mul, mul_div_cancel_left₀ _ ha0] using h
  have hker : ∀ u : ℝ, (1 - (u / a) ^ 2) ^ (n - 2)
      = (a ^ 2 - u ^ 2) ^ (n - 2) * (a ^ (2 * (n - 2)))⁻¹ := by
    intro u
    have h1 : (1 - (u / a) ^ 2) = (a ^ 2 - u ^ 2) / a ^ 2 := by
      field_simp
    rw [h1, div_pow, div_eq_mul_inv, ← pow_mul]
  have hint : (∫ u in (-a)..a, γ u * (1 - (u / a) ^ 2) ^ (n - 2))
      = (a ^ (2 * (n - 2)))⁻¹ * ∫ u in (-a)..a, γ u * (a ^ 2 - u ^ 2) ^ (n - 2) := by
    have h1 : (∫ u in (-a)..a, γ u * (1 - (u / a) ^ 2) ^ (n - 2))
        = ∫ u in (-a)..a,
            (γ u * (a ^ 2 - u ^ 2) ^ (n - 2)) * (a ^ (2 * (n - 2)))⁻¹ := by
      apply intervalIntegral.integral_congr
      intro u _
      change γ u * (1 - (u / a) ^ 2) ^ (n - 2) =
        γ u * (a ^ 2 - u ^ 2) ^ (n - 2) * (a ^ (2 * (n - 2)))⁻¹
      rw [hker u, mul_assoc]
    rw [h1, intervalIntegral.integral_mul_const, mul_comm]
  have hexp : a ^ (2 * n - 3) * a⁻¹ * (a ^ (2 * (n - 2)))⁻¹ = 1 := by
    have h1 : 2 * n - 3 = 2 * (n - 2) + 1 := by omega
    rw [h1, pow_succ, mul_assoc (a ^ (2 * (n - 2))) a a⁻¹, mul_inv_cancel₀ ha0, mul_one]
    exact mul_inv_cancel₀ (pow_ne_zero _ ha0)
  have hJ : a ^ (2 * n - 3) * (a⁻¹ * ((a ^ (2 * (n - 2)))⁻¹ *
        (∫ u in (-a)..a, γ u * (a ^ 2 - u ^ 2) ^ (n - 2)))) =
      (a ^ (2 * n - 3) * a⁻¹ * (a ^ (2 * (n - 2)))⁻¹) *
        (∫ u in (-a)..a, γ u * (a ^ 2 - u ^ 2) ^ (n - 2)) := by ring
  rw [hcv, hint, hJ, hexp, one_mul]

/-!
## Commons status and next rungs

Published (import from these modules):

* `Submission.Commons.Analysis.Radon.toSphere_neg` — `ω ↦ -ω` preserves the equator measure.
* `Submission.Commons.Analysis.Radon.sphericalRadon_rot` — `𝓡 f (k ξ) = 𝓡 f ξ` for orthogonal `k`
  fixing `f`, plus `sphereCongr`/`sphereCongr_measurePreserving`.
* `Submission.Commons.Analysis.InnerProductSpace.orthogonal_transitive_level_sets` — the
  stabiliser of `e` acts transitively on the level sets of `⟪·, e⟫` on spheres.

Proved in this file (no gaps), publication queued: `sphericalRadon_odd`,
`sphericalRadon_factors_coord`, `invariant_apply_eq_of_norm_inner_eq`.

## Queued for the fleet

* `Analysis/Radon/radial_reduction_of_radonOver`: the 1-dimensional reduction
  `𝓡 g (ξ) = c ∫_{-1}^{1} γ (√(1-t²) s) (1-s²)^{(d-4)/2} ds`, `t = ⟪ξ.1, e⟫`.
* `Analysis/Calculus/abel_differentiation_recursion`: for `k ≥ 1` and continuous `γ`,
  `HasDerivAt (fun a => ∫_{u=-a}^{a} γ u (a²-u²)^k)
              (2 a k ∫_{u=-a}^{a} γ u (a²-u²)^{k-1}) a`
  (boundary terms vanish since `(a²-u²)^k|_{u=±a} = 0`).

## The even-dimensional inversion (`d = 2n`, kernel `(1-s²)^{n-2}`)

The radial reduction gives, with `F_k(a) := ∫_{-a}^{a} γ u (a²-u²)^k du` and `a = √(1-t²)`,

  `(Tγ)(t) = a^{-(2n-3)} F_{n-2}(a)`,  so  `F_{n-2}(a) = a^{2n-3} (Tγ)(√(1-a²))`.

The recursion `F_k' = 2 a k F_{k-1}` then gives, with the substitution `A = a²` (so that
`(1/(2ak)) d/da = (1/k) d/dA`), the explicit inversion

  `γ y + γ(-y) = F_0'(y) = 2 y · (1/(n-2)!) · (d/dA)^{n-1} [ A^{n-3/2} (Tγ)(√(1-A)) ]|_{A=y²}`,

and for even `γ`: `γ y = y · (1/(n-2)!) · (d/dA)^{n-1}[A^{n-3/2}(Tγ)(√(1-A))]|_{A=y²}`.
Consequently `T` is injective on even profiles.  This is the `(n-1)`-fold differentiation of the
Abel-type transform; it is the tool the odd-dimensional construction consumes.
-/
