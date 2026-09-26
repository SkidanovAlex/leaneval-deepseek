import Mathlib
import Submission.Work.Drive.Generic.HeightDefs

/-!
# The derivative of the Gauss normal, tested against the second derivative

For an immersion `Φ : ℝ × ℝ → ℝ³` the Gauss map is `normal Φ p = ∂₁Φ(p) ⨯ ∂₂Φ(p)`.  Its derivative
at `p` in the direction `x` is, by the product rule for the cross product,

`D(normal Φ)(p) x = ∂₁Φ(p) ⨯ D²Φ(p)(x, ∂₂) + D²Φ(p)(x, ∂₁) ⨯ ∂₂Φ(p)`,

where `D²Φ(p)(x, ∂ᵢ)` is the second derivative of `Φ` at `p` applied to `x` and to the `i`-th
coordinate direction.  This file computes `fderiv ℝ (normal Φ) p x` explicitly
(`fderiv_normal_apply`) and deduces the two orthogonality relations that drive the proof that
almost every direction gives a Morse height function:

* `⟪D(normal Φ)(p) x, ∂₂Φ(p)⟫ = -⟪normal Φ p, D²Φ(p)(x, ∂₂)⟫` (this file),
* `⟪D(normal Φ)(p) x, ∂₁Φ(p)⟫ = -⟪normal Φ p, D²Φ(p)(x, ∂₁)⟫` (the companion file
  `inner_fderiv_normal_d1`).

Both sides only involve the second derivative of `Φ` through its value on one coordinate
direction: the Gauss map is orthogonal to the tangent plane, so the component of its derivative
that is tangent to `Φ` measures exactly the failure of `Φ` to be "second order flat" at `p`.

## Implementation notes

The cross product on `EuclideanSpace ℝ (Fin 3)` is only given in Mathlib on the model space
`Fin 3 → ℝ` (`crossProduct`), so `crossE` is its transport to `E3`.  In order to differentiate it
we bundle it as a continuous bilinear map `crossEC : E3 →L[ℝ] E3 →L[ℝ] E3`; this is built from
`LinearMap.mk₂` and `LinearMap.toContinuousLinearMap`, which uses finite-dimensionality of `E3`
rather than an explicit norm estimate.
-/

namespace Work.Drive.Generic

open scoped Matrix RealInnerProductSpace
open MeasureTheory

/-! ### Elementary identities for the cross product on `E3` -/

/-- The scalar triple product changes sign when its last two entries are exchanged. -/
lemma dot_cross_swap (x y z : Fin 3 → ℝ) :
    (x ⨯₃ y) ⬝ᵥ z = -((x ⨯₃ z) ⬝ᵥ y) := by
  have h1 : (x ⨯₃ y) ⬝ᵥ z = x ⬝ᵥ (y ⨯₃ z) := by
    rw [dotProduct_comm, triple_product_permutation]
  have h2 : (x ⨯₃ z) ⬝ᵥ y = -(x ⬝ᵥ (y ⨯₃ z)) := by
    rw [dotProduct_comm, triple_product_permutation, ← cross_anticomm y z, dotProduct_neg]
  rw [h1, h2, neg_neg]

/-- The scalar triple product of `a`, `b`, `c` changes sign when `b` and `c` are exchanged. -/
lemma inner_crossE_swap (a b c : E3) : ⟪crossE a b, c⟫ = -⟪crossE a c, b⟫ := by
  rw [inner_eq_dotProduct, inner_eq_dotProduct]
  simp only [ofLp_crossE]
  exact dot_cross_swap _ _ _

/-- The cross product is orthogonal to its second argument. -/
lemma inner_crossE_self (u v : E3) : ⟪crossE u v, v⟫ = 0 := by
  rw [real_inner_comm, inner_crossE_right]

/-! ### The cross product as a continuous bilinear map -/

/-- The cross product of `E3`, as a bilinear map. -/
noncomputable def crossLM : E3 →ₗ[ℝ] E3 →ₗ[ℝ] E3 :=
  LinearMap.mk₂ ℝ (fun u v => crossE u v)
    (fun u₁ u₂ v => by apply WithLp.ofLp_injective; simp [ofLp_crossE])
    (fun c u v => by apply WithLp.ofLp_injective; simp [ofLp_crossE])
    (fun u v₁ v₂ => by apply WithLp.ofLp_injective; simp [ofLp_crossE])
    (fun c u v => by apply WithLp.ofLp_injective; simp [ofLp_crossE])

/-- The cross product of `E3`, as a continuous bilinear map. -/
noncomputable def crossEC : E3 →L[ℝ] E3 →L[ℝ] E3 :=
  LinearMap.toContinuousLinearMap
    (LinearMap.comp (LinearMap.toContinuousLinearMap (E := E3) (F' := E3)).toLinearMap crossLM)

@[simp] lemma crossEC_apply (u v : E3) : crossEC u v = crossE u v := by
  simp [crossEC, crossLM, LinearMap.mk₂_apply]

/-! ### The derivatives of `d1`, `d2` and `normal` -/

/-- The first partial derivative `d1 Φ`, as a function of its base point, has derivative
`D²Φ(p)(·, ∂₁)` at `p`. -/
lemma hasFDerivAt_d1 {Φ : ℝ × ℝ → E3} (hΦ : ContDiff ℝ 3 Φ) (p : ℝ × ℝ) :
    HasFDerivAt (fun q => d1 Φ q) (D2 Φ p |>.flip (1, 0)) p := by
  have hfd : HasFDerivAt (fun q => fderiv ℝ Φ q) (D2 Φ p) p :=
    ((hΦ.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)).differentiableAt
      |>.hasFDerivAt
  have h := hfd.clm_apply (hasFDerivAt_const (1, 0) p)
  simpa [d1] using h

/-- The second partial derivative `d2 Φ`, as a function of its base point, has derivative
`D²Φ(p)(·, ∂₂)` at `p`. -/
lemma hasFDerivAt_d2 {Φ : ℝ × ℝ → E3} (hΦ : ContDiff ℝ 3 Φ) (p : ℝ × ℝ) :
    HasFDerivAt (fun q => d2 Φ q) (D2 Φ p |>.flip (0, 1)) p := by
  have hfd : HasFDerivAt (fun q => fderiv ℝ Φ q) (D2 Φ p) p :=
    ((hΦ.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)).differentiableAt
      |>.hasFDerivAt
  have h := hfd.clm_apply (hasFDerivAt_const (0, 1) p)
  simpa [d2] using h

/-- The product rule for the Gauss map. -/
lemma hasFDerivAt_normal {Φ : ℝ × ℝ → E3} (hΦ : ContDiff ℝ 3 Φ) (p : ℝ × ℝ) :
    HasFDerivAt (normal Φ)
      (crossEC.precompR (ℝ × ℝ) (d1 Φ p) (D2 Φ p |>.flip (0, 1)) +
        (crossEC.precompL (ℝ × ℝ) (D2 Φ p |>.flip (1, 0))) (d2 Φ p)) p :=
  ContinuousLinearMap.hasFDerivAt_of_bilinear crossEC (hasFDerivAt_d1 hΦ p) (hasFDerivAt_d2 hΦ p)

/-- Explicit formula for the derivative of the Gauss map: the derivative of
`p ↦ ∂₁Φ(p) ⨯ ∂₂Φ(p)` is `∂₁Φ(p) ⨯ D²Φ(p)(x, ∂₂) + D²Φ(p)(x, ∂₁) ⨯ ∂₂Φ(p)`. -/
lemma fderiv_normal_apply {Φ : ℝ × ℝ → E3} (hΦ : ContDiff ℝ 3 Φ) (p x : ℝ × ℝ) :
    fderiv ℝ (normal Φ) p x =
      crossE (d1 Φ p) (D2 Φ p x (0, 1)) + crossE (D2 Φ p x (1, 0)) (d2 Φ p) := by
  rw [(hasFDerivAt_normal hΦ p).fderiv]
  simp [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]

/-! ### The target identity -/

theorem inner_fderiv_normal_d2 {Φ : ℝ × ℝ → Work.Drive.Generic.E3} (hΦ : ContDiff ℝ 3 Φ)
    (p x : ℝ × ℝ) :
    inner ℝ (fderiv ℝ (Work.Drive.Generic.normal Φ) p x) (Work.Drive.Generic.d2 Φ p) =
      - inner ℝ (Work.Drive.Generic.normal Φ p) (Work.Drive.Generic.D2 Φ p x (0, 1)) := by
  rw [fderiv_normal_apply hΦ p x, inner_add_left]
  have h1 : inner ℝ (crossE (d1 Φ p) (D2 Φ p x (0, 1))) (d2 Φ p)
      = - inner ℝ (crossE (d1 Φ p) (d2 Φ p)) (D2 Φ p x (0, 1)) :=
    inner_crossE_swap (d1 Φ p) (D2 Φ p x (0, 1)) (d2 Φ p)
  have h2 : inner ℝ (crossE (D2 Φ p x (1, 0)) (d2 Φ p)) (d2 Φ p) = 0 :=
    inner_crossE_self (D2 Φ p x (1, 0)) (d2 Φ p)
  rw [h1, h2, add_zero]
  rfl

end Work.Drive.Generic
