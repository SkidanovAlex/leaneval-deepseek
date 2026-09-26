import Mathlib

/-!
# The Gauss map of a plane immersion and the parametrisation of critical heights

For an immersion `Φ : ℝ × ℝ → ℝ³` and a direction `v : ℝ³`, the height function
`h_v = q ↦ ⟪v, Φ q⟫` has a critical point at `p` exactly when `v` is orthogonal to the tangent
plane at `p`, i.e. when `v` is a multiple of the normal vector
`normal Φ p = ∂₁Φ(p) ⨯ ∂₂Φ(p)`.  This file fixes the vocabulary used by the proof that almost every
`v` gives a Morse height:

* `crossE` — the cross product on `EuclideanSpace ℝ (Fin 3)` (transported from `crossProduct`);
* `d1`, `d2` — the two partial derivatives of `Φ`;
* `normal` — the Gauss map `p ↦ d1 Φ p ⨯₃ d2 Φ p`;
* `D2` — the second derivative of `Φ`;
* `toE3` — the coordinates `(p, t) ↦ (p.1, p.2, t)` of `ℝ² × ℝ` as a point of `ℝ³`;
* `gaussParam` — the parametrisation `(p, t) ↦ t • normal Φ p` of the set of pairs (direction,
  critical point), read as a self-map of `ℝ³`;
* `badSet` — the set of directions `v` for which `h_v` has a degenerate critical point;
* `critSet` — the set of parameters `z` where the differential of `gaussParam` is singular.
-/

namespace Work.Drive.Generic

open scoped Matrix RealInnerProductSpace
open MeasureTheory

/-- Euclidean `3`-space, written as `WithLp 2 (Fin 3 → ℝ)`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The cross product of two vectors of `ℝ³`, on `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def crossE (u v : E3) : E3 :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))

@[simp] lemma ofLp_crossE (u v : E3) :
    WithLp.ofLp (crossE u v) = crossProduct (WithLp.ofLp u) (WithLp.ofLp v) :=
  WithLp.ofLp_toLp _ _

lemma inner_eq_dotProduct (u v : E3) : ⟪u, v⟫ = WithLp.ofLp u ⬝ᵥ WithLp.ofLp v := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

@[simp] lemma inner_crossE_left (u v : E3) : ⟪u, crossE u v⟫ = 0 := by
  rw [inner_eq_dotProduct, ofLp_crossE]; simp

@[simp] lemma inner_crossE_right (u v : E3) : ⟪v, crossE u v⟫ = 0 := by
  rw [inner_eq_dotProduct, ofLp_crossE]; simp

/-- The scalar triple-product expansion of the vector triple product. -/
lemma crossE_crossE (u v w : E3) : crossE u (crossE v w) = ⟪u, w⟫ • v - ⟪v, u⟫ • w := by
  apply WithLp.ofLp_injective
  simp only [ofLp_crossE, WithLp.ofLp_sub, WithLp.ofLp_smul]
  rw [cross_cross_eq_smul_sub_smul', inner_eq_dotProduct, inner_eq_dotProduct]

/-- `crossE u v` vanishes exactly when `u` and `v` are linearly dependent. -/
lemma crossE_ne_zero_iff {u v : E3} :
    crossE u v ≠ 0 ↔ ∀ c d : ℝ, c • u + d • v = 0 → c = 0 ∧ d = 0 := by
  have key : crossProduct (WithLp.ofLp u) (WithLp.ofLp v) ≠ 0 ↔
      ∀ c d : ℝ, c • WithLp.ofLp u + d • WithLp.ofLp v = 0 → c = 0 ∧ d = 0 := by
    rw [crossProduct_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff]
  have h1 : crossE u v ≠ 0 ↔ crossProduct (WithLp.ofLp u) (WithLp.ofLp v) ≠ 0 := by
    rw [ne_eq, ne_eq]
    exact not_congr (WithLp.toLp_eq_zero (p := 2))
  rw [h1, key]
  constructor
  · intro h c d hcd
    exact h c d (by have := congrArg WithLp.ofLp hcd; simpa using this)
  · intro h c d hcd
    refine h c d ?_
    apply WithLp.ofLp_injective
    simpa using hcd

/-- If `crossE u v = 0` and `v ≠ 0` then `u` is a multiple of `v`. -/
lemma exists_smul_of_crossE_eq_zero {u v : E3} (h : crossE u v = 0) (hv : v ≠ 0) :
    ∃ c : ℝ, u = c • v := by
  have h' : ¬ (∀ c d : ℝ, c • u + d • v = 0 → c = 0 ∧ d = 0) := by
    rw [← crossE_ne_zero_iff]
    simp [h]
  push Not at h'
  obtain ⟨c, d, hcd, hne⟩ := h'
  by_cases hc : c = 0
  · exfalso
    simp only [hc, zero_smul, zero_add] at hcd
    exact hne hc ((smul_eq_zero.mp hcd).resolve_right hv)
  · refine ⟨-(c⁻¹ * d), ?_⟩
    have h1 : c • u = -(d • v) := eq_neg_of_add_eq_zero_left hcd
    calc u = c⁻¹ • (c • u) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • (-(d • v)) := by rw [h1]
      _ = -(c⁻¹ * d) • v := by rw [smul_neg, smul_smul, neg_smul]

/-! ### The partial derivatives and the Gauss map -/

/-- The first partial derivative of `Φ`. -/
noncomputable def d1 (Φ : ℝ × ℝ → E3) (p : ℝ × ℝ) : E3 := fderiv ℝ Φ p (1, 0)

/-- The second partial derivative of `Φ`. -/
noncomputable def d2 (Φ : ℝ × ℝ → E3) (p : ℝ × ℝ) : E3 := fderiv ℝ Φ p (0, 1)

/-- The Gauss map `p ↦ ∂₁Φ(p) ⨯ ∂₂Φ(p)`. -/
noncomputable def normal (Φ : ℝ × ℝ → E3) (p : ℝ × ℝ) : E3 := crossE (d1 Φ p) (d2 Φ p)

/-- The second derivative of `Φ` at `p`, as a bilinear map. -/
noncomputable def D2 (Φ : ℝ × ℝ → E3) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E3 :=
  fderiv ℝ (fun q => fderiv ℝ Φ q) p

/-- `(p, t) ↦ (p.1, p.2, t)` as a point of `ℝ³`. -/
noncomputable def toE3 (p : ℝ × ℝ) (t : ℝ) : E3 := WithLp.toLp 2 ![p.1, p.2, t]

@[simp] lemma toE3_apply_zero (p : ℝ × ℝ) (t : ℝ) : toE3 p t 0 = p.1 := rfl
@[simp] lemma toE3_apply_one (p : ℝ × ℝ) (t : ℝ) : toE3 p t 1 = p.2 := rfl
@[simp] lemma toE3_apply_two (p : ℝ × ℝ) (t : ℝ) : toE3 p t 2 = t := rfl

/-- The parametrisation `z ↦ z 2 • N(z 0, z 1)` of the critical directions of the height functions,
as a self-map of `ℝ³`. -/
noncomputable def gaussParam (Φ : ℝ × ℝ → E3) (z : E3) : E3 :=
  (z 2) • normal Φ (z 0, z 1)

@[simp] lemma gaussParam_toE3 (Φ : ℝ × ℝ → E3) (p : ℝ × ℝ) (t : ℝ) :
    gaussParam Φ (toE3 p t) = t • normal Φ p := rfl

/-- The set of parameters at which the differential of the Gauss parametrisation is singular. -/
def critSet (Φ : ℝ × ℝ → E3) : Set E3 := {z | (fderiv ℝ (gaussParam Φ) z).det = 0}

/-- The directions `v` for which the height `q ↦ ⟪v, Φ q⟫` has a degenerate critical point,
i.e. the negated conclusion of `ae_height_morse`. -/
def badSet (Φ : ℝ × ℝ → E3) : Set E3 :=
  {v | ¬ (∀ p : ℝ × ℝ,
    fderiv ℝ (fun q => ⟪v, Φ q⟫) p = 0 →
      ∀ w : ℝ × ℝ,
        (∀ w' : ℝ × ℝ, fderiv ℝ (fderiv ℝ (fun q => ⟪v, Φ q⟫)) p w w' = 0) → w = 0)}

end Work.Drive.Generic
