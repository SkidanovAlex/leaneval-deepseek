import Mathlib

/-!
# Definitions for the continuous descent-direction construction

The domain `D k l = ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))` carries the
sup norm (`Prod.norm_mk`).  For a continuous linear functional `L : D k l →L[ℝ] ℝ` we write it in
coordinates as

* `cval L = L (1, 0, 0)`,
* `g1 L` = the Riesz vector of the restriction of `L` to the `k`-block,
* `g2 L` = the Riesz vector of the restriction of `L` to the `l`-block,

so that `L (a, (x, y)) = cval L * a + ⟪g1 L, x⟫ + ⟪g2 L, y⟫`.  The descent direction `uvec β L` is
obtained by (softly) normalising each block at scale `β`.
-/

namespace Work.RPCore.Saddle

open scoped RealInnerProductSpace

noncomputable section

/-- The domain of the saddle problem. -/
abbrev D (k l : ℕ) : Type :=
  ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))

/-- Inclusion of the first coordinate: `a ↦ (a, 0, 0)`. -/
def d0 (k l : ℕ) : ℝ →L[ℝ] D k l :=
  ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))

/-- Inclusion of the `k`-block: `x ↦ (0, (x, 0))`. -/
def d1 (k l : ℕ) : EuclideanSpace ℝ (Fin k) →L[ℝ] D k l :=
  (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))).comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin l)))

/-- Inclusion of the `l`-block: `y ↦ (0, (0, y))`. -/
def d2 (k l : ℕ) : EuclideanSpace ℝ (Fin l) →L[ℝ] D k l :=
  (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))).comp
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin l)))

/-- The `a`-component of a continuous linear functional. -/
def cval {k l : ℕ} (L : D k l →L[ℝ] ℝ) : ℝ := L (d0 k l 1)

/-- The Riesz vector of the restriction of `L` to the `k`-block. -/
def g1 {k l : ℕ} (L : D k l →L[ℝ] ℝ) : EuclideanSpace ℝ (Fin k) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (L.comp (d1 k l))

/-- The Riesz vector of the restriction of `L` to the `l`-block. -/
def g2 {k l : ℕ} (L : D k l →L[ℝ] ℝ) : EuclideanSpace ℝ (Fin l) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin l))).symm (L.comp (d2 k l))

/-- The soft normalisation of a real number at scale `β`. -/
def hnorm (β t : ℝ) : ℝ := t ^ 2 / max t β

/-- The descent vector built from a continuous linear functional, softly normalised at scale `β`. -/
def uvec {k l : ℕ} (β : ℝ) (L : D k l →L[ℝ] ℝ) : D k l :=
  (-(cval L) / max |cval L| β,
    (-(max ‖g1 L‖ β)⁻¹ • g1 L, -(max ‖g2 L‖ β)⁻¹ • g2 L))

end

end Work.RPCore.Saddle
