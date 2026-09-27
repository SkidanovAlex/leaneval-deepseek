import Mathlib

/-!
# Definitions for `Work.Drive.Whitney.glAuxCore`

Given smooth `u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m)` with `u` and `w` nowhere zero on the square
`K = [0,1]²`, we build a smooth family `U` of linear isomorphisms with `U p (u p) = w p` on `K` and
`U = 1` on the two edges `s = 0`, `s = 1`.

The construction uses a smooth cutoff `φ` (equal to `1` on `K`, supported inside an open set where
`u` and `w` are nonzero) to make all the auxiliary data globally smooth.  All the objects below are
*global* smooth functions of the point; the identities are proved only on the square.

With `Am = φ ‖u‖² + (1 - φ)` (positive everywhere), and writing `a`, `n`, `N`, `c` for
`⟪w,u⟫/Am`, `w - a u`, `⟪n,n⟫`, `N/Am`, the operator is

  `U = a • 1 + J + (C - a • 1) (1 - Pu)`,   `C = (1 - Pu) + z ⊗ χ`,

with `z = λ ψ`, `χ = (a + c) ψ - (⟪ψ,n⟫ / Am) n`, and `λ` chosen so that
`det U = (a + c) + λ Θ` with `Θ = (a + c) ⟪ψ,χ⟫ - (⟪ψ,n⟫ ⟪χ,n⟫)/Am` equals `1` on the square.
The key algebraic fact (to be proved where needed) is that `Θ = ‖χ‖² ≥ 0`.
-/

namespace Work.Drive.Whitney

open scoped Real ContDiff Topology
open Set

/-- The `C^∞` order as it appears in the target statement. -/
abbrev smw : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {m : ℕ}

/-- Modified squared norm of `u`, used to make everything globally smooth.  It agrees with `‖u‖²`
on the square when `φ = 1` there. -/
noncomputable def gAm (φ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (p : ℝ × ℝ) : ℝ := φ p * inner ℝ (u p) (u p) + (1 - φ p)

/-- The `u`-coefficient of `w`. -/
noncomputable def gAl (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (p : ℝ × ℝ) : ℝ := inner ℝ (w p) (u p) / gAm φ u p

/-- The component of `w` orthogonal to `u` (for the modified inner product data). -/
noncomputable def gNn (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin m) := w p - gAl φ u w p • u p

/-- Squared norm of `n`. -/
noncomputable def gN (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (p : ℝ × ℝ) : ℝ := inner ℝ (gNn φ u w p) (gNn φ u w p)

/-- The ratio `N / Am`. -/
noncomputable def gC (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (p : ℝ × ℝ) : ℝ := gN φ u w p / gAm φ u p

/-- The infinitesimal rotation in the `u`–`n` plane. -/
noncomputable def gJ (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) :
    ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) := fun p =>
  (gAm φ u p)⁻¹ •
    ((innerSL ℝ (u p)).smulRight (gNn φ u w p) - (innerSL ℝ (gNn φ u w p)).smulRight (u p))

/-- The (modified) orthogonal projection onto `ℝ u`. -/
noncomputable def gPu (φ : ℝ × ℝ → ℝ) (u : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) :
    ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) := fun p =>
  (gAm φ u p)⁻¹ • (innerSL ℝ (u p)).smulRight (u p)

/-- The field `χ = (a + c) ψ - (⟪ψ,n⟫ / Am) n`. -/
noncomputable def gChi (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin m) :=
  (gAl φ u w p + gC φ u w p) • ψ p
    - (inner ℝ (ψ p) (gNn φ u w p) / gAm φ u p) • gNn φ u w p

/-- `Θ = (a + c) ⟪ψ,χ⟫ - (⟪ψ,n⟫ ⟪χ,n⟫)/Am`. -/
noncomputable def gTheta (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (p : ℝ × ℝ) : ℝ :=
  (gAl φ u w p + gC φ u w p) * inner ℝ (ψ p) (gChi φ u w ψ p)
    - inner ℝ (ψ p) (gNn φ u w p) * inner ℝ (gChi φ u w ψ p) (gNn φ u w p) / gAm φ u p

/-- The scalar `λ`; `1 + Θ ≥ 1 > 0`, so this is a perfectly regular smooth function. -/
noncomputable def gLam (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (p : ℝ × ℝ) : ℝ :=
  (1 - (gAl φ u w p + gC φ u w p)) / (1 + gTheta φ u w ψ p)

/-- The vector field `z = λ ψ`. -/
noncomputable def gZ (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin m) :=
  gLam φ u w ψ p • ψ p

/-- The operator `C = (1 - Pu) + z ⊗ χ`. -/
noncomputable def gCfam (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) :
    ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) := fun p =>
  (1 - gPu φ u p) + (innerSL ℝ (gZ φ u w ψ p)).smulRight (gChi φ u w ψ p)

/-- The operator `U`. -/
noncomputable def gU (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) :
    ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) := fun p =>
  gAl φ u w p • 1 + gJ φ u w p
    + (gCfam φ u w ψ p - gAl φ u w p • 1) * (1 - gPu φ u p)

end Work.Drive.Whitney
