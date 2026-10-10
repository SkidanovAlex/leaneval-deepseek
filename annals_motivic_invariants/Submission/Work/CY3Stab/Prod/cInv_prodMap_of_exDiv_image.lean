import Mathlib
import Submission.Work.CY3Stab.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- **Counting transport along a residue-class-preserving injection of exceptional divisors.**

If `p : X → X'` is injective, carries `exDiv φ` onto `exDiv ψ`, and preserves the `𝕜`-birational
class of every point (`ResEquiv 𝕜 (p x) z ↔ ResEquiv 𝕜 x z`), then the `[κ(z)]`-coefficients
agree: `excCount 𝕜 z ψ = excCount 𝕜 z φ`.

The proof is pure counting: `excCount` is the cardinality of `{x ∈ exDiv φ | ResEquiv 𝕜 x z}`
(`Submission/Work/LLink/Count.lean`), the hypothesis rewrites the exceptional set as an image, and
`Set.ncard_image_of_injective` (unconditional in Mathlib, both sides being `0` on infinite sets)
removes the injection. -/
theorem excCount_eq_of_exDiv_image (𝕜 : Type) [Field 𝕜] {X X' Y Y' Z : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace X'] [IrreducibleSpace Y] [IrreducibleSpace Y']
    [X.Over (Spec (.of 𝕜))] [X'.Over (Spec (.of 𝕜))]
    [Y.Over (Spec (.of 𝕜))] [Y'.Over (Spec (.of 𝕜))] [Z.Over (Spec (.of 𝕜))]
    (z : Z) (φ : X.BirationalMap Y) (ψ : X'.BirationalMap Y') (p : X → X')
    (hp : Function.Injective p) (h : exDiv ψ = p '' exDiv φ)
    (hr : ∀ x : X, ResEquiv 𝕜 (p x) z ↔ ResEquiv 𝕜 x z) :
    excCount 𝕜 z ψ = excCount 𝕜 z φ := by
  have hset : {w : X' | w ∈ exDiv ψ ∧ ResEquiv 𝕜 w z}
      = p '' {x : X | x ∈ exDiv φ ∧ ResEquiv 𝕜 x z} := by
    ext w
    constructor
    · rintro ⟨hw, hres⟩
      rw [h] at hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact ⟨x, ⟨hx, (hr x).mp hres⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hres⟩, rfl⟩
      exact ⟨by rw [h]; exact ⟨x, hx, rfl⟩, (hr x).mpr hres⟩
  unfold excCount
  rw [hset, Set.ncard_image_of_injective _ hp]

theorem cInv_prodMap_of_exDiv_image (𝕜 : Type) [Field 𝕜] (k : ℕ)
    {X Y S : AlgebraicGeometry.Scheme.{0}} [MotivicInvariants.Variety 𝕜 X]
    [MotivicInvariants.Variety 𝕜 Y] (φ : X.BirationalMap Y)
    [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)]
    (p : X → Work.CY3Stab.WProd (𝕜 := 𝕜) X k) (q : Y → Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)
    (h : exDiv (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) = p '' exDiv φ)
    (h' : exDiv ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm) = q '' exDiv φ.symm)
    (hp : Function.Injective p) (hq : Function.Injective q)
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (z : S)
    (hr : ∀ x : X, ResEquiv 𝕜 (p x) z ↔ ResEquiv 𝕜 x z)
    (hr' : ∀ y : Y, ResEquiv 𝕜 (q y) z ↔ ResEquiv 𝕜 y z) :
    cInv 𝕜 z (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) = cInv 𝕜 z φ := by
  classical
  have h1 : excCount 𝕜 z (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) = excCount 𝕜 z φ :=
    excCount_eq_of_exDiv_image 𝕜 z φ
      (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) p hp h hr
  have h2 : excCount 𝕜 z ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm)
      = excCount 𝕜 z φ.symm :=
    excCount_eq_of_exDiv_image 𝕜 z φ.symm
      ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm) q hq h' hr'
  unfold cInv
  rw [h2, h1]

end Work.CY3Stab.Prod
