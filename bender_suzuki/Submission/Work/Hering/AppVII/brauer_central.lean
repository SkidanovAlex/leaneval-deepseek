import Mathlib
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The complex element `Eℂ χ` lifted to `ℂ[A]`

For a finite group `A` and a function `χ : A → ℂ` we put

`Eℂ χ = (irrDeg χ) • ∑ g : A, χ g⁻¹ • single g 1`   in `ℂ[A]`.

For an irreducible character `χ` this is `|A| • e_χ`, where
`e_χ = (χ 1 / |A|) ∑_g χ(g⁻¹) g` is the central primitive idempotent of the group algebra
`ℂ[A]` attached to `χ`.  The element `Eℂ χ` is the image of `tildeE χ` (the lift of
`|A| • e_χ` inside `ℤ[ζ_|A|][A]`) under `MonoidAlgebra.map (iota |A|)`, and it is used to
transfer the standard properties of the `e_χ` (centrality, `∑_χ e_χ = 1`, `e_χ e_ψ = δ_{χψ} e_χ`)
from `ℂ` to the coprime Brauer reduction `k[A]`, `k = F̄_r`.
-/

noncomputable section

open Classical

open scoped BigOperators MonoidAlgebra

namespace Work.Hering.AppVII

/-- For a function `χ : A → ℂ`, the element `irrDeg χ • ∑ g, χ g⁻¹ • single g 1` of the complex
group algebra `ℂ[A]`. -/
def Eℂ {A : Type*} [Group A] [Fintype A] (χ : A → ℂ) : MonoidAlgebra ℂ A :=
  (Work.CharCore.irrDeg χ : ℂ) • ∑ g : A, (χ g⁻¹ : ℂ) • MonoidAlgebra.single g (1 : ℂ)

end Work.Hering.AppVII
