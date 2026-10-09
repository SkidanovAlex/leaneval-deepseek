/-
The coefficient-level transfer (corestriction) cochains of a finite-index subgroup `S ≤ Γ` of a
group `Γ`, for coefficients in an arbitrary `Rep k Γ`.

For a `1`-cochain `b : S → A` the transfer is

`cor1 b σ = ∑_{c ∈ S\Γ} ρ(x_c)⁻¹ (b (x_c σ x_{cσ}⁻¹))`,

and for a `2`-cochain `v : S → S → A`

`cor2 v σ τ = ∑_{c ∈ S\Γ} ρ(x_c)⁻¹ (v (x_c σ x_{cσ}⁻¹) (x_{cσ} τ x_{c,στ}⁻¹))`,

where `x_c` is the chosen representative of the left coset `c` (`NK.GCTransfer.sRep`).

The two auxiliary cochains `Xi` and `Pb` on `Γ` are the ones occurring in the correction term of
the classical identity "the transfer of the restriction of a `2`-cocycle is `[Γ : S]` times the
cocycle, up to a coboundary".
-/
import Submission.NK.GCTransfer.Coset
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation Rep

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

namespace NK.GCTransfer

variable {Γ : Type u} [Group Γ] [Fintype Γ] (S : Subgroup Γ)
variable {k : Type u} [CommRing k] (A : Rep.{u,u,u} k Γ)

/-- **The transfer of a `1`-cochain** `b : S → A` to a `1`-cochain on `Γ`. -/
noncomputable def cor1 (b : S → A) (σ : Γ) : A :=
  ∑ c : Quotient (QuotientGroup.rightRel S),
    A.ρ ((Quotient.out c)⁻¹) (b (sXS S (Quotient.out c) σ))

/-- **The transfer of a `2`-cochain** `v : S → S → A` to a `2`-cochain on `Γ`. -/
noncomputable def cor2 (v : S → S → A) (σ τ : Γ) : A :=
  ∑ c : Quotient (QuotientGroup.rightRel S),
    A.ρ ((Quotient.out c)⁻¹)
      (v (sXS S (Quotient.out c) σ) (sXS S (sRep S (Quotient.out c * σ)) τ))

/-- The auxiliary cochain `Ξ` of the transfer computation. -/
noncomputable def Xi (z : Γ × Γ → A) (γ : Γ) : A :=
  ∑ c : Quotient (QuotientGroup.rightRel S),
    A.ρ ((Quotient.out c)⁻¹) (z (sX S (Quotient.out c) γ, sRep S (Quotient.out c * γ)))

/-- The auxiliary cochain `P` of the transfer computation. -/
noncomputable def Pb (z : Γ × Γ → A) (γ : Γ) : A :=
  ∑ c : Quotient (QuotientGroup.rightRel S), A.ρ ((Quotient.out c)⁻¹) (z (Quotient.out c, γ))

end NK.GCTransfer
