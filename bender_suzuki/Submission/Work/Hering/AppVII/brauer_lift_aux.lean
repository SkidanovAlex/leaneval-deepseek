import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.Hering.AppVII.brauer_setup
import Submission.Work.Hering.AppVII.iota_injective
import Submission.Work.Hering.AppVII.exists_charLift

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Coprime Brauer lifting: reduction of the central idempotents of `ℂ[G]`

Let `A` be a finite group, `r` a prime with `r ∤ |A|`, `n = |A|`, `k = F̄_r`, and
`R = ℤ[ζ_n] = ℤ[X]/(Φ_n)` with its two ring homomorphisms `iota : R → ℂ` (sending `ζ` to
`exp(2πi/n)`) and `jred : R → k`.

`tildeE χ : R[A]` is `|A| • e_χ` where `e_χ = (χ(1)/|A|) ∑_g χ(g⁻¹) g` is the central
primitive idempotent of `ℂ[A]` attached to `χ`; `toK χ : k[A]` is the reduction of `e_χ`.
-/

noncomputable section

open Classical

open scoped BigOperators

namespace Work.Hering.AppVII

variable {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]

theorem not_dvd_card (hcop : Nat.Coprime r (Nat.card A)) : ¬ r ∣ Nat.card A := by
  intro hd
  have h1 : r ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (dvd_refl r) hd
  exact (Fact.out : r.Prime).ne_one (Nat.dvd_one.mp h1)

/-- The element of `ℤ[ζ_|A|]` lifting `χ g`. -/
def charLift (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (g : A) :
    CycloRing (Nat.card A) :=
  Classical.choose (exists_charLift χ hχ g)

theorem iota_charLift (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (g : A) :
    iota (Nat.card A) (charLift χ hχ g) = χ g :=
  Classical.choose_spec (exists_charLift χ hχ g)

/-- `|A| • e_χ`, the `|A|`-multiple of the central idempotent of `ℂ[A]` attached to `χ`,
realised inside `ℤ[ζ_|A|][A]`. -/
def tildeE (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) :
    MonoidAlgebra (CycloRing (Nat.card A)) A :=
  (Work.CharCore.irrDeg χ : CycloRing (Nat.card A)) •
    ∑ g : A, charLift χ hχ g⁻¹ • MonoidAlgebra.single g (1 : CycloRing (Nat.card A))

/-- The reduction of `e_χ` to `k[A]`, for each `χ ∈ Irr A`. -/
def toK (hcop : Nat.Coprime r (Nat.card A)) (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) :
    MonoidAlgebra (BrauerField r) A :=
  (Nat.card A : BrauerField r)⁻¹ •
    MonoidAlgebra.map (jred r (Nat.card A) (not_dvd_card hcop)) (tildeE χ hχ)

end Work.Hering.AppVII
