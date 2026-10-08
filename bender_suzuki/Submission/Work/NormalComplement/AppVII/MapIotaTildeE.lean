import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.brauer_central
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `MonoidAlgebra.map (iota |A|) (tildeE χ) = Eℂ χ`

`tildeE χ = (irrDeg χ) • ∑_g (charLift χ g⁻¹) • single g 1` lives in `ℤ[ζ_|A|][A]`, where
`charLift χ g` is an integral lift of the algebraic integer `χ g`.  Applying the coefficient
map `MonoidAlgebra.map (iota |A|)` induced by the ring homomorphism `iota |A| : ℤ[ζ_|A|] → ℂ`
therefore sends it to `(irrDeg χ) • ∑_g (χ g⁻¹) • single g 1 = Eℂ χ`, using
`iota (charLift χ g) = χ g`.

The proof pushes `MonoidAlgebra.map` through the outer scalar (`map_smul_ringHom`), the finite
sum (`MonoidAlgebra.map_sum`), and the inner scalar-times-`single` (`map_smul_single`), the last
step using `map_one` and `iota_charLift`.
-/

noncomputable section

open Classical

open scoped BigOperators MonoidAlgebra

namespace Work.NormalComplement.AppVII

/-- `MonoidAlgebra.map` of a ring homomorphism commutes with scalar multiplication of the base
ring: `map f (c • x) = f c • map f x`. -/
lemma map_smul_ringHom {R S : Type*} [CommSemiring R] [CommSemiring S] {M : Type*} [Monoid M]
    (f : R →+* S) (c : R) (x : R[M]) :
    MonoidAlgebra.map (f : R →+ S) (c • x) = f c • MonoidAlgebra.map (f : R →+ S) x := by
  rw [Algebra.smul_def (R := R) (A := R[M]) c x, Algebra.smul_def (R := S) (A := S[M]) (f c)]
  rw [MonoidAlgebra.map_mul f]
  congr 1
  rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, MonoidAlgebra.map_single]
  simp

/-- `MonoidAlgebra.map` of a ring homomorphism on a scalar multiple of a basis element. -/
lemma map_smul_single {R S : Type*} [CommSemiring R] [CommSemiring S] {M : Type*} [Monoid M]
    (f : R →+* S) (c : R) (m : M) :
    MonoidAlgebra.map (f : R →+ S) (c • MonoidAlgebra.single m 1) =
      f c • MonoidAlgebra.single m 1 := by
  rw [map_smul_ringHom, MonoidAlgebra.map_single]
  congr 1
  congr 1
  exact map_one f

theorem MapIotaTildeE {A : Type*} [Group A] [Fintype A] (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) :
    MonoidAlgebra.map (Work.Hering.AppVII.iota (Nat.card A)) (Work.Hering.AppVII.tildeE χ hχ) =
      Work.Hering.AppVII.Eℂ χ := by
  rw [Work.Hering.AppVII.tildeE, Work.Hering.AppVII.Eℂ]
  rw [map_smul_ringHom]
  rw [MonoidAlgebra.map_sum]
  rw [show (Work.Hering.AppVII.iota (Nat.card A))
        ((Work.CharCore.irrDeg χ : Work.Hering.AppVII.CycloRing (Nat.card A))) =
      (Work.CharCore.irrDeg χ : ℂ) from map_natCast _ _]
  congr 1
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [map_smul_single, Work.Hering.AppVII.iota_charLift]

end Work.NormalComplement.AppVII
