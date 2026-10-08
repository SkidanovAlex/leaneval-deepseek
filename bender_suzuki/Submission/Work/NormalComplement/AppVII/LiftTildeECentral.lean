import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.iota_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `tildeE χ` is central in `ℤ[ζ_|A|][A]`

Let `A` be a finite group, `n = |A|`, `R = ℤ[ζ_n] = ℤ[X]/(Φ_n)` and
`χ ∈ Work.CharCore.Irr A` an irreducible complex character.  In
`Submission/Work/Hering/AppVII/brauer_lift_aux.lean` the element

`tildeE χ = (χ(1) : R) • ∑ g : A, charLift χ g⁻¹ • single g 1`

of `R[A]` is defined; it is `|A|` times the central primitive idempotent `e_χ` of `ℂ[A]`
attached to `χ`, lifted to `R[A]` along `iota : R → ℂ`, and it is the input of the coprime
Brauer lifting of `e_χ`.

The main result here, `LiftTildeECentral`, is that `tildeE χ` is central:

`x * tildeE χ = tildeE χ * x`   for all `x : R[A]`.

It is stated in area `Work.NormalComplement.AppVII` (it is the `R[A]`-centrality input for the
extraspecial case of the `AppVII` argument) and proved from scratch, without using the (still
unproved) `Work.Hering.AppVII.tildeE_central`.

The proof is the standard one:

* a finite sum `∑ g, c g • single g 1` with `c` a class function is central, because it commutes
  with every `single h r` (compare coefficients of `single h r * _` and `_ * single h r` using
  `MonoidAlgebra.coeff_single_mul_apply` / `coeff_mul_single_apply`, where the two arguments of
  `c` that appear are `h⁻¹ * k` and `k * h⁻¹ = h * (h⁻¹ * k) * h⁻¹`), and every element of `R[A]`
  is a sum of such `single`s (`MonoidAlgebra.sum_coeff_single` with `Finsupp.sum_mul` /
  `Finsupp.mul_sum`);
* `g ↦ charLift χ hχ g⁻¹` is a class function because `iota` is injective (`iota_injective`) and
  `χ` is a class function (`Work.CharCore.isClassFun_of_mem_Irr`).
-/

noncomputable section

open Classical

open scoped BigOperators

namespace Work.NormalComplement.AppVII

variable {R G : Type*}

/-- The coefficients of the finite sum `∑ g, c g • single g 1` in `R[G]` are the values of `c`. -/
theorem coeff_sum_smul_single [CommSemiring R] [Fintype G] (c : G → R) (k : G) :
    (∑ g : G, c g • MonoidAlgebra.single g (1 : R)).coeff k = c k := by
  classical
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

/-- If `c` is a class function on `G` then `∑ g, c g • single g 1` is central in `R[G]`. -/
theorem classFun_sum_single_central [CommSemiring R] [Group G] [Fintype G]
    (c : G → R) (hc : ∀ g h : G, c (h * g * h⁻¹) = c g) (x : MonoidAlgebra R G) :
    x * (∑ g : G, c g • MonoidAlgebra.single g (1 : R)) =
      (∑ g : G, c g • MonoidAlgebra.single g (1 : R)) * x := by
  classical
  have hcoeff : ∀ k : G, (∑ g : G, c g • MonoidAlgebra.single g (1 : R)).coeff k = c k :=
    coeff_sum_smul_single c
  -- it suffices to commute with every `single h r`
  have key : ∀ (h : G) (r : R),
      MonoidAlgebra.single h r * (∑ g : G, c g • MonoidAlgebra.single g (1 : R)) =
        (∑ g : G, c g • MonoidAlgebra.single g (1 : R)) * MonoidAlgebra.single h r := by
    intro h r
    ext k
    rw [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
      hcoeff (h⁻¹ * k), hcoeff (k * h⁻¹), mul_comm r]
    congr 1
    have h2 := hc (h⁻¹ * k) h
    rw [← h2]
    congr 1
    group
  -- every element of `R[G]` is a sum of `single`s
  rw [show x = x.coeff.sum MonoidAlgebra.single from (MonoidAlgebra.sum_coeff_single x).symm,
    Finsupp.sum_mul, Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro g _
  exact key g (x.coeff g)

/-- `charLift χ hχ : A → ℤ[ζ_|A|]` is a class function: it lifts the class function `χ`. -/
theorem charLift_conj {A : Type*} [Group A] [Fintype A]
    (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (g h : A) :
    Work.Hering.AppVII.charLift χ hχ (h * g * h⁻¹) = Work.Hering.AppVII.charLift χ hχ g := by
  apply Work.Hering.AppVII.iota_injective
  rw [Work.Hering.AppVII.iota_charLift, Work.Hering.AppVII.iota_charLift]
  exact Work.CharCore.isClassFun_of_mem_Irr hχ g h

/-- **`tildeE χ` is central in `ℤ[ζ_|A|][A]`** (the `ℤ[ζ_|A|][A]`-lift of the centrality of the
central idempotent `e_χ` of `ℂ[A]`). -/
theorem LiftTildeECentral {A : Type*} [Group A] [Fintype A] (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A)
    (x : MonoidAlgebra (Work.Hering.AppVII.CycloRing (Nat.card A)) A) :
    x * Work.Hering.AppVII.tildeE χ hχ = Work.Hering.AppVII.tildeE χ hχ * x := by
  classical
  -- `g ↦ charLift χ g⁻¹` is a class function
  have hc : ∀ g h : A, (fun g => Work.Hering.AppVII.charLift χ hχ g⁻¹) (h * g * h⁻¹)
      = (fun g => Work.Hering.AppVII.charLift χ hχ g⁻¹) g := by
    intro g h
    show Work.Hering.AppVII.charLift χ hχ (h * g * h⁻¹)⁻¹
      = Work.Hering.AppVII.charLift χ hχ g⁻¹
    have h1 : (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ := by group
    rw [h1]
    exact charLift_conj χ hχ g⁻¹ h
  have hcentral := classFun_sum_single_central
    (R := Work.Hering.AppVII.CycloRing (Nat.card A))
    (fun g => Work.Hering.AppVII.charLift χ hχ g⁻¹) hc x
  -- `tildeE χ` is a scalar multiple of that sum, and central elements are closed under scalars
  show x * ((Work.CharCore.irrDeg χ : Work.Hering.AppVII.CycloRing (Nat.card A)) •
      (∑ g : A, Work.Hering.AppVII.charLift χ hχ g⁻¹ •
        MonoidAlgebra.single g (1 : Work.Hering.AppVII.CycloRing (Nat.card A))))
    = ((Work.CharCore.irrDeg χ : Work.Hering.AppVII.CycloRing (Nat.card A)) •
      (∑ g : A, Work.Hering.AppVII.charLift χ hχ g⁻¹ •
        MonoidAlgebra.single g (1 : Work.Hering.AppVII.CycloRing (Nat.card A)))) * x
  rw [mul_smul_comm, smul_mul_assoc, hcentral]

end Work.NormalComplement.AppVII
