import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.brauer_central
import Submission.Work.Hering.AppVII.iota_injective
import Submission.Work.Hering.AppVII.exists_charLift
import Submission.Work.CharCore.Main
import Submission.Work.Clifford.CharPair
import Submission.Work.NormalComplement.AppVII.LiftTildeECentral

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Auxiliary definitions for `TildeEProps`

Let `A` be a finite group, `n = |A|`, `R = ℤ[ζ_n] = ℤ[X]/(Φ_n)` and `iota : R → ℂ` the
canonical map sending the root of `Φ_n` to `exp (2 π i / n)`.

* `iotaAlgHom` is `iota` packaged as a `ℤ`-algebra homomorphism, and `iotaAlg` is the
  coefficientwise extension `R[A] → ℂ[A]` of `iota` (an `AlgHom` via
  `MonoidAlgebra.mapAlgHom`).  Since `iota` is injective, so is `iotaAlg`
  (`iotaAlg_injective`), which is how the identities of `TildeEProps` are transferred from
  `ℂ[A]` to `R[A]`.
* `zℂ χ = ∑ g, χ g⁻¹ • single g 1` is the class sum attached to `χ` in `ℂ[A]`, and
  `Eℂ χ = irrDeg χ • zℂ χ = Work.Hering.AppVII.Eℂ χ` is `|A| • e_χ`; its `iotaAlg`-preimage is
  `tildeE χ` (`iotaAlg_tildeE`).

Everything here is a definition or an elementary consequence of `iota_injective` and
`isClassFun_of_mem_Irr`.
-/

noncomputable section

open Classical

open scoped BigOperators MonoidAlgebra

namespace Work.NormalComplement.AppVII

/-- The canonical `ℤ`-algebra map `ℤ[ζ_n] → ℂ` (as an `AlgHom`), sending the root of the
`n`-th cyclotomic polynomial to `exp (2 π i / n)`.  It is the `AlgHom` version of
`Work.Hering.AppVII.iota`. -/
def iotaAlgHom (n : ℕ) [NeZero n] : Work.Hering.AppVII.CycloRing n →ₐ[ℤ] ℂ where
  toRingHom := Work.Hering.AppVII.iota n
  commutes' r := by
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.lift_of _ (x := r)

theorem iotaAlgHom_apply (n : ℕ) [NeZero n] (x : Work.Hering.AppVII.CycloRing n) :
    iotaAlgHom n x = Work.Hering.AppVII.iota n x := rfl

/-- The coefficientwise extension of `iota` to the group algebra: the ring hom
`ℤ[ζ_|A|][A] → ℂ[A]` sending `single g r` to `single g (iota r)`. -/
def iotaAlg {A : Type*} [Group A] [Fintype A] :
    MonoidAlgebra (Work.Hering.AppVII.CycloRing (Nat.card A)) A →+*
      MonoidAlgebra ℂ A :=
  (MonoidAlgebra.mapAlgHom A (iotaAlgHom (Nat.card A))).toRingHom

theorem iotaAlg_apply {A : Type*} [Group A] [Fintype A]
    (x : MonoidAlgebra (Work.Hering.AppVII.CycloRing (Nat.card A)) A) :
    iotaAlg x = MonoidAlgebra.mapAlgHom A (iotaAlgHom (Nat.card A)) x := rfl

theorem iotaAlg_single {A : Type*} [Group A] [Fintype A] (g : A)
    (r : Work.Hering.AppVII.CycloRing (Nat.card A)) :
    iotaAlg (MonoidAlgebra.single g r) = MonoidAlgebra.single g (iotaAlgHom _ r) :=
  MonoidAlgebra.mapAlgHom_single _ g r

/-- `iotaAlg` is injective, because `iota` is (`iota_injective`). -/
theorem iotaAlg_injective {A : Type*} [Group A] [Fintype A] :
    Function.Injective (iotaAlg (A := A)) := by
  intro x y hxy
  ext m
  have h := congrArg (fun z : MonoidAlgebra ℂ A => z.coeff m) hxy
  simp only [iotaAlg_apply, MonoidAlgebra.coeff_mapAlgHom] at h
  exact Work.Hering.AppVII.iota_injective h

/-- The image of `tildeE χ` under `iotaAlg` is `Eℂ χ = |A| • e_χ`, the `|A|`-multiple of the
central primitive idempotent of `ℂ[A]` attached to `χ`. -/
theorem iotaAlg_tildeE {A : Type*} [Group A] [Fintype A] (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) :
    iotaAlg (Work.Hering.AppVII.tildeE χ hχ) = Work.Hering.AppVII.Eℂ χ := by
  ext g
  rw [iotaAlg_apply, MonoidAlgebra.coeff_mapAlgHom, Work.Hering.AppVII.tildeE,
    Work.Hering.AppVII.Eℂ, MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_smul_apply,
    coeff_sum_smul_single, coeff_sum_smul_single, smul_eq_mul, map_mul, map_natCast,
    iotaAlgHom_apply, Work.Hering.AppVII.iota_charLift, smul_eq_mul]

/-- `iotaAlg` commutes with the coefficient scalars: the image of the `ℤ[ζ_|A|]`-multiple
`r • W` is the `ℂ`-multiple `iota r • iotaAlg W`. -/
theorem iotaAlg_smul {A : Type*} [Group A] [Fintype A]
    (r : Work.Hering.AppVII.CycloRing (Nat.card A))
    (W : MonoidAlgebra (Work.Hering.AppVII.CycloRing (Nat.card A)) A) :
    iotaAlg (r • W) = iotaAlgHom (Nat.card A) r • iotaAlg W := by
  ext g
  rw [iotaAlg_apply, MonoidAlgebra.coeff_mapAlgHom, MonoidAlgebra.coeff_smul_apply,
    MonoidAlgebra.coeff_smul_apply, smul_eq_mul, map_mul, iotaAlgHom_apply, iotaAlg_apply,
    MonoidAlgebra.coeff_mapAlgHom, iotaAlgHom_apply, smul_eq_mul]

/-- The class sum `z_χ = ∑_g χ(g⁻¹) • single g 1` of `ℂ[A]`. -/
noncomputable def zℂ {A : Type*} [Group A] [Fintype A] (χ : A → ℂ) : MonoidAlgebra ℂ A :=
  ∑ g : A, (χ (g⁻¹) : ℂ) • MonoidAlgebra.single g (1 : ℂ)

/-- The coefficient of `single g 1` in `zℂ χ` is `χ g⁻¹`. -/
theorem coeff_zℂ {A : Type*} [Group A] [Fintype A] (χ : A → ℂ) (g : A) :
    (zℂ χ).coeff g = χ (g⁻¹) :=
  coeff_sum_smul_single (fun g => χ (g⁻¹)) g

/-- `Eℂ χ` is `irrDeg χ` times the class sum `zℂ χ`. -/
theorem Eℂ_eq_zℂ {A : Type*} [Group A] [Fintype A] (χ : A → ℂ) :
    Work.Hering.AppVII.Eℂ χ = (Work.CharCore.irrDeg χ : ℂ) • zℂ χ := rfl

/-- The class sum `zℂ χ` is central in `ℂ[A]` for an irreducible `χ`. -/
theorem zℂ_central {A : Type*} [Group A] [Fintype A] {χ : A → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr A) (x : MonoidAlgebra ℂ A) :
    x * zℂ χ = zℂ χ * x := by
  have hc : ∀ g h : A, (fun g => χ (g⁻¹)) (h * g * h⁻¹) = (fun g => χ (g⁻¹)) g := by
    intro g h
    show χ (h * g * h⁻¹)⁻¹ = χ (g⁻¹)
    have h1 : (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ := by group
    rw [h1]
    exact Work.CharCore.isClassFun_of_mem_Irr hχ g⁻¹ h
  exact classFun_sum_single_central (fun g => χ (g⁻¹)) hc x

/-- `Eℂ χ` is central in `ℂ[A]` for an irreducible `χ`. -/
theorem Eℂ_central {A : Type*} [Group A] [Fintype A] {χ : A → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr A) (x : MonoidAlgebra ℂ A) :
    x * Work.Hering.AppVII.Eℂ χ = Work.Hering.AppVII.Eℂ χ * x := by
  rw [Eℂ_eq_zℂ, mul_smul_comm, smul_mul_assoc, zℂ_central hχ]

end Work.NormalComplement.AppVII
