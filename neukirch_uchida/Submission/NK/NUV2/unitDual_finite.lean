import Mathlib
import Submission.NK.NUV2.rank_addMonoidHom_units_eq_rank

/-!
# Finiteness of `Hom(𝒪_Kˣ, ℤ₂)`

The dual `Hom(𝒪_Kˣ, ℤ₂)` of the unit group of the ring of integers of a number field is a
finitely generated `ℤ₂`-module: by Dirichlet's unit theorem `𝒪_Kˣ` is a finitely generated abelian
group, and the `ℤ₂`-dual of a finitely generated abelian group is finitely generated (the torsion
part dies because `ℤ₂` is torsion free, and the free part contributes a free `ℤ₂`-module of the
same rank).

The general statement is proved first: for a `ℤ`-module `U` which is finitely generated, the
`ℤ₂`-module `Hom_ℤ(U, ℤ₂)` is finitely generated.  The proof uses the Noetherianity of `ℤ₂`
(`ℤ₂` is a discrete valuation ring): the evaluation map on a finite spanning set is an injective
`ℤ₂`-linear map into a finite free module, and submodules of finitely generated modules over a
Noetherian ring are finitely generated.
-/

set_option linter.style.haveILetI false

namespace NK.NUV2

open Submodule

/-- **The `ℤ_p`-dual of a finitely generated `ℤ`-module is finitely generated.**
If `U` is a finitely generated abelian group then `Hom(U, ℤ_p)` is a finitely generated
`ℤ_p`-module. -/
theorem finite_addMonoidHom_padicInt {p : ℕ} [Fact p.Prime] (U : Type*) [AddCommGroup U]
    [Module.Finite ℤ U] : Module.Finite (PadicInt p) (U →+ PadicInt p) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := U)
  haveI : IsNoetherianRing (PadicInt p) := inferInstance
  -- Evaluation at the spanning family `s` is an injective `ℤ_p`-linear map into `ℤ_p ^ n`.
  let Φ : (U →+ PadicInt p) →ₗ[PadicInt p] (Fin n → PadicInt p) :=
    { toFun := fun f i => f (s i)
      map_add' := by intro f g; ext i; rfl
      map_smul' := by intro c f; ext i; rfl }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    -- `f` vanishes on the spanning family, hence on all of `U`.
    have hf' : ∀ i, f (s i) = 0 := fun i => by
      have h := congrFun hf i
      simpa [Φ] using h
    have h0 : f.toIntLinearMap = 0 :=
      LinearMap.ker_eq_top.mp (top_le_iff.mp (hs ▸ Submodule.span_le.mpr
        (by rintro x ⟨i, rfl⟩; simpa using hf' i)))
    ext u
    have h := congrFun (congrArg DFunLike.coe h0) u
    simpa using h
  -- Submodules of a finitely generated module over the Noetherian ring `ℤ_p` are finitely
  -- generated.
  have htop : (⊤ : Submodule (PadicInt p) (Fin n → PadicInt p)).FG := Module.Finite.fg_top
  have hrange : (LinearMap.range Φ).FG := Submodule.FG.of_le htop le_top
  haveI : Module.Finite (PadicInt p) (LinearMap.range Φ) := Module.Finite.of_fg hrange
  exact Module.Finite.equiv (LinearEquiv.ofInjective Φ hinj).symm

theorem unitDual_finite (K : Type) [Field K] [NumberField K] :
    Module.Finite (PadicInt 2) (Additive ((NumberField.RingOfIntegers K)ˣ) →+ PadicInt 2) :=
  finite_addMonoidHom_padicInt (p := 2) (Additive (NumberField.RingOfIntegers K)ˣ)

end NK.NUV2
