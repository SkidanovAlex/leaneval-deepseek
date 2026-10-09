import Mathlib
import Submission.NK.NUV2.RouteE.levelSymbol
import Submission.NK.NUV2.RouteE.cupNaturality
import Submission.NK.NUV2.RouteC.LevelInf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction compatibility of the level symbols (L5)

For a tower of fields `F ⊆ M ⊆ L` (`M/F` normal) with abelian Galois groups, and fundamental
classes `u_M ∈ H²(Gal(M/F), Mˣ)`, `u_L ∈ H²(Gal(L/F), Lˣ)` related by the *coherence* relation

`Inf u_M = [L : M] · u_L`

(`Inf` the level inflation), the level symbols of `NK.NUV2.RouteE.levelSymbol` are *compatible*
with the restriction of automorphisms:

`res (θ_{M,u_M} a) = θ_{L,u_L} a`.

This is step L5 of the character-formula route to the local reciprocity law: it is what makes the
per-level symbols the level maps of a single Artin map.  The proof is the character formula at the
two levels, the compatibility of the invariants `ι_u` under `Inf`
(`NK.NUV2.RouteC.invariantOf_comp_eq_of_inf`) and the naturality of the cup product under `Inf`
(the statement `hcup`, "Brick E"). -/

open scoped BigOperators
open CategoryTheory

namespace NK.NUV2.RouteE

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section Compat

variable {F M L : Type} [Field F] [Field M] [Field L]
  [Algebra F M] [Algebra F L] [Algebra M L] [IsScalarTower F M L] [Normal F M]
variable [FiniteDimensional F M] [FiniteDimensional F L]
variable [IsGalois F M] [IsGalois F L]
variable [Fintype (M ≃ₐ[F] M)] [Fintype (L ≃ₐ[F] L)]
variable [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits F M) 2)]
variable [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2)]

/-- **L5: compatibility of the level symbols with restriction.**  If the fundamental classes `u_M`
and `u_L` are related by `Inf u_M = [L:M] · u_L`, and if the cup product is natural under the level
inflation (the statement `hcup`), then the level symbol at `M` restricted to `L` is the level
symbol at `L`. -/
theorem levelSymbol_restrict
    (hcommM : ∀ σ τ : M ≃ₐ[F] M, σ * τ = τ * σ)
    (hcommL : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ)
    (uM : groupCohomology (Rep.ofAlgebraAutOnUnits F M) 2)
    (huM : addOrderOf uM = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F M) 2))
    (uL : groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2)
    (huL : addOrderOf uL = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2))
    (hdvd : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F M) 2)
      ∣ Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2))
    (hcoh : (NK.NUV2.RouteC.levelInfMap (F := F) (M := M) (L := L)) uM
      = ((Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2)
          / Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F M) 2) : ℕ) : ℤ) • uL)
    (a : Fˣ) :
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M))
        (levelSymbol (F := F) (E := L) hcommL uL huL a)
      = levelSymbol (F := F) (E := M) hcommM uM huM a := by
  classical
  apply doubleDual_injective hcommM
  intro χ
  rw [show χ (Additive.ofMul ((AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M))
        (levelSymbol (F := F) (E := L) hcommL uL huL a)))
      = (χ.comp (MonoidHom.toAdditive
          (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M))))
          (Additive.ofMul (levelSymbol (F := F) (E := L) hcommL uL huL a)) from rfl]
  rw [levelSymbol_apply (F := F) (E := L) hcommL uL huL a
    (χ.comp (MonoidHom.toAdditive
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M))))]
  rw [levelSymbol_apply (F := F) (E := M) hcommM uM huM a χ]
  show NK.NUV2.RouteC.invariantOf uL huL
      ((groupCohomology.map (MonoidHom.id (L ≃ₐ[F] L))
        (NK.NUV2.RouteC.powHom (F := F) (E := L) a) 2)
        (NK.NUV2.RouteC.deltaHomChar (L ≃ₐ[F] L)
          (χ.comp (MonoidHom.toAdditive
            (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M))))))
    = NK.NUV2.RouteC.invariantOf uM huM
      ((groupCohomology.map (MonoidHom.id (M ≃ₐ[F] M))
        (NK.NUV2.RouteC.powHom (F := F) (E := M) a) 2)
        (NK.NUV2.RouteC.deltaHomChar (M ≃ₐ[F] M) χ))
  have hcomp : NK.NUV2.RouteC.invariantOf uM huM
      = (NK.NUV2.RouteC.invariantOf uL huL).comp
          ((NK.NUV2.RouteC.levelInfMap (F := F) (M := M) (L := L)).hom.toAddMonoidHom) :=
    NK.NUV2.RouteC.invariantOf_comp_eq_of_inf uM huM uL huL hdvd
      ((NK.NUV2.RouteC.levelInfMap (F := F) (M := M) (L := L)).hom.toAddMonoidHom) hcoh
  rw [← NK.NUV2.RouteE.deltaHomChar_naturality
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M)) χ]
  rw [← NK.NUV2.RouteE.levelInfMap_cup_coeff (F := F) (M := M) (L := L) a
    (NK.NUV2.RouteC.deltaHomChar (M ≃ₐ[F] M) χ)]
  rw [hcomp, AddMonoidHom.comp_apply]
  rfl

/-- **L5, invariant form.**  Same as `levelSymbol_restrict`, with the coherence relation stated as
`ι_{uM} = ι_{uL} ∘ Inf` (the form produced by `NK.NUV2.RouteC.invariantOf_comp_eq_of_inf`). -/
theorem levelSymbol_restrict_of_invariant
    (hcommM : ∀ σ τ : M ≃ₐ[F] M, σ * τ = τ * σ)
    (hcommL : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ)
    (uM : groupCohomology (Rep.ofAlgebraAutOnUnits F M) 2)
    (huM : addOrderOf uM = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F M) 2))
    (uL : groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2)
    (huL : addOrderOf uL = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2))
    (hrel : NK.NUV2.RouteC.invariantOf uM huM
      = (NK.NUV2.RouteC.invariantOf uL huL).comp
          ((NK.NUV2.RouteC.levelInfMap (F := F) (M := M) (L := L)).hom.toAddMonoidHom))
    (a : Fˣ) :
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M))
        (levelSymbol (F := F) (E := L) hcommL uL huL a)
      = levelSymbol (F := F) (E := M) hcommM uM huM a := by
  classical
  apply doubleDual_injective hcommM
  intro χ
  rw [show χ (Additive.ofMul ((AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M))
        (levelSymbol (F := F) (E := L) hcommL uL huL a)))
      = (χ.comp (MonoidHom.toAdditive
          (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M))))
          (Additive.ofMul (levelSymbol (F := F) (E := L) hcommL uL huL a)) from rfl]
  rw [levelSymbol_apply (F := F) (E := L) hcommL uL huL a
    (χ.comp (MonoidHom.toAdditive
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M))))]
  rw [levelSymbol_apply (F := F) (E := M) hcommM uM huM a χ]
  show NK.NUV2.RouteC.invariantOf uL huL
      ((groupCohomology.map (MonoidHom.id (L ≃ₐ[F] L))
        (NK.NUV2.RouteC.powHom (F := F) (E := L) a) 2)
        (NK.NUV2.RouteC.deltaHomChar (L ≃ₐ[F] L)
          (χ.comp (MonoidHom.toAdditive
            (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M))))))
    = NK.NUV2.RouteC.invariantOf uM huM
      ((groupCohomology.map (MonoidHom.id (M ≃ₐ[F] M))
        (NK.NUV2.RouteC.powHom (F := F) (E := M) a) 2)
        (NK.NUV2.RouteC.deltaHomChar (M ≃ₐ[F] M) χ))
  rw [← NK.NUV2.RouteE.deltaHomChar_naturality
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := M)) χ]
  rw [← NK.NUV2.RouteE.levelInfMap_cup_coeff (F := F) (M := M) (L := L) a
    (NK.NUV2.RouteC.deltaHomChar (M ≃ₐ[F] M) χ)]
  rw [hrel, AddMonoidHom.comp_apply]
  rfl

end Compat

end NK.NUV2.RouteE
