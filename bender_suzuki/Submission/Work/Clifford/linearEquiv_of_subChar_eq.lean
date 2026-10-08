import Mathlib
import Submission.Work.Clifford.ResSetup
import Submission.Work.Clifford.exists_simple_fdrep_of_submodule
import Submission.Work.CharCore.mem_Irr_iff_fdrep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.linearEquiv_of_subChar_eq`

Let `N ⊴ G` be a normal subgroup of a finite group, `V : FDRep ℂ G` and let
`X, Y ≤ ResMod N V` be simple `ℂ[N]`-submodules (i.e. simple constituents of the restriction
of `V` to `N`).  If the associated characters — the sub-characters
`Work.Clifford.subChar V X` and `Work.Clifford.subChar V Y` of `ResSetup` — agree, then `X`
and `Y` are isomorphic as `ℂ[N]`-modules.

Equivalently: *a simple complex `ℂ[N]`-module is determined, up to isomorphism, by its
trace character*.  The proof has three steps.

* `Work.Clifford.character_ofModule'_submodule`: the character of the representation
  `Representation.ofModule' ↥X` of `↥N` on `↥X` is exactly `subChar V X`.
* By Schur's lemma, `Representation.ofModule' ↥X` is irreducible, and Mathlib's
  orthogonality of characters `Representation.char_orthonormal` combined with the equality of
  characters shows that the two representations are equivalent
  (the same computation as `Work.Clifford.nonempty_iso_of_char_eq` for `FDRep`).
* `Work.CharCore.asModuleLinearEquivOfEquiv` turns a `Representation.Equiv` into an
  isomorphism of `ℂ[N]`-modules, and `Work.Clifford.ofModule'AsModuleLinearEquiv` identifies
  `↥X` with the module `(ofModule' ↥X).asModule`.
-/

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open Classical
open scoped MonoidAlgebra

namespace Work.Clifford

universe u

variable {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]

/-- The identity map, viewed as a `ℂ[G]`-linear equivalence from a module `M` to the module
`(Representation.ofModule' M).asModule` associated with the representation `ofModule' M`.

`(Representation.ofModule' M).asModule` is the same type as `M`, but its `ℂ[G]`-module
structure is the one induced by the representation, i.e. `r • x = ρ.asAlgebraHom r x`. -/
def ofModule'AsModuleLinearEquiv (M : Type*) [AddCommGroup M] [Module ℂ M]
    [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M] :
    M ≃ₗ[MonoidAlgebra ℂ G]
      (Representation.ofModule' (k := ℂ) (G := G) M).asModule where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun r x => Work.CharCore.smul_eq_asAlgebraHom_ofModule' M r x

/-- The character of `Representation.ofModule' (G := ↥N) ↥X`, i.e. of the representation of
`↥N` on the simple constituent `X`, is the sub-character `subChar V X`. -/
theorem character_ofModule'_submodule (V : FDRep ℂ G)
    (X : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) :
    (Representation.ofModule' (k := ℂ) (G := ↥N) ↥X).character = subChar V X := by
  ext n
  rw [Representation.character, subChar_apply]
  congr 1
  ext x
  rw [Work.CharCore.ofModule'_apply_of]
  rw [Submodule.coe_smul, of_smul, subAct_apply]

theorem linearEquiv_of_subChar_eq {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    (V : FDRep ℂ G) (X Y : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V))
    [IsSimpleModule (MonoidAlgebra ℂ ↥N) ↥X] [IsSimpleModule (MonoidAlgebra ℂ ↥N) ↥Y]
    (h : subChar V X = subChar V Y) : Nonempty (↥X ≃ₗ[MonoidAlgebra ℂ ↥N] ↥Y) := by
  -- `Nat.card ↥N` is invertible in `ℂ`.
  haveI : Invertible (Nat.card ↥N : ℂ) :=
    invertibleOfNonzero (by
      have := Nat.card_pos (α := ↥N)
      exact_mod_cast this.ne')
  -- the two representations of `↥N` on `↥X` and `↥Y`
  let ρX := Representation.ofModule' (k := ℂ) (G := ↥N) ↥X
  let ρY := Representation.ofModule' (k := ℂ) (G := ↥N) ↥Y
  -- finiteness over `ℂ` (needed for orthogonality of characters)
  haveI : FiniteDimensional ℂ ↥X :=
    (inferInstance : FiniteDimensional ℂ (X.restrictScalars ℂ))
  haveI : FiniteDimensional ℂ ↥Y :=
    (inferInstance : FiniteDimensional ℂ (Y.restrictScalars ℂ))
  -- both representations are irreducible by Schur's lemma
  haveI : Representation.IsIrreducible ρX :=
    Work.CharCore.isIrreducible_ofModule' ↥X ‹IsSimpleModule (MonoidAlgebra ℂ ↥N) ↥X›
  haveI : Representation.IsIrreducible ρY :=
    Work.CharCore.isIrreducible_ofModule' ↥Y ‹IsSimpleModule (MonoidAlgebra ℂ ↥N) ↥Y›
  -- the two characters are equal
  have hch : ρX.character = ρY.character := by
    rw [character_ofModule'_submodule V X, character_ofModule'_submodule V Y, h]
  -- orthogonality of characters: `⟪χ_X, χ_Y⟫ = 1` if the representations are equivalent
  -- and `0` otherwise; the diagonal case is `1`, so they must be equivalent.
  have hortho := Representation.char_orthonormal ρX ρY
  rw [← hch] at hortho
  have hdiag : (Nat.card ↥N : ℂ)⁻¹ * ∑ n : ↥N, ρX.character n * ρX.character n⁻¹ = 1 := by
    rw [Representation.char_orthonormal ρX ρX]
    rw [ite_eq_left ⟨Representation.Equiv.refl ρX⟩]
  rw [hortho] at hdiag
  obtain ⟨φ⟩ : Nonempty (Representation.Equiv ρY ρX) := by
    by_contra hne
    rw [ite_eq_right hne] at hdiag
    exact zero_ne_one hdiag
  -- convert the equivalence of representations into a `ℂ[N]`-linear equivalence of the
  -- underlying modules
  exact ⟨(ofModule'AsModuleLinearEquiv (G := ↥N) ↥X).trans
    (((Work.CharCore.asModuleLinearEquivOfEquiv φ).symm).trans
      (ofModule'AsModuleLinearEquiv (G := ↥N) ↥Y).symm)⟩

end Work.Clifford
