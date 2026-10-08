import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irreducible_character_mem_Irr
import Submission.Work.CharCore.fdRep_simple_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.mem_Irr_iff_fdrep`

`Work.CharCore.Irr G` is the finset of irreducible complex characters of `G`, built from the
characters of a chosen family `irrSubmodules G` of simple submodules of the regular module
`ℂ[G]`.  This file shows that it coincides with the set of characters of the simple objects of
the category `FDRep ℂ G` of finite dimensional complex representations of `G`:

`χ ∈ Irr G ↔ ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ`.

The reverse implication is the completeness statement `irreducible_character_mem_Irr` already
proved for the chosen family, together with `Work.CharCore.fdRep_simple_iff`, which identifies
categorical simplicity of `V : FDRep ℂ G` with irreducibility of the representation `V.ρ`.

For the forward implication we must produce, for a simple submodule `N ≤ ℂ[G]`, an honest
object of `FDRep ℂ G` whose character is `(submoduleRep N).character`.  Since `FDRep ℂ G` is
built from `FGModuleCat ℂ` — the finite dimensional `ℂ`-vector spaces living in the *same
universe* as `ℂ` — while `N` lives in the universe of `G`, we first transport the
representation along a `ℂ`-linear isomorphism `N ≃ₗ[ℂ] (Fin (finrank ℂ N) → ℂ)` to the
standard model.  Traces are invariant under conjugation, so the character is unchanged, and
`Simple` is transported along the equivalence of representations.

## Main result

* `Work.CharCore.mem_Irr_iff_fdrep`
-/

noncomputable section

open CategoryTheory

open scoped MonoidAlgebra

namespace Work.CharCore

section Helpers

variable {G : Type*} [Group G]

/-- The `ℂ[G]`-module structure on `(ofModule' M).asModule` is the given one: the action of
`r : ℂ[G]` is the given scalar multiplication by `r` on `M`. -/
theorem smul_eq_asAlgebraHom_ofModule' (M : Type*) [AddCommGroup M] [Module ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] (r : ℂ[G]) (x : M) :
    r • x = ((Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom r) x := by
  rw [Representation.asAlgebraHom_def]
  unfold Representation.ofModule'
  rw [Equiv.apply_symm_apply]
  rfl

/-- `LinearEquiv.conjRingEquiv` is conjugation by the linear equivalence. -/
theorem conjRingEquiv_apply_conj {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (e : M ≃ₗ[ℂ] N) (f : Module.End ℂ M) :
    LinearEquiv.conjRingEquiv e f = e.conj f := by
  rw [LinearEquiv.conjRingEquiv]
  rfl

/-- The character of `FDRep.of ρ` is the character of `ρ`. -/
theorem fdRep_character_of_eq {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) : (FDRep.of ρ).character = ρ.character := by
  funext g
  rfl

/-- A bijective intertwining map is an isomorphism of `ℂ[G]`-modules between the associated
modules. -/
def asModuleLinearEquivOfEquiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : Representation.Equiv ρ σ) : ρ.asModule ≃ₗ[ℂ[G]] σ.asModule :=
  LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap)
    (by
      rw [show (⇑(Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
          φ.toIntertwiningMap)) = ⇑φ from rfl]
      exact φ.bijective)

/-- Simplicity of the associated `ℂ[G]`-module is invariant under equivalence of
representations. -/
theorem isSimpleModule_asModule_of_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : Representation.Equiv ρ σ) (h : IsSimpleModule ℂ[G] ρ.asModule) :
    IsSimpleModule ℂ[G] σ.asModule :=
  IsSimpleModule.congr (asModuleLinearEquivOfEquiv φ).symm

/-- If `M` is a simple `ℂ[G]`-module then `ofModule' M` is an irreducible representation. -/
theorem isIrreducible_ofModule' (M : Type*) [AddCommGroup M] [Module ℂ M] [Module ℂ[G] M]
    [IsScalarTower ℂ ℂ[G] M] (h : IsSimpleModule ℂ[G] M) :
    Representation.IsIrreducible (Representation.ofModule' (k := ℂ) (G := G) M) := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have e : (Representation.ofModule' (k := ℂ) (G := G) M).asModule ≃ₗ[ℂ[G]] M :=
  { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
    map_add' := fun _ _ => rfl,
    map_smul' := fun r x => (smul_eq_asAlgebraHom_ofModule' M r x).symm }
  exact IsSimpleModule.congr e

/-- A finite dimensional simple `ℂ[G]`-module in an arbitrary universe has a model in the
universe of `ℂ`: its representation can be transported to `Fin (finrank ℂ M) → ℂ` along a
`ℂ`-linear isomorphism.  This yields an object of `FDRep ℂ G` with a simple underlying object
and the same character. -/
theorem exists_fdRep_of_isSimpleModule (M : Type*) [AddCommGroup M] [Module ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] [Module.Finite ℂ M]
    (h : IsSimpleModule ℂ[G] M) :
    ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧
      V.character = (Representation.ofModule' (k := ℂ) (G := G) M).character := by
  classical
  let e : M ≃ₗ[ℂ] (Fin (Module.finrank ℂ M) → ℂ) := (Module.finBasis ℂ M).equivFun
  let ρ : Representation ℂ G M := Representation.ofModule' (k := ℂ) (G := G) M
  let ρ' : Representation ℂ G (Fin (Module.finrank ℂ M) → ℂ) :=
    (LinearEquiv.conjRingEquiv e).toMonoidHom.comp ρ
  have hρ : Representation.IsIrreducible ρ := isIrreducible_ofModule' M h
  have hφ : Representation.Equiv ρ ρ' :=
    Representation.Equiv.mk e (fun g => by
      show e.toLinearMap.comp (ρ g) = (ρ' g).comp e.toLinearMap
      rw [show ρ' g = (LinearEquiv.conjRingEquiv e) (ρ g) from rfl, conjRingEquiv_apply_conj]
      ext v
      simp [LinearEquiv.conj_apply_apply])
  have hS : IsSimpleModule ℂ[G] ρ'.asModule :=
    isSimpleModule_asModule_of_equiv hφ
      ((Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ)
  have hρ' : Representation.IsIrreducible ρ' :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ').mpr hS
  refine ⟨FDRep.of ρ', ?_, ?_⟩
  · rw [fdRep_simple_iff]
    simpa [FDRep.of_ρ'] using hρ'
  · rw [fdRep_character_of_eq]
    funext g
    show LinearMap.trace ℂ (Fin (Module.finrank ℂ M) → ℂ) (ρ' g) = LinearMap.trace ℂ M (ρ g)
    rw [show ρ' g = (LinearEquiv.conjRingEquiv e) (ρ g) from rfl, conjRingEquiv_apply_conj]
    exact LinearMap.trace_conj' (ρ g) e

end Helpers

theorem mem_Irr_iff_fdrep {G : Type*} [Group G] [Fintype G] (χ : G → ℂ) :
    χ ∈ Irr G ↔ ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ V.character = χ := by
  constructor
  · intro hχ
    obtain ⟨N, hN, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
    have hsimple : IsSimpleModule (groupAlgebra G) N := isSimpleModule_of_mem_irrSubmodules N hN
    obtain ⟨V, hV, hchar⟩ := exists_fdRep_of_isSimpleModule N hsimple
    exact ⟨V, hV, hchar.trans hNχ⟩
  · rintro ⟨V, hV, rfl⟩
    have hmem : Representation.character (V.ρ) ∈ Irr G :=
      irreducible_character_mem_Irr (V.ρ) ((fdRep_simple_iff V).mp hV)
    exact hmem

end Work.CharCore
