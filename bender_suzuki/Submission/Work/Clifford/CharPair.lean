import Mathlib
import Submission.Work.Clifford.CFun
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irreducible_character_mem_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.CharPair`: the bilinear character pairing and its orthonormality

`Work.Clifford.charPair f g = |G|⁻¹ ∑_x f x * g x⁻¹` is the *bilinear* companion of the
conjugate-linear `Work.Clifford.cfInner`.  Unlike `cfInner` it needs no knowledge of
`star (χ g) = χ g⁻¹` to be orthonormal on `Work.CharCore.Irr G`: it is exactly the pairing that
Mathlib's `Representation.char_orthonormal` computes.

## Main results

* `Work.Clifford.finrank_classFun_eq_card_conjClasses` — the space of class functions has
  dimension the number of conjugacy classes;
* `Work.Clifford.charPair_eq_ite_of_mem_Irr` — `Irr G` is orthonormal for `charPair`.
-/

noncomputable section
set_option linter.unusedSectionVars false
open Classical

namespace Work.Clifford

variable {G : Type*} [Group G] [Fintype G]

/-! ### The class-function space -/

/-- The space of class functions on `G` has dimension the number of conjugacy classes. -/
theorem finrank_classFun_eq_card_conjClasses :
    Module.finrank ℂ (Work.CharCore.classFunSubmodule G) = Nat.card (ConjClasses G) := by
  classical
  let rep (c : ConjClasses G) : G := Classical.choose (ConjClasses.exists_rep c)
  have rep_spec (c : ConjClasses G) : ConjClasses.mk (rep c) = c :=
    Classical.choose_spec (ConjClasses.exists_rep c)
  have key : ∀ (f : Work.CharCore.classFunSubmodule G) (a b : G), IsConj a b →
      (f : G → ℂ) a = (f : G → ℂ) b := by
    rintro ⟨f, hf⟩ a b hab
    obtain ⟨d, hd⟩ := isConj_iff.mp hab
    rw [← hd]
    exact (hf a d).symm
  let e : Work.CharCore.classFunSubmodule G ≃ₗ[ℂ] (ConjClasses G → ℂ) :=
    { toFun := fun f => fun c => (f : G → ℂ) (rep c)
      invFun := fun F => ⟨fun g => F (ConjClasses.mk g), by
        intro a b
        refine congrArg F ((ConjClasses.mk_eq_mk_iff_isConj).mpr ?_)
        exact isConj_iff.mpr ⟨b⁻¹, by group⟩⟩
      map_add' := by intro f₁ f₂; funext c; rfl
      map_smul' := by intro r f; funext c; rfl
      left_inv := by
        intro f
        ext g
        show (f : G → ℂ) (rep (ConjClasses.mk g)) = (f : G → ℂ) g
        refine key f _ g ?_
        exact (ConjClasses.mk_eq_mk_iff_isConj).mp (rep_spec (ConjClasses.mk g))
      right_inv := by
        intro F
        funext c
        show F (ConjClasses.mk (rep c)) = F c
        rw [rep_spec c] }
  rw [LinearEquiv.finrank_eq e, Module.finrank_fintype_fun_eq_card ℂ,
    Nat.card_eq_fintype_card]

/-! ### The pairing -/

/-- The bilinear character pairing `⟪f, g⟫ = |G|⁻¹ ∑_x f x * g x⁻¹`. -/
def charPair (f g : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ x : G, f x * g x⁻¹

@[simp] theorem charPair_apply (f g : G → ℂ) :
    charPair f g = (Nat.card G : ℂ)⁻¹ * ∑ x : G, f x * g x⁻¹ := rfl

/-- `Nat.card G` is invertible in `ℂ`. -/
def invertibleNatCard : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (by
    have h : 0 < Nat.card G := Nat.card_pos
    exact_mod_cast h.ne')

/-! ### The underlying `ℂ[G]`-module of `Representation.ofModule'` -/

theorem asAlgebraHom_ofModule'_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (Work.CharCore.groupAlgebra G) M] [IsScalarTower ℂ (Work.CharCore.groupAlgebra G) M]
    (r : Work.CharCore.groupAlgebra G) (x : M) :
    (Representation.asAlgebraHom (Representation.ofModule' (k := ℂ) (G := G) M)) r x = r • x := by
  rw [Representation.asAlgebraHom_def, Representation.ofModule', Equiv.apply_symm_apply]
  exact Algebra.lsmul_apply ℂ ℂ M r x

theorem asModuleEquiv_smul_ofModule' {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (Work.CharCore.groupAlgebra G) M] [IsScalarTower ℂ (Work.CharCore.groupAlgebra G) M]
    (r : Work.CharCore.groupAlgebra G)
    (x : (Representation.ofModule' (k := ℂ) (G := G) M).asModule) :
    Representation.asModuleEquiv (Representation.ofModule' (k := ℂ) (G := G) M) (r • x) =
      r • Representation.asModuleEquiv (Representation.ofModule' (k := ℂ) (G := G) M) x :=
  (Representation.asModuleEquiv_map_smul (ρ := Representation.ofModule' (k := ℂ) (G := G) M) r x).trans
    (asAlgebraHom_ofModule'_apply r _)

/-- `Representation.asModuleEquiv` for `ofModule'` is `ℂ[G]`-linear. -/
noncomputable def ofModule'_asModuleLinearEquiv {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (Work.CharCore.groupAlgebra G) M] [IsScalarTower ℂ (Work.CharCore.groupAlgebra G) M] :
    (Representation.ofModule' (k := ℂ) (G := G) M).asModule ≃ₗ[Work.CharCore.groupAlgebra G] M :=
  { Representation.asModuleEquiv (Representation.ofModule' (k := ℂ) (G := G) M) with
    map_smul' := asModuleEquiv_smul_ofModule' }

/-- `ofModule'` does not change simplicity of the underlying module. -/
theorem isSimpleModule_ofModule'_asModule_iff {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (Work.CharCore.groupAlgebra G) M] [IsScalarTower ℂ (Work.CharCore.groupAlgebra G) M] :
    IsSimpleModule (Work.CharCore.groupAlgebra G)
        (Representation.ofModule' (k := ℂ) (G := G) M).asModule
      ↔ IsSimpleModule (Work.CharCore.groupAlgebra G) M := by
  constructor
  · intro h
    haveI := h
    exact IsSimpleModule.congr (e := ofModule'_asModuleLinearEquiv.symm)
  · intro h
    haveI := h
    exact IsSimpleModule.congr (e := ofModule'_asModuleLinearEquiv)

/-- The representation `Work.CharCore.submoduleRep N` attached to a simple submodule of the
regular module is irreducible. -/
theorem submoduleRep_isIrreducible {N : Submodule (Work.CharCore.groupAlgebra G)
    (Work.CharCore.groupAlgebra G)} (hN : N ∈ Work.CharCore.irrSubmodules G) :
    (Work.CharCore.submoduleRep N).IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact isSimpleModule_ofModule'_asModule_iff.mpr
    (Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hN)

/-! ### Orthonormality -/

/-- Two irreducible representations have the same character iff they are isomorphic. -/
theorem nonempty_equiv_iff_char_eq {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ] :
    Nonempty (Representation.Equiv σ ρ) ↔ ρ.character = σ.character := by
  haveI := invertibleNatCard (G := G)
  constructor
  · rintro ⟨φ⟩; exact (Representation.char_iso φ).symm
  · intro h
    by_contra hc
    have h1 : charPair ρ.character σ.character = 1 := by
      rw [h.symm, charPair, Representation.char_orthonormal ρ ρ]
      exact if_pos ⟨Representation.Equiv.refl ρ⟩
    rw [show charPair ρ.character σ.character =
        (if Nonempty (Representation.Equiv σ ρ) then (1 : ℂ) else 0) from
      Representation.char_orthonormal ρ σ] at h1
    rw [if_neg hc] at h1
    exact one_ne_zero h1.symm

/-- The elements of `Work.CharCore.Irr G` are orthonormal for the bilinear pairing `charPair`. -/
theorem charPair_eq_ite_of_mem_Irr {χ ψ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) (hψ : ψ ∈ Work.CharCore.Irr G) :
    charPair χ ψ = if χ = ψ then 1 else 0 := by
  classical
  obtain ⟨N, hN, rfl⟩ := (Work.CharCore.mem_Irr_iff_exists χ).mp hχ
  obtain ⟨N', hN', rfl⟩ := (Work.CharCore.mem_Irr_iff_exists ψ).mp hψ
  haveI hirr : (Work.CharCore.submoduleRep N).IsIrreducible := submoduleRep_isIrreducible hN
  haveI hirr' : (Work.CharCore.submoduleRep N').IsIrreducible := submoduleRep_isIrreducible hN'
  haveI := invertibleNatCard (G := G)
  have hiff := nonempty_equiv_iff_char_eq (Work.CharCore.submoduleRep N) (Work.CharCore.submoduleRep N')
  rw [charPair, Representation.char_orthonormal (Work.CharCore.submoduleRep N)
    (Work.CharCore.submoduleRep N')]
  by_cases h : (Work.CharCore.submoduleRep N).character = (Work.CharCore.submoduleRep N').character
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]

end Work.Clifford
