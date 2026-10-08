/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : almost simple overgroups with dihedral Sylow 2-subgroups

This file is the *interface* of the area `Submission/Work/AUTL2/` for the Gorenstein–Walter
project (route: Bender 1981 + Bender–Glauberman 1981, Feit–Thompson available).

## The deliverable

`Work.GW2.AutL2Prop`, copied verbatim from `Submission/Work/_design_gw/Contracts2.lean`:

if `L ◁ Q`, `L ≃ PSL(2,q)` (`q = p^k` odd, `q ≥ 5`), `C_Q(L) = 1` and `Q` has cyclic or
dihedral Sylow 2-subgroups, then `Q` has a normal subgroup `M ⊇ L` of odd index with
`M ≃ PSL(2,q)` or `M ≃ PGL(2,q)`.

## The model used by the proof (design `NOTES_LEAD_gw_design2.md` §5, steps A1–A6)

Everything happens on the projective line `ℙ¹(F) = OnePoint F` of a finite field `F = GF(q)`:

* `Work.AUTL2.P1 F`   : the projective line `OnePoint F` (`∞` adjoined to `F`);
* `Work.AUTL2.pglHom` : `PGL(2,F) →* Perm ℙ¹(F)` (faithful), `pglImage` its range;
* `Work.AUTL2.pslHom` : `PSL(2,F) →* Perm ℙ¹(F)` (faithful), `pslImage` its range;
* `Work.AUTL2.galHom` : `Aut(F) →* Perm ℙ¹(F)`, `σ ↦ (x ↦ σ x, ∞ ↦ ∞)`;  `galSub` its range;
* `Work.AUTL2.pgammaL` : `PΓL(2,F) = pglImage ⊔ galSub`.

The main theorem is `normalizer pslImage = pgammaL` (`Normalizer.lean`, step A3), the Sylow
analysis is `A5`/`A6` (`Sylow.lean`), and the transfer to an abstract group `Q` is `Main.lean`.

## Conventions

* `F` is a field with `[DecidableEq F]` (needed for the Möbius action of Mathlib).
* `pglImage ≤ pgammaL`, `pslImage ≤ pglImage`, `pglImage ◁ pgammaL`;
* for `q = p^k` with `k` even, `sigmaPerm` is the *field involution* `x ↦ x^(p^(k/2))`.

The definitions of the vocabulary and the Prop statements are copied **verbatim** from
`Submission/Work/_design_gw/Contracts2.lean`, in the namespace `Work.GW2`, so that the area can
be composed with the other areas against those contracts.
-/
import Mathlib
import Submission.Work.ASM.Defs

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Work.GW2

open Subgroup

variable {G : Type*} [Group G]

/-! ## Vocabulary (verbatim from `Contracts2.lean` §0) -/


/-! ## The deliverable (verbatim from `Contracts2.lean` §3) -/


end Work.GW2

/-! ## The model: `ℙ¹(F)` and the actions of `PGL`, `PSL`, `Aut F` -/

namespace Work.AUTL2

open OnePoint Subgroup

variable (F : Type*) [Field F] [DecidableEq F]

/-- The projective line over `F`, as the one-point extension `F ∪ {∞}`. -/
abbrev P1 : Type _ := OnePoint F

/-- The scalar matrices act trivially on the projective line. -/
lemma scalar_smul_eq_self (u : Fˣ) (x : P1 F) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u • x = x := by
  suffices h : Matrix.GeneralLinearGroup.scalar (Fin 2) u • x =
      (1 : Matrix.GeneralLinearGroup (Fin 2) F) • x by simpa using h
  apply (OnePoint.equivProjectivization F).injective
  rw [OnePoint.equivProjectivization_smul, OnePoint.equivProjectivization_smul]
  induction (OnePoint.equivProjectivization F x) using Projectivization.ind with | h v hv =>
  rw [Projectivization.smul_mk, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨u, by ext i; fin_cases i <;> simp [Matrix.GeneralLinearGroup.coe_scalar]⟩

/-- The action of `PGL(2,F)` on the projective line. -/
noncomputable instance : MulAction (PGL(2, F)) (P1 F) :=
  Matrix.ProjGenLinGroup.mulActionOfGL (fun u a => scalar_smul_eq_self F u a)

/-- The faithful permutation representation of `PGL(2,F)` on the projective line. -/
noncomputable def pglHom : PGL(2, F) →* Equiv.Perm (P1 F) :=
  MulAction.toPermHom (PGL(2, F)) (P1 F)

/-- The faithful permutation representation of `PSL(2,F)` on the projective line. -/
noncomputable def pslHom : PSL(2, F) →* Equiv.Perm (P1 F) :=
  (pglHom F).comp Matrix.ProjectiveSpecialLinearGroup.toPGL

/-- The image of `PGL(2,F)` in the symmetric group on the projective line. -/
noncomputable def pglImage : Subgroup (Equiv.Perm (P1 F)) := (pglHom F).range

/-- The image of `PSL(2,F)` in the symmetric group on the projective line. -/
noncomputable def pslImage : Subgroup (Equiv.Perm (P1 F)) := (pslHom F).range

lemma pslImage_le_pglImage : pslImage F ≤ pglImage F := by
  rintro _ ⟨g, rfl⟩
  exact ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL g, rfl⟩

/-- The permutation of the projective line induced by a field automorphism. -/
noncomputable def fieldPerm (σ : F ≃+* F) : Equiv.Perm (P1 F) where
  toFun := OnePoint.map σ
  invFun := OnePoint.map σ.symm
  left_inv := by
    rw [Function.LeftInverse, OnePoint.forall]
    exact ⟨rfl, fun y => by simp only [OnePoint.map_some, RingEquiv.symm_apply_apply]⟩
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse, OnePoint.forall]
    exact ⟨rfl, fun y => by simp only [OnePoint.map_some, RingEquiv.apply_symm_apply]⟩

@[simp]
lemma fieldPerm_apply_coe (σ : F ≃+* F) (x : F) :
    fieldPerm F σ (x : P1 F) = (σ x : P1 F) := rfl

@[simp]
lemma fieldPerm_apply_infty (σ : F ≃+* F) :
    fieldPerm F σ (∞ : P1 F) = ∞ := rfl

/-- The field automorphisms (`Gal(F/F_p)` in the application) as permutations of `ℙ¹(F)`. -/
noncomputable def galHom : (F ≃+* F) →* Equiv.Perm (P1 F) where
  toFun := fieldPerm F
  map_one' := by
    rw [Equiv.ext_iff, OnePoint.forall]
    exact ⟨rfl, fun y => by simp only [fieldPerm_apply_coe]; rfl⟩
  map_mul' σ τ := by
    rw [Equiv.ext_iff, OnePoint.forall]
    refine ⟨?_, fun y => ?_⟩
    · rfl
    · rfl

/-- The image of `Aut F` in the symmetric group on the projective line (`PΣL`). -/
noncomputable def galSub : Subgroup (Equiv.Perm (P1 F)) := (galHom F).range

/-- `PΓL(2,F)`, as the subgroup of `Perm ℙ¹(F)` generated by `PGL` and the field
automorphisms. By `Work.AUTL2.normalizer_pslImage_eq` this is exactly
`N(P S L(2,F))`. -/
noncomputable def pgammaL : Subgroup (Equiv.Perm (P1 F)) := pglImage F ⊔ galSub F

/-! ## The standard Möbius elements

`transl b` is `x ↦ x + b`, `dil a` is `x ↦ a² x` and `weyl` is `x ↦ -1/x`; all three are
elements of `pslImage F`.  These are the elements out of which the argument of step A3 is
built: the translation group `U_∞`, its normalizer (the Borel), and the Weyl element. -/

section Standard

/-- The upper unitriangular matrix `!![1,b;0,1]`, as an element of `SL(2,F)`. -/
def unipotentMat (b : F) : SL(2, F) :=
  ⟨!![1, b; 0, 1], by rw [Matrix.det_fin_two]; simp⟩

/-- The diagonal matrix `!![a,0;0,a⁻¹]`, as an element of `SL(2,F)`. -/
def diagMat (a : Fˣ) : SL(2, F) :=
  ⟨!![↑a, 0; 0, ↑a⁻¹], by rw [Matrix.det_fin_two]; simp⟩

/-- The Weyl element `!![0,1;-1,0]`, as an element of `SL(2,F)`. -/
def weylMat : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two]; simp⟩

/-- Compatibility of the `PSL(2,F)`-action with the `GL(2,F)`-action on `ℙ¹(F)`. -/
lemma pslHom_toGL (g : SL(2, F)) (x : P1 F) :
    pslHom F (QuotientGroup.mk g) x = (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) F) • x := by
  rw [pslHom, MonoidHom.comp_apply, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, pglHom,
    MulAction.toPermHom_apply, MulAction.toPerm_apply]
  simp only [Matrix.ProjGenLinGroup.mk_smul]

/-- The element `x ↦ x + b` of `PSL(2,F)`, as a permutation of `ℙ¹(F)`. -/
noncomputable def transl (b : F) : Equiv.Perm (P1 F) :=
  pslHom F (QuotientGroup.mk (unipotentMat F b))

/-- The element `x ↦ a² x` of `PSL(2,F)`, as a permutation of `ℙ¹(F)`. -/
noncomputable def dil (a : Fˣ) : Equiv.Perm (P1 F) :=
  pslHom F (QuotientGroup.mk (diagMat F a))

/-- The Weyl element `x ↦ -1/x` of `PSL(2,F)`, as a permutation of `ℙ¹(F)`. -/
noncomputable def weylEl : Equiv.Perm (P1 F) :=
  pslHom F (QuotientGroup.mk (weylMat F))

lemma transl_mem (b : F) : transl F b ∈ pslImage F := ⟨_, rfl⟩
lemma dil_mem (a : Fˣ) : dil F a ∈ pslImage F := ⟨_, rfl⟩
lemma weylEl_mem : weylEl F ∈ pslImage F := ⟨_, rfl⟩

end Standard

end Work.AUTL2
