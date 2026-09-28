import Mathlib
import Submission.Work.Cohomology.dualZ

/-!
# Dualising homotopy equivalences of `ℤ`-chain complexes with values in a ring `R`

For a chain complex `C` of `ℤ`-modules, `Work.Cohomology.dualZ R C` is its `R`-dual cochain
complex (`Submission/Work/Cohomology/dualZ.lean`), with objects `Hom_ℤ(C_n, R)` and transposed
differentials, and `Work.Cohomology.dualZMap R C D f` is the contravariant action of the chain
map `f : C ⟶ D`.

The point of this file is that `dualZ R` turns homotopy equivalences into homotopy equivalences:
the `R`-dual of a chain homotopy `f ~ g` is a cochain homotopy `g* ~ f*` (with a sign, which the
dualisation introduces), whence a homotopy equivalence `C ≃ D` dualises to a homotopy equivalence
`D* ≃ C*`.  As a consequence a homotopy equivalence of `ℤ`-chain complexes induces an isomorphism
on the homology (= cohomology) of the dual complexes: this is the statement

* `isIso_homologyMap_dualZMap` — **the target of this file**.

The supporting material is

* `dualZHom` — the transpose `Hom_ℤ(Y,R) ⟶ Hom_ℤ(X,R)` of a morphism `X ⟶ Y` of `ℤ`-modules,
  with its (contravariant) functoriality `dualZHom_zero`, `dualZHom_neg`, `dualZHom_add`,
  `dualZHom_comp`;
* `dualZ_d_self`, `dualZ_d_sub` — the differentials of `dualZ R C` in the two forms needed;
* `dualZHomotopyHom`, `dualZHomotopy` — the dual of a chain homotopy;
* `homotopyEquivDualZ` — the dual of a homotopy equivalence.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-! ## The transpose of a morphism of `ℤ`-modules -/

/-- The `R`-dual map `Hom_ℤ(Y,R) ⟶ Hom_ℤ(X,R)` induced by `m : X ⟶ Y`: precomposition with `m`.
This is `R`-linear because `R` acts on the values only. -/
def dualZHom {X Y : ModuleCat ℤ} (m : X ⟶ Y) :
    ModuleCat.of R (Y →ₗ[ℤ] R) ⟶ ModuleCat.of R (X →ₗ[ℤ] R) :=
  ModuleCat.ofHom
    { toFun := fun φ => φ.comp m.hom
      map_add' := fun φ ψ => by ext x; simp [LinearMap.comp_apply]
      map_smul' := fun a φ => by ext x; simp [LinearMap.comp_apply] }

@[simp]
theorem dualZHom_hom_apply {X Y : ModuleCat ℤ} (m : X ⟶ Y) (φ : Y →ₗ[ℤ] R) :
    (dualZHom R m).hom φ = φ.comp m.hom := rfl

theorem dualZHom_zero {X Y : ModuleCat ℤ} : dualZHom R (0 : X ⟶ Y) = 0 := by
  ext φ x; simp [dualZHom]

theorem dualZHom_neg {X Y : ModuleCat ℤ} (m : X ⟶ Y) : dualZHom R (-m) = -dualZHom R m := by
  ext φ x; simp [dualZHom]

theorem dualZHom_add {X Y : ModuleCat ℤ} (m n : X ⟶ Y) :
    dualZHom R (m + n) = dualZHom R m + dualZHom R n := by
  ext φ x; simp [dualZHom]

/-- Contravariant functoriality of `dualZHom`. -/
theorem dualZHom_comp {X Y Z : ModuleCat ℤ} (m : X ⟶ Y) (n : Y ⟶ Z) :
    dualZHom R (m ≫ n) = dualZHom R n ≫ dualZHom R m := by
  ext ψ x; simp [dualZHom, ModuleCat.hom_comp]

/-! ## The differential of the dual complex in the two forms needed below -/

/-- The differential of the dual complex in degree `i`, `Hom(C_i,R) ⟶ Hom(C_{i+1},R)`,
is the dual of `d_{i+1,i}`. -/
theorem dualZ_d_self (C : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) :
    (dualZ R C).d i (i+1) = dualZHom R (C.d (i+1) i) := by
  rw [dualZ_d]
  rfl

/-- The differential of the dual complex regarded as a map `Hom(C_{i-1},R) ⟶ Hom(C_i,R)`.
This uniform form also covers `i = 0`, where both sides vanish. -/
theorem dualZ_d_sub (C : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) :
    (dualZ R C).d (i-1) i = dualZHom R (C.d i (i-1)) := by
  cases i with
  | zero =>
    show (dualZ R C).d 0 0 = dualZHom R (C.d 0 0)
    rw [HomologicalComplex.shape (dualZ R C) 0 0 (by simp [ComplexShape.up]),
        HomologicalComplex.shape C 0 0 (by simp [ComplexShape.down]), dualZHom_zero]
  | succ k =>
    rw [show (k+1) - 1 = k from rfl]
    rw [dualZ_d]
    rfl

/-! ## Dualising a chain homotopy -/

/-- The components of the dual of a chain homotopy: in bidegree `(i,j)` the dual of the
`(j,i)`-component of `H`, with a sign. -/
def dualZHomotopyHom {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D} (H : Homotopy f g)
    (i j : ℕ) : (dualZ R D).X i ⟶ (dualZ R C).X j :=
  - dualZHom R (H.hom j i)

/-- The "`d s`" part of the dual homotopy is the dual of the "`s d`" part of the original
homotopy (up to the sign, which the dualisation introduces). -/
theorem dualZHomotopy_dNext {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D}
    (H : Homotopy f g) (i : ℕ) :
    dNext i (dualZHomotopyHom R H) = - dualZHom R (prevD i H.hom) := by
  rw [dNext_eq (dualZHomotopyHom R H) (show (ComplexShape.up ℕ).Rel i (i+1) from rfl)]
  rw [dualZ_d_self R D i]
  rw [dualZHomotopyHom]
  rw [prevD_eq H.hom (show (ComplexShape.down ℕ).Rel (i+1) i from rfl)]
  rw [dualZHom_comp]
  rw [Preadditive.comp_neg]

/-- The "`s d`" part of the dual homotopy is the dual of the "`d s`" part of the original
homotopy. -/
theorem dualZHomotopy_prevD {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D}
    (H : Homotopy f g) (i : ℕ) :
    prevD i (dualZHomotopyHom R H) = - dualZHom R (dNext i H.hom) := by
  rw [prevD_nat (dualZ R D) (dualZ R C) i (dualZHomotopyHom R H)]
  rw [dualZHomotopyHom]
  rw [dualZ_d_sub R C i]
  rw [dNext_nat C D i H.hom]
  rw [dualZHom_comp]
  rw [Preadditive.neg_comp]

/-- **The dual of a chain homotopy.**  A homotopy `f ~ g` between chain maps dualises to a
homotopy `g* ~ f*` between the dual cochain maps. -/
def dualZHomotopy {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D} (H : Homotopy f g) :
    Homotopy (dualZMap R C D g) (dualZMap R C D f) where
  hom := dualZHomotopyHom R H
  zero i j h := by
    show dualZHomotopyHom R H i j = 0
    rw [dualZHomotopyHom, H.zero j i h, dualZHom_zero, neg_zero]
  comm i := by
    rw [dualZHomotopy_dNext R H i, dualZHomotopy_prevD R H i]
    change dualZHom R (g.f i)
      = - dualZHom R (prevD i H.hom) + - dualZHom R (dNext i H.hom) + dualZHom R (f.f i)
    rw [← neg_add, ← dualZHom_add, ← dualZHom_neg, ← dualZHom_add]
    congr 1
    rw [H.comm i]
    abel

/-- **The dual of a homotopy equivalence.**  The `R`-dual cochain complex is contravariantly
functorial on the homotopy category, so a homotopy equivalence `C ≃ D` of `ℤ`-chain complexes
induces a homotopy equivalence `D* ≃ C*`. -/
def homotopyEquivDualZ {C D : ChainComplex (ModuleCat ℤ) ℕ} (e : HomotopyEquiv C D) :
    HomotopyEquiv (dualZ R D) (dualZ R C) where
  hom := dualZMap R C D e.hom
  inv := dualZMap R D C e.inv
  homotopyHomInvId := by
    rw [(dualZMap_comp R D C D e.inv e.hom).symm, ← dualZMap_id]
    exact (dualZHomotopy R e.homotopyInvHomId).symm
  homotopyInvHomId := by
    rw [(dualZMap_comp R C D C e.hom e.inv).symm, ← dualZMap_id]
    exact (dualZHomotopy R e.homotopyHomInvId).symm

/-! ## The target statement -/

/-- **A homotopy equivalence of `ℤ`-chain complexes induces an isomorphism on the homology of
the dual complexes with coefficients in any commutative ring `R`.** -/
theorem isIso_homologyMap_dualZMap (R : Type) [CommRing R]
    {C D : ChainComplex (ModuleCat ℤ) ℕ} (e : HomotopyEquiv C D) (n : ℕ) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.dualZMap R C D e.hom) n) :=
  (HomotopyEquiv.toHomologyIso (homotopyEquivDualZ R e) n).isIso_hom

end

end Work.Cohomology
