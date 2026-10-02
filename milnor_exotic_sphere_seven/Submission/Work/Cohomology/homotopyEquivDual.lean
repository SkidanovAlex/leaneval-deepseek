import Mathlib
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.DualComplexMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Dualising homotopy equivalences of chain complexes

For a chain complex `C` of `R`-modules, `Work.Cohomology.dualComplex R C` is its `R`-dual
cochain complex, and `Work.Cohomology.dualComplexMap R f` is the contravariant action of a chain
map.  This file proves that this construction is well behaved with respect to homotopies: a
homotopy `f ~ g` dualises to a homotopy `g* ~ f*` (with the expected sign), and consequently a
homotopy equivalence `C ≃ D` dualises to a homotopy equivalence `D* ≃ C*`.

The main results are

* `dualHom` — the `R`-dual `Hom(Y,R) ⟶ Hom(X,R)` of a morphism `X ⟶ Y` of `R`-modules,
  together with its (contravariant) functoriality `dualHom_zero`, `dualHom_add`, `dualHom_neg`,
  `dualHom_comp`;
* `dualHomotopy` — **the dual of a chain homotopy**;
* `homotopyEquivDual` — **the dual of a homotopy equivalence**.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-- The `R`-dual map `Hom_R(Y,R) ⟶ Hom_R(X,R)` induced by `m : X ⟶ Y`: precomposition with `m`. -/
def dualHom {X Y : ModuleCat R} (m : X ⟶ Y) :
    ModuleCat.of R (Y →ₗ[R] R) ⟶ ModuleCat.of R (X →ₗ[R] R) :=
  ModuleCat.ofHom m.hom.dualMap

@[simp]
theorem dualHom_hom_apply {X Y : ModuleCat R} (m : X ⟶ Y) (ψ : Y →ₗ[R] R) :
    (dualHom R m).hom ψ = ψ.comp m.hom := rfl

theorem dualHom_zero {X Y : ModuleCat R} : dualHom R (0 : X ⟶ Y) = 0 := by
  ext ψ x; simp [dualHom]

theorem dualHom_neg {X Y : ModuleCat R} (m : X ⟶ Y) : dualHom R (-m) = - dualHom R m := by
  ext ψ x; simp [dualHom]

theorem dualHom_add {X Y : ModuleCat R} (m n : X ⟶ Y) :
    dualHom R (m + n) = dualHom R m + dualHom R n := by
  ext ψ x; simp [dualHom]

/-- Contravariant functoriality of `dualHom`. -/
theorem dualHom_comp {X Y Z : ModuleCat R} (m : X ⟶ Y) (n : Y ⟶ Z) :
    dualHom R (m ≫ n) = dualHom R n ≫ dualHom R m := by
  ext ψ x; simp [dualHom, ModuleCat.hom_comp]

/-- The differential of the dual complex in degree `i`, `Hom(C_i,R) ⟶ Hom(C_{i+1},R)`,
is the dual of `d_{i+1,i}`. -/
theorem dualComplex_d_self (C : ChainComplex (ModuleCat R) ℕ) (i : ℕ) :
    (dualComplex R C).d i (i+1) = dualHom R (C.d (i+1) i) := by
  simp only [dualComplex, CochainComplex.of_d]
  rfl

/-- The differential of the dual complex regarded as a map `Hom(C_{i-1},R) ⟶ Hom(C_i,R)`.
This uniform form also covers `i = 0` where both sides vanish. -/
theorem dualComplex_d_sub (C : ChainComplex (ModuleCat R) ℕ) (i : ℕ) :
    (dualComplex R C).d (i-1) i = dualHom R (C.d i (i-1)) := by
  cases i with
  | zero =>
    show (dualComplex R C).d 0 0 = dualHom R (C.d 0 0)
    rw [HomologicalComplex.shape (dualComplex R C) 0 0 (by simp [ComplexShape.up]),
        HomologicalComplex.shape C 0 0 (by simp [ComplexShape.down]), dualHom_zero]
  | succ k =>
    rw [show (k+1) - 1 = k from rfl]
    simp only [dualComplex, CochainComplex.of_d]
    rfl

/-- The components of the dual of a chain homotopy: in bidegree `(i,j)` the dual of the
`(j,i)`-component of `H`, with a sign. -/
def dualHomotopyHom {C D : ChainComplex (ModuleCat R) ℕ} {f g : C ⟶ D} (H : Homotopy f g)
    (i j : ℕ) : (dualComplex R D).X i ⟶ (dualComplex R C).X j :=
  - dualHom R (H.hom j i)

/-- The "`d s`" part of the dual homotopy is the dual of the "`s d`" part of the original
homotopy (up to the sign, which the dualisation introduces). -/
theorem dualHomotopy_dNext {C D : ChainComplex (ModuleCat R) ℕ} {f g : C ⟶ D}
    (H : Homotopy f g) (i : ℕ) :
    dNext i (dualHomotopyHom R H) = - dualHom R (prevD i H.hom) := by
  rw [dNext_eq (dualHomotopyHom R H) (show (ComplexShape.up ℕ).Rel i (i+1) from rfl)]
  rw [dualComplex_d_self R D i]
  rw [dualHomotopyHom]
  rw [prevD_eq H.hom (show (ComplexShape.down ℕ).Rel (i+1) i from rfl)]
  rw [dualHom_comp]
  rw [Preadditive.comp_neg]

/-- The "`s d`" part of the dual homotopy is the dual of the "`d s`" part of the original
homotopy. -/
theorem dualHomotopy_prevD {C D : ChainComplex (ModuleCat R) ℕ} {f g : C ⟶ D}
    (H : Homotopy f g) (i : ℕ) :
    prevD i (dualHomotopyHom R H) = - dualHom R (dNext i H.hom) := by
  rw [prevD_nat (dualComplex R D) (dualComplex R C) i (dualHomotopyHom R H)]
  rw [dualHomotopyHom]
  rw [dualComplex_d_sub R C i]
  rw [dNext_nat C D i H.hom]
  rw [dualHom_comp]
  rw [Preadditive.neg_comp]

/-- **The dual of a chain homotopy.**  A homotopy `f ~ g` between chain maps dualises to a
homotopy `g* ~ f*` between the dual cochain maps. -/
def dualHomotopy {C D : ChainComplex (ModuleCat R) ℕ} {f g : C ⟶ D} (H : Homotopy f g) :
    Homotopy (dualComplexMap R C D g) (dualComplexMap R C D f) where
  hom := dualHomotopyHom R H
  zero i j h := by
    show dualHomotopyHom R H i j = 0
    rw [dualHomotopyHom, H.zero j i h, dualHom_zero, neg_zero]
  comm i := by
    rw [dualHomotopy_dNext R H i, dualHomotopy_prevD R H i]
    change dualHom R (g.f i)
      = - dualHom R (prevD i H.hom) + - dualHom R (dNext i H.hom) + dualHom R (f.f i)
    rw [← neg_add, ← dualHom_add, ← dualHom_neg, ← dualHom_add]
    congr 1
    rw [H.comm i]
    abel

/-- **The dual of a homotopy equivalence.**  The `R`-dual cochain complex is contravariantly
functorial on the homotopy category, so a homotopy equivalence `C ≃ D` induces a homotopy
equivalence `D* ≃ C*`. -/
theorem homotopyEquivDual {C D : ChainComplex (ModuleCat R) ℕ} (e : HomotopyEquiv C D) :
    Nonempty (HomotopyEquiv (dualComplex R D) (dualComplex R C)) := by
  refine ⟨{
    hom := dualComplexMap R C D e.hom
    inv := dualComplexMap R D C e.inv
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_ }⟩
  · rw [← dualComplexMap_comp (R := R) (f := e.inv) (g := e.hom), ← dualComplexMap_id]
    exact (dualHomotopy R e.homotopyInvHomId).symm
  · rw [← dualComplexMap_comp (R := R) (f := e.hom) (g := e.inv), ← dualComplexMap_id]
    exact (dualHomotopy R e.homotopyHomInvId).symm

end

end Work.Cohomology
