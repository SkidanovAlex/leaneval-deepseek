import Mathlib
import Submission.Work.Cohomology.CompatTrans.dualZ

/-!
# Compatible-tree copies of `dualZSplitExact` and `isIso_homologyMap_dualZMap`

The workspace contains two copies of the `ℤ`-dual constructions, `Work.Cohomology.dualZ`
(`Submission/Work/Cohomology/dualZ.lean`) and `Work.Cohomology.dualZCompat`
(`Submission/Work/Cohomology/CompatTrans/dualZ.lean`); they declare the same auxiliary names and
therefore cannot be imported together.

This file contains the two lemmas of the `dualZ`-tree that the `A+B` quasi-isomorphism needs,
restated against `dualZCompat`, so that the development can be carried out on the side of the
`CompatTrans` tree (which is the tree the cup-product files of `Work.Whitney` build on).

* `dualZSplitExactCompat` — the `ℤ`-dual of a degreewise split short exact sequence is short
  exact;
* `isIso_homologyMap_dualZMapCompat` — the `ℤ`-dual of a homotopy equivalence is a
  quasi-isomorphism.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000

open CategoryTheory AlgebraicTopology
open Work.Cohomology

namespace Work.Whitney

noncomputable section


/-!
# Exactness of the `ℤ`-dual of a degreewise split short exact sequence

Let `S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)` be a short exact sequence of chain
complexes of `ℤ`-modules whose first map `S.f` is *degreewise* a split monomorphism
(`Work.Cohomology.IsDegreewiseSplitCompat S`): for every degree `n` there is a `ℤ`-linear retraction
`r n` of `S.f.f n`.

The main result `Work.Cohomology.dualZSplitExact` says that then the `ℤ`-dual of `S` with values
in an arbitrary commutative ring `R`,

`0 ⟶ dualZCompat R S.X₃ ⟶ dualZCompat R S.X₂ ⟶ dualZCompat R S.X₁ ⟶ 0`

(`Work.Cohomology.dualZShortCompat R S`) is again short exact.

The mathematical content is degreewise: if `0 → A --f--> B --g--> C → 0` is a short exact
sequence of `ℤ`-modules and `f` admits a retraction `r` (`r ∘ f = id`), then

`0 → Hom_ℤ(C,R) --g*--> Hom_ℤ(B,R) --f*--> Hom_ℤ(A,R) → 0`

is exact in `ModuleCat R`: `g*` is injective because `g` is surjective, `f*` is surjective
because `f` is a split mono (a preimage of `ψ` is `ψ ∘ r`), and exactness in the middle is left
exactness of `Hom` (`LinearMap.exact_lcomp_of_exact_of_surjective`).  Degreewise short exactness
of a short complex of cochain complexes is equivalent to short exactness of the complex
(`HomologicalComplex.shortExact_of_degreewise_shortExact`), which finishes the proof.

The `set_option` below is the same one used in `Submission/Work/Cohomology/dualZCompat.lean`: it makes
defeq checking disregard the transparency of the module instances stored in `ModuleCat` objects.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology


noncomputable section

/-- **Degreewise short exactness of the `ℤ`-dual.**  For a short exact sequence `S` of chain
complexes of `ℤ`-modules whose first map is degreewise a split monomorphism, the `n`-th
degreewise piece of `dualZShortCompat R S` is a short exact sequence of `R`-modules. -/
theorem dualZShortCompat_degreewise_shortExact (R : Type) [CommRing R]
    {S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)} (hS : S.ShortExact)
    (hs : IsDegreewiseSplitCompat S) (n : ℕ) :
    ((dualZShortCompat R S).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).ShortExact := by
  -- degreewise data provided by the short exactness of `S`
  have hSn : (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  have hex : Function.Exact ((S.f.f n) : S.X₁.X n → S.X₂.X n) ((S.g.f n) : S.X₂.X n → S.X₃.X n) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n))).mp hSn.exact
  have hsurj : Function.Surjective ((S.g.f n) : S.X₂.X n → S.X₃.X n) :=
    (ModuleCat.epi_iff_surjective _).mp hSn.epi_g
  -- the degreewise retraction of `S.f`
  obtain ⟨r, hr⟩ := hs n
  have hr' : (ModuleCat.Hom.hom r).comp (ModuleCat.Hom.hom (S.f.f n)) = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom hr
    rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  -- identify the two maps of the degreewise dual complex with the transposes of `g` and `f`
  have hf : ((dualZShortCompat R S).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).f
      = ModuleCat.ofHom (LinearMap.lcomp R R ((S.g.f n).hom)) := by
    rw [show ((dualZShortCompat R S).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).f
        = dualZMapCompCompat R S.X₂ S.X₃ S.g n from rfl]
    apply ModuleCat.hom_ext
    ext φ
    rw [dualZMapCompCompat_apply']
    rfl
  have hg : ((dualZShortCompat R S).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).g
      = ModuleCat.ofHom (LinearMap.lcomp R R ((S.f.f n).hom)) := by
    rw [show ((dualZShortCompat R S).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n)).g
        = dualZMapCompCompat R S.X₁ S.X₂ S.f n from rfl]
    apply ModuleCat.hom_ext
    ext φ
    rw [dualZMapCompCompat_apply']
    rfl
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · -- exactness in the middle: left exactness of `Hom`
    rw [hf, hg]
    exact LinearMap.exact_lcomp_of_exact_of_surjective R hex hsurj
  · -- injectivity of the transpose of `g`
    rw [hf]
    exact LinearMap.lcomp_injective_of_surjective _ hsurj
  · -- surjectivity of the transpose of `f`, using the retraction of `f`
    rw [hg]
    intro ψ
    refine ⟨ψ.comp (ModuleCat.Hom.hom r), ?_⟩
    change (LinearMap.lcomp R R ((S.f.f n).hom))
      (ψ.comp (ModuleCat.Hom.hom r)) = ψ
    ext x
    rw [LinearMap.lcomp_apply, LinearMap.comp_apply]
    have hx : (ModuleCat.Hom.hom r) ((ModuleCat.Hom.hom (S.f.f n)) x) = x := by
      rw [← LinearMap.comp_apply, hr', LinearMap.id_apply]
    rw [hx]

end



noncomputable section

open CategoryTheory AlgebraicTopology

/-- **The `ℤ`-dual of a degreewise split short exact sequence is short exact.**

If `S` is a short exact sequence of chain complexes of `ℤ`-modules and `S.f` is degreewise a
split monomorphism, then its `ℤ`-dual `dualZShortCompat R S` with values in any commutative ring `R`
is short exact. -/
theorem dualZSplitExactCompat (R : Type) [CommRing R]
    {S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)} (hS : S.ShortExact)
    (hs : Work.Cohomology.IsDegreewiseSplitCompat S) :
    (Work.Cohomology.dualZShortCompat R S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact dualZShortCompat_degreewise_shortExact R hS hs n

end



/-!
# Dualising homotopy equivalences of `ℤ`-chain complexes with values in a ring `R`

For a chain complex `C` of `ℤ`-modules, `Work.Cohomology.dualZCompat R C` is its `R`-dual cochain
complex (`Submission/Work/Cohomology/dualZCompat.lean`), with objects `Hom_ℤ(C_n, R)` and transposed
differentials, and `Work.Cohomology.dualZMapCompat R C D f` is the contravariant action of the chain
map `f : C ⟶ D`.

The point of this file is that `dualZCompat R` turns homotopy equivalences into homotopy equivalences:
the `R`-dual of a chain homotopy `f ~ g` is a cochain homotopy `g* ~ f*` (with a sign, which the
dualisation introduces), whence a homotopy equivalence `C ≃ D` dualises to a homotopy equivalence
`D* ≃ C*`.  As a consequence a homotopy equivalence of `ℤ`-chain complexes induces an isomorphism
on the homology (= cohomology) of the dual complexes: this is the statement

* `isIso_homologyMap_dualZMap` — **the target of this file**.

The supporting material is

* `dualZHom` — the transpose `Hom_ℤ(Y,R) ⟶ Hom_ℤ(X,R)` of a morphism `X ⟶ Y` of `ℤ`-modules,
  with its (contravariant) functoriality `dualZHom_zero`, `dualZHom_neg`, `dualZHom_add`,
  `dualZHom_comp`;
* `dualZCompat_d_self`, `dualZCompat_d_sub` — the differentials of `dualZCompat R C` in the two forms needed;
* `dualZHomotopyHom`, `dualZHomotopy` — the dual of a chain homotopy;
* `homotopyEquivDualZ` — the dual of a homotopy equivalence.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology


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
theorem dualZCompat_d_self (C : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) :
    (dualZCompat R C).d i (i+1) = dualZHom R (C.d (i+1) i) := by
  rw [dualZCompat_d]
  rfl

/-- The differential of the dual complex regarded as a map `Hom(C_{i-1},R) ⟶ Hom(C_i,R)`.
This uniform form also covers `i = 0`, where both sides vanish. -/
theorem dualZCompat_d_sub (C : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) :
    (dualZCompat R C).d (i-1) i = dualZHom R (C.d i (i-1)) := by
  cases i with
  | zero =>
    show (dualZCompat R C).d 0 0 = dualZHom R (C.d 0 0)
    rw [HomologicalComplex.shape (dualZCompat R C) 0 0 (by simp [ComplexShape.up]),
        HomologicalComplex.shape C 0 0 (by simp [ComplexShape.down]), dualZHom_zero]
  | succ k =>
    rw [show (k+1) - 1 = k from rfl]
    rw [dualZCompat_d]
    rfl

/-! ## Dualising a chain homotopy -/

/-- The components of the dual of a chain homotopy: in bidegree `(i,j)` the dual of the
`(j,i)`-component of `H`, with a sign. -/
def dualZHomotopyHom {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D} (H : Homotopy f g)
    (i j : ℕ) : (dualZCompat R D).X i ⟶ (dualZCompat R C).X j :=
  - dualZHom R (H.hom j i)

/-- The "`d s`" part of the dual homotopy is the dual of the "`s d`" part of the original
homotopy (up to the sign, which the dualisation introduces). -/
theorem dualZHomotopy_dNext {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D}
    (H : Homotopy f g) (i : ℕ) :
    dNext i (dualZHomotopyHom R H) = - dualZHom R (prevD i H.hom) := by
  rw [dNext_eq (dualZHomotopyHom R H) (show (ComplexShape.up ℕ).Rel i (i+1) from rfl)]
  rw [dualZCompat_d_self R D i]
  rw [dualZHomotopyHom]
  rw [prevD_eq H.hom (show (ComplexShape.down ℕ).Rel (i+1) i from rfl)]
  rw [dualZHom_comp]
  rw [Preadditive.comp_neg]

/-- The "`s d`" part of the dual homotopy is the dual of the "`d s`" part of the original
homotopy. -/
theorem dualZHomotopy_prevD {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D}
    (H : Homotopy f g) (i : ℕ) :
    prevD i (dualZHomotopyHom R H) = - dualZHom R (dNext i H.hom) := by
  rw [prevD_nat (dualZCompat R D) (dualZCompat R C) i (dualZHomotopyHom R H)]
  rw [dualZHomotopyHom]
  rw [dualZCompat_d_sub R C i]
  rw [dNext_nat C D i H.hom]
  rw [dualZHom_comp]
  rw [Preadditive.neg_comp]

/-- **The dual of a chain homotopy.**  A homotopy `f ~ g` between chain maps dualises to a
homotopy `g* ~ f*` between the dual cochain maps. -/
def dualZHomotopy {C D : ChainComplex (ModuleCat ℤ) ℕ} {f g : C ⟶ D} (H : Homotopy f g) :
    Homotopy (dualZMapCompat R C D g) (dualZMapCompat R C D f) where
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
    HomotopyEquiv (dualZCompat R D) (dualZCompat R C) where
  hom := dualZMapCompat R C D e.hom
  inv := dualZMapCompat R D C e.inv
  homotopyHomInvId := by
    rw [(dualZMapCompat_comp R D C D e.inv e.hom).symm, ← dualZMapCompat_id]
    exact (dualZHomotopy R e.homotopyInvHomId).symm
  homotopyInvHomId := by
    rw [(dualZMapCompat_comp R C D C e.hom e.inv).symm, ← dualZMapCompat_id]
    exact (dualZHomotopy R e.homotopyHomInvId).symm

/-! ## The target statement -/

/-- **A homotopy equivalence of `ℤ`-chain complexes induces an isomorphism on the homology of
the dual complexes with coefficients in any commutative ring `R`.** -/
theorem isIso_homologyMap_dualZMapCompat (R : Type) [CommRing R]
    {C D : ChainComplex (ModuleCat ℤ) ℕ} (e : HomotopyEquiv C D) (n : ℕ) :
    CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Cohomology.dualZMapCompat R C D e.hom) n) :=
  (HomotopyEquiv.toHomologyIso (homotopyEquivDualZ R e) n).isIso_hom

end


end

end Work.Whitney
