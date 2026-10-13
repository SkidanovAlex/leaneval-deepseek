import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSEQ0.Gamma
import Submission.Work.DSF1.Cech.CoaugCycle
import Submission.Work.DSEQ0.cechPresheaf_isSheaf
import Submission.Work.DSEQ0.cechZ_homology_zero_iso_ker

/-!
# `H⁰` of the Čech complex of `𝒪_X` (as `A`-modules) is `Γ(X, 𝒪_X)`

This file proves `Work.DSEQ0.cechZ_homology_zero_iso_gamma`: for a scheme `X` with
`f : X ⟶ Spec A`, a *covering* family of opens `U : ι → X.Opens`, the degree-`0`
cohomology of the Čech complex `DSMap.cechZ A X f U` of the structure sheaf (with its
`A`-module structure induced by `f`) is the ring of global sections `Γ(X, ⊤)`, as
`A`-modules for the algebra structure `A → Γ(X,⊤)` induced by `f`.

The proof has three parts.

* The purely homological part: `H⁰` of the `ℤ`-indexed Čech complex is the kernel of
  `d 0 1` (`Work.DSEQ0.cechZ_homology_zero_iso_ker`).
* The degree-`0` differential of the Čech complex is computed componentwise
  (`Work.DSF1.Cech.cech_d_comp_π`): for `j : Fin 2 → ι` the `j`-th component of
  `d 0 1 y` is the difference of the two restrictions of the components of `y` indexed
  by the functions `fun _ => j 0` and `fun _ => j 1`.
* The sheaf condition: this matching condition says exactly that the family of
  components of `y` (over the cover by the degree-`0` opens `∏ᶜ (U ∘ x)`, `x : Fin 1 → ι`)
  glues, and glue uniquely, to a global section.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

universe a

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

variable {A : Type a} [CommRing A] {X : Scheme.{a}} {f : X ⟶ Spec (.of A)} {ι : Type a}
  {U : ι → X.Opens}

section Transport

/-- Transport of sections of a presheaf of modules along an equality of open sets:
`trv Q h : Q(V) ⟶ Q(W)` for `h : V = W`; it moves an element of `Q(V)` to the "same"
element of `Q(W)`. -/
noncomputable def trv (Q : X.Opensᵒᵖ ⥤ ModuleCat A) {V W : X.Opens} (h : V = W) :
    Q.obj (op V) ⟶ Q.obj (op W) :=
  Q.map (eqToHom (congrArg op h))

@[simp]
lemma trv_rfl (Q : X.Opensᵒᵖ ⥤ ModuleCat A) (V : X.Opens) : trv Q (rfl : V = V) = 𝟙 _ := by
  simp [trv]

lemma trv_comp (Q : X.Opensᵒᵖ ⥤ ModuleCat A) {V W Z : X.Opens} (h : V = W) (h' : W = Z) :
    trv Q h ≫ trv Q h' = trv Q (h.trans h') := by
  subst h h'
  simp

/-- The two transports along an equality and its inverse are mutually inverse. -/
lemma trv_inv (Q : X.Opensᵒᵖ ⥤ ModuleCat A) {V W : X.Opens} (h : V = W) :
    trv Q h ≫ trv Q h.symm = 𝟙 _ := by
  subst h; simp

lemma trv_inv' (Q : X.Opensᵒᵖ ⥤ ModuleCat A) {V W : X.Opens} (h : V = W) :
    trv Q h.symm ≫ trv Q h = 𝟙 _ := by
  subst h; simp

/-- **The transport lemma.**  Two morphisms of `X.Opens` with equal (up to transport)
source and target give the same map on sections, after transport.  This holds because
the homs of a poset category are subsingletons. -/
lemma trv_map_op (Q : X.Opensᵒᵖ ⥤ ModuleCat A) {V W V' W' : X.Opens}
    (hV : V = V') (hW : W = W') (g : V ⟶ W) (g' : V' ⟶ W') :
    Q.map g.op ≫ trv Q hV = trv Q hW ≫ Q.map g'.op := by
  rw [trv, trv, ← Q.map_comp, ← Q.map_comp,
    Subsingleton.elim (g.op ≫ eqToHom (congrArg op hV)) (eqToHom (congrArg op hW) ≫ g'.op)]

end Transport

section Cech

/-- Products in `Opens X` are infima. -/
lemma pi_eq_iInf {α : Type*} (V : α → X.Opens) : ∏ᶜ V = ⨅ i, V i := by
  refine le_antisymm (le_iInf fun i => ?_) ?_
  · exact CategoryTheory.leOfHom (Pi.π V i)
  · exact CategoryTheory.leOfHom (Pi.lift fun i => homOfLE (iInf_le V i))

/-- The degree-`0` open attached to `x : Fin 1 → ι` is the open indexed by the value of
`x`. -/
lemma Eobj_zero_eq (x : Fin 1 → ι) : DSF1.Cech.Eobj U 0 x = U (x 0) := by
  show (∏ᶜ fun a : Fin 1 => U (x a)) = U (x 0)
  rw [pi_eq_iInf]
  refine le_antisymm (iInf_le _ 0) (le_iInf fun a => ?_)
  rw [Subsingleton.elim a 0]

/-- The degree-`1` open attached to `j : Fin 2 → ι` is the intersection of the two
opens indexed by the values of `j`. -/
lemma Eobj_one_eq (j : Fin 2 → ι) : DSF1.Cech.Eobj U 1 j = U (j 0) ⊓ U (j 1) := by
  show (∏ᶜ fun a : Fin 2 => U (j a)) = U (j 0) ⊓ U (j 1)
  rw [pi_eq_iInf]
  refine le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1)) (le_iInf fun a => ?_)
  fin_cases a <;> simp

/-- The two-element family `![i, i']`. -/
abbrev pair (i i' : ι) : Fin 2 → ι := Fin.cases i (fun _ => i')

@[simp]
lemma pair_zero (i i' : ι) : pair i i' 0 = i := rfl

@[simp]
lemma pair_one (i i' : ι) : pair i i' 1 = i' := rfl

/-- The index map of the `0`-th coface in degree `0`. -/
lemma map_delta_zero_f (j : Fin 2 → ι) :
    ((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f j = (fun _ : Fin 1 => j 1) := by
  show (FormalCoproduct.mapPower (FormalCoproduct.mk ι U)
    (SimplexCategory.δ 0).toOrderHom.toFun).f j = (fun _ : Fin 1 => j 1)
  rw [FormalCoproduct.mapPower_f]
  funext b
  fin_cases b
  rfl

/-- The index map of the `1`-st coface in degree `0`. -/
lemma map_delta_one_f (j : Fin 2 → ι) :
    ((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f j = (fun _ : Fin 1 => j 0) := by
  show (FormalCoproduct.mapPower (FormalCoproduct.mk ι U)
    (SimplexCategory.δ 1).toOrderHom.toFun).f j = (fun _ : Fin 1 => j 0)
  rw [FormalCoproduct.mapPower_f]
  funext b
  fin_cases b
  rfl

@[simp]
lemma map_delta_zero_f_pair (i i' : ι) :
    ((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f (pair i i') = (fun _ : Fin 1 => i') := by
  rw [map_delta_zero_f]
  rfl

@[simp]
lemma map_delta_one_f_pair (i i' : ι) :
    ((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f (pair i i') = (fun _ : Fin 1 => i) := by
  rw [map_delta_one_f]
  rfl

@[simp]
lemma Eobj_zero_const (i : ι) : DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i) = U i := by
  rw [Eobj_zero_eq]

@[simp]
lemma Eobj_one_pair (i i' : ι) : DSF1.Cech.Eobj U 1 (pair i i') = U i ⊓ U i' := by
  rw [Eobj_one_eq, pair_zero, pair_one]

end Cech

section Main

/-- **Component formula for the degree-`0` differential of the Čech complex.**  The
`j`-th component of `d 0 1 y` is the alternating sum of the restrictions of the
components of `y` at the two deleted indices. -/
lemma cech_d01_apply (j : Fin 2 → ι) (y : ↥((DSMap.cech A X f U).X 0)) :
    (Pi.π (fun x => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 1 x))) j)
        (((DSMap.cech A X f U).d 0 1).hom y)
      = (ConcreteCategory.hom ((DSMap.cechPresheaf A X f).map
            (((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).φ j).op))
          ((Pi.π (fun x => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x)))
            (((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f j)) y)
        - (ConcreteCategory.hom ((DSMap.cechPresheaf A X f).map
            (((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).φ j).op))
          ((Pi.π (fun x => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x)))
            (((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f j)) y) := by
  have hsum : (∑ a : Fin 2, (-1 : ℤ) ^ (a : ℕ) •
      (Pi.π (fun y => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 y)))
          (((DSF1.Cech.E U).map (SimplexCategory.δ a).op).f j) ≫
        (DSMap.cechPresheaf A X f).map (((DSF1.Cech.E U).map (SimplexCategory.δ a).op).φ j).op))
      = (Pi.π (fun y => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 y)))
            (((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f j) ≫
          (DSMap.cechPresheaf A X f).map
            (((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).φ j).op)
        - (Pi.π (fun y => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 y)))
            (((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f j) ≫
          (DSMap.cechPresheaf A X f).map
            (((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).φ j).op) := by
    rw [Fin.sum_univ_two, sub_eq_add_neg]
    simp
  have h := congrArg (fun (m : (DSMap.cech A X f U).X 0 ⟶
      (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 1 j))) =>
        (ConcreteCategory.hom m) y)
    (Work.DSF1.Cech.cech_d_comp_π U (DSMap.cechPresheaf A X f) 0 j)
  rw [hsum] at h
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_sub, LinearMap.sub_apply] at h
  exact h

/-- **The kernel of `d 0 1`, componentwise.**  If `y` is a cocycle in degree `0`, then
for every degree-`1` index `j` the two restrictions of the corresponding components of
`y` agree. -/
lemma cech_d01_ker_apply (y : ↥((DSMap.cech A X f U).X 0))
    (hy : ((DSMap.cech A X f U).d 0 1).hom y = 0) (j : Fin 2 → ι) :
    (ConcreteCategory.hom ((DSMap.cechPresheaf A X f).map
        (((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).φ j).op))
        ((Pi.π (fun x => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x)))
          (((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f j)) y)
      = (ConcreteCategory.hom ((DSMap.cechPresheaf A X f).map
        (((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).φ j).op))
        ((Pi.π (fun x => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x)))
          (((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f j)) y) := by
  have h2 : (Pi.π (fun x => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 1 x))) j)
      (((DSMap.cech A X f U).d 0 1).hom y) = 0 := by rw [hy]; simp
  rw [cech_d01_apply, sub_eq_zero] at h2
  exact h2

/-- Two elements of a product in `ModuleCat A` are equal as soon as all their components
are. -/
lemma ModuleCat.pi_ext {β : Type*} {F : β → ModuleCat A} {x y : ↥(∏ᶜ F)}
    (h : ∀ b, (Pi.π F b) x = (Pi.π F b) y) : x = y := by
  have h1 : (ConcreteCategory.hom (ModuleCat.piIsoPi F).hom) x
      = (ConcreteCategory.hom (ModuleCat.piIsoPi F).hom) y := by
    funext b
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    exact h b
  have h2 := congrArg (ConcreteCategory.hom (ModuleCat.piIsoPi F).inv) h1
  rwa [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply,
      ← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply] at h2

end Main

section Compat

/-- The cover of `X` by the degree-`0` opens of the Čech nerve of `U`. -/
noncomputable abbrev Vc (U : ι → X.Opens) : (Fin 1 → ι) → X.Opens := fun a => DSF1.Cech.Eobj U 0 a

/-- The family of Čech degree-`0` terms attached to the cover `Vc U`. -/
noncomputable abbrev Cech0 (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) {ι : Type a}
    (U : ι → X.Opens) : (Fin 1 → ι) → ModuleCat A :=
  fun a => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 a))

/-- The degree-`0` Čech datum of a cochain `y`, as a family over the cover `Vc U`. -/
noncomputable def sfam (y : ↥((DSMap.cech A X f U).X 0)) (a : Fin 1 → ι) :
    ↥((DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 a))) :=
  (Pi.π (fun x : Fin 1 → ι => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x))) a) y

/-- Transport of a degree-`0` component along an equality of indices. -/
lemma trv_index (y : ↥((DSMap.cech A X f U).X 0)) {a b : Fin 1 → ι} (h : a = b) :
    (ConcreteCategory.hom (trv (DSMap.cechPresheaf A X f)
        (congrArg (fun t => DSF1.Cech.Eobj U 0 t) h))) ((sfam (A := A) (X := X) (f := f)
          (U := U) y) a) = (sfam (A := A) (X := X) (f := f) (U := U) y) b := by
  have htrv : trv (DSMap.cechPresheaf A X f) (congrArg (fun t => DSF1.Cech.Eobj U 0 t) h)
      = eqToHom (congrArg (fun t : Fin 1 → ι =>
          (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 t))) h) := by
    rw [trv, eqToHom_map]
  have hπ := Pi.π_comp_eqToHom (fun x : Fin 1 → ι =>
      (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x))) h
  have h2 := congrArg (fun (m : (DSMap.cech A X f U).X 0 ⟶
      (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 b))) =>
        (ConcreteCategory.hom m) y) hπ
  rw [ConcreteCategory.comp_apply] at h2
  rw [← htrv] at h2
  exact h2

/-- The cover `Vc U` covers `⊤` whenever `U` does. -/
lemma iSup_Vc (hcov : ⨆ i, U i = ⊤) : (⨆ a : Fin 1 → ι, Vc U a) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hcov]
  refine iSup_le fun i => ?_
  rw [← Eobj_zero_const (U := U) i]
  exact le_iSup (fun a : Fin 1 → ι => DSF1.Cech.Eobj U 0 a) (fun _ : Fin 1 => i)

/-- **The matching condition.**  A cocycle in degree `0` of the Čech complex gives a
compatible family over the cover by the degree-`0` opens. -/
lemma cech_isCompatible (y : ↥((DSMap.cech A X f U).X 0))
    (hy : ((DSMap.cech A X f U).d 0 1).hom y = 0) :
    TopCat.Presheaf.IsCompatible (DSMap.cechPresheaf A X f) (Vc U)
      (sfam (A := A) (X := X) (f := f) (U := U) y) := by
  intro a a'
  have h0 : ((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f (pair (a 0) (a' 0)) = a' := by
    rw [map_delta_zero_f]
    funext b
    rw [Subsingleton.elim b 0]
    rfl
  have h1 : ((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f (pair (a 0) (a' 0)) = a := by
    rw [map_delta_one_f]
    funext b
    rw [Subsingleton.elim b 0]
    rfl
  have hWt : DSF1.Cech.Eobj U 1 (pair (a 0) (a' 0)) = Vc U a ⊓ Vc U a' := by
    rw [Eobj_one_eq, pair_zero, pair_one]
    exact congrArg₂ (· ⊓ ·) (Eobj_zero_eq (U := U) a).symm (Eobj_zero_eq (U := U) a').symm
  have hV0 : DSF1.Cech.Eobj U 0 (((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f
      (pair (a 0) (a' 0))) = Vc U a' := congrArg (fun t => DSF1.Cech.Eobj U 0 t) h0
  have hV1 : DSF1.Cech.Eobj U 0 (((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f
      (pair (a 0) (a' 0))) = Vc U a := congrArg (fun t => DSF1.Cech.Eobj U 0 t) h1
  have T0 := trv_map_op (DSMap.cechPresheaf A X f) hWt hV0
    (((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).φ (pair (a 0) (a' 0)))
    (TopologicalSpace.Opens.infLERight (Vc U a) (Vc U a'))
  have T1 := trv_map_op (DSMap.cechPresheaf A X f) hWt hV1
    (((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).φ (pair (a 0) (a' 0)))
    (TopologicalSpace.Opens.infLELeft (Vc U a) (Vc U a'))
  have hj := cech_d01_ker_apply (A := A) (X := X) (f := f) (U := U) y hy (pair (a 0) (a' 0))
  have key := congrArg (ConcreteCategory.hom (trv (DSMap.cechPresheaf A X f) hWt)) hj
  have e0 : (ConcreteCategory.hom (trv (DSMap.cechPresheaf A X f) hWt))
        ((ConcreteCategory.hom ((DSMap.cechPresheaf A X f).map
          (((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).φ (pair (a 0) (a' 0))).op))
          ((Pi.π (fun x : Fin 1 → ι => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x)))
            (((DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f (pair (a 0) (a' 0)))) y))
      = (ConcreteCategory.hom ((DSMap.cechPresheaf A X f).map
          (TopologicalSpace.Opens.infLERight (Vc U a) (Vc U a')).op))
          (sfam (A := A) (X := X) (f := f) (U := U) y a') := by
    rw [← ConcreteCategory.comp_apply, T0, ConcreteCategory.comp_apply]
    congr 1
    exact trv_index (A := A) (X := X) (f := f) (U := U) y h0
  have e1 : (ConcreteCategory.hom (trv (DSMap.cechPresheaf A X f) hWt))
        ((ConcreteCategory.hom ((DSMap.cechPresheaf A X f).map
          (((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).φ (pair (a 0) (a' 0))).op))
          ((Pi.π (fun x : Fin 1 → ι => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x)))
            (((DSF1.Cech.E U).map (SimplexCategory.δ 1).op).f (pair (a 0) (a' 0)))) y))
      = (ConcreteCategory.hom ((DSMap.cechPresheaf A X f).map
          (TopologicalSpace.Opens.infLELeft (Vc U a) (Vc U a')).op))
          (sfam (A := A) (X := X) (f := f) (U := U) y a) := by
    rw [← ConcreteCategory.comp_apply, T1, ConcreteCategory.comp_apply]
    congr 1
    exact trv_index (A := A) (X := X) (f := f) (U := U) y h1
  exact e1.symm.trans (key.symm.trans e0)

end Compat

section Glue

/-- **The gluing step.**  Every cocycle in degree `0` of the Čech complex is the
coaugmentation of a global section. -/
lemma exists_coaug_of_mem_ker (hcov : ⨆ i, U i = ⊤) (y : ↥((DSMap.cech A X f U).X 0))
    (hy : ((DSMap.cech A X f U).d 0 1).hom y = 0) :
    ∃ t : ↥((DSMap.cechPresheaf A X f).obj (op ⊤)),
      (ConcreteCategory.hom (Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f))) t = y := by
  haveI : TopCat.Presheaf.IsSheaf (DSMap.cechPresheaf A X f) := cechPresheaf_isSheaf A X f
  let F : TopCat.Sheaf (ModuleCat A) X.toPresheafedSpace :=
    ⟨DSMap.cechPresheaf A X f, cechPresheaf_isSheaf A X f⟩
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' (C := ModuleCat A) F
    (fun x : Fin 1 → ι => DSF1.Cech.Eobj U 0 x) ⊤
    (fun a => CategoryTheory.homOfLE (le_top : DSF1.Cech.Eobj U 0 a ≤ ⊤))
    (le_of_eq (iSup_Vc (U := U) hcov).symm)
    (sfam (A := A) (X := X) (f := f) (U := U) y)
    (cech_isCompatible (A := A) (X := X) (f := f) (U := U) y hy)
  refine ⟨t, ?_⟩
  have hcoaug : Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f)
      = Pi.lift (fun x : Fin 1 → ι => (DSMap.cechPresheaf A X f).map
          (CategoryTheory.homOfLE (le_top : DSF1.Cech.Eobj U 0 x ≤ ⊤)).op) := rfl
  refine ModuleCat.pi_ext (A := A)
    (F := fun x : Fin 1 → ι => (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x)))
    (fun a => ?_)
  rw [hcoaug]
  erw [Pi.lift_comp_π_apply]
  exact ht a

/-- **The coaugmentation is injective.**  A global section whose restriction to every
member of the cover vanishes is zero. -/
lemma coaug_injective (hcov : ⨆ i, U i = ⊤)
    (t : ↥((DSMap.cechPresheaf A X f).obj (op ⊤)))
    (h : (ConcreteCategory.hom (Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f))) t = 0) :
    t = 0 := by
  haveI : TopCat.Presheaf.IsSheaf (DSMap.cechPresheaf A X f) := cechPresheaf_isSheaf A X f
  let F : TopCat.Sheaf (ModuleCat A) X.toPresheafedSpace :=
    ⟨DSMap.cechPresheaf A X f, cechPresheaf_isSheaf A X f⟩
  have hcoaug : Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f)
      = Pi.lift (fun x : Fin 1 → ι => (DSMap.cechPresheaf A X f).map
          (CategoryTheory.homOfLE (le_top : DSF1.Cech.Eobj U 0 x ≤ ⊤)).op) := rfl
  have hres : ∀ a : Fin 1 → ι, (ConcreteCategory.hom ((DSMap.cechPresheaf A X f).map
      (CategoryTheory.homOfLE (le_top : DSF1.Cech.Eobj U 0 a ≤ ⊤)).op)) t = 0 := by
    intro a
    have h2 : (Pi.π (fun x : Fin 1 → ι =>
          (DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x))) a)
        ((ConcreteCategory.hom (Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f))) t) = 0 := by
      rw [h]; simp
    rw [hcoaug] at h2
    erw [Pi.lift_comp_π_apply] at h2
    exact h2
  obtain ⟨s, hs, huniq⟩ := TopCat.Sheaf.existsUnique_gluing' (C := ModuleCat A) F
    (fun x : Fin 1 → ι => DSF1.Cech.Eobj U 0 x) ⊤
    (fun a => CategoryTheory.homOfLE (le_top : DSF1.Cech.Eobj U 0 a ≤ ⊤))
    (le_of_eq (iSup_Vc (U := U) hcov).symm)
    (fun x : Fin 1 → ι => (0 : ↥((DSMap.cechPresheaf A X f).obj (op (DSF1.Cech.Eobj U 0 x)))))
    (by intro a b; simp)
  rw [huniq t hres, huniq 0 (fun a => by simp)]

end Glue

section Final

/-- The structure map of the presheaf of `A`-module sections at `⊤` is `DSMap.phi`. -/
lemma phiU_top_eq : DSMap.phiU A X f ⊤ = DSMap.phi A X f := by
  show (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op).hom.comp (DSMap.phi A X f)
    = DSMap.phi A X f
  rw [show homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤) = 𝟙 (⊤ : X.Opens) from Subsingleton.elim _ _,
    op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The `A`-module structure on `Γ(X, ⊤)` induced by `cechPresheaf` is the one given by
the hypothesis `hφ`. -/
lemma smul_gammaTop [Algebra A (Work.DSEQ0.GammaTop X)]
    (hφ : ∀ a : A, algebraMap A (Work.DSEQ0.GammaTop X) a = DSMap.phi A X f a) :
    ∀ (a : A) (y : Work.DSEQ0.GammaTop X),
      (letI : Algebra A (Work.DSEQ0.GammaTop X) := (DSMap.phiU A X f ⊤).toAlgebra; a • y) = a • y := by
  intro a y
  have h1 : (letI : Algebra A (Work.DSEQ0.GammaTop X) := (DSMap.phiU A X f ⊤).toAlgebra; a • y)
      = (DSMap.phiU A X f ⊤) a * y := RingHom.smul_toAlgebra (DSMap.phiU A X f ⊤) a y
  rw [h1, Algebra.smul_def, hφ a, phiU_top_eq]


/-- **The kernel of the degree-`0` differential of the Čech complex is the ring of
global sections.** -/
lemma ker_d01_iso_gamma [Algebra A (Work.DSEQ0.GammaTop X)]
    (hφ : ∀ a : A, algebraMap A (Work.DSEQ0.GammaTop X) a = DSMap.phi A X f a)
    (hcov : ⨆ i, U i = ⊤) :
    Nonempty (↥(LinearMap.ker ((DSMap.cech A X f U).d 0 1).hom) ≃ₗ[A]
      Work.DSEQ0.GammaTop X) := by
  have hmem : ∀ t : ↥((DSMap.cechPresheaf A X f).obj (op ⊤)),
      ((DSMap.cech A X f U).d 0 1).hom
        ((ConcreteCategory.hom (Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f))) t) = 0 := by
    intro t
    have h := congrArg (fun (m : (DSMap.cechPresheaf A X f).obj (op ⊤) ⟶
        (DSMap.cech A X f U).X 1) => (ConcreteCategory.hom m) t)
      (Work.DSF1.Cech.CoaugCycle U (DSMap.cechPresheaf A X f))
    rw [ConcreteCategory.comp_apply] at h
    exact h
  refine ⟨(LinearEquiv.ofBijective
    ({ toFun := fun t => ⟨(ConcreteCategory.hom
          (Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f))) t, hmem t⟩
       map_add' := fun x y => Subtype.ext
          ((Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f)).hom.map_add x y)
       map_smul' := fun a x => Subtype.ext (by
          show (ConcreteCategory.hom (Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f))) (a • x)
            = a • (ConcreteCategory.hom (Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f))) x
          rw [← smul_gammaTop (A := A) (X := X) (f := f) hφ a x]
          exact (Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f)).hom.map_smul a x) }
      : Work.DSEQ0.GammaTop X →ₗ[A]
        ↥(LinearMap.ker ((DSMap.cech A X f U).d 0 1).hom)) ⟨?_, ?_⟩).symm⟩
  · intro x y hxy
    have hxy' : (ConcreteCategory.hom (Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f))) x
        = (ConcreteCategory.hom (Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f))) y := by
      simpa using congrArg Subtype.val hxy
    have hx : (ConcreteCategory.hom
        (Work.DSF1.Cech.coaug U (DSMap.cechPresheaf A X f))) (x - y) = 0 := by
      rw [map_sub, hxy', sub_self]
    exact sub_eq_zero.mp (coaug_injective (A := A) (X := X) (f := f) (U := U) hcov (x - y) hx)
  · intro y
    obtain ⟨t, ht⟩ := exists_coaug_of_mem_ker (A := A) (X := X) (f := f) (U := U) hcov y.1 y.2
    exact ⟨t, Subtype.ext ht⟩

end Final

section Target

theorem cechZ_homology_zero_iso_gamma (A : Type a) [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} [Finite ι] (U : ι → X.Opens)
    (hcov : ⨆ i, U i = ⊤) [Algebra A (Work.DSEQ0.GammaTop X)]
    (hφ : ∀ a : A, algebraMap A (Work.DSEQ0.GammaTop X) a = DSMap.phi A X f a) :
    Nonempty ((DSMap.cechZ A X f U).homology 0 ≃ₗ[A] Work.DSEQ0.GammaTop X) := by
  obtain ⟨e1⟩ := cechZ_homology_zero_iso_ker (A := A) X f U
  obtain ⟨e2⟩ := ker_d01_iso_gamma (A := A) (X := X) (f := f) (U := U) hφ hcov
  exact ⟨e1.trans e2⟩

end Target

end Work.DSEQ0
