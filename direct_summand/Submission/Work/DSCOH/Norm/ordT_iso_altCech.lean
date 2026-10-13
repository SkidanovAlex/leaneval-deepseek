import Mathlib
import Submission.Work.DSCOH.Norm.SemiOrd
import Submission.Work.DSCOH.Norm.Maps
import Submission.Work.DSCOH.AltCechComplex
import Submission.Work.DSCOH.altCech_d_comp

namespace Work.DSCOH.Norm

universe u v w

open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators

namespace OrdT

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
variable [HasProducts (ModuleCat A)]

/-! ## The index bijection: strictly increasing tuples vs. `(n+1)`-element subsets -/

/-- The image (range) of a strictly increasing tuple, as a finset of cardinality `n+1`. -/
noncomputable def idxOfFam {n : ℕ} (x : OrdIdx ι n) : {S : Finset ι // S.card = n+1} :=
  ⟨Finset.univ.image x.val,
    Finset.card_image_of_injective _ x.property.injective ▸ by simp⟩

@[simp]
lemma idxOfFam_val {n : ℕ} (x : OrdIdx ι n) :
    (idxOfFam x).1 = Finset.univ.image x.val := rfl

/-- The increasing enumeration of an `(n+1)`-element subset, as a strictly increasing tuple. -/
noncomputable def famOfIdx {n : ℕ} (S : {S : Finset ι // S.card = n+1}) : OrdIdx ι n :=
  ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩

@[simp]
lemma famOfIdx_val {n : ℕ} (S : {S : Finset ι // S.card = n+1}) :
    (famOfIdx S).val = S.1.orderEmbOfFin S.2 := rfl

lemma card_image_ordIdx {n : ℕ} (x : OrdIdx ι n) :
    (Finset.univ.image x.val).card = n+1 :=
  Finset.card_image_of_injective _ x.property.injective ▸ by simp

lemma idxOfFam_famOfIdx {n : ℕ} (S : {S : Finset ι // S.card = n+1}) :
    idxOfFam (famOfIdx S) = S := by
  refine Subtype.ext ?_
  show Finset.univ.image (S.1.orderEmbOfFin S.2) = S.1
  have h := Finset.range_orderEmbOfFin S.1 S.2
  apply Finset.coe_injective
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact h

lemma famOfIdx_idxOfFam {n : ℕ} (x : OrdIdx ι n) : famOfIdx (idxOfFam x) = x := by
  refine Subtype.ext ?_
  show (Finset.univ.image x.val).orderEmbOfFin (card_image_ordIdx x) = x.val
  exact (Finset.orderEmbOfFin_unique (card_image_ordIdx x)
    (fun a => Finset.mem_image_of_mem _ (Finset.mem_univ a)) x.property).symm

lemma mem_idxOfFam {n : ℕ} (x : OrdIdx ι n) (i : ι) :
    i ∈ (idxOfFam x).1 ↔ ∃ a, x.val a = i := by
  simp [idxOfFam]

lemma idxOfFam_del {n : ℕ} (x : OrdIdx ι (n+1)) (b : Fin (n+2)) :
    (idxOfFam ⟨del x.val b, strictMono_del x.val b x.property⟩).1
      = (idxOfFam x).1.erase (x.val b) := by
  show Finset.univ.image (del x.val b) = (Finset.univ.image x.val).erase (x.val b)
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne b a (x.property.injective h), ⟨b.succAbove a, rfl⟩⟩
  · rintro ⟨hne, a, rfl⟩
    obtain ⟨a', ha'⟩ := Fin.exists_succAbove_eq (h := fun h => hne (congrArg x.val h))
    exact ⟨a', by rw [del_apply, ← ha']⟩

lemma card_filter_idxOfFam_lt {n : ℕ} (x : OrdIdx ι (n+1)) (b : Fin (n+2)) :
    (((idxOfFam x).1.filter (fun j => j < x.val b))).card = (b : ℕ) := by
  show ((Finset.univ.image x.val).filter (fun j => j < x.val b)).card = (b : ℕ)
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injOn (f := x.val)
    (s := Finset.univ.filter (fun a : Fin (n+2) => x.val a < x.val b))
    (fun a _ c _ h => x.property.injective h)]
  have hf : (Finset.univ.filter (fun a : Fin (n+2) => x.val a < x.val b)) =
      Finset.univ.filter (fun a : Fin (n+2) => a < b) := by
    apply Finset.filter_congr
    intro a _
    exact x.property.lt_iff_lt
  rw [hf]
  have : (Finset.univ.filter (fun a : Fin (n+2) => a < b)) = Finset.Iio b := by
    ext a
    simp [Finset.mem_Iio]
  rw [this, Fin.card_Iio]

/-! ## The open attached to a tuple -/

lemma finset_prod_eq_inf {n : ℕ} (f : Fin n → Opens X) :
    (∏ᶜ f) = Finset.univ.inf f := by
  apply le_antisymm
  · exact Finset.le_inf (fun a _ => leOfHom (Pi.π f a))
  · exact leOfHom (Pi.lift (fun a => homOfLE (Finset.inf_le (Finset.mem_univ a))))

variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)

lemma tupleOp_eq_inf {n : ℕ} (x : Fin (n+1) → ι) :
    tupleOp U x = (Finset.univ.image x).inf U := by
  change (∏ᶜ fun a : Fin (n+1) => U (x a)) = (Finset.univ.image x).inf U
  rw [finset_prod_eq_inf]
  exact (Finset.inf_image _ _ _).symm

lemma inf_eq_tupleOp {n : ℕ} (S : {S : Finset ι // S.card = n+1}) :
    S.1.inf U = tupleOp U (famOfIdx S).val := by
  have h : S.1 = Finset.univ.image (famOfIdx S).val :=
    (congrArg Subtype.val (idxOfFam_famOfIdx S)).symm
  rw [h, ← tupleOp_eq_inf U (famOfIdx S).val]

/-! ## General transport lemmas -/

/-- `congrArg` of a composition, with a definitionally-transparent composition. -/
lemma congrArg_comp_aux {α β γ : Type*} (f : α → β) (g : β → γ) {a b : α} (h : a = b) :
    congrArg (fun x => g (f x)) h = congrArg g (congrArg f h) := by
  cases h; rfl

/-- Pushing an `eqToHom` through a projection of a product. -/
lemma Pi_π_comp_eqToHom {β : Type*} {C : Type*} [Category C] (Y : β → C) [HasProduct Y]
    {a b : β} (h : a = b) :
    Pi.π Y a ≫ eqToHom (congrArg Y h) = Pi.π Y b := by
  subst h; simp

/-- The same, in the other direction. -/
lemma eqToHom_comp_Pi_π {β : Type*} {C : Type*} [Category C] (Y : β → C) [HasProduct Y]
    {a b : β} (h : a = b) :
    Pi.π Y b ≫ eqToHom (congrArg Y h.symm) = Pi.π Y a := by
  subst h; simp

/-- An `eqToHom` in a preorder category is the `homOfLE` of the induced inequality. -/
lemma eqToHom_eq_homOfLE {V W : Opens X} (h : V = W) :
    eqToHom h = homOfLE (le_of_eq h) := Subsingleton.elim _ _

/-- Two parallel morphisms of opens induce the same morphism after applying `P` (up to `op`). -/
lemma Pmap_op_congr {V W : Opens X} (φ ψ : V ⟶ W) : P.map φ.op = P.map ψ.op := by
  rw [Subsingleton.elim φ ψ]

/-- An `eqToHom` between the values of a presheaf along an equality of opens is the restriction
map. -/
lemma eqToHom_PobjFun {V W : Opens X} (h : V = W) :
    eqToHom (congrArg (fun V : Opens X => P.obj (op V)) h) = P.map (eqToHom h.symm).op := by
  subst h; simp

/-- The same as `eqToHom_PobjFun`, in the `homOfLE` form. -/
lemma eqToHom_PobjFun' {V W : Opens X} (h : V = W) :
    eqToHom (congrArg (fun V : Opens X => P.obj (op V)) h) =
      P.map (homOfLE (le_of_eq h.symm)).op :=
  (eqToHom_PobjFun P h).trans
    (congrArg (fun φ : W ⟶ V => P.map φ.op) (eqToHom_eq_homOfLE h.symm))

/-! ## The term families of the two complexes -/

/-- The open attached to a strictly increasing tuple. -/
noncomputable abbrev tupFam (n : ℕ) : OrdIdx ι n → Opens X := fun z => tupleOp U z.val

/-- The open attached to an `(n+1)`-element subset. -/
noncomputable abbrev infFam (n : ℕ) : {S : Finset ι // S.card = n+1} → Opens X := fun S => S.1.inf U

/-- The `n`-th family of the ordered Čech complex: the sections over the intersection of the
opens of a strictly increasing tuple. -/
noncomputable abbrev ordFam (n : ℕ) : OrdIdx ι n → ModuleCat A := fun z => tupleMod P U z.val

/-- The `n`-th family of the alternating Čech complex: the sections over the intersection of
the opens of an `(n+1)`-element subset. -/
noncomputable abbrev altFam (n : ℕ) : {S : Finset ι // S.card = n+1} → ModuleCat A :=
  fun S => P.obj (op (S.1.inf U))

/-- `congrArg` of the ordered family is `congrArg` of the presheaf applied to the tuple. -/
lemma congrArg_ordFam (n : ℕ) {z w : OrdIdx ι n} (h : z = w) :
    congrArg (ordFam P U n) h =
      congrArg (fun V : Opens X => P.obj (op V)) (congrArg (tupFam U n) h) := by
  cases h; rfl

/-- `congrArg` of the alternating family is `congrArg` of the presheaf applied to the subset. -/
lemma congrArg_altFam (n : ℕ) {S S' : {S : Finset ι // S.card = n+1}} (h : S = S') :
    congrArg (altFam P U n) h =
      congrArg (fun V : Opens X => P.obj (op V)) (congrArg (infFam U n) h) := by
  cases h; rfl

/-- An `eqToHom` between ordered components is a restriction map. -/
lemma eqToHom_ordFam (n : ℕ) {z w : OrdIdx ι n} (h : z = w) :
    eqToHom (congrArg (ordFam P U n) h) =
      P.map (homOfLE (le_of_eq (congrArg (tupFam U n) h).symm)).op :=
  (congrArg eqToHom (congrArg_ordFam P U n h)).trans
    (eqToHom_PobjFun' P (congrArg (tupFam U n) h))

/-- An `eqToHom` between alternating components is a restriction map. -/
lemma eqToHom_altFam (n : ℕ) {S S' : {S : Finset ι // S.card = n+1}} (h : S = S') :
    eqToHom (congrArg (altFam P U n) h) =
      P.map (homOfLE (le_of_eq (congrArg (infFam U n) h).symm)).op :=
  (congrArg eqToHom (congrArg_altFam P U n h)).trans
    (eqToHom_PobjFun' P (congrArg (infFam U n) h))

/-- The restriction map from the tuple component to the subset component. -/
noncomputable def compT (n : ℕ) (z : OrdIdx ι n) :
    ordFam P U n z ⟶ altFam P U n (idxOfFam z) :=
  P.map (homOfLE (le_of_eq (tupleOp_eq_inf U z.val).symm)).op

/-- The restriction map from the tuple component to the subset component, expressed in terms of
the subset index (using the increasing enumeration). -/
noncomputable def compS (n : ℕ) (S : {S : Finset ι // S.card = n+1}) :
    ordFam P U n (famOfIdx S) ⟶ altFam P U n S :=
  compT P U n (famOfIdx S) ≫ eqToHom (congrArg (altFam P U n) (idxOfFam_famOfIdx S))

/-- The inverse restriction map. -/
noncomputable def compTinv (n : ℕ) (z : OrdIdx ι n) :
    altFam P U n (idxOfFam z) ⟶ ordFam P U n z :=
  P.map (homOfLE (le_of_eq (tupleOp_eq_inf U z.val))).op

/-- The increasing enumeration of the finset obtained by erasing the `b`-th smallest element of
the range of a strictly increasing tuple is the deletion of the `b`-th entry. -/
lemma famOfIdx_erase {n : ℕ} (T : {S : Finset ι // S.card = n+2}) (b : Fin (n+2))
    (D : {S : Finset ι // S.card = n+1}) (hD : D.1 = T.1.erase ((famOfIdx T).val b)) :
    famOfIdx D =
      ⟨del (famOfIdx T).val b, strictMono_del (famOfIdx T).val b (famOfIdx T).property⟩ := by
  have himg : Finset.univ.image (del (famOfIdx T).val b)
      = T.1.erase ((famOfIdx T).val b) := by
    have h1 := idxOfFam_del (x := famOfIdx T) b
    rw [show (idxOfFam (famOfIdx T)).1 = T.1 from
      congrArg Subtype.val (idxOfFam_famOfIdx T)] at h1
    exact h1
  refine Subtype.ext ?_
  show D.1.orderEmbOfFin D.2 = del (famOfIdx T).val b
  exact (Finset.orderEmbOfFin_unique D.2 (fun a => by
      rw [hD, ← himg]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ a))
    (strictMono_del (famOfIdx T).val b (famOfIdx T).property)).symm

/-- `compS` followed by `compTinv` is the transport along the round trip `famOfIdx (idxOfFam z) = z`. -/
lemma compS_compTinv_cancel (n : ℕ) (z : OrdIdx ι n) :
    compS P U n (idxOfFam z) ≫ compTinv P U n z =
      eqToHom (congrArg (ordFam P U n) (famOfIdx_idxOfFam z)) := by
  have hβ := eqToHom_altFam P U n (idxOfFam_famOfIdx (idxOfFam z))
  have hα := eqToHom_ordFam P U n (famOfIdx_idxOfFam z)
  simp only [hα, hβ, compS, compT, compTinv]
  simp only [← Functor.map_comp, ← op_comp]
  exact Pmap_op_congr P _ _

/-- `compTinv` followed by `compS` is the transport along the round trip `idxOfFam (famOfIdx S) = S`. -/
lemma compTinv_compS_cancel (n : ℕ) (S : {S : Finset ι // S.card = n+1}) :
    compTinv P U n (famOfIdx S) ≫ compS P U n S =
      eqToHom (congrArg (altFam P U n) (idxOfFam_famOfIdx S)) := by
  have hβ := eqToHom_altFam P U n (idxOfFam_famOfIdx S)
  simp only [hβ, compS, compT, compTinv]
  simp only [← Functor.map_comp, ← op_comp]
  exact Pmap_op_congr P _ _

/-- The compatibility of the component isomorphisms with the two differentials: the two ways of
"delete the `b`-th entry and restrict" agree, up to the identification of the ordered index
`famOfIdx D` (the increasing enumeration of the erased subset) with the tuple `del x b`. -/
lemma compS_res (n : ℕ) (T : {S : Finset ι // S.card = n+2}) (b : Fin (n+2))
    (D : {S : Finset ι // S.card = n+1}) (hD : D.1 = T.1.erase ((famOfIdx T).val b))
    (hres : T.1.inf U ≤ D.1.inf U) :
    eqToHom (congrArg (ordFam P U n) (famOfIdx_erase T b D hD).symm) ≫
        compS P U n D ≫ P.map (homOfLE hres).op =
      resDel P U (famOfIdx T).val b ≫ compS P U (n+1) T := by
  have hα : eqToHom (congrArg (ordFam P U n) (famOfIdx_erase T b D hD).symm) =
      P.map (homOfLE (le_of_eq (congrArg (tupFam U n)
        (famOfIdx_erase T b D hD).symm).symm)).op :=
    eqToHom_ordFam P U n (famOfIdx_erase T b D hD).symm
  have hβ : eqToHom (congrArg (altFam P U n) (idxOfFam_famOfIdx D)) =
      P.map (homOfLE (le_of_eq (congrArg (infFam U n)
        (idxOfFam_famOfIdx D)).symm)).op :=
    eqToHom_altFam P U n (idxOfFam_famOfIdx D)
  have hγ : eqToHom (congrArg (altFam P U (n+1)) (idxOfFam_famOfIdx T)) =
      P.map (homOfLE (le_of_eq (congrArg (infFam U (n+1))
        (idxOfFam_famOfIdx T)).symm)).op :=
    eqToHom_altFam P U (n+1) (idxOfFam_famOfIdx T)
  simp only [hα, hβ, hγ, compS, compT, resDel]
  simp only [← Functor.map_comp, ← op_comp]
  exact Pmap_op_congr P _ _

/-- The pairing of an element of `T` with the corresponding entry of the increasing
enumeration of `T`. -/
noncomputable abbrev pairIdx {n : ℕ} (T : {S : Finset ι // S.card = n+2}) (b : Fin (n+2)) : T.1 :=
  ⟨(famOfIdx T).val b, by
    rw [← congrArg Subtype.val (idxOfFam_famOfIdx T)]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ b)⟩

/-- Sums over the elements of a finset can be reindexed by the increasing enumeration. -/
lemma sum_attach_eq_sum_fin {M : Type*} [AddCommMonoid M] {n : ℕ}
    (T : {S : Finset ι // S.card = n+2}) (G : T.1 → M) :
    (∑ i ∈ T.1.attach, G i) = ∑ b : Fin (n+2), G (pairIdx T b) := by
  have hinj : Function.Injective (pairIdx T) := by
    intro a c h
    exact (famOfIdx T).property.injective (congrArg Subtype.val h)
  have hsurj : ∀ i : T.1, ∃ b : Fin (n+2), pairIdx T b = i := by
    intro i
    have hi : i.1 ∈ Finset.univ.image (famOfIdx T).val := by
      rw [show Finset.univ.image (famOfIdx T).val = T.1 from by
        rw [← idxOfFam_val (famOfIdx T)]
        exact congrArg Subtype.val (idxOfFam_famOfIdx T)]
      exact i.2
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hi
    exact ⟨b, Subtype.ext hb⟩
  have hmap : (Finset.univ : Finset (Fin (n+2))).map
      (Function.Embedding.mk (pairIdx T) hinj) = T.1.attach := by
    ext i
    rw [Finset.mem_map]
    constructor
    · rintro ⟨b, -, hb⟩
      exact Finset.mem_attach T.1 i
    · intro _
      obtain ⟨b, hb⟩ := hsurj i
      exact ⟨b, Finset.mem_univ b, hb⟩
  rw [← hmap, Finset.sum_map]
  simp

/-- The projection of the ordered term onto the component of a tuple. -/
noncomputable def ordComp (n : ℕ) (z : OrdIdx ι n) : ordTerm P U n ⟶ tupleMod P U z.val :=
  Pi.π (fun y : OrdIdx ι n => tupleMod P U y.val) z

/-- The projection of the alternating term onto the component of a subset. -/
noncomputable def altProj (n : ℕ) (S : {S : Finset ι // S.card = n+1}) :
    (altCech P U).X n ⟶ altFam P U n S :=
  (ModuleCat.piIsoPi (altFam P U n)).inv ≫ Pi.π (altFam P U n) S

/-- The `altProj` of a subset is the same as the concrete projection. -/
lemma altProj_eq_ofHom (n : ℕ) (S : {S : Finset ι // S.card = n+1}) :
    altProj P U n S = ModuleCat.ofHom (LinearMap.proj
      (φ := fun S : {S : Finset ι // S.card = n+1} => P.obj (op (S.1.inf U))) S) :=
  ModuleCat.piIsoPi_inv_kernel_ι (altFam P U n) S

/-- The transport of `ordComp` along an equality of tuples. -/
lemma ordComp_eqToHom (n : ℕ) {z w : OrdIdx ι n} (h : z = w) :
    ordComp P U n z ≫ eqToHom (congrArg (ordFam P U n) h) = ordComp P U n w := by
  rw [ordComp, ordComp]
  exact Pi_π_comp_eqToHom (ordFam P U n) h

/-- The transport of `ordComp` along an equality of tuples (folding form). -/
lemma eqToHom_ordComp (n : ℕ) {z w : OrdIdx ι n} (h : z = w) :
    ordComp P U n z = ordComp P U n w ≫ eqToHom (congrArg (ordFam P U n) h.symm) := by
  rw [ordComp, ordComp]
  exact (eqToHom_comp_Pi_π (ordFam P U n) h).symm

/-- The reindexing map from the ordered to the alternating complex. -/
noncomputable def psiHom (n : ℕ) : ordTerm P U n ⟶ (altCech P U).X n :=
  Pi.lift (fun S : {S : Finset ι // S.card = n+1} =>
      ordComp P U n (famOfIdx S) ≫ compS P U n S) ≫
    (ModuleCat.piIsoPi (altFam P U n)).hom

/-- The inverse of the reindexing map. -/
noncomputable def psiInv (n : ℕ) : (altCech P U).X n ⟶ ordTerm P U n :=
  (ModuleCat.piIsoPi (altFam P U n)).inv ≫
    Pi.lift (fun z : OrdIdx ι n => Pi.π (altFam P U n) (idxOfFam z) ≫ compTinv P U n z)

/-- The `S`-component of `psiHom`. -/
lemma psiHom_π (n : ℕ) (S : {S : Finset ι // S.card = n+1}) :
    psiHom P U n ≫ altProj P U n S = ordComp P U n (famOfIdx S) ≫ compS P U n S := by
  rw [psiHom, altProj]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Pi.lift_comp_π, ordComp]

/-- The `S`-component of `psiHom`, with a further factor. -/
lemma psiHom_π_assoc (n : ℕ) (S : {S : Finset ι // S.card = n+1}) {W : ModuleCat A}
    (g : altFam P U n S ⟶ W) :
    psiHom P U n ≫ altProj P U n S ≫ g = ordComp P U n (famOfIdx S) ≫ compS P U n S ≫ g := by
  rw [← Category.assoc, psiHom_π, Category.assoc]

/-- The `z`-component of `psiInv`. -/
lemma psiInv_π (n : ℕ) (z : OrdIdx ι n) :
    psiInv P U n ≫ ordComp P U n z = altProj P U n (idxOfFam z) ≫ compTinv P U n z := by
  rw [psiInv]
  simp only [ordComp, altProj, Category.assoc, Pi.lift_comp_π]

/-- Extensionality for maps into the ordered term. -/
lemma ordTerm_ext {n : ℕ} {D : ModuleCat A} {f g : D ⟶ ordTerm P U n}
    (h : ∀ z : OrdIdx ι n, f ≫ ordComp P U n z = g ≫ ordComp P U n z) : f = g :=
  Pi.hom_ext (f := fun y : OrdIdx ι n => tupleMod P U y.val) f g fun z => h z

/-- Extensionality for maps into the alternating term. -/
lemma altTerm_ext {n : ℕ} {D : ModuleCat A} {f g : D ⟶ (altCech P U).X n}
    (h : ∀ S : {S : Finset ι // S.card = n+1}, f ≫ altProj P U n S = g ≫ altProj P U n S) :
    f = g := by
  apply ModuleCat.hom_ext
  ext x
  funext S
  have h' : (f ≫ altProj P U n S).hom x = (g ≫ altProj P U n S).hom x := by rw [h S]
  rw [altProj, ModuleCat.piIsoPi_inv_kernel_ι] at h'
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] at h'
  exact h'

/-- `psiHom` and `psiInv` are inverse. -/
lemma psiHom_psiInv (n : ℕ) : psiHom P U n ≫ psiInv P U n = 𝟙 (ordTerm P U n) := by
  apply ordTerm_ext
  intro z
  rw [Category.assoc, psiInv_π, psiHom_π_assoc, Category.id_comp,
    compS_compTinv_cancel]
  exact Pi_π_comp_eqToHom (ordFam P U n) (famOfIdx_idxOfFam z)

/-- `psiInv` and `psiHom` are inverse. -/
lemma psiInv_psiHom (n : ℕ) : psiInv P U n ≫ psiHom P U n = 𝟙 ((altCech P U).X n) := by
  apply altTerm_ext
  intro S
  rw [Category.assoc, psiHom_π, Category.id_comp, ← Category.assoc, psiInv_π,
    Category.assoc, compTinv_compS_cancel]
  exact congrArg (fun t => (ModuleCat.piIsoPi (altFam P U n)).inv ≫ t)
    (Pi_π_comp_eqToHom (altFam P U n) (idxOfFam_famOfIdx S))

/-- The reindexing isomorphism between the ordered and the alternating Čech complexes. -/
noncomputable def psiIso (n : ℕ) : ordTerm P U n ≅ (altCech P U).X n :=
  Iso.mk (psiHom P U n) (psiInv P U n) (psiHom_psiInv P U n) (psiInv_psiHom P U n)

/-- The `z`-component of the ordered Čech differential. -/
lemma ordD_π (n : ℕ) (z : OrdIdx ι (n+1)) :
    ordD P U n ≫ Pi.π (ordFam P U (n+1)) z =
      ∑ b : Fin (n+2), (-1 : ℤ) ^ (b : ℕ) •
        (Pi.π (ordFam P U n) ⟨del z.val b, strictMono_del z.val b z.property⟩ ≫
          resDel P U z.val b) :=
  Pi.lift_comp_π _ z

/-- The `z`-component of the ordered Čech differential. -/
lemma ordD_ordComp (n : ℕ) (z : OrdIdx ι (n+1)) :
    ordD P U n ≫ ordComp P U (n+1) z =
      ∑ b : Fin (n+2), (-1 : ℤ) ^ (b : ℕ) •
        (ordComp P U n ⟨del z.val b, strictMono_del z.val b z.property⟩ ≫ resDel P U z.val b) := by
  rw [ordComp, ordD]
  exact Pi.lift_comp_π _ _

/-- The termwise comparison of the two differentials, in the form needed for the reindexed sum. -/
lemma ordComp_term_eq (n : ℕ) (T : {S : Finset ι // S.card = n+2}) (b : Fin (n+2))
    (D : {S : Finset ι // S.card = n+1}) (hD : D.1 = T.1.erase ((famOfIdx T).val b))
    (hres : T.1.inf U ≤ D.1.inf U) :
    ordComp P U n (famOfIdx D) ≫ compS P U n D ≫ P.map (homOfLE hres).op =
      ordComp P U n ⟨del (famOfIdx T).val b,
          strictMono_del (famOfIdx T).val b (famOfIdx T).property⟩ ≫
        resDel P U (famOfIdx T).val b ≫ compS P U (n+1) T := by
  calc ordComp P U n (famOfIdx D) ≫ compS P U n D ≫ P.map (homOfLE hres).op
      = (ordComp P U n ⟨del (famOfIdx T).val b,
            strictMono_del (famOfIdx T).val b (famOfIdx T).property⟩ ≫
          eqToHom (congrArg (ordFam P U n) (famOfIdx_erase T b D hD).symm)) ≫
          compS P U n D ≫ P.map (homOfLE hres).op :=
        congrArg (fun t => t ≫ compS P U n D ≫ P.map (homOfLE hres).op)
          (eqToHom_ordComp P U n (famOfIdx_erase T b D hD))
    _ = ordComp P U n ⟨del (famOfIdx T).val b,
            strictMono_del (famOfIdx T).val b (famOfIdx T).property⟩ ≫
          (eqToHom (congrArg (ordFam P U n) (famOfIdx_erase T b D hD).symm) ≫
            compS P U n D ≫ P.map (homOfLE hres).op) := by rw [Category.assoc]
    _ = ordComp P U n ⟨del (famOfIdx T).val b,
            strictMono_del (famOfIdx T).val b (famOfIdx T).property⟩ ≫
          (resDel P U (famOfIdx T).val b ≫ compS P U (n+1) T) :=
        congrArg (fun t => ordComp P U n ⟨del (famOfIdx T).val b,
            strictMono_del (famOfIdx T).val b (famOfIdx T).property⟩ ≫ t)
          (compS_res P U n T b D hD hres)
    _ = ordComp P U n ⟨del (famOfIdx T).val b,
            strictMono_del (famOfIdx T).val b (famOfIdx T).property⟩ ≫
          resDel P U (famOfIdx T).val b ≫ compS P U (n+1) T := rfl

/-- The `T`-component of the alternating Čech differential. -/
lemma altCech_d_altProj (n : ℕ) (T : {S : Finset ι // S.card = n+2}) :
    (altCech P U).d n (n+1) ≫ altProj P U (n+1) T =
      ∑ i ∈ T.1.attach, ((-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card) •
        (altProj P U n ⟨T.1.erase i.1,
            by rw [Finset.card_erase_of_mem i.2, T.2]; omega⟩ ≫
          P.map (homOfLE (Finset.le_inf fun k hk => Finset.inf_le (Finset.mem_of_mem_erase hk))).op) := by
  refine (congrArg (fun t => (altCech P U).d n (n+1) ≫ t) (altProj_eq_ofHom P U (n+1) T)).trans ?_
  rw [altCech_d_comp P U n T]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact congrArg (fun t => ((-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card) •
      (t ≫ P.map (homOfLE (Finset.le_inf fun k hk => Finset.inf_le (Finset.mem_of_mem_erase hk))).op))
    (altProj_eq_ofHom P U n ⟨T.1.erase i.1,
      by rw [Finset.card_erase_of_mem i.2, T.2]; omega⟩).symm

end OrdT

open OrdT

/-- The tuple-indexed "ordered" Čech complex (`Work.DSCOH.Norm.ordTerm` / `ordD`, whose terms
are products over the *strictly increasing* tuples `Fin (n+1) → ι`) is isomorphic, as a cochain
complex, to the alternating Čech complex `Work.DSCOH.altCech` (whose terms are products over the
`(n+1)`-element subsets `S ⊆ ι` of `P (⋂_{i ∈ S} U i)`).

The isomorphism is the reindexing by the increasing enumeration of a subset
(`Finset.orderIsoOfFin`), whose inverse sends a strictly increasing tuple to its range; it has to
be checked that the two differentials correspond, i.e. that deleting the `a`-th entry of a
strictly increasing tuple corresponds to erasing the `a`-th smallest element of the subset, with
the same sign `(-1)^a = (-1)^{#{j ∈ S : j < i_a}}`. -/
theorem ordT_iso_altCech {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : Opposite (TopologicalSpace.Opens X) ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) :
    ∃ e : ∀ n : ℕ, Work.DSCOH.Norm.ordTerm P U n ≅ (Work.DSCOH.altCech P U).X n,
      ∀ n : ℕ,
        (e n).hom ≫ (Work.DSCOH.altCech P U).d n (n + 1) =
          Work.DSCOH.Norm.ordD P U n ≫ (e (n + 1)).hom := by
  classical
  refine ⟨fun n => psiIso P U n, ?_⟩
  intro n
  show psiHom P U n ≫ (altCech P U).d n (n+1) = ordD P U n ≫ psiHom P U (n+1)
  apply altTerm_ext
  intro T
  -- the right-hand side
  have hR : (ordD P U n ≫ psiHom P U (n+1)) ≫ altProj P U (n+1) T
      = ∑ b : Fin (n+2), (-1 : ℤ) ^ (b : ℕ) •
          (ordComp P U n ⟨del (famOfIdx T).val b,
              strictMono_del (famOfIdx T).val b (famOfIdx T).property⟩ ≫
            resDel P U (famOfIdx T).val b ≫ compS P U (n+1) T) := by
    rw [Category.assoc, psiHom_π, ← Category.assoc, ordD_ordComp, Preadditive.sum_comp]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Preadditive.zsmul_comp, Category.assoc]
  -- the left-hand side
  have hL : (psiHom P U n ≫ (altCech P U).d n (n+1)) ≫ altProj P U (n+1) T
      = ∑ i ∈ T.1.attach, ((-1 : ℤ) ^ ((T.1.filter fun j => j < i.1)).card) •
          (ordComp P U n (famOfIdx (⟨T.1.erase i.1,
              by rw [Finset.card_erase_of_mem i.2, T.2]; omega⟩ :
                {S : Finset ι // S.card = n+1})) ≫
            compS P U n (⟨T.1.erase i.1,
              by rw [Finset.card_erase_of_mem i.2, T.2]; omega⟩ :
                {S : Finset ι // S.card = n+1}) ≫
            P.map (homOfLE (Finset.le_inf fun k hk =>
              Finset.inf_le (Finset.mem_of_mem_erase hk))).op) := by
    rw [Category.assoc, altCech_d_altProj, Preadditive.comp_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Preadditive.comp_zsmul, psiHom_π_assoc]
  rw [hL, hR]
  rw [sum_attach_eq_sum_fin]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  -- the sign agrees
  have hsign : (((T.1.filter fun j => j < (pairIdx T b).1)).card) = (b : ℕ) := by
    have h1 : (pairIdx T b).1 = (famOfIdx T).val b := rfl
    rw [h1, ← congrArg Subtype.val (idxOfFam_famOfIdx T)]
    exact card_filter_idxOfFam_lt (famOfIdx T) b
  rw [hsign]
  refine congrArg (fun t => (-1 : ℤ) ^ (b : ℕ) • t) ?_
  -- the restriction maps agree
  exact ordComp_term_eq P U n T b _ rfl _

end Work.DSCOH.Norm
