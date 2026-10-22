/-
# AREA CONDMV — Mayer–Vietoris for `ℤ[−]` on open covers

Let `X` be a topological space with open subsets `U`, `V` covering `X`.  The main result of this
file is that the square of light condensed sets

```
  (U ∩ V)_cond  ⟶  V_cond
       |                  |
       v                  v
    U_cond       ⟶    X_cond
```

is a pushout (and hence, after applying the free light condensed abelian group functor, a pushout
of light condensed abelian groups, see `Work.CONDMV.isPushout_free`).

The proof follows `REFS/01` F11: every continuous map `S → X` from a light profinite set `S`
refines, along a clopen partition `S = A ⊔ B` (produced by
`Work.CONDMV.Refine.exists_isClopen_partition_of_open_cover`), to a pair of maps `A → U`,
`B → V`.  The universal property of the pushout is then proved by gluing sections of an arbitrary
light condensed set over such clopen partitions, which is the content of
`Work.CONDMV.ClopenSheaf.restrict_bijective_of_clopen_partition`.

Main definitions and results:

* `glueSec` — the glued section of a light condensed set over `S`;
* `glueSec_naturality` — naturality of the glued section;
* `glueHom` — the induced morphism `X_cond ⟶ Z` gluing maps out of `U_cond` and `V_cond`;
* `iU_glueHom`, `iV_glueHom`, `glueHom_unique` — its universal property;
* `isPushout_condOf` — the pushout statement in light condensed sets;
* `isPushout_free` — the pushout statement in light condensed abelian groups.

The statement `Submission.Blueprint.CondMVProp` is proved in `Submission.Work.CONDMV.Main`.
-/
import Submission.Work.CONDMV.Basic
import Submission.Work.CONDMV.Refine.exists_isClopen_partition_of_open_cover
import Submission.Work.CONDMV.ClopenSheaf.restrict_bijective_of_clopen_partition

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

namespace Work.CONDMV

variable {X : TopCat.{0}} {U V : Set X} {S T P : LightProfinite.{0}}

/-- A section of `condOf X` at `S`, as an actual continuous map. -/
def asCMap (f : (condOf X).obj.obj (op S)) : C(↥S, ↥X) := f

@[simp]
lemma condOf_map_apply (f : (condOf X).obj.obj (op S)) (v : T ⟶ S) :
    (condOf X).obj.map v.op f =
      ⟨fun t => asCMap f (v t), (asCMap f).continuous.comp v.hom.hom.continuous⟩ := rfl

/-- The map `T ⟶ S → X` underlying a section of `condOf X` at `S`, as an element of the
sections of `setCond U` at `T`, assuming its image lies in `U`. -/
def toUMap (U : Set X) (f : (condOf X).obj.obj (op S)) (v : T ⟶ S)
    (hv : ∀ t : ↥T, asCMap f (v t) ∈ U) : (setCond U).obj.obj (op T) :=
  ⟨fun t => ⟨asCMap f (v t), hv t⟩,
    Continuous.subtype_mk ((asCMap f).continuous.comp v.hom.hom.continuous) hv⟩

/-- The map `T ⟶ S → X` underlying a section of `condOf X` at `S`, as an element of the
sections of `setCond V` at `T`, assuming its image lies in `V`. -/
def toVMap (V : Set X) (f : (condOf X).obj.obj (op S)) (v : T ⟶ S)
    (hv : ∀ t : ↥T, asCMap f (v t) ∈ V) : (setCond V).obj.obj (op T) :=
  ⟨fun t => ⟨asCMap f (v t), hv t⟩,
    Continuous.subtype_mk ((asCMap f).continuous.comp v.hom.hom.continuous) hv⟩

/-- The map `T → U ∩ V` underlying a section of `condOf X` at `S` whose image on `T` lies in
`U ∩ V`. -/
def toWMap (U V : Set X) (f : (condOf X).obj.obj (op S)) (v : T ⟶ S)
    (hv : ∀ t : ↥T, asCMap f (v t) ∈ U ∩ V) : (setCond (U ∩ V)).obj.obj (op T) :=
  ⟨fun t => ⟨asCMap f (v t), hv t⟩,
    Continuous.subtype_mk ((asCMap f).continuous.comp v.hom.hom.continuous) hv⟩

/-- A clopen partition of `S` refining the open cover `U ∪ V = X`, for a fixed map `S → X`. -/
structure RefinePart (U V : Set X) (hUV : U ∪ V = (Set.univ : Set X)) {S : LightProfinite.{0}}
    (f : (condOf X).obj.obj (op S)) where
  /-- the first piece -/
  A : Set S
  /-- the second piece -/
  B : Set S
  isClopen_A : IsClopen A
  isClopen_B : IsClopen B
  union_eq : A ∪ B = (Set.univ : Set S)
  disjoint : Disjoint A B
  mapsToU : ∀ x ∈ A, asCMap f x ∈ U
  mapsToV : ∀ x ∈ B, asCMap f x ∈ V

lemma exists_refinePart (U V : Set X) (hUV : U ∪ V = (Set.univ : Set X)) (hU : IsOpen U)
    (hV : IsOpen V) (f : (condOf X).obj.obj (op S)) : Nonempty (RefinePart U V hUV f) := by
  have hcov : asCMap f ⁻¹' U ∪ asCMap f ⁻¹' V = (Set.univ : Set S) := by
    rw [← Set.preimage_union, hUV, Set.preimage_univ]
  obtain ⟨A', B', hA', hB', hA'sub, hB'sub, hunion, hdisj⟩ :=
    Refine.exists_isClopen_partition_of_open_cover (A := asCMap f ⁻¹' U) (B := asCMap f ⁻¹' V)
      (hU.preimage (asCMap f).continuous) (hV.preimage (asCMap f).continuous) hcov
  exact ⟨⟨A', B', hA', hB', hunion, hdisj, fun x hx => hA'sub hx, fun x hx => hB'sub hx⟩⟩

noncomputable def refinePart (U V : Set X) (hUV : U ∪ V = (Set.univ : Set X)) (hU : IsOpen U)
    (hV : IsOpen V) (f : (condOf X).obj.obj (op S)) : RefinePart U V hUV f :=
  Classical.choice (exists_refinePart U V hUV hU hV f)

lemma restrict_eq_of_restrict_eq (Z : LightCondSet.{0}) (A B : Set S) (hA : IsClopen A)
    (hB : IsClopen B) (hcov : A ∪ B = (Set.univ : Set S)) (hdisj : Disjoint A B)
    {z z' : Z.obj.obj (op S)}
    (h₁ : restrict Z S A hA z = restrict Z S A hA z')
    (h₂ : restrict Z S B hB z = restrict Z S B hB z') : z = z' :=
  (ClopenSheaf.restrict_bijective_of_clopen_partition Z S A B hA hB hcov hdisj).1 (Prod.ext h₁ h₂)

lemma exists_restrict_eq (Z : LightCondSet.{0}) (A B : Set S) (hA : IsClopen A)
    (hB : IsClopen B) (hcov : A ∪ B = (Set.univ : Set S)) (hdisj : Disjoint A B)
    (a : Z.obj.obj (op (clopenLP S A hA))) (b : Z.obj.obj (op (clopenLP S B hB))) :
    ∃ z : Z.obj.obj (op S), restrict Z S A hA z = a ∧ restrict Z S B hB z = b := by
  obtain ⟨z, hz⟩ := (ClopenSheaf.restrict_bijective_of_clopen_partition Z S A B hA hB hcov hdisj).2 (a, b)
  exact ⟨z, Prod.ext_iff.mp hz⟩

noncomputable def glueOf (Z : LightCondSet.{0}) (A B : Set S) (hA : IsClopen A)
    (hB : IsClopen B) (hcov : A ∪ B = (Set.univ : Set S)) (hdisj : Disjoint A B)
    (a : Z.obj.obj (op (clopenLP S A hA))) (b : Z.obj.obj (op (clopenLP S B hB))) :
    Z.obj.obj (op S) :=
  Classical.choose (exists_restrict_eq Z A B hA hB hcov hdisj a b)

lemma restrict_glueOf_left (Z : LightCondSet.{0}) (A B : Set S) (hA : IsClopen A)
    (hB : IsClopen B) (hcov : A ∪ B = (Set.univ : Set S)) (hdisj : Disjoint A B)
    (a : Z.obj.obj (op (clopenLP S A hA))) (b : Z.obj.obj (op (clopenLP S B hB))) :
    restrict Z S A hA (glueOf Z A B hA hB hcov hdisj a b) = a :=
  (Classical.choose_spec (exists_restrict_eq Z A B hA hB hcov hdisj a b)).1

lemma restrict_glueOf_right (Z : LightCondSet.{0}) (A B : Set S) (hA : IsClopen A)
    (hB : IsClopen B) (hcov : A ∪ B = (Set.univ : Set S)) (hdisj : Disjoint A B)
    (a : Z.obj.obj (op (clopenLP S A hA))) (b : Z.obj.obj (op (clopenLP S B hB))) :
    restrict Z S B hB (glueOf Z A B hA hB hcov hdisj a b) = b :=
  (Classical.choose_spec (exists_restrict_eq Z A B hA hB hcov hdisj a b)).2

/-- The section of `setCond U` over a clopen piece `A` of `S` cut out by a map `S → X` whose
image on `A` lies in `U`. -/
def toUOnA (U : Set X) (f : (condOf X).obj.obj (op S)) (A : Set S) (hA : IsClopen A)
    (hAU : ∀ x ∈ A, asCMap f x ∈ U) : (setCond U).obj.obj (op (clopenLP S A hA)) :=
  ⟨fun a => ⟨asCMap f a.1, hAU _ a.2⟩,
    Continuous.subtype_mk ((asCMap f).continuous.comp continuous_subtype_val) (fun a => hAU _ a.2)⟩

/-- The section of `setCond V` over a clopen piece `B` of `S` cut out by a map `S → X` whose
image on `B` lies in `V`. -/
def toVOnB (V : Set X) (f : (condOf X).obj.obj (op S)) (B : Set S) (hB : IsClopen B)
    (hBV : ∀ x ∈ B, asCMap f x ∈ V) : (setCond V).obj.obj (op (clopenLP S B hB)) :=
  ⟨fun b => ⟨asCMap f b.1, hBV _ b.2⟩,
    Continuous.subtype_mk ((asCMap f).continuous.comp continuous_subtype_val) (fun b => hBV _ b.2)⟩

/-- A section of `setCond U` at `S`, as an actual continuous map. -/
def asUMap (U : Set X) (g : (setCond U).obj.obj (op S)) : C(↥S, ↥U) := g

@[simp]
lemma setCond_map_apply (U : Set X) (g : (setCond U).obj.obj (op S)) (v : T ⟶ S) :
    (setCond U).obj.map v.op g =
      ⟨fun t => asUMap U g (v t),
        (asUMap U g).continuous.comp v.hom.hom.continuous⟩ := rfl

/-- The glued section of `Z` over `S` associated to a refinement partition of the cover and to
sections of `Z` over the two pieces. -/
noncomputable def glueAbove (U V : Set X) (hUV : U ∪ V = (Set.univ : Set X))
    (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z) (gV : setCond V ⟶ Z)
    (f : (condOf X).obj.obj (op S)) (P : RefinePart U V hUV f) : Z.obj.obj (op S) :=
  glueOf Z P.A P.B P.isClopen_A P.isClopen_B P.union_eq P.disjoint
    (gU.hom.app _ (toUOnA U f P.A P.isClopen_A P.mapsToU))
    (gV.hom.app _ (toVOnB V f P.B P.isClopen_B P.mapsToV))

lemma restrict_glueAbove_left (U V : Set X) (hUV : U ∪ V = (Set.univ : Set X))
    (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z) (gV : setCond V ⟶ Z)
    (f : (condOf X).obj.obj (op S)) (P : RefinePart U V hUV f) :
    Z.obj.map (clopenIncl S P.A P.isClopen_A).op (glueAbove U V hUV Z gU gV f P) =
      gU.hom.app _ (toUOnA U f P.A P.isClopen_A P.mapsToU) :=
  restrict_glueOf_left Z P.A P.B P.isClopen_A P.isClopen_B P.union_eq P.disjoint _ _

lemma restrict_glueAbove_right (U V : Set X) (hUV : U ∪ V = (Set.univ : Set X))
    (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z) (gV : setCond V ⟶ Z)
    (f : (condOf X).obj.obj (op S)) (P : RefinePart U V hUV f) :
    Z.obj.map (clopenIncl S P.B P.isClopen_B).op (glueAbove U V hUV Z gU gV f P) =
      gV.hom.app _ (toVOnB V f P.B P.isClopen_B P.mapsToV) :=
  restrict_glueOf_right Z P.A P.B P.isClopen_A P.isClopen_B P.union_eq P.disjoint _ _

/-- The glued section of `Z` over `S`, using the chosen refinement partition. -/
noncomputable def glueSec (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (f : (condOf X).obj.obj (op S)) : Z.obj.obj (op S) :=
  glueAbove U V hUV Z gU gV f (refinePart U V hUV hU hV f)

/-! ## Helper lemmas for the naturality computation -/

section Helper

variable {P T : LightProfinite.{0}}

/-- Restriction is precomposition. -/
lemma restrict_eq_map (Z : LightCondSet.{0}) (S : LightProfinite.{0}) (A : Set S)
    (hA : IsClopen A) (z : Z.obj.obj (op S)) :
    restrict Z S A hA z = Z.obj.map (clopenIncl S A hA).op z := rfl

/-- Restriction along the identity is the identity. -/
@[simp]
lemma map_id_op (Z : LightCondSet.{0}) (T : LightProfinite.{0}) (z : Z.obj.obj (op T)) :
    Z.obj.map (𝟙 T).op z = z := by
  rw [CategoryTheory.op_id, Z.obj.map_id]
  rfl

/-- Functoriality of restriction, in the form used below. -/
lemma map_op_map_op (Z : LightCondSet.{0}) {A₀ A₁ A₂ : LightProfinite.{0}} (u : A₁ ⟶ A₀)
    (w : A₂ ⟶ A₁) (z : Z.obj.obj (op A₀)) :
    Z.obj.map w.op (Z.obj.map u.op z) = Z.obj.map (w ≫ u).op z := by
  rw [← CategoryTheory.Functor.map_comp_apply, CategoryTheory.op_comp]

@[simp]
lemma toUMap_natural (U : Set X) (f : (condOf X).obj.obj (op S)) (v : P ⟶ S)
    (hv : ∀ p : ↥P, asCMap f (v p) ∈ U) (w : T ⟶ P) :
    (setCond U).obj.map w.op (toUMap U f v hv) = toUMap U f (w ≫ v) (fun t => hv (w t)) :=
  rfl

@[simp]
lemma toUOnA_natural (U : Set X) (f : (condOf X).obj.obj (op S)) (A : Set S) (hA : IsClopen A)
    (hAU : ∀ x ∈ A, asCMap f x ∈ U) (w : T ⟶ clopenLP S A hA)
    (h : ∀ t : ↥T, asCMap f ((w ≫ clopenIncl S A hA) t) ∈ U) :
    (setCond U).obj.map w.op (toUOnA U f A hA hAU) =
      toUMap U f (w ≫ clopenIncl S A hA) h :=
  rfl

@[simp]
lemma toVMap_natural (V : Set X) (f : (condOf X).obj.obj (op S)) (v : P ⟶ S)
    (hv : ∀ p : ↥P, asCMap f (v p) ∈ V) (w : T ⟶ P) :
    (setCond V).obj.map w.op (toVMap V f v hv) = toVMap V f (w ≫ v) (fun t => hv (w t)) :=
  rfl

@[simp]
lemma toVOnB_natural (V : Set X) (f : (condOf X).obj.obj (op S)) (B : Set S) (hB : IsClopen B)
    (hBV : ∀ x ∈ B, asCMap f x ∈ V) (w : T ⟶ clopenLP S B hB)
    (h : ∀ t : ↥T, asCMap f ((w ≫ clopenIncl S B hB) t) ∈ V) :
    (setCond V).obj.map w.op (toVOnB V f B hB hBV) =
      toVMap V f (w ≫ clopenIncl S B hB) h :=
  rfl

/-- The morphism `P → A` induced by a map `w : P → S` whose image lies in the clopen `A`. -/
def toClopen (A : Set S) (hA : IsClopen A) (w : P ⟶ S) (hw : ∀ p : ↥P, w p ∈ A) :
    P ⟶ clopenLP S A hA := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA.1.isCompact
  exact CompHausLike.ofHom _ ⟨fun p => ⟨w p, hw p⟩,
    Continuous.subtype_mk w.hom.hom.continuous hw⟩

@[reassoc]
lemma toClopen_incl (A : Set S) (hA : IsClopen A) (w : P ⟶ S) (hw : ∀ p : ↥P, w p ∈ A) :
    toClopen A hA w hw ≫ clopenIncl S A hA = w := by
  ext p
  rfl

end Helper

/-- The glued section over the chosen partition restricts to the `U`-section on the first piece. -/
lemma restrict_glueSec_left (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (f : (condOf X).obj.obj (op S)) :
    Z.obj.map (clopenIncl S (refinePart U V hUV hU hV f).A
        (refinePart U V hUV hU hV f).isClopen_A).op (glueSec U V hU hV hUV Z gU gV f) =
      gU.hom.app _ (toUOnA U f (refinePart U V hUV hU hV f).A
        (refinePart U V hUV hU hV f).isClopen_A (refinePart U V hUV hU hV f).mapsToU) :=
  restrict_glueAbove_left U V hUV Z gU gV f _

/-- The glued section over the chosen partition restricts to the `V`-section on the second piece. -/
lemma restrict_glueSec_right (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (f : (condOf X).obj.obj (op S)) :
    Z.obj.map (clopenIncl S (refinePart U V hUV hU hV f).B
        (refinePart U V hUV hU hV f).isClopen_B).op (glueSec U V hU hV hUV Z gU gV f) =
      gV.hom.app _ (toVOnB V f (refinePart U V hUV hU hV f).B
        (refinePart U V hUV hU hV f).isClopen_B (refinePart U V hUV hU hV f).mapsToV) :=
  restrict_glueAbove_right U V hUV Z gU gV f _

section LemmaG

/-- The image of the glued section under a map `P → S` whose composite with the given map `S → X`
lands in `U` is the corresponding section of `setCond U`. -/
lemma glueSec_mapsToU (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (hcompat : iWU U V ≫ gU = iWV U V ≫ gV)
    (v : P ⟶ S) (f : (condOf X).obj.obj (op S))
    (hv : ∀ p : ↥P, asCMap f (v p) ∈ U) :
    Z.obj.map v.op (glueSec U V hU hV hUV Z gU gV f) = gU.hom.app _ (toUMap U f v hv) := by
  set P₀ : RefinePart U V hUV f := refinePart U V hUV hU hV f with hP₀
  have hcov : v ⁻¹' P₀.A ∪ v ⁻¹' P₀.B = (Set.univ : Set P) := by
    rw [← Set.preimage_union, P₀.union_eq, Set.preimage_univ]
  obtain ⟨D₁, D₂, hD₁, hD₂, hD₁sub, hD₂sub, hDunion, hDdisj⟩ :=
    Refine.exists_isClopen_partition_of_open_cover (A := v ⁻¹' P₀.A) (B := v ⁻¹' P₀.B)
      (IsOpen.preimage v.hom.hom.continuous P₀.isClopen_A.isOpen)
      (IsOpen.preimage v.hom.hom.continuous P₀.isClopen_B.isOpen) hcov
  refine restrict_eq_of_restrict_eq Z D₁ D₂ hD₁ hD₂ hDunion hDdisj ?_ ?_
  · -- first piece: comparison through `U` and `P₀.A`
    let w : clopenLP P D₁ hD₁ ⟶ clopenLP S P₀.A P₀.isClopen_A :=
      toClopen P₀.A P₀.isClopen_A (clopenIncl P D₁ hD₁ ≫ v) (fun d => hD₁sub d.2)
    have hw : w ≫ clopenIncl S P₀.A P₀.isClopen_A = clopenIncl P D₁ hD₁ ≫ v :=
      toClopen_incl P₀.A P₀.isClopen_A (clopenIncl P D₁ hD₁ ≫ v) (fun d => hD₁sub d.2)
    have hs : (setCond U).obj.map w.op (toUOnA U f P₀.A P₀.isClopen_A P₀.mapsToU) =
        (setCond U).obj.map (clopenIncl P D₁ hD₁).op (toUMap U f v hv) := rfl
    have hnat := CategoryTheory.NatTrans.naturality_apply gU.hom w.op
      (toUOnA U f P₀.A P₀.isClopen_A P₀.mapsToU)
    have hnat₂ := CategoryTheory.NatTrans.naturality_apply gU.hom (clopenIncl P D₁ hD₁).op
      (toUMap U f v hv)
    rw [restrict_eq_map, restrict_eq_map]
    rw [map_op_map_op Z v (clopenIncl P D₁ hD₁)]
    rw [← hw]
    rw [← map_op_map_op Z (clopenIncl S P₀.A P₀.isClopen_A) w
      (glueSec U V hU hV hUV Z gU gV f)]
    rw [restrict_glueSec_left]
    rw [← hnat]
    rw [hs]
    rw [hnat₂]
  · -- second piece: compare through `U`, using the compatibility of `gU` and `gV` on `U ∩ V`
    let v₂ : clopenLP P D₂ hD₂ ⟶ S := clopenIncl P D₂ hD₂ ≫ v
    let hvU : ∀ d : ↥(clopenLP P D₂ hD₂), asCMap f (v₂ d) ∈ U :=
      fun d => hv (clopenIncl P D₂ hD₂ d)
    let hvB : ∀ d : ↥(clopenLP P D₂ hD₂), v₂ d ∈ P₀.B := fun d => hD₂sub d.2
    let hvV : ∀ d : ↥(clopenLP P D₂ hD₂), asCMap f (v₂ d) ∈ V := fun d => P₀.mapsToV _ (hvB d)
    let hvW : ∀ d : ↥(clopenLP P D₂ hD₂), asCMap f (v₂ d) ∈ U ∩ V := fun d => ⟨hvU d, hvV d⟩
    let w : clopenLP P D₂ hD₂ ⟶ clopenLP S P₀.B P₀.isClopen_B :=
      toClopen P₀.B P₀.isClopen_B v₂ hvB
    have hw : w ≫ clopenIncl S P₀.B P₀.isClopen_B = clopenIncl P D₂ hD₂ ≫ v :=
      toClopen_incl P₀.B P₀.isClopen_B v₂ hvB
    have hcomp : gU.hom.app (op (clopenLP P D₂ hD₂)) (toUMap U f v₂ hvU) =
        gV.hom.app (op (clopenLP P D₂ hD₂)) (toVMap V f v₂ hvV) := by
      have h := congrArg (fun (φ : setCond (U ∩ V) ⟶ Z) =>
        φ.hom.app (op (clopenLP P D₂ hD₂)) (toWMap U V f v₂ hvW)) hcompat
      have e1 : (iWU U V ≫ gU).hom.app (op (clopenLP P D₂ hD₂)) (toWMap U V f v₂ hvW) =
          gU.hom.app (op (clopenLP P D₂ hD₂))
            ((iWU U V).hom.app (op (clopenLP P D₂ hD₂)) (toWMap U V f v₂ hvW)) := rfl
      have e2 : (iWU U V).hom.app (op (clopenLP P D₂ hD₂)) (toWMap U V f v₂ hvW) =
          toUMap U f v₂ hvU := rfl
      have e3 : (iWV U V ≫ gV).hom.app (op (clopenLP P D₂ hD₂)) (toWMap U V f v₂ hvW) =
          gV.hom.app (op (clopenLP P D₂ hD₂))
            ((iWV U V).hom.app (op (clopenLP P D₂ hD₂)) (toWMap U V f v₂ hvW)) := rfl
      have e4 : (iWV U V).hom.app (op (clopenLP P D₂ hD₂)) (toWMap U V f v₂ hvW) =
          toVMap V f v₂ hvV := rfl
      rw [e1, e2, e3, e4] at h
      exact h
    have hVmap : (setCond V).obj.map w.op (toVOnB V f P₀.B P₀.isClopen_B P₀.mapsToV) =
        toVMap V f v₂ hvV := rfl
    have hUmap : (setCond U).obj.map (clopenIncl P D₂ hD₂).op (toUMap U f v hv) =
        toUMap U f v₂ hvU := rfl
    rw [restrict_eq_map, restrict_eq_map]
    rw [map_op_map_op Z v (clopenIncl P D₂ hD₂)]
    rw [← hw]
    rw [← map_op_map_op Z (clopenIncl S P₀.B P₀.isClopen_B) w
      (glueSec U V hU hV hUV Z gU gV f)]
    rw [restrict_glueSec_right]
    rw [← CategoryTheory.NatTrans.naturality_apply gV.hom w.op
      (toVOnB V f P₀.B P₀.isClopen_B P₀.mapsToV)]
    rw [hVmap]
    rw [← hcomp]
    rw [← CategoryTheory.NatTrans.naturality_apply gU.hom (clopenIncl P D₂ hD₂).op
      (toUMap U f v hv)]
    rw [hUmap]

/-- Compatibility of `gU` and `gV`, evaluated on a common `U ∩ V`-section. -/
lemma compat_apply (U V : Set X) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (hcompat : iWU U V ≫ gU = iWV U V ≫ gV)
    (f : (condOf X).obj.obj (op S)) (v : T ⟶ S)
    (hvU : ∀ t : ↥T, asCMap f (v t) ∈ U) (hvV : ∀ t : ↥T, asCMap f (v t) ∈ V) :
    gU.hom.app (op T) (toUMap U f v hvU) = gV.hom.app (op T) (toVMap V f v hvV) := by
  have h := congrArg (fun (φ : setCond (U ∩ V) ⟶ Z) =>
    φ.hom.app (op T) (toWMap U V f v (fun t => ⟨hvU t, hvV t⟩))) hcompat
  have e1 : (iWU U V ≫ gU).hom.app (op T) (toWMap U V f v (fun t => ⟨hvU t, hvV t⟩)) =
      gU.hom.app (op T) ((iWU U V).hom.app (op T)
        (toWMap U V f v (fun t => ⟨hvU t, hvV t⟩))) := rfl
  have e2 : (iWU U V).hom.app (op T) (toWMap U V f v (fun t => ⟨hvU t, hvV t⟩)) =
      toUMap U f v hvU := rfl
  have e3 : (iWV U V ≫ gV).hom.app (op T) (toWMap U V f v (fun t => ⟨hvU t, hvV t⟩)) =
      gV.hom.app (op T) ((iWV U V).hom.app (op T)
        (toWMap U V f v (fun t => ⟨hvU t, hvV t⟩))) := rfl
  have e4 : (iWV U V).hom.app (op T) (toWMap U V f v (fun t => ⟨hvU t, hvV t⟩)) =
      toVMap V f v hvV := rfl
  rw [e1, e2, e3, e4] at h
  exact h

/-- The image of the glued section under a map `P → S` whose composite with the given map `S → X`
lands in `V` is the corresponding section of `setCond V`. -/
lemma glueSec_mapsToV (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (hcompat : iWU U V ≫ gU = iWV U V ≫ gV)
    (v : P ⟶ S) (f : (condOf X).obj.obj (op S))
    (hv : ∀ p : ↥P, asCMap f (v p) ∈ V) :
    Z.obj.map v.op (glueSec U V hU hV hUV Z gU gV f) = gV.hom.app _ (toVMap V f v hv) := by
  set P₀ : RefinePart U V hUV f := refinePart U V hUV hU hV f with hP₀
  have hcov : v ⁻¹' P₀.A ∪ v ⁻¹' P₀.B = (Set.univ : Set P) := by
    rw [← Set.preimage_union, P₀.union_eq, Set.preimage_univ]
  obtain ⟨D₁, D₂, hD₁, hD₂, hD₁sub, hD₂sub, hDunion, hDdisj⟩ :=
    Refine.exists_isClopen_partition_of_open_cover (A := v ⁻¹' P₀.A) (B := v ⁻¹' P₀.B)
      (IsOpen.preimage v.hom.hom.continuous P₀.isClopen_A.isOpen)
      (IsOpen.preimage v.hom.hom.continuous P₀.isClopen_B.isOpen) hcov
  refine restrict_eq_of_restrict_eq Z D₁ D₂ hD₁ hD₂ hDunion hDdisj ?_ ?_
  · -- first piece: both sides reduce to `V`-sections, compared through the compatibility
    let w : clopenLP P D₁ hD₁ ⟶ clopenLP S P₀.A P₀.isClopen_A :=
      toClopen P₀.A P₀.isClopen_A (clopenIncl P D₁ hD₁ ≫ v) (fun d => hD₁sub d.2)
    have hw : w ≫ clopenIncl S P₀.A P₀.isClopen_A = clopenIncl P D₁ hD₁ ≫ v :=
      toClopen_incl P₀.A P₀.isClopen_A (clopenIncl P D₁ hD₁ ≫ v) (fun d => hD₁sub d.2)
    have hv₁ : ∀ d : ↥(clopenLP P D₁ hD₁), asCMap f ((clopenIncl P D₁ hD₁ ≫ v) d) ∈ V :=
      fun d => hv (clopenIncl P D₁ hD₁ d)
    have hv₁U : ∀ d : ↥(clopenLP P D₁ hD₁), asCMap f ((clopenIncl P D₁ hD₁ ≫ v) d) ∈ U :=
      fun d => P₀.mapsToU _ (hD₁sub d.2)
    have hc := compat_apply U V Z gU gV hcompat f (clopenIncl P D₁ hD₁ ≫ v) hv₁U hv₁
    have hsU : (setCond U).obj.map w.op (toUOnA U f P₀.A P₀.isClopen_A P₀.mapsToU) =
        toUMap U f (clopenIncl P D₁ hD₁ ≫ v) hv₁U := rfl
    have hsV' : (setCond V).obj.map (clopenIncl P D₁ hD₁).op (toVMap V f v hv) =
        toVMap V f (clopenIncl P D₁ hD₁ ≫ v) hv₁ := rfl
    rw [restrict_eq_map, restrict_eq_map]
    rw [map_op_map_op Z v (clopenIncl P D₁ hD₁)]
    rw [← hw]
    rw [← map_op_map_op Z (clopenIncl S P₀.A P₀.isClopen_A) w
      (glueSec U V hU hV hUV Z gU gV f)]
    rw [restrict_glueSec_left]
    rw [← CategoryTheory.NatTrans.naturality_apply gU.hom w.op
      (toUOnA U f P₀.A P₀.isClopen_A P₀.mapsToU)]
    rw [hsU]
    rw [hc]
    rw [← CategoryTheory.NatTrans.naturality_apply gV.hom (clopenIncl P D₁ hD₁).op
      (toVMap V f v hv)]
    rw [hsV']
  · -- second piece: both sides reduce to `V`-sections over `P₀.B`
    let w : clopenLP P D₂ hD₂ ⟶ clopenLP S P₀.B P₀.isClopen_B :=
      toClopen P₀.B P₀.isClopen_B (clopenIncl P D₂ hD₂ ≫ v) (fun d => hD₂sub d.2)
    have hw : w ≫ clopenIncl S P₀.B P₀.isClopen_B = clopenIncl P D₂ hD₂ ≫ v :=
      toClopen_incl P₀.B P₀.isClopen_B (clopenIncl P D₂ hD₂ ≫ v) (fun d => hD₂sub d.2)
    have hv₂ : ∀ d : ↥(clopenLP P D₂ hD₂), asCMap f ((clopenIncl P D₂ hD₂ ≫ v) d) ∈ V :=
      fun d => hv (clopenIncl P D₂ hD₂ d)
    have hsV : (setCond V).obj.map w.op (toVOnB V f P₀.B P₀.isClopen_B P₀.mapsToV) =
        toVMap V f (clopenIncl P D₂ hD₂ ≫ v) hv₂ := rfl
    have hsV' : (setCond V).obj.map (clopenIncl P D₂ hD₂).op (toVMap V f v hv) =
        toVMap V f (clopenIncl P D₂ hD₂ ≫ v) hv₂ := rfl
    rw [restrict_eq_map, restrict_eq_map]
    rw [map_op_map_op Z v (clopenIncl P D₂ hD₂)]
    rw [← hw]
    rw [← map_op_map_op Z (clopenIncl S P₀.B P₀.isClopen_B) w
      (glueSec U V hU hV hUV Z gU gV f)]
    rw [restrict_glueSec_right]
    rw [← CategoryTheory.NatTrans.naturality_apply gV.hom w.op
      (toVOnB V f P₀.B P₀.isClopen_B P₀.mapsToV)]
    rw [hsV]
    rw [← CategoryTheory.NatTrans.naturality_apply gV.hom (clopenIncl P D₂ hD₂).op
      (toVMap V f v hv)]
    rw [hsV']


/-- Naturality of the glued section in the map `S → X`. -/
lemma glueSec_naturality (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (hcompat : iWU U V ≫ gU = iWV U V ≫ gV)
    (u : T ⟶ S) (f : (condOf X).obj.obj (op S)) :
    Z.obj.map u.op (glueSec U V hU hV hUV Z gU gV f) =
      glueSec U V hU hV hUV Z gU gV ((condOf X).obj.map u.op f) := by
  set P₁ : RefinePart U V hUV ((condOf X).obj.map u.op f) :=
    refinePart U V hUV hU hV ((condOf X).obj.map u.op f) with hP₁
  refine restrict_eq_of_restrict_eq Z P₁.A P₁.B P₁.isClopen_A P₁.isClopen_B P₁.union_eq
    P₁.disjoint ?_ ?_
  · -- first piece: both sides are `U`-sections over `P₁.A`
    have hv : ∀ a : ↥(clopenLP T P₁.A P₁.isClopen_A),
        asCMap f ((clopenIncl T P₁.A P₁.isClopen_A ≫ u) a) ∈ U :=
      fun a => P₁.mapsToU _ a.2
    have key : toUMap U f (clopenIncl T P₁.A P₁.isClopen_A ≫ u) hv =
        toUOnA U ((condOf X).obj.map u.op f) P₁.A P₁.isClopen_A P₁.mapsToU := rfl
    have hfac : Z.obj.map (clopenIncl T P₁.A P₁.isClopen_A).op
        (glueSec U V hU hV hUV Z gU gV ((condOf X).obj.map u.op f)) =
        gU.hom.app (op (clopenLP T P₁.A P₁.isClopen_A))
          (toUOnA U ((condOf X).obj.map u.op f) P₁.A P₁.isClopen_A P₁.mapsToU) :=
      restrict_glueSec_left U V hU hV hUV Z gU gV ((condOf X).obj.map u.op f)
    rw [restrict_eq_map, restrict_eq_map]
    rw [map_op_map_op Z u (clopenIncl T P₁.A P₁.isClopen_A)]
    rw [glueSec_mapsToU U V hU hV hUV Z gU gV hcompat
      (clopenIncl T P₁.A P₁.isClopen_A ≫ u) f hv]
    rw [hfac]
    rw [← key]
  · -- second piece: both sides are `V`-sections over `P₁.B`
    have hv : ∀ b : ↥(clopenLP T P₁.B P₁.isClopen_B),
        asCMap f ((clopenIncl T P₁.B P₁.isClopen_B ≫ u) b) ∈ V :=
      fun b => P₁.mapsToV _ b.2
    have key : toVMap V f (clopenIncl T P₁.B P₁.isClopen_B ≫ u) hv =
        toVOnB V ((condOf X).obj.map u.op f) P₁.B P₁.isClopen_B P₁.mapsToV := rfl
    have hfac : Z.obj.map (clopenIncl T P₁.B P₁.isClopen_B).op
        (glueSec U V hU hV hUV Z gU gV ((condOf X).obj.map u.op f)) =
        gV.hom.app (op (clopenLP T P₁.B P₁.isClopen_B))
          (toVOnB V ((condOf X).obj.map u.op f) P₁.B P₁.isClopen_B P₁.mapsToV) :=
      restrict_glueSec_right U V hU hV hUV Z gU gV ((condOf X).obj.map u.op f)
    rw [restrict_eq_map, restrict_eq_map]
    rw [map_op_map_op Z u (clopenIncl T P₁.B P₁.isClopen_B)]
    rw [glueSec_mapsToV U V hU hV hUV Z gU gV hcompat
      (clopenIncl T P₁.B P₁.isClopen_B ≫ u) f hv]
    rw [hfac]
    rw [← key]


end LemmaG


section GlueHom

/-- The natural transformation whose components are the glued sections. -/
noncomputable def glueNatTrans (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (hcompat : iWU U V ≫ gU = iWV U V ≫ gV) :
    (condOf X).obj ⟶ Z.obj where
  app S := ↾fun f => glueSec U V hU hV hUV Z gU gV (S := Opposite.unop S) f
  naturality S T g := by
    ext f
    exact (glueSec_naturality U V hU hV hUV Z gU gV hcompat (Opposite.unop g) f).symm

/-- The morphism `X_cond ⟶ Z` gluing two maps out of `U_cond` and `V_cond`. -/
noncomputable def glueHom (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (hcompat : iWU U V ≫ gU = iWV U V ≫ gV) : condOf X ⟶ Z :=
  Sheaf.homEquiv.symm (glueNatTrans U V hU hV hUV Z gU gV hcompat)

@[simp]
lemma glueHom_hom (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (hcompat : iWU U V ≫ gU = iWV U V ≫ gV) :
    (glueHom U V hU hV hUV Z gU gV hcompat).hom =
      (glueNatTrans U V hU hV hUV Z gU gV hcompat) := rfl

lemma glueHom_apply (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (hcompat : iWU U V ≫ gU = iWV U V ≫ gV)
    (T : LightProfinite.{0}) (f : (condOf X).obj.obj (op T)) :
    (glueHom U V hU hV hUV Z gU gV hcompat).hom.app (op T) f =
      glueSec U V hU hV hUV Z gU gV f := rfl

end GlueHom

section GlueHomFac

lemma iU_glueHom (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (hcompat : iWU U V ≫ gU = iWV U V ≫ gV) :
    iU U ≫ glueHom U V hU hV hUV Z gU gV hcompat = gU := by
  apply LightCondensed.hom_ext
  intro S
  cases S with
  | op T =>
    ext x
    have hv : ∀ t : ↥T, asCMap ((iU U).hom.app (op T) x) ((𝟙 T) t) ∈ U := by
      intro t
      exact (asUMap U x t).2
    have key := glueSec_mapsToU U V hU hV hUV Z gU gV hcompat (𝟙 T)
      ((iU U).hom.app (op T) x) hv
    have h2 : toUMap U ((iU U).hom.app (op T) x) (𝟙 T) hv = x := by
      have h2' : (toUMap U ((iU U).hom.app (op T) x) (𝟙 T) hv : C(↥T, ↥U)) =
          (x : C(↥T, ↥U)) := by
        apply ContinuousMap.ext
        intro t
        exact Subtype.ext rfl
      exact h2'
    calc (iU U ≫ glueHom U V hU hV hUV Z gU gV hcompat).hom.app (op T) x
        = glueSec U V hU hV hUV Z gU gV ((iU U).hom.app (op T) x) := rfl
      _ = Z.obj.map (𝟙 T).op (glueSec U V hU hV hUV Z gU gV ((iU U).hom.app (op T) x)) :=
          (map_id_op Z T _).symm
      _ = gU.hom.app (op T) (toUMap U ((iU U).hom.app (op T) x) (𝟙 T) hv) := key
      _ = gU.hom.app (op T) x := by rw [h2]

lemma iV_glueHom (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (hcompat : iWU U V ≫ gU = iWV U V ≫ gV) :
    iV V ≫ glueHom U V hU hV hUV Z gU gV hcompat = gV := by
  apply LightCondensed.hom_ext
  intro S
  cases S with
  | op T =>
    ext x
    have hv : ∀ t : ↥T, asCMap ((iV V).hom.app (op T) x) ((𝟙 T) t) ∈ V := by
      intro t
      exact (asUMap V x t).2
    have key := glueSec_mapsToV U V hU hV hUV Z gU gV hcompat (𝟙 T)
      ((iV V).hom.app (op T) x) hv
    have h2 : toVMap V ((iV V).hom.app (op T) x) (𝟙 T) hv = x := by
      have h2' : (toVMap V ((iV V).hom.app (op T) x) (𝟙 T) hv : C(↥T, ↥V)) =
          (x : C(↥T, ↥V)) := by
        apply ContinuousMap.ext
        intro t
        exact Subtype.ext rfl
      exact h2'
    calc (iV V ≫ glueHom U V hU hV hUV Z gU gV hcompat).hom.app (op T) x
        = glueSec U V hU hV hUV Z gU gV ((iV V).hom.app (op T) x) := rfl
      _ = Z.obj.map (𝟙 T).op (glueSec U V hU hV hUV Z gU gV ((iV V).hom.app (op T) x)) :=
          (map_id_op Z T _).symm
      _ = gV.hom.app (op T) (toVMap V ((iV V).hom.app (op T) x) (𝟙 T) hv) := key
      _ = gV.hom.app (op T) x := by rw [h2]

end GlueHomFac

section GlueHomUnique

lemma glueHom_unique (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) (Z : LightCondSet.{0}) (gU : setCond U ⟶ Z)
    (gV : setCond V ⟶ Z) (hcompat : iWU U V ≫ gU = iWV U V ≫ gV) (m : condOf X ⟶ Z)
    (hmU : iU U ≫ m = gU) (hmV : iV V ≫ m = gV) :
    m = glueHom U V hU hV hUV Z gU gV hcompat := by
  apply LightCondensed.hom_ext
  intro S
  cases S with
  | op T =>
    ext f
    show (ConcreteCategory.hom (m.hom.app (op T))) f =
      (ConcreteCategory.hom ((glueHom U V hU hV hUV Z gU gV hcompat).hom.app (op T))) f
    rw [glueHom_apply]
    set P₀ : RefinePart U V hUV f := refinePart U V hUV hU hV f with hP₀
    refine restrict_eq_of_restrict_eq Z P₀.A P₀.B P₀.isClopen_A P₀.isClopen_B P₀.union_eq
      P₀.disjoint ?_ ?_
    · -- first piece
      rw [restrict_eq_map, restrict_eq_map]
      have hfac : Z.obj.map (clopenIncl T P₀.A P₀.isClopen_A).op
          (glueSec U V hU hV hUV Z gU gV f) =
          gU.hom.app (op (clopenLP T P₀.A P₀.isClopen_A))
            (toUOnA U f P₀.A P₀.isClopen_A P₀.mapsToU) :=
        restrict_glueSec_left U V hU hV hUV Z gU gV f
      rw [hfac]
      rw [← CategoryTheory.NatTrans.naturality_apply m.hom (clopenIncl T P₀.A P₀.isClopen_A).op f]
      have hx : (condOf X).obj.map (clopenIncl T P₀.A P₀.isClopen_A).op f =
          (iU U).hom.app (op (clopenLP T P₀.A P₀.isClopen_A))
            (toUOnA U f P₀.A P₀.isClopen_A P₀.mapsToU) := rfl
      rw [hx]
      have hmU' := congrArg (fun (φ : setCond U ⟶ Z) => φ.hom.app
        (op (clopenLP T P₀.A P₀.isClopen_A)) (toUOnA U f P₀.A P₀.isClopen_A P₀.mapsToU)) hmU
      have e : (iU U ≫ m).hom.app (op (clopenLP T P₀.A P₀.isClopen_A))
          (toUOnA U f P₀.A P₀.isClopen_A P₀.mapsToU) =
          m.hom.app (op (clopenLP T P₀.A P₀.isClopen_A))
            ((iU U).hom.app (op (clopenLP T P₀.A P₀.isClopen_A))
              (toUOnA U f P₀.A P₀.isClopen_A P₀.mapsToU)) := rfl
      rw [e] at hmU'
      exact hmU'
    · -- second piece
      rw [restrict_eq_map, restrict_eq_map]
      have hfac : Z.obj.map (clopenIncl T P₀.B P₀.isClopen_B).op
          (glueSec U V hU hV hUV Z gU gV f) =
          gV.hom.app (op (clopenLP T P₀.B P₀.isClopen_B))
            (toVOnB V f P₀.B P₀.isClopen_B P₀.mapsToV) :=
        restrict_glueSec_right U V hU hV hUV Z gU gV f
      rw [hfac]
      rw [← CategoryTheory.NatTrans.naturality_apply m.hom (clopenIncl T P₀.B P₀.isClopen_B).op f]
      have hx : (condOf X).obj.map (clopenIncl T P₀.B P₀.isClopen_B).op f =
          (iV V).hom.app (op (clopenLP T P₀.B P₀.isClopen_B))
            (toVOnB V f P₀.B P₀.isClopen_B P₀.mapsToV) := rfl
      rw [hx]
      have hmV' := congrArg (fun (φ : setCond V ⟶ Z) => φ.hom.app
        (op (clopenLP T P₀.B P₀.isClopen_B)) (toVOnB V f P₀.B P₀.isClopen_B P₀.mapsToV)) hmV
      have e : (iV V ≫ m).hom.app (op (clopenLP T P₀.B P₀.isClopen_B))
          (toVOnB V f P₀.B P₀.isClopen_B P₀.mapsToV) =
          m.hom.app (op (clopenLP T P₀.B P₀.isClopen_B))
            ((iV V).hom.app (op (clopenLP T P₀.B P₀.isClopen_B))
              (toVOnB V f P₀.B P₀.isClopen_B P₀.mapsToV)) := rfl
      rw [e] at hmV'
      exact hmV'

end GlueHomUnique

section MainPushout

theorem isPushout_condOf (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) :
    IsPushout (iWU U V) (iWV U V) (iU U) (iV V) := by
  have hcolim : IsColimit (PushoutCocone.mk (iU U) (iV V) (iWU_iU_eq_iWV_iV U V)) :=
    PushoutCocone.IsColimit.mk (iWU_iU_eq_iWV_iV U V)
      (fun s => glueHom U V hU hV hUV s.pt s.inl s.inr (PushoutCocone.condition s))
      (fun s => iU_glueHom U V hU hV hUV s.pt s.inl s.inr (PushoutCocone.condition s))
      (fun s => iV_glueHom U V hU hV hUV s.pt s.inl s.inr (PushoutCocone.condition s))
      (fun s m h₁ h₂ =>
        glueHom_unique U V hU hV hUV s.pt s.inl s.inr (PushoutCocone.condition s) m h₁ h₂)
  exact ⟨⟨iWU_iU_eq_iWV_iV U V⟩, ⟨hcolim⟩⟩

end MainPushout

section MonoLemmas

/-- A natural transformation of type-valued presheaves is a mono if all its components are
injective. -/
lemma mono_hom_of_pointwise_injective {F G : CategoryTheory.Functor LightProfinite.{0}ᵒᵖ Type}
    (φ : F ⟶ G) (h : ∀ (S : LightProfinite.{0}), Function.Injective (φ.app (op S))) :
    Mono φ where
  right_cancellation g₁ g₂ hgg := by
    ext S y
    cases S with
    | op T =>
      apply h T
      have := congrArg (fun (q : _ ⟶ G) => q.app (op T) y) hgg
      simpa using this

/-- The component at a light profinite set of the map induced by an inclusion of subspaces is
injective. -/
lemma injective_app_incl {A B : Set X} (h : A ⊆ B) (S : LightProfinite.{0}) :
    Function.Injective ((topCatToLightCondSet.map (Submission.Blueprint.incl h)).hom.app (op S)) := by
  have key : ∀ (g : (setCond A).obj.obj (op S)),
      ((topCatToLightCondSet.map (Submission.Blueprint.incl h)).hom.app (op S)) g =
        (⟨fun t => ⟨(asUMap A g t).1, h (asUMap A g t).2⟩,
          Continuous.subtype_mk (continuous_subtype_val.comp (asUMap A g).continuous)
            (fun t => h (asUMap A g t).2)⟩ :
          C(↥S, ↥B)) := fun g => rfl
  intro g₁ g₂ hgg
  rw [key g₁, key g₂] at hgg
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  have := congrFun (congrArg (fun (q : C(↥S, ↥B)) => fun t : ↥S => ((q t : ↥B) : ↥X)) hgg) t
  exact this


/-- The morphism of light condensed sets induced by an inclusion of subspaces is a
monomorphism. -/
lemma mono_map_incl {A B : Set X} (h : A ⊆ B) :
    Mono (topCatToLightCondSet.map (Submission.Blueprint.incl h)) :=
  Sheaf.Hom.mono_of_presheaf_mono _ _ _
    (h := mono_hom_of_pointwise_injective _ (fun S => injective_app_incl h S))

/-- The first leg `(U ∩ V)_cond ⟶ U_cond` of the Mayer–Vietoris square is a monomorphism. -/
lemma mono_iWU (U V : Set X) : Mono (iWU U V) :=
  mono_map_incl (Set.inter_subset_left : U ∩ V ⊆ U)

/-- The second leg `(U ∩ V)_cond ⟶ V_cond` of the Mayer–Vietoris square is a monomorphism. -/
lemma mono_iWV (U V : Set X) : Mono (iWV U V) :=
  mono_map_incl (Set.inter_subset_right : U ∩ V ⊆ V)

/-- The component at a light profinite set of the map induced by the inclusion of a subspace is
injective. -/
lemma injective_app_inclTop (A : Set X) (S : LightProfinite.{0}) :
    Function.Injective
      ((topCatToLightCondSet.map (Submission.Blueprint.inclTop A)).hom.app (op S)) := by
  have key : ∀ (g : (setCond A).obj.obj (op S)),
      ((topCatToLightCondSet.map (Submission.Blueprint.inclTop A)).hom.app (op S)) g =
        (⟨fun t => ((asUMap A g t : ↥A) : ↥X),
          continuous_subtype_val.comp (asUMap A g).continuous⟩ : C(↥S, ↥X)) := fun g => rfl
  intro g₁ g₂ hgg
  rw [key g₁, key g₂] at hgg
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  have := congrFun (congrArg (fun (q : C(↥S, ↥X)) => (q : ↥S → ↥X)) hgg) t
  exact this

/-- The inclusion `U_cond ⟶ X_cond` is a monomorphism. -/
lemma mono_iU (U : Set X) : Mono (iU U) :=
  Sheaf.Hom.mono_of_presheaf_mono _ _ _
    (h := mono_hom_of_pointwise_injective _ (fun S => injective_app_inclTop U S))

/-- The inclusion `V_cond ⟶ X_cond` is a monomorphism. -/
lemma mono_iV (V : Set X) : Mono (iV V) :=
  Sheaf.Hom.mono_of_presheaf_mono _ _ _
    (h := mono_hom_of_pointwise_injective _ (fun S => injective_app_inclTop V S))

end MonoLemmas

section FreePushout

theorem isPushout_free (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = (Set.univ : Set X)) :
    IsPushout ((LightCondensed.free ℤ).map (iWU U V)) ((LightCondensed.free ℤ).map (iWV U V))
      ((LightCondensed.free ℤ).map (iU U)) ((LightCondensed.free ℤ).map (iV V)) :=
  CategoryTheory.Functor.map_isPushout (LightCondensed.free ℤ) (isPushout_condOf U V hU hV hUV)

end FreePushout

end Work.CONDMV
