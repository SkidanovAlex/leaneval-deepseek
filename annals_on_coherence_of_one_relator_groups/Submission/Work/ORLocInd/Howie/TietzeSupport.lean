/-
# The Tietze elimination step of Howie's Case 2: support definitions

This file contains the definitions used by the Tietze transformation `vertexGroup_eliminate`
(`Submission/Work/ORLocInd/Howie/vertexGroup_eliminate.lean`, lemma L4 of `N4_LOCIND_LEAD.md`).

Setting: `P : Presentation V` is a staggered groupoid presentation on a graph `Γ` (a quiver with an
involutive reversal), `f` is an arrow of `Γ`, `i₀` a relator of `P` which contains exactly one arrow
of the code of `f` and all of whose other arrows have a different code, and no other relator contains
the code of `f`.  Writing that relator as `q₁ · g · q₂` (`g` the distinguished arrow of code
`edgeOf f`, `q₁`, `q₂` paths whose arrows are all kept), the Tietze transformation deletes the arrow
pair `{f, f⁻¹}` and the relator `i₀`, and solves `g = q₁⁻¹ · q₂⁻¹`.

The contents:

* `conjPathHom` : conjugation of an element of a vertex group by a path of the graph;
* `PathSubst` and `PathSubst.mapPath` : a "path-valued graph morphism", the abstract form of the
  substitution `f ↦ q₁⁻¹ · q₂⁻¹` that eliminates the arrow `f`;
* `DelV`-bookkeeping: `delPrefunctor`, `inclPath` (the inclusion of the arrow-deleted graph into `Γ`
  on paths) and `restrictPath` (its partial inverse);
* `TietzeData`, the data of the transformation (the distinguished arrow `g` together with the
  splitting of the relator `i₀`), `TietzeData.phi` (the value of `g`, a path of the arrow-deleted
  graph) and `TietzeData.substArrow` (the substitution on single arrows).

**Terminology.**  A path of the arrow-deleted graph `DelV K` is a `Quiver.Path` whose vertices are
written `show DelV K from _`; this forces the quiver instance `instDelQuiver K (so `cons`, `comp`,
`nil`, `reverse` on such paths all elaborate with the deleted instance).  The abbreviations
`DPath K a b`, `DArrow K a b`, `dnil`, `dcons`, `dcomp`, `dreverse` collect the corresponding
operations, so that later files never have to mention the casts explicitly.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.Basic
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.LabellingAux
import Submission.Work.ORLocInd.Howie.pmul_conj_comp
import Submission.Work.ORLocInd.Howie.erase_pmul

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Conjugation by a path -/

/-- Conjugation of an element of the vertex group at `w` by a path `δ : a → w`: the map
`x ↦ δ · x · δ⁻¹`.  This is a group homomorphism. -/
noncomputable def conjPathHom {a b : V} (δ : Quiver.Path a b) : VertexGroup b →* VertexGroup a where
  toFun x := ⟨pmul (pmul δ x.1) δ.reverse, pmul_isReduced _ _⟩
  map_one' := by
    apply Subtype.ext
    show pmul (pmul δ (1 : VertexGroup b).1) δ.reverse = (1 : VertexGroup a).1
    rw [VertexGroup.coe_one, VertexGroup.coe_one, pmul_nil_right, pmul_red_left]
    exact pmul_reverse δ
  map_mul' x y := by
    apply Subtype.ext
    show pmul (pmul δ (pmul x.1 y.1)) δ.reverse =
      pmul (pmul (pmul δ x.1) δ.reverse) (pmul (pmul δ y.1) δ.reverse)
    have h : pmul (pmul δ (pmul x.1 y.1)) δ.reverse =
        pmul (pmul δ (x.1.comp y.1)) δ.reverse := by
      rw [show pmul (pmul δ (pmul x.1 y.1)) δ.reverse =
          pmul (pmul δ (red (x.1.comp y.1))) δ.reverse from rfl,
        pmul_red_right δ (x.1.comp y.1)]
    rw [h, pmul_conj_comp δ δ δ x.1 y.1]

@[simp] theorem conjPathHom_apply {a b : V} (δ : Quiver.Path a b) (x : VertexGroup b) :
    (conjPathHom δ x).1 = pmul (pmul δ x.1) δ.reverse := rfl

/-! ## The arrow-deleted graph: paths, arrows and their elementary operations -/

/-- A path of `DelV K` from `a` to `b` (with the quiver instance `instDelQuiver K`). -/
abbrev DPath (K : Keep V) (a b : V) : Type u :=
  Quiver.Path (show DelV K from a) (show DelV K from b)

/-- An arrow of `DelV K` from `a` to `b`. -/
abbrev DArrow (K : Keep V) (a b : V) : Type u :=
  (show DelV K from a) ⟶ (show DelV K from b)

/-- The empty path of the arrow-deleted graph. -/
abbrev dnil (K : Keep V) (a : V) : DPath K a a := Quiver.Path.nil

/-- Concatenation of paths of the arrow-deleted graph. -/
abbrev dcomp {K : Keep V} {a b c : V} (p : DPath K a b) (q : DPath K b c) : DPath K a c :=
  p.comp q

/-- Extension of a path of the arrow-deleted graph by an arrow. -/
abbrev dcons {K : Keep V} {a b c : V} (p : DPath K a b) (e : DArrow K b c) : DPath K a c :=
  p.cons e

/-- Reversal of a path of the arrow-deleted graph. -/
abbrev dreverse {K : Keep V} {a b : V} (p : DPath K a b) : DPath K b a := p.reverse

/-- Reversal of an arrow of the arrow-deleted graph. -/
abbrev DReverse {K : Keep V} {a b : V} (e : DArrow K a b) : DArrow K b a := Quiver.reverse e

@[simp] theorem DReverse_involutive {K : Keep V} {a b : V} (e : DArrow K a b) :
    DReverse (DReverse e) = e := Subtype.ext (Quiver.reverse_reverse e.1)

@[simp] theorem dcomp_nil {K : Keep V} {a b : V} (p : DPath K a b) : dcomp p (dnil K b) = p := rfl

theorem dcomp_assoc {K : Keep V} {a b c d : V} (p : DPath K a b) (q : DPath K b c)
    (r : DPath K c d) : dcomp (dcomp p q) r = dcomp p (dcomp q r) :=
  Quiver.Path.comp_assoc p q r

theorem dnil_dcomp {K : Keep V} {a b : V} (p : DPath K a b) : dcomp (dnil K a) p = p :=
  Quiver.Path.nil_comp p

theorem dreverse_dreverse {K : Keep V} {a b : V} (p : DPath K a b) :
    dreverse (dreverse p) = p := Quiver.Path.reverse_reverse p

/-- The reverse of a one-arrow path of the deleted graph. -/
theorem dreverse_dcons_dnil {K : Keep V} {a b : V} (e : DArrow K a b) :
    dreverse (dcons (dnil K a) e) = dcons (dnil K b) (DReverse e) := rfl

/-! ## Path-valued graph morphisms -/

/-- A *path-valued graph morphism* into the arrow-deleted graph: for every arrow `e` of `Γ`, a path
of `DelV K` from the source of `e` to its target, compatible with reversal.  The substitution of the
Tietze step (`f ↦ q₁⁻¹ · q₂⁻¹`) is the main example. -/
structure PathSubst (K : Keep V) where
  /-- the image of an arrow -/
  mapArrow : (e : Quiver.Total V) → DPath K e.left e.right
  /-- reversal compatibility -/
  mapArrow_reverse : ∀ e : Quiver.Total V,
    mapArrow (Quiver.totalReverse e) = dreverse (mapArrow e)

namespace PathSubst

variable {K : Keep V}

/-- The image of a path under a path-valued graph morphism: a path of the arrow-deleted graph. -/
noncomputable def mapPath (s : PathSubst K) {a : V} :
    ∀ {b : V}, Quiver.Path a b → DPath K a b
  | _, .nil => dnil K a
  | _, .cons p e => dcomp (mapPath s p) (s.mapArrow (Quiver.Total.mk _ _ e))

end PathSubst

/-! ## The inclusion of the arrow-deleted graph, and its partial inverse -/

/-- The inclusion of the arrow-deleted graph `DelV K` in `Γ`, as a prefunctor (the identity on
vertices). -/
def delPrefunctor (K : Keep V) : DelV K ⥤q V where
  obj := fun x => x
  map := fun {_ _} e => e.1

@[simp] theorem delPrefunctor_map (K : Keep V) {a b : DelV K} (e : a ⟶ b) :
    (delPrefunctor K).map e = e.1 := rfl

/-- The inclusion of the arrow-deleted graph on *paths*. -/
noncomputable def inclPath (K : Keep V) {a : V} {b : V} (p : DPath K a b) : Quiver.Path a b :=
  (delPrefunctor K).mapPath p

theorem inclPath_nil (K : Keep V) (a : V) : inclPath K (dnil K a) = Quiver.Path.nil := rfl

theorem inclPath_dcons (K : Keep V) {a b c : V} (p : DPath K a b) (e : DArrow K b c) :
    inclPath K (dcons p e) = (inclPath K p).cons e.1 := rfl

/-- The restriction of a path of `Γ` all of whose arrows are kept to a path of the arrow-deleted
graph `DelV K`. -/
noncomputable def restrictPath (K : Keep V) (a : V) : ∀ {b : V} (p : Quiver.Path a b),
    (∀ f ∈ Quiver.Path.arrowList p, K.pred f) → DPath K a b
  | _, .nil, _ => dnil K a
  | _, .cons p e, h =>
      dcons ((restrictPath K a p) (fun f hf => h f (by
        rw [Quiver.Path.arrowList_cons]
        exact List.mem_append.mpr (Or.inl hf))))
        ⟨e, h (Quiver.Total.mk _ _ e) (by
          rw [Quiver.Path.arrowList_cons]
          exact List.mem_append.mpr (Or.inr (by simp)))⟩

/-- The equation of `restrictPath` on a path ending with an arrow. -/
theorem restrictPath_cons (K : Keep V) {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (h : ∀ f ∈ Quiver.Path.arrowList (p.cons e), K.pred f) :
    restrictPath K a (p.cons e) h =
      dcons ((restrictPath K a p) (fun f hf => h f (by
        rw [Quiver.Path.arrowList_cons]
        exact List.mem_append.mpr (Or.inl hf))))
        ⟨e, h (Quiver.Total.mk b c e) (by
          rw [Quiver.Path.arrowList_cons]
          exact List.mem_append.mpr (Or.inr (by simp)))⟩ := rfl

/-- The restriction of a path with all arrows kept, included back into `Γ`, is the path itself. -/
theorem inclPath_restrictPath (K : Keep V) (a : V) :
    ∀ {b : V} (p : Quiver.Path a b) (h : ∀ f ∈ Quiver.Path.arrowList p, K.pred f),
      inclPath K (restrictPath K a p h) = p
  | _, .nil, _ => rfl
  | _, .cons p e, h => by
      have h1 : inclPath K (restrictPath K a p (fun f hf => h f (by
          rw [Quiver.Path.arrowList_cons]
          exact List.mem_append.mpr (Or.inl hf)))) = p :=
        inclPath_restrictPath K a p _
      calc inclPath K (restrictPath K a (p.cons e) h)
          = inclPath K (dcons (restrictPath K a p (fun f hf => h f (by
              rw [Quiver.Path.arrowList_cons]
              exact List.mem_append.mpr (Or.inl hf)))) ⟨e, _⟩) :=
            congrArg (inclPath K) (restrictPath_cons K p e h)
        _ = (inclPath K (restrictPath K a p (fun f hf => h f (by
              rw [Quiver.Path.arrowList_cons]
              exact List.mem_append.mpr (Or.inl hf))))).cons e :=
            inclPath_dcons K _ _
        _ = p.cons e := by rw [h1]


/-! ## The data of the Tietze transformation -/

/-- The data of the Tietze elimination: besides the graph, the arrow set and the relator index, the
distinguished arrow `g` of the relator `i₀` (the one whose code is the code of `f`) and the
splitting `P.path i₀ = q₁ · g · q₂` with all arrows of `q₁`, `q₂` kept. -/
structure TietzeData (P : Presentation V) where
  /-- the arrows kept by the transformation -/
  K : Keep V
  /-- the arrow pair `{f, f⁻¹}` that is deleted -/
  f : Quiver.Total V
  /-- the relator that is deleted -/
  i₀ : P.ι
  /-- the kept arrows are exactly those whose code is not the code of `f` -/
  hK : ∀ e : Quiver.Total V, K.pred e ↔ P.edgeOf e ≠ P.edgeOf f
  /-- the code separates unoriented edges -/
  hsep : P.CodeSeparates
  /-- the distinguished arrow of the relator `i₀` -/
  g : Quiver.Total V
  /-- the initial segment of the relator `i₀` -/
  q₁ : Quiver.Path (P.base i₀) g.left
  /-- the final segment of the relator `i₀` -/
  q₂ : Quiver.Path g.right (P.base i₀)
  /-- the splitting of the relator -/
  split : P.path i₀ = q₁.comp (g.hom.toPath.comp q₂)
  /-- the distinguished arrow has the code of `f` -/
  code : P.edgeOf g = P.edgeOf f
  /-- the arrows of the initial segment are kept -/
  keep₁ : ∀ e ∈ Quiver.Path.arrowList q₁, K.pred e
  /-- the arrows of the final segment are kept -/
  keep₂ : ∀ e ∈ Quiver.Path.arrowList q₂, K.pred e

namespace TietzeData

variable {P : Presentation V} (D : TietzeData P)

/-- The value of the distinguished arrow `g` in the arrow-deleted graph: the path
`q₁⁻¹ · q₂⁻¹`, which the relator `q₁ · g · q₂ = 1` forces `g` to take. -/
noncomputable def phi : DPath D.K D.g.left D.g.right :=
  pmul (dreverse (restrictPath D.K (P.base D.i₀) D.q₁ D.keep₁))
    (dreverse (restrictPath D.K D.g.right D.q₂ D.keep₂))

/-- The substitution on single arrows: the identity on the kept arrows, `g ↦ q₁⁻¹ · q₂⁻¹` and
`g⁻¹ ↦ q₂ · q₁`. -/
noncomputable def substArrow (e : Quiver.Total V) : DPath D.K e.left e.right := by
  classical
  exact
    if he : e = D.g then he ▸ D.phi
    else if he' : e = Quiver.totalReverse D.g then he' ▸ dreverse D.phi
    else
      (dnil D.K e.left).cons ⟨e.hom, (D.hK e).mpr (by
        intro hcode
        rcases D.hsep e D.g (hcode.trans D.code.symm) with h | h
        · exact he h
        · exact he' h)⟩

/-- The distinguished arrow is not its own reverse (the graph has no self-inverse arrow). -/
theorem totalReverse_g_ne_g : Quiver.totalReverse D.g ≠ D.g := by
  rintro heq
  have hleft : D.g.right = D.g.left := congrArg Quiver.Total.left heq
  have hhom : HEq (Quiver.reverse D.g.hom) D.g.hom :=
    ((Quiver.Total.mk.injEq D.g.right D.g.left (Quiver.reverse D.g.hom) D.g.left D.g.right
      D.g.hom).mp heq).2.2
  have h1 : HEq ((Quiver.reverse D.g.hom).cast hleft rfl) (Quiver.reverse D.g.hom) :=
    Quiver.Hom.cast_heq _ _ _
  have h2 : HEq (D.g.hom.cast rfl hleft) D.g.hom := Quiver.Hom.cast_heq _ _ _
  have h3 : HEq ((Quiver.reverse D.g.hom).cast hleft rfl) (D.g.hom.cast rfl hleft) :=
    (h1.trans hhom).trans h2.symm
  refine P.noSelfLoop D.g.left (D.g.hom.cast rfl hleft) ?_
  rw [Quiver.Hom.cast_reverse]
  exact eq_of_heq h3

theorem substArrow_g : D.substArrow D.g = D.phi := by
  rw [substArrow, dif_pos rfl]

theorem substArrow_reverse_g :
    D.substArrow (Quiver.totalReverse D.g) = dreverse D.phi := by
  rw [substArrow, dif_neg D.totalReverse_g_ne_g, dif_pos rfl]
  rfl

theorem substArrow_of_ne {e : Quiver.Total V} (he : e ≠ D.g)
    (he' : e ≠ Quiver.totalReverse D.g) :
    D.substArrow e = dcons (dnil D.K e.left) ⟨e.hom, (D.hK e).mpr (by
      intro hcode
      rcases D.hsep e D.g (hcode.trans D.code.symm) with h | h
      · exact he h
      · exact he' h)⟩ := by
  rw [substArrow, dif_neg he, dif_neg he']

theorem totalReverse_ne_g {e : Quiver.Total V} (he : e ≠ Quiver.totalReverse D.g) :
    Quiver.totalReverse e ≠ D.g := by
  intro h
  exact he (Quiver.totalReverse_injective (by rw [h, Quiver.totalReverse_involutive]))

theorem totalReverse_ne_totalReverse {e : Quiver.Total V} (he : e ≠ D.g) :
    Quiver.totalReverse e ≠ Quiver.totalReverse D.g :=
  fun h => he (Quiver.totalReverse_injective h)

end TietzeData

end Work.ORLocInd.Howie
