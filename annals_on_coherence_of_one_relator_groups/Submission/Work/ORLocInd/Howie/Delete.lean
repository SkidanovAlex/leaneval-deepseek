/-
# Deleting arrows and relators from a groupoid presentation (Howie 2000, Case 2)

Howie's proof of Theorem 3.1 (*A short proof of a theorem of Brodskii*) proceeds by induction on the
number of relators, and each step *deletes* a relator together with the arrows of a chosen code.
The present file develops that deletion on a fixed vertex type:

* `delIncl K : DelV K ⥤q V` — the inclusion of the subgraph with the same vertices and only the
  arrows satisfying `K.pred`;
* `DelV.erasePath` / `DelV.liftPath` — the transport of paths back and forth along it, with
  `IsReduced`, `IsCyclicallyReduced` and `IsProperPower` preserved;
* `Presentation.deleteSub P K J` — the subpresentation on `DelV K` whose relators are those
  satisfying `J` and using only arrows satisfying `K.pred`;
* `Presentation.deleteSubInclVG` — the induced homomorphism of vertex groups
  `(P.deleteSub K J).vertexGroup x →* P.vertexGroup x`.

The bijectivity of `deleteSubInclVG` under the hypotheses of Howie's Tietze step (L4 of
`N4_LOCIND_LEAD.md`) is proved in `Submission/Work/ORLocInd/Howie/L4/vertexGroup_eliminate.lean`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.Basic
import Submission.Work.ORLocInd.Howie.Cover
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Prefunctor

open Quiver

/-- A prefunctor preserving reversal preserves the deletion of a backtrack. -/
theorem mapPath_deleteBacktrack {U : Type*} {W : Type*}
    [Quiver U] [Quiver.HasReverse U] [Quiver W] [Quiver.HasReverse W]
    (F : U ⥤q W) [F.MapReverse] {a b : U} {p r : Quiver.Path a b}
    (h : Quiver.Path.DeleteBacktrack p r) :
    Quiver.Path.DeleteBacktrack (F.mapPath p) (F.mapPath r) := by
  cases h with
  | intro p₁ e p₂ =>
      rw [Prefunctor.mapPath_comp, Prefunctor.mapPath_comp, Prefunctor.mapPath_comp,
        Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath, Prefunctor.mapPath_toPath,
        Prefunctor.map_reverse]
      exact Quiver.Path.DeleteBacktrack.intro (F.mapPath p₁) (F.map e) (F.mapPath p₂)

end Prefunctor

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## The inclusion `DelV K ⥤q V` -/

/-- The inclusion of the subgraph `DelV K` (same vertices, only the arrows satisfying `K.pred`) into
`V`. -/
def delIncl (K : Keep V) : DelV K ⥤q V where
  obj := fun x => x
  map := fun {_ _} e => e.1

instance instDelInclMapReverse (K : Keep V) : (delIncl K).MapReverse where
  map_reverse' := fun {_ _} _ => rfl

theorem delIncl_obj_injective (K : Keep V) : Function.Injective (delIncl K).obj := fun _ _ h => h

theorem delIncl_map_injective (K : Keep V) :
    ∀ {a b : DelV K}, Function.Injective fun e : a ⟶ b => (delIncl K).map e :=
  fun {_ _} e e' h => Subtype.ext h

namespace DelV

/-! ## Total arrows -/

/-- The underlying total arrow of an arrow of the deleted graph. -/
def toTotal (K : Keep V) (g : Quiver.Total (DelV K)) : Quiver.Total V :=
  Quiver.Total.mk g.left g.right g.hom.1

/-- The total arrow of `DelV K` associated with a total arrow of `V` satisfying `K.pred`. -/
def ofTotal (K : Keep V) (e : Quiver.Total V) (h : K.pred e) : Quiver.Total (DelV K) :=
  Quiver.Total.mk e.left e.right ⟨e.hom, h⟩

@[simp] theorem toTotal_ofTotal (K : Keep V) (e : Quiver.Total V) (h : K.pred e) :
    toTotal K (ofTotal K e h) = e := by cases e with | mk a b f => rfl

theorem ofTotal_toTotal (K : Keep V) (g : Quiver.Total (DelV K))
    (h : K.pred (toTotal K g)) : ofTotal K (toTotal K g) h = g := rfl

theorem toTotal_injective (K : Keep V) : Function.Injective (toTotal K) := by
  intro g g' h
  obtain ⟨a, b, f⟩ := g
  obtain ⟨a', b', f'⟩ := g'
  obtain ⟨ha, hb, hf⟩ := Quiver.Total.mk.inj h
  subst ha
  subst hb
  have hff : f = f' := Subtype.ext (eq_of_heq hf)
  subst hff
  rfl

@[simp] theorem toTotal_totalReverse (K : Keep V) (g : Quiver.Total (DelV K)) :
    toTotal K (Quiver.totalReverse (V := DelV K) g) =
      Quiver.totalReverse (V := V) (toTotal K g) := rfl

@[simp] theorem toTotal_mk (K : Keep V) {a b : DelV K} (e : a ⟶ b) :
    toTotal K (Quiver.Total.mk a b e) = Quiver.Total.mk (V := V) a b e.1 := rfl

@[simp] theorem ofTotal_mk (K : Keep V) {a b : V} (e : a ⟶ b)
    (h : K.pred (Quiver.Total.mk a b e)) :
    ofTotal K (Quiver.Total.mk a b e) h =
      (Quiver.Total.mk a b ⟨e, h⟩ : Quiver.Total (DelV K)) := rfl

/-! ## Erasure and lifting of paths -/

/-- The erasure of a path of `DelV K` to a path of `V`. -/
def erasePath (K : Keep V) (a : V) : ∀ {b : V},
    @Quiver.Path (DelV K) (instDelQuiver K) a b → @Quiver.Path V _ a b
  | _, .nil => .nil
  | _, .cons p e => (erasePath K a p).cons e.1

@[simp] theorem erasePath_nil (K : Keep V) (a : V) :
    erasePath K a (Quiver.Path.nil : @Quiver.Path (DelV K) (instDelQuiver K) a a) =
      Quiver.Path.nil := rfl

theorem erasePath_cons (K : Keep V) {a b c : V}
    (p : @Quiver.Path (DelV K) (instDelQuiver K) a b) (e : DelArrow K b c) :
    erasePath K a (p.cons e) = (erasePath K a p).cons e.1 := rfl

theorem erasePath_comp (K : Keep V) {a b c : V}
    (p : @Quiver.Path (DelV K) (instDelQuiver K) a b)
    (q : @Quiver.Path (DelV K) (instDelQuiver K) b c) :
    erasePath K a (p.comp q) = (erasePath K a p).comp (erasePath K b q) := by
  induction q with
  | nil => rw [Quiver.Path.comp_nil, erasePath_nil, Quiver.Path.comp_nil]
  | cons q e ih =>
      rw [Quiver.Path.comp_cons, erasePath_cons, ih, erasePath_cons, Quiver.Path.comp_cons]

theorem erasePath_toPath (K : Keep V) {a b : V} (e : DelArrow K a b) :
    erasePath K a (@Quiver.Hom.toPath (DelV K) (instDelQuiver K) a b e) =
      @Quiver.Hom.toPath V _ a b e.1 := rfl

theorem erasePath_reverse (K : Keep V) {a b : V}
    (p : @Quiver.Path (DelV K) (instDelQuiver K) a b) :
    erasePath K b p.reverse = (erasePath K a p).reverse := by
  induction p with
  | nil => rfl
  | cons q e ih =>
      rw [Quiver.Path.reverse, erasePath_comp]
      rw [erasePath_toPath]
      rw [ih]
      rw [erasePath_cons, Quiver.Path.reverse]
      rfl

theorem erasePath_eq_mapPath (K : Keep V) {a b : V}
    (p : @Quiver.Path (DelV K) (instDelQuiver K) a b) :
    (delIncl K).mapPath p = erasePath K a p := by
  induction p with
  | nil => rfl
  | cons p e ih => rw [Prefunctor.mapPath_cons, erasePath_cons, ih]; rfl

/-- The erasure of a reduced path of `DelV K` is reduced. -/
theorem isReduced_erasePath (K : Keep V) {a b : V}
    {p : @Quiver.Path (DelV K) (instDelQuiver K) a b} (hp : p.IsReduced) :
    (erasePath K a p).IsReduced := by
  rw [← erasePath_eq_mapPath]
  exact Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced (delIncl K) (delIncl_obj_injective K)
    (fun {_ _} => delIncl_map_injective K) hp

/-- `DeleteBacktrack` is preserved by the erasure `DelV K → V`. -/
theorem erasePath_deleteBacktrack (K : Keep V) {a b : V}
    {p r : @Quiver.Path (DelV K) (instDelQuiver K) a b}
    (h : Quiver.Path.DeleteBacktrack p r) :
    Quiver.Path.DeleteBacktrack (erasePath K a p) (erasePath K a r) := by
  rw [← erasePath_eq_mapPath K p, ← erasePath_eq_mapPath K r]
  exact Prefunctor.mapPath_deleteBacktrack (delIncl K) h

theorem isReduced_of_erasePath (K : Keep V) {a b : V}
    {p : @Quiver.Path (DelV K) (instDelQuiver K) a b}
    (h : (erasePath K a p).IsReduced) : p.IsReduced :=
  fun r hr => h _ (erasePath_deleteBacktrack K hr)

/-- Erasure and `IsReduced` are equivalent. -/
theorem isReduced_erasePath_iff (K : Keep V) {a b : V}
    {p : @Quiver.Path (DelV K) (instDelQuiver K) a b} :
    (erasePath K a p).IsReduced ↔ p.IsReduced :=
  ⟨isReduced_of_erasePath K, isReduced_erasePath K⟩

/-- Reduction of a path of `DelV K` and its erasure commute. -/
theorem red_erasePath (K : Keep V) {a b : V}
    (p : @Quiver.Path (DelV K) (instDelQuiver K) a b) :
    red (erasePath K a p) = erasePath K a (red p) := by
  have key : ∀ {c : V} {p r : @Quiver.Path (DelV K) (instDelQuiver K) a c},
      p.ReducesTo r → (erasePath K a p).ReducesTo (erasePath K a r) := by
    intro c p r hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail (erasePath_deleteBacktrack K hstep)
  exact red_eq_of_reducesTo_isReduced (key (reducesTo_red p))
    (isReduced_erasePath K (isReduced_red p))

/-! ## Lifting paths -/

/-- The lift of a path of `V` all of whose arrows satisfy `K.pred`, as a path of `DelV K`. -/
noncomputable def liftPath (K : Keep V) (a : V) : ∀ {b : V} (p : Quiver.Path a b),
    (∀ g ∈ p.arrowList, K.pred g) → @Quiver.Path (DelV K) (instDelQuiver K) a b
  | _, .nil, _ => .nil
  | _, .cons p e, h =>
      ((liftPath K a p (fun g hg => h g (by
          rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hg)))).cons
        ⟨e, h (Quiver.Total.mk _ _ e) (by
          rw [Quiver.Path.arrowList_cons]
          exact List.mem_append.mpr (Or.inr (by simp)))⟩)

@[simp] theorem liftPath_nil (K : Keep V) (a : V)
    (h : ∀ g ∈ (Quiver.Path.nil : Quiver.Path a a).arrowList, K.pred g) :
    liftPath K a Quiver.Path.nil h = Quiver.Path.nil := rfl

theorem liftPath_cons (K : Keep V) {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (h : ∀ g ∈ (p.cons e).arrowList, K.pred g)
    (h' : ∀ g ∈ p.arrowList, K.pred g) (he : K.pred (Quiver.Total.mk b c e)) :
    liftPath K a (p.cons e) h = (liftPath K a p h').cons ⟨e, he⟩ := rfl

theorem erasePath_liftPath (K : Keep V) {a b : V} (p : Quiver.Path a b)
    (h : ∀ g ∈ p.arrowList, K.pred g) :
    erasePath K a (liftPath K a p h) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [liftPath_cons K p e h
        (fun g hg => h g (by
          rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hg)))
        (h (Quiver.Total.mk _ _ e) (by
          rw [Quiver.Path.arrowList_cons]
          exact List.mem_append.mpr (Or.inr (by simp))))]
      rw [erasePath_cons, ih]

theorem isReduced_liftPath (K : Keep V) {a b : V} (p : Quiver.Path a b)
    (h : ∀ g ∈ p.arrowList, K.pred g) :
    (liftPath K a p h).IsReduced ↔ p.IsReduced := by
  rw [← isReduced_erasePath_iff K, erasePath_liftPath]

/-- The erasure of the arrow list of a lift. -/
theorem map_arrowList_liftPath (K : Keep V) {a b : V} (p : Quiver.Path a b)
    (h : ∀ g ∈ p.arrowList, K.pred g) :
    (liftPath K a p h).arrowList.map (toTotal K) = p.arrowList := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have h' : ∀ g ∈ p.arrowList, K.pred g := fun g hg => h g (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hg))
      have he : K.pred (Quiver.Total.mk _ _ e) := h (Quiver.Total.mk _ _ e) (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inr (by simp)))
      rw [liftPath_cons K p e h h' he, Quiver.Path.arrowList_cons, List.map_append, ih,
        Quiver.Path.arrowList_cons]
      rfl

/-- The total arrow associated with an arrow of `p` is an arrow of the lift. -/
theorem ofTotal_mem_arrowList_liftPath (K : Keep V) {a b : V} (p : Quiver.Path a b)
    (h : ∀ g ∈ p.arrowList, K.pred g) {g : Quiver.Total V} (hg : g ∈ p.arrowList) :
    ofTotal K g (h g hg) ∈ (liftPath K a p h).arrowList := by
  induction p with
  | nil => exact absurd hg (by simp)
  | cons p e ih =>
      rw [Quiver.Path.arrowList_cons] at hg
      rcases List.mem_append.mp hg with hg | hg
      · have h' : ∀ g ∈ p.arrowList, K.pred g := fun g hg => h g (by
          rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hg))
        have he : K.pred (Quiver.Total.mk _ _ e) := h (Quiver.Total.mk _ _ e) (by
          rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inr (by simp)))
        rw [liftPath_cons K p e h h' he, Quiver.Path.arrowList_cons]
        exact List.mem_append.mpr (Or.inl (ih h' hg))
      · simp only [List.mem_singleton] at hg
        subst hg
        have he : K.pred (Quiver.Total.mk _ _ e) := h (Quiver.Total.mk _ _ e) (by
          rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inr (by simp)))
        rw [liftPath_cons K p e h (fun g hg => h g (by
          rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hg))) he,
          Quiver.Path.arrowList_cons]
        exact List.mem_append.mpr (Or.inr (by simp))

theorem pathMax_liftPath (K : Keep V) {α : Type u} [LinearOrder α] (ω : Quiver.Total V → α)
    {a b : V} (p : Quiver.Path a b) (h : ∀ g ∈ p.arrowList, K.pred g) :
    pathMax (fun g => ω (toTotal K g)) (liftPath K a p h) = pathMax ω p := by
  rw [pathMax, pathMax, ← map_arrowList_liftPath K p h, List.map_map]
  rfl

theorem pathMin_liftPath (K : Keep V) {α : Type u} [LinearOrder α] (ω : Quiver.Total V → α)
    {a b : V} (p : Quiver.Path a b) (h : ∀ g ∈ p.arrowList, K.pred g) :
    pathMin (fun g => ω (toTotal K g)) (liftPath K a p h) = pathMin ω p := by
  rw [pathMin, pathMin, ← map_arrowList_liftPath K p h, List.map_map]
  rfl

/-- A lift of a cyclically reduced path is cyclically reduced. -/
theorem isCyclicallyReduced_liftPath (K : Keep V) {a : V} (p : Quiver.Path a a)
    (h : ∀ g ∈ p.arrowList, K.pred g) (hp : IsCyclicallyReduced p) :
    IsCyclicallyReduced (liftPath K a p h) := by
  rintro ⟨u, e, q, heq⟩
  have h2 : erasePath K a (liftPath K a p h) =
      erasePath K a (e.toPath.comp (q.cons (Quiver.reverse e))) := congrArg (erasePath K a) heq
  rw [erasePath_liftPath] at h2
  have h3 : erasePath K a (e.toPath.comp (q.cons (Quiver.reverse e))) =
      (e.1.toPath).comp ((erasePath K u q).cons ((Quiver.reverse e).1)) := by
    rw [erasePath_comp, erasePath_toPath, erasePath_cons]
  rw [h3] at h2
  exact hp ⟨u, e.1, erasePath K u q, h2⟩

theorem erasePath_compPower (K : Keep V) {a : V}
    (q : @Quiver.Path (DelV K) (instDelQuiver K) a a) (m : ℕ) :
    erasePath K a (Quiver.Path.compPower q m) = Quiver.Path.compPower (erasePath K a q) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Quiver.Path.compPower_succ, Quiver.Path.compPower_succ, erasePath_comp, ih]

/-- A lift of a path that is not a proper power is not a proper power. -/
theorem not_isProperPower_liftPath (K : Keep V) {a : V} (p : Quiver.Path a a)
    (h : ∀ g ∈ p.arrowList, K.pred g) (hp : ¬ IsProperPower p) :
    ¬ IsProperPower (liftPath K a p h) := by
  rintro ⟨q, m, hm, heq⟩
  refine hp ⟨erasePath K a q, m, hm, ?_⟩
  have h2 : erasePath K a (liftPath K a p h) = erasePath K a (Quiver.Path.compPower q m) :=
    congrArg (erasePath K a) heq
  rw [erasePath_liftPath, erasePath_compPower] at h2
  exact h2

/-- Erasure is multiplicative for the free-groupoid product. -/
theorem erasePath_pmul (K : Keep V) {a b c : V}
    (p : @Quiver.Path (DelV K) (instDelQuiver K) a b)
    (q : @Quiver.Path (DelV K) (instDelQuiver K) b c) :
    erasePath K a (pmul p q) = pmul (erasePath K a p) (erasePath K b q) := by
  show erasePath K a (red (p.comp q)) = red ((erasePath K a p).comp (erasePath K b q))
  rw [← red_erasePath K (p.comp q), erasePath_comp]

end DelV

/-! ## The induced map on the free groupoid -/

/-- The monoid homomorphism `F(DelV K)_x →* F(V)_x` induced by the erasure of paths. -/
noncomputable def delEraseVG (K : Keep V) (x : V) :
    VertexGroup (V := DelV K) x →* VertexGroup (V := V) x where
  toFun q := ⟨DelV.erasePath K x q.1, DelV.isReduced_erasePath K q.2⟩
  map_one' := Subtype.ext (by
    show DelV.erasePath K x (Quiver.Path.nil : @Quiver.Path (DelV K) (instDelQuiver K) x x) =
      Quiver.Path.nil
    rw [DelV.erasePath_nil])
  map_mul' p q := Subtype.ext (by
    show DelV.erasePath K x (pmul p.1 q.1) = pmul (DelV.erasePath K x p.1) (DelV.erasePath K x q.1)
    exact DelV.erasePath_pmul K p.1 q.1)

theorem delEraseVG_apply (K : Keep V) (x : V) (q : VertexGroup (V := DelV K) x) :
    (delEraseVG K x q).1 = DelV.erasePath K x q.1 := rfl

namespace Presentation

variable (P : Presentation V)

/-! ## The deleted presentation -/

/-- The subpresentation on `DelV K` whose relators are those `i` with `J i` all of whose arrows
satisfy `K.pred`. -/
noncomputable def deleteSub (K : Keep V) (J : P.ι → Prop) : Presentation (DelV K) where
  α := P.α
  linearOrder := inferInstance
  edgeOf := fun g => P.edgeOf (DelV.toTotal K g)
  edgeOf_reverse := by
    intro g
    rw [DelV.toTotal_totalReverse, P.edgeOf_reverse]
  noSelfLoop := by
    intro v e hrev
    exact P.noSelfLoop v e.1 (Subtype.ext_iff.mp hrev)
  ι := {i : P.ι // J i ∧ ∀ g ∈ (P.path i).arrowList, K.pred g}
  linearOrder_ι := inferInstance
  base := fun i => P.base i.1
  path := fun i => DelV.liftPath K (P.base i.1) (P.path i.1) i.2.2
  reduced := fun i => (DelV.isReduced_liftPath K (P.path i.1) i.2.2).mpr (P.reduced i.1)
  cyclicallyReduced := fun i =>
    DelV.isCyclicallyReduced_liftPath K (P.path i.1) i.2.2 (P.cyclicallyReduced i.1)
  notProperPower := fun i =>
    DelV.not_isProperPower_liftPath K (P.path i.1) i.2.2 (P.notProperPower i.1)
  staggered := by
    intro i j hij
    rw [DelV.pathMax_liftPath, DelV.pathMax_liftPath, DelV.pathMin_liftPath,
      DelV.pathMin_liftPath]
    exact P.staggered i.1 j.1 hij

@[simp] theorem deleteSub_edgeOf (K : Keep V) (J : P.ι → Prop) (g : Quiver.Total (DelV K)) :
    (P.deleteSub K J).edgeOf g = P.edgeOf (DelV.toTotal K g) := rfl

/-- The inclusion of vertex groups `(P.deleteSub K J).vertexGroup x →* P.vertexGroup x` induced by the
inclusion of the subpresentation. -/
noncomputable def deleteSubInclVG (K : Keep V) (J : P.ι → Prop) (x : DelV K) :
    (P.deleteSub K J).vertexGroup x →* P.vertexGroup x :=
  QuotientGroup.lift ((P.deleteSub K J).relatorNormalClosure x)
    ((P.toVertexGroup x).comp (delEraseVG K x))
    (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro y ⟨i, δ, hδ, rfl⟩
      change P.toVertexGroup x (delEraseVG K x ⟨pmul δ (pmul ((P.deleteSub K J).path i) δ.reverse),
        pmul_isReduced _ _⟩) = 1
      have hmem : delEraseVG K x ⟨pmul δ (pmul ((P.deleteSub K J).path i) δ.reverse),
          pmul_isReduced _ _⟩ ∈ P.relatorNormalClosure x := by
        apply Subgroup.subset_normalClosure
        refine ⟨i.1, DelV.erasePath K x δ, DelV.isReduced_erasePath K hδ, ?_⟩
        apply Subtype.ext
        show DelV.erasePath K x (pmul δ (pmul ((P.deleteSub K J).path i) δ.reverse)) =
          pmul (DelV.erasePath K x δ) (pmul (P.path i.1) (DelV.erasePath K x δ).reverse)
        rw [DelV.erasePath_pmul, DelV.erasePath_pmul, DelV.erasePath_reverse,
          show DelV.erasePath K ((P.deleteSub K J).base i) ((P.deleteSub K J).path i) = P.path i.1 from
            DelV.erasePath_liftPath K (P.path i.1) i.2.2]
      rw [P.toVertexGroup_apply, QuotientGroup.eq_one_iff]
      exact hmem)

end Presentation

end Work.ORLocInd.Howie
