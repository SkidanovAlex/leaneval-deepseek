/-
# Substitution machinery for the Tietze elimination step (L4)

This file develops the path-substitution `PathSubst.mapPath` of a path-valued graph morphism
(`TietzeSupport.PathSubst`) into a homomorphism of free-groupoid vertex groups
(`PathSubst.vertexHom`), together with the lemmas needed to run the Tietze elimination
`deleteSubInclVG` of `Delete.lean` through `abstract_tietze`.

It also constructs the data `TietzeData P` from the hypotheses of the edge-count form of the
Tietze step (`edgeCount P.edgeOf (P.path i₀) f = 1`).
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.TietzeSupport
import Submission.Work.ORLocInd.Howie.Delete
import Submission.Work.ORLocInd.Howie.exists_split_arrowList
import Submission.Work.ORLocInd.Howie.filter_length_one
import Submission.Work.ORLocInd.Howie.mem_relatorNormalClosure_conj
import Submission.Work.ORLocInd.Howie.pmul_congr_left
import Submission.Work.ORLocInd.Howie.abstract_tietze

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Building the Tietze data from the edge-count hypotheses -/

/-- If no arrow of `P.path i` carries the code of `f`, then every arrow of `P.path i` is kept by
`P.keepCode (P.edgeOf f)`. -/
theorem keepPath_of_edgeCount_zero (P : Presentation V) (i : P.ι) (f : Quiver.Total V)
    (hf : edgeCount P.edgeOf (P.path i) f = 0) :
    ∀ e ∈ (P.path i).arrowList, (P.keepCode (P.edgeOf f)).pred e := by
  intro e he hcode
  have hnil : (P.path i).arrowList.filter (fun g => P.edgeOf g = P.edgeOf f) = [] :=
    List.length_eq_zero_iff.mp hf
  exact (List.filter_eq_nil_iff.mp hnil e he) (by simpa using hcode)

/-- From `edgeCount P.edgeOf (P.path i₀) f = 1`, build the Tietze data: the distinguished arrow
`g` of the relator `i₀` (the unique one of code `P.edgeOf f`) and the splitting of the relator at
it, with the arrow set pinned to `P.keepCode (P.edgeOf f)`, and `f`, `i₀` fixed. -/
theorem exists_tietzeData (P : Presentation V) (hsep : P.CodeSeparates) (i₀ : P.ι)
    (f : Quiver.Total V) (hf₀ : edgeCount P.edgeOf (P.path i₀) f = 1) :
    ∃ D : TietzeData P, D.K = P.keepCode (P.edgeOf f) ∧ D.f = f ∧ D.i₀ = i₀ := by
  classical
  have hfilt : ((P.path i₀).arrowList.filter (fun g => P.edgeOf g = P.edgeOf f)).length = 1 := hf₀
  obtain ⟨g, hg_eq, hg_mem, hg_code, hg_uniq⟩ := filter_length_one hfilt
  obtain ⟨q₁, q₂, hsplit, harrow⟩ := exists_split_arrowList (P.path i₀) g hg_mem
  have hlen : ((P.path i₀).arrowList.filter (fun g => P.edgeOf g = P.edgeOf f)).length
      = (q₁.arrowList.filter (fun g => P.edgeOf g = P.edgeOf f)).length
        + ([g].filter (fun g => P.edgeOf g = P.edgeOf f)).length
        + (q₂.arrowList.filter (fun g => P.edgeOf g = P.edgeOf f)).length := by
    rw [harrow, List.filter_append, List.filter_append, List.length_append, List.length_append]
  have hfilter_g : ([g].filter (fun g => P.edgeOf g = P.edgeOf f)).length = 1 := by
    rw [List.filter_singleton]
    simp [hg_code]
  have hkeep_of : ∀ {l : List (Quiver.Total V)},
      (l.filter (fun g => P.edgeOf g = P.edgeOf f)).length = 0 →
      ∀ e ∈ l, P.edgeOf e ≠ P.edgeOf f := by
    intro l hl e he hcode
    have hnil : l.filter (fun g => P.edgeOf g = P.edgeOf f) = [] := List.length_eq_zero_iff.mp hl
    exact (List.filter_eq_nil_iff.mp hnil e he) (by simpa using hcode)
  have hlen₁ : (q₁.arrowList.filter (fun g => P.edgeOf g = P.edgeOf f)).length = 0 := by
    rw [hfilt, hfilter_g] at hlen; omega
  have hlen₂ : (q₂.arrowList.filter (fun g => P.edgeOf g = P.edgeOf f)).length = 0 := by
    rw [hfilt, hfilter_g] at hlen; omega
  refine ⟨TietzeData.mk (P.keepCode (P.edgeOf f)) f i₀ (fun e => ⟨fun h => h, fun h => h⟩) hsep
      g q₁ q₂ hsplit hg_code (hkeep_of hlen₁) (hkeep_of hlen₂), rfl, rfl, rfl⟩

/-! ## `substArrow` sends reverses to reverses and keeps kept arrows -/

namespace TietzeData

variable {P : Presentation V} (D : TietzeData P)

theorem substArrow_reverse (e : Quiver.Total V) :
    D.substArrow (Quiver.totalReverse e) = dreverse (D.substArrow e) := by
  classical
  by_cases he : e = D.g
  · subst he
    rw [D.substArrow_reverse_g, D.substArrow_g]
  · by_cases he' : e = Quiver.totalReverse D.g
    · subst he'
      have hX : D.substArrow (Quiver.totalReverse (Quiver.totalReverse D.g)) = D.phi := by
        have h2 : Quiver.totalReverse (Quiver.totalReverse D.g) = D.g :=
          Quiver.totalReverse_involutive D.g
        rw [TietzeData.substArrow, dif_pos h2]
        exact eq_of_heq (eqRec_heq_iff.mpr HEq.rfl)
      rw [hX, D.substArrow_reverse_g, dreverse_dreverse]
    · rw [D.substArrow_of_ne (D.totalReverse_ne_g he') (D.totalReverse_ne_totalReverse he),
        D.substArrow_of_ne he he', dreverse_dcons_dnil]
      first
        | rfl
        | exact congrArg (fun x => dcons (dnil D.K e.right) x) (Subtype.ext rfl)

theorem substArrow_of_pred {e : Quiver.Total V} (h : D.K.pred e) :
    D.substArrow e = dcons (dnil D.K e.left) ⟨e.hom, h⟩ := by
  classical
  have hne1 : e ≠ D.g := fun he => (D.hK e).mp h (by rw [he]; exact D.code)
  have hne2 : e ≠ Quiver.totalReverse D.g := fun he =>
    (D.hK e).mp h (by rw [he, P.edgeOf_reverse]; exact D.code)
  rw [D.substArrow_of_ne hne1 hne2]

end TietzeData

/-- The reduced form of a concatenation is the free-groupoid product of the reduced forms. -/
theorem red_comp {a b c : V} (A : Quiver.Path a b) (B : Quiver.Path b c) :
    red (A.comp B) = pmul (red A) (red B) := by
  have h1 : (A.comp B).ReducesTo ((red A).comp (red B)) :=
    (Quiver.Path.ReducesTo.comp_right (reducesTo_red A) B).trans
      (reducesTo_comp_left (reducesTo_red B) (red A))
  have h2 : (A.comp B).ReducesTo (red ((red A).comp (red B))) := h1.trans (reducesTo_red _)
  rw [red_eq_of_reducesTo_isReduced h2 (isReduced_red _)]
  rfl

namespace DelV

theorem restrictPath_eq_liftPath (K : Keep V) {a b : V} (p : Quiver.Path a b)
    (h : ∀ e ∈ p.arrowList, K.pred e) :
    restrictPath K a p h = liftPath K a p h := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have h' : ∀ g ∈ p.arrowList, K.pred g := fun g hg => h g (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hg))
      have he : K.pred (Quiver.Total.mk _ _ e) := h (Quiver.Total.mk _ _ e) (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inr (by simp)))
      rw [restrictPath_cons K p e h, liftPath_cons K p e h h' he, ih h']

theorem isReduced_restrictPath (K : Keep V) {a b : V} (p : Quiver.Path a b)
    (h : ∀ e ∈ p.arrowList, K.pred e) :
    (restrictPath K a p h).IsReduced ↔ p.IsReduced := by
  rw [restrictPath_eq_liftPath K p h]
  exact isReduced_liftPath K p h

end DelV

/-! ## `PathSubst.mapPath` basic equations -/

namespace PathSubst

variable {K : Keep V}

theorem mapPath_nil (s : PathSubst K) (a : V) :
    s.mapPath (Quiver.Path.nil : Quiver.Path a a) = dnil K a := rfl

theorem mapPath_cons (s : PathSubst K) {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c) :
    s.mapPath (p.cons e) = dcomp (s.mapPath p) (s.mapArrow (Quiver.Total.mk b c e)) := rfl

theorem mapPath_toPath (s : PathSubst K) {a b : V} (e : a ⟶ b) :
    s.mapPath (Quiver.Hom.toPath e) = s.mapArrow (Quiver.Total.mk a b e) := by
  simp only [Quiver.Hom.toPath]
  rw [mapPath_cons, mapPath_nil]
  exact dnil_dcomp _

theorem mapArrow_reverse_mk (s : PathSubst K) {a b : V} (e : a ⟶ b) :
    s.mapArrow (Quiver.Total.mk b a (Quiver.reverse e)) =
      (s.mapArrow (Quiver.Total.mk a b e)).reverse :=
  s.mapArrow_reverse (Quiver.Total.mk a b e)

theorem mapPath_comp (s : PathSubst K) {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) :
    s.mapPath (p.comp q) = dcomp (s.mapPath p) (s.mapPath q) := by
  induction q with
  | nil => rw [Quiver.Path.comp_nil, mapPath_nil, dcomp_nil]
  | cons q e ih => rw [Quiver.Path.comp_cons, mapPath_cons, ih, mapPath_cons, dcomp_assoc]

theorem mapPath_comp_red (s : PathSubst K) {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) :
    red (s.mapPath (p.comp q)) = pmul (red (s.mapPath p)) (red (s.mapPath q)) := by
  rw [mapPath_comp, red_comp]

theorem mapPath_reverse (s : PathSubst K) {a b : V} (p : Quiver.Path a b) :
    s.mapPath p.reverse = (s.mapPath p).reverse := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hrev : (p.cons e).reverse = (Quiver.reverse e).toPath.comp p.reverse := rfl
      rw [hrev, mapPath_comp, mapPath_toPath, ih, mapPath_cons, Quiver.Path.reverse_comp,
        mapArrow_reverse_mk]

theorem mapPath_deleteBacktrack (s : PathSubst K) {a b : V} {p q : Quiver.Path a b}
    (h : Quiver.Path.DeleteBacktrack p q) : (s.mapPath p).ReducesTo (s.mapPath q) := by
  cases h with
  | intro p₁ e p₂ =>
    have hL : s.mapPath (p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)))
        = dcomp (s.mapPath p₁) (dcomp (s.mapArrow (Quiver.Total.mk _ _ e))
            (dcomp ((s.mapArrow (Quiver.Total.mk _ _ e)).reverse) (s.mapPath p₂))) := by
      rw [mapPath_comp, mapPath_comp, mapPath_comp, mapPath_toPath, mapPath_toPath,
        mapArrow_reverse_mk]
    rw [hL, mapPath_comp]
    refine reducesTo_comp_left ?_ (s.mapPath p₁)
    rw [← dcomp_assoc]
    have h1 : (dcomp (s.mapArrow (Quiver.Total.mk _ _ e))
        (dreverse (s.mapArrow (Quiver.Total.mk _ _ e)))).ReducesTo (dnil K _) :=
      Work.ORBassSerre.Path.Reduction.reducesTo_nil_comp_reverse _
    have h2 := h1.comp_right (s.mapPath p₂)
    simpa only [dnil_dcomp] using h2

theorem mapPath_reducesTo (s : PathSubst K) {a b : V} {p q : Quiver.Path a b}
    (h : p.ReducesTo q) : (s.mapPath p).ReducesTo (s.mapPath q) := by
  induction h with
  | refl => exact Quiver.Path.ReducesTo.refl _
  | tail _ hstep ih => exact ih.trans (mapPath_deleteBacktrack s hstep)

theorem mapPath_red (s : PathSubst K) {a b : V} (X : Quiver.Path a b) :
    red (s.mapPath X) = red (s.mapPath (red X)) :=
  red_eq_of_reducesTo_isReduced
    ((mapPath_reducesTo s (reducesTo_red X)).trans (reducesTo_red _)) (isReduced_red _)

theorem mapPath_erasePath (s : PathSubst K)
    (hmap : ∀ (e : Quiver.Total V) (h : K.pred e),
      s.mapArrow e = dcons (dnil K e.left) ⟨e.hom, h⟩)
    {a b : V} (p : @Quiver.Path (DelV K) (instDelQuiver K) a b) :
    s.mapPath (DelV.erasePath K a p) = p := by
  induction p using Quiver.Path.rec with
  | nil => rfl
  | cons p e ih =>
      obtain ⟨e₀, he₀⟩ := e
      rw [DelV.erasePath_cons, mapPath_cons, ih, hmap (Quiver.Total.mk _ _ e₀) he₀]
      exact @Quiver.Path.comp_toPath_eq_cons (DelV K) (instDelQuiver K) _ _ _ p ⟨e₀, he₀⟩

/-! ## The induced homomorphism of vertex groups -/

/-- The homomorphism of free-groupoid vertex groups `F(Γ)_x →* F(Γ')_x` induced by a
path-valued graph morphism `s`. -/
noncomputable def vertexHom (s : PathSubst K) (x : V) :
    VertexGroup x →* VertexGroup (V := DelV K) x where
  toFun p := ⟨red (s.mapPath p.1), isReduced_red _⟩
  map_one' := Subtype.ext (by
    show red (s.mapPath (Quiver.Path.nil : Quiver.Path x x)) = Quiver.Path.nil
    rw [mapPath_nil, red_nil])
  map_mul' p q := Subtype.ext (by
    show red (s.mapPath (pmul p.1 q.1)) =
      pmul (red (s.mapPath p.1)) (red (s.mapPath q.1))
    rw [show pmul p.1 q.1 = red (p.1.comp q.1) from rfl,
      ← mapPath_red s (p.1.comp q.1), mapPath_comp]
    show pmul (s.mapPath p.1) (s.mapPath q.1) =
      pmul (red (s.mapPath p.1)) (red (s.mapPath q.1))
    exact (pmul_congr_left (s.mapPath p.1) (red (s.mapPath p.1)) (reducesTo_red _)
      (s.mapPath q.1)).trans (pmul_congr_right (red (s.mapPath p.1)) (reducesTo_red _)))

@[simp] theorem vertexHom_apply (s : PathSubst K) (x : V) (p : VertexGroup x) :
    ((vertexHom s x) p).1 = red (s.mapPath p.1) := rfl

theorem mapPath_pmul (s : PathSubst K) {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) :
    red (s.mapPath (pmul p q)) = pmul (red (s.mapPath p)) (red (s.mapPath q)) := by
  rw [show pmul p q = red (p.comp q) from rfl, ← mapPath_red s (p.comp q), mapPath_comp]
  show pmul (s.mapPath p) (s.mapPath q) =
    pmul (red (s.mapPath p)) (red (s.mapPath q))
  exact (pmul_congr_left (s.mapPath p) (red (s.mapPath p)) (reducesTo_red _)
    (s.mapPath q)).trans (pmul_congr_right (red (s.mapPath p)) (reducesTo_red _))

theorem mapPath_eq_liftPath (s : PathSubst K)
    (hmap : ∀ (e : Quiver.Total V) (h : K.pred e),
      s.mapArrow e = dcons (dnil K e.left) ⟨e.hom, h⟩)
    {a b : V} (p : Quiver.Path a b) (h : ∀ e ∈ p.arrowList, K.pred e) :
    s.mapPath p = DelV.liftPath K a p h := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have h' : ∀ g ∈ p.arrowList, K.pred g := fun g hg => h g (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hg))
      have he : K.pred (Quiver.Total.mk _ _ e) := h (Quiver.Total.mk _ _ e) (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inr (by simp)))
      rw [DelV.liftPath_cons K p e h h' he, mapPath_cons, ih h',
        hmap (Quiver.Total.mk _ _ e) he]
      exact @Quiver.Path.comp_toPath_eq_cons (DelV K) (instDelQuiver K) _ _ _
        (DelV.liftPath K a p h') ⟨e, he⟩

theorem mapPath_eq_restrictPath (s : PathSubst K)
    (hmap : ∀ (e : Quiver.Total V) (h : K.pred e),
      s.mapArrow e = dcons (dnil K e.left) ⟨e.hom, h⟩)
    {a b : V} (p : Quiver.Path a b) (h : ∀ e ∈ p.arrowList, K.pred e) :
    s.mapPath p = restrictPath K a p h :=
  (mapPath_eq_liftPath s hmap p h).trans
    (DelV.restrictPath_eq_liftPath K p h).symm

end PathSubst

/-! ## The path substitution attached to the Tietze data -/

namespace TietzeData

variable {P : Presentation V} (D : TietzeData P)

/-- The path-valued graph morphism of the Tietze elimination: the identity on kept arrows and
`g ↦ q₁⁻¹ · q₂⁻¹` on the distinguished arrow of the relator `i₀`. -/
noncomputable def pathSubst : PathSubst D.K :=
  ⟨D.substArrow, D.substArrow_reverse⟩

@[simp] theorem pathSubst_mapArrow (e : Quiver.Total V) :
    D.pathSubst.mapArrow e = D.substArrow e := rfl

theorem pathSubst_mapPath_erasePath {a b : V} (p : DPath D.K a b) :
    D.pathSubst.mapPath (DelV.erasePath D.K a p) = p :=
  PathSubst.mapPath_erasePath D.pathSubst (fun e h => D.substArrow_of_pred h) p

theorem pathSubst_mapPath_liftPath {a b : V} (p : Quiver.Path a b)
    (h : ∀ e ∈ p.arrowList, D.K.pred e) :
    D.pathSubst.mapPath p = DelV.liftPath D.K a p h :=
  PathSubst.mapPath_eq_liftPath D.pathSubst (fun e h => D.substArrow_of_pred h) p h

theorem pathSubst_mapPath_restrictPath {a b : V} (p : Quiver.Path a b)
    (h : ∀ e ∈ p.arrowList, D.K.pred e) :
    D.pathSubst.mapPath p = restrictPath D.K a p h :=
  PathSubst.mapPath_eq_restrictPath D.pathSubst (fun e h => D.substArrow_of_pred h) p h

/-- A path immediately preceded by its reverse is null-reducible. -/
theorem reducesTo_reverse_comp_nil {a : V} (p : DPath D.K a a) :
    (dcomp (dreverse p) p).ReducesTo (dnil D.K a) := by
  have h := Work.ORBassSerre.Path.Reduction.reducesTo_nil_comp_reverse (dreverse p)
  simpa [dreverse_dreverse] using h

theorem phi_isReduced : D.phi.IsReduced := pmul_isReduced _ _

/-- The distinguished relator of the Tietze data becomes null after the substitution. -/
theorem red_pathSubst_path_i₀ :
    red (D.pathSubst.mapPath (P.path D.i₀)) = dnil D.K (P.base D.i₀) := by
  have hφ : red (D.pathSubst.mapPath (P.path D.i₀))
      = pmul (red (restrictPath D.K (P.base D.i₀) D.q₁ D.keep₁))
          (pmul D.phi (red (restrictPath D.K D.g.right D.q₂ D.keep₂))) := by
    rw [D.split, PathSubst.mapPath_comp, PathSubst.mapPath_comp, red_comp, red_comp,
      PathSubst.mapPath_toPath, TietzeData.pathSubst_mapArrow,
      show D.substArrow (Quiver.Total.mk D.g.left D.g.right D.g.hom) = D.phi from D.substArrow_g,
      red_eq_self D.phi_isReduced,
      D.pathSubst_mapPath_restrictPath D.q₁ D.keep₁,
      D.pathSubst_mapPath_restrictPath D.q₂ D.keep₂]
  rw [hφ]
  have hφ2 : D.phi = pmul (dreverse (restrictPath D.K (P.base D.i₀) D.q₁ D.keep₁))
      (dreverse (restrictPath D.K D.g.right D.q₂ D.keep₂)) := rfl
  rw [hφ2, ← pmul_assoc, ← pmul_assoc,
    show pmul (red (restrictPath D.K (P.base D.i₀) D.q₁ D.keep₁))
        (dreverse (restrictPath D.K (P.base D.i₀) D.q₁ D.keep₁)) = dnil D.K (P.base D.i₀) from
      (pmul_red_left _ _).trans (pmul_reverse _),
    pmul_nil_left,
    show red (dreverse (restrictPath D.K D.g.right D.q₂ D.keep₂))
        = (red (restrictPath D.K D.g.right D.q₂ D.keep₂)).reverse from
      red_reverse (restrictPath D.K D.g.right D.q₂ D.keep₂)]
  exact pmul_reverse_left _

end TietzeData

end Work.ORLocInd.Howie
