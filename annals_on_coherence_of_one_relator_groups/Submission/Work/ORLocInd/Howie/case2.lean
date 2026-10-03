import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.indicable_of_labelling
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.Basic
import Submission.Work.ORLocInd.Howie.Cover
import Submission.Work.ORLocInd.Howie.CoverPresentation
import Submission.Work.ORLocInd.Howie.PathSumHom
import Submission.Work.ORLocInd.Howie.hasIndicableLabelling_of_loop
import Submission.Work.ORLocInd.Howie.presentation_path_ne_nil
import Submission.Work.ORLocInd.Howie.edgeCount_cons
import Submission.Work.ORLocInd.Howie.span_noSelfLoop
import Submission.Work.ORLocInd.Howie.Delete
import Submission.Work.ORLocInd.Howie.Case2Labelling
import Submission.Work.ORLocInd.Howie.Case2Bridge
import Submission.Work.ORLocInd.Howie.L5.edgeCount_eq_one_of_forest_del
import Submission.Work.ORLocInd.Howie.L5.edgeCount_even_of_bridge_del
import Submission.Work.ORLocInd.Howie.L5.false_of_bridge_forest_side_del
import Submission.Work.ORLocInd.Howie.hasIndicableLabelling_of_bijective
import Submission.Work.ORLocInd.Howie.DelReach
import Submission.Work.ORLocInd.Howie.L4.deleteSubInclVG_bijective
import Submission.Work.ORLocInd.Howie.C2.inSide_arrow_of_code_eq_of_mem
import Submission.Work.ORLocInd.Howie.C2.hasIndicableLabelling_of_both_sides
import Submission.Work.ORLocInd.Howie.C2.not_hasIndicableLabelling_bridgePresentation
import Submission.Work.ORLocInd.Howie.C2.false_of_bridge_forest_side_exists

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Auxiliary lemmas on `pathMax` and `pathMin` -/

section EdgeOrder

variable {α : Type u} [LinearOrder α]

theorem le_foldr_max {l : List (WithBot α)} {x : WithBot α} (hx : x ∈ l) :
    x ≤ l.foldr max ⊥ := by
  induction l with
  | nil => simp at hx
  | cons y t ih =>
      show x ≤ max y (t.foldr max ⊥)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih hx) (le_max_right _ _)

theorem foldr_max_mem : ∀ {l : List (WithBot α)}, l ≠ [] → l.foldr max ⊥ ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons y t ih =>
      intro _
      show max y (t.foldr max ⊥) ∈ y :: t
      rcases eq_or_ne t [] with rfl | ht
      · show max y ⊥ ∈ [y]
        rw [le_antisymm (max_le le_rfl (bot_le : (⊥ : WithBot α) ≤ y)) (le_max_left _ _)]
        exact List.mem_cons.mpr (Or.inl rfl)
      · rcases max_choice y (t.foldr max ⊥) with h | h
        · rw [h]; exact List.mem_cons.mpr (Or.inl rfl)
        · rw [h]; exact List.mem_cons.mpr (Or.inr (ih ht))

theorem foldr_min_le {l : List (WithTop α)} {x : WithTop α} (hx : x ∈ l) :
    l.foldr min ⊤ ≤ x := by
  induction l with
  | nil => simp at hx
  | cons y t ih =>
      show min y (t.foldr min ⊤) ≤ x
      rcases List.mem_cons.mp hx with rfl | hx
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih hx)

theorem foldr_min_mem : ∀ {l : List (WithTop α)}, l ≠ [] → l.foldr min ⊤ ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons y t ih =>
      intro _
      show min y (t.foldr min ⊤) ∈ y :: t
      rcases eq_or_ne t [] with rfl | ht
      · show min y ⊤ ∈ [y]
        rw [← le_antisymm (le_min le_rfl (le_top : y ≤ (⊤ : WithTop α))) (min_le_left _ _)]
        exact List.mem_cons.mpr (Or.inl rfl)
      · rcases min_choice y (t.foldr min ⊤) with h | h
        · rw [h]; exact List.mem_cons.mpr (Or.inl rfl)
        · rw [h]; exact List.mem_cons.mpr (Or.inr (ih ht))

theorem le_pathMax (ω : Quiver.Total V → α) {a b : V} {p : Quiver.Path a b} {g : Quiver.Total V}
    (hg : g ∈ p.arrowList) : (ω g : WithBot α) ≤ pathMax ω p :=
  le_foldr_max (List.mem_map_of_mem hg)

theorem pathMin_le (ω : Quiver.Total V → α) {a b : V} {p : Quiver.Path a b} {g : Quiver.Total V}
    (hg : g ∈ p.arrowList) : pathMin ω p ≤ (ω g : WithTop α) :=
  foldr_min_le (List.mem_map_of_mem hg)

theorem exists_pathMax_eq (ω : Quiver.Total V → α) {a b : V} {p : Quiver.Path a b}
    (hp : p.arrowList ≠ []) : ∃ g ∈ p.arrowList, pathMax ω p = (ω g : WithBot α) := by
  have hne : p.arrowList.map (fun e => (ω e : WithBot α)) ≠ [] := by simpa using hp
  have hmem := foldr_max_mem (l := p.arrowList.map (fun e => (ω e : WithBot α))) hne
  obtain ⟨g, hg, hgeq⟩ := List.mem_map.mp hmem
  exact ⟨g, hg, hgeq.symm⟩

theorem exists_pathMin_eq (ω : Quiver.Total V → α) {a b : V} {p : Quiver.Path a b}
    (hp : p.arrowList ≠ []) : ∃ g ∈ p.arrowList, pathMin ω p = (ω g : WithTop α) := by
  have hne : p.arrowList.map (fun e => (ω e : WithTop α)) ≠ [] := by simpa using hp
  have hmem := foldr_min_mem (l := p.arrowList.map (fun e => (ω e : WithTop α))) hne
  obtain ⟨g, hg, hgeq⟩ := List.mem_map.mp hmem
  exact ⟨g, hg, hgeq.symm⟩

/-- `edgeCount` vanishes exactly when no arrow of the path has the code of `e`. -/
theorem edgeCount_eq_zero_iff (ω : Quiver.Total V → α) {a b : V} (p : Quiver.Path a b)
    (e : Quiver.Total V) :
    edgeCount ω p e = 0 ↔ ∀ g ∈ p.arrowList, ω g ≠ ω e := by
  show ((p.arrowList.filter (fun g => ω g = ω e))).length = 0 ↔ _
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  constructor
  · intro h g hg hge
    exact h g hg (by simp [hge])
  · intro h g hg
    simpa using h g hg

/-- If no arrow of `p` has the code of `e`, then `edgeCount` vanishes. -/
theorem edgeCount_eq_zero (ω : Quiver.Total V → α) {a b : V} (p : Quiver.Path a b)
    (e : Quiver.Total V) (h : ∀ g ∈ p.arrowList, ω g ≠ ω e) : edgeCount ω p e = 0 := by
  show ((p.arrowList.filter (fun g => ω g = ω e))).length = 0
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  simpa using h g hg

/-- `edgeCount` depends on `e` only through its code. -/
theorem edgeCount_congr_code (ω : Quiver.Total V → α) {a b : V} (p : Quiver.Path a b)
    {e e' : Quiver.Total V} (h : ω e = ω e') : edgeCount ω p e = edgeCount ω p e' := by
  show ((p.arrowList.filter (fun g => ω g = ω e))).length =
    ((p.arrowList.filter (fun g => ω g = ω e'))).length
  rw [h]

end EdgeOrder

/-! ## Relator paths are nonempty -/

theorem arrowList_ne_nil (P : Presentation V) (i : P.ι) : (P.path i).arrowList ≠ [] := by
  intro h
  refine presentation_path_ne_nil P i (Quiver.Path.eq_nil_of_length_zero (P.path i) ?_)
  rw [← Quiver.Path.arrowList_length_eq, h]
  rfl

/-! ## An arrow of maximal code in the maximal relator -/

/-- An arrow `e` of the maximal relator `m` whose code occurs in no other relator. -/
theorem exists_maxCode_arrow (P : Presentation V) (m : P.ι) (hm : ∀ i : P.ι, i ≤ m) :
    ∃ e ∈ (P.path m).arrowList, ∀ i : P.ι, i ≠ m → edgeCount P.edgeOf (P.path i) e = 0 := by
  obtain ⟨e, he, hmax⟩ := exists_pathMax_eq P.edgeOf (arrowList_ne_nil P m)
  refine ⟨e, he, ?_⟩
  intro i him
  have hli : i < m := lt_of_le_of_ne (hm i) him
  have hst := (P.staggered i m hli).1
  rw [hmax] at hst
  refine edgeCount_eq_zero P.edgeOf _ e ?_
  intro g hg hge
  have h1 := le_pathMax P.edgeOf hg
  have h2 : (P.edgeOf g : WithBot P.α) < (P.edgeOf e : WithBot P.α) := lt_of_le_of_lt h1 hst
  rw [hge] at h2
  exact absurd h2 (lt_irrefl _)

/-! ## Basic properties of the deleted presentation -/

theorem deleteSub_codeSeparates (P : Presentation V) (K : Keep V) (J : P.ι → Prop)
    (hsep : P.CodeSeparates) : (P.deleteSub K J).CodeSeparates := by
  intro g g' h
  have h' : P.edgeOf (DelV.toTotal K g) = P.edgeOf (DelV.toTotal K g') := h
  rcases hsep _ _ h' with h1 | h1
  · exact Or.inl (DelV.toTotal_injective K h1)
  · refine Or.inr (DelV.toTotal_injective K ?_)
    rw [DelV.toTotal_totalReverse]
    exact h1

theorem finite_total_delV (K : Keep V) [Finite (Quiver.Total V)] :
    Finite (Quiver.Total (DelV K)) :=
  Finite.of_injective (DelV.toTotal K) (DelV.toTotal_injective K)

theorem finite_deleteSub_iota (P : Presentation V) (K : Keep V) (J : P.ι → Prop)
    [Finite P.ι] : Finite (P.deleteSub K J).ι :=
  Finite.of_injective Subtype.val (fun _ _ h => Subtype.ext h)

/-! ## Transferring edge counts between a presentation and its deletion -/

theorem length_filter_map {α β : Type*} (f : β → α) (l : List β) (q : α → Prop)
    [DecidablePred q] :
    ((l.map f).filter q).length = (l.filter (fun b => q (f b))).length := by
  induction l with
  | nil => rfl
  | cons b t ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases hb : q (f b)
      · simp [hb, ih]
      · simp [hb, ih]

/-- The edge count of a relator of `P` equals the edge count of the corresponding relator of
`P.deleteSub K J`. -/
theorem edgeCount_deleteSub (P : Presentation V) (K : Keep V) (J : P.ι → Prop)
    (i : P.ι) (hJ : J i) (hK : ∀ g ∈ (P.path i).arrowList, K.pred g)
    (g : Quiver.Total V) (hg : g ∈ (P.path i).arrowList) :
    edgeCount P.edgeOf (P.path i) g =
      edgeCount (P.deleteSub K J).edgeOf ((P.deleteSub K J).path ⟨i, hJ, hK⟩)
        (DelV.ofTotal K g (hK g hg)) := by
  show ((P.path i).arrowList.filter (fun f => P.edgeOf f = P.edgeOf g)).length =
    (((DelV.liftPath K (P.base i) (P.path i) hK).arrowList).filter
      (fun f' => P.edgeOf (DelV.toTotal K f') = P.edgeOf g)).length
  rw [← length_filter_map (DelV.toTotal K) ((DelV.liftPath K (P.base i) (P.path i) hK).arrowList)
      (fun f => P.edgeOf f = P.edgeOf g),
    DelV.map_arrowList_liftPath K (P.path i) hK]

/-- An arrow of the lifted path corresponds to an arrow of the original path satisfying the
keep predicate. -/
theorem toTotal_mem_arrowList_liftPath (K : Keep V) {a b : V} (p : Quiver.Path a b)
    (h : ∀ g ∈ p.arrowList, K.pred g) {g' : Quiver.Total (DelV K)}
    (hg' : g' ∈ (DelV.liftPath K a p h).arrowList) :
    DelV.toTotal K g' ∈ p.arrowList ∧ K.pred (DelV.toTotal K g') := by
  have h1 : DelV.toTotal K g' ∈ (DelV.liftPath K a p h).arrowList.map (DelV.toTotal K) :=
    List.mem_map_of_mem hg'
  rw [DelV.map_arrowList_liftPath K p h] at h1
  exact ⟨h1, h _ h1⟩

/-! ## The code of the arrows of an erased path -/

theorem code_ne_of_mem_erasePath (P : Presentation V) (K : Keep V) (e : Quiver.Total V)
    (hK : ∀ g : Quiver.Total V, K.pred g → P.edgeOf g ≠ P.edgeOf e) :
    ∀ {a b : V} (q : @Quiver.Path (DelV K) (instDelQuiver K) a b) {g : Quiver.Total V},
      g ∈ (DelV.erasePath K a q).arrowList → P.edgeOf g ≠ P.edgeOf e := by
  intro a b q
  induction q with
  | nil =>
      intro g hg
      rw [DelV.erasePath_nil, Quiver.Path.arrowList_nil] at hg
      exact absurd hg List.not_mem_nil
  | cons q f ih =>
      intro g hg
      rw [DelV.erasePath_cons, Quiver.Path.arrowList_cons] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact ih hg
      · simp only [List.mem_singleton] at hg
        subst hg
        exact hK _ f.2

/-! ## Step 1 of Howie's Case 2 in the connected case -/

/-- Deleting the maximal relator, together with the arrows of its maximal code, does not create an
indicable labelling (provided the deleted edge is not a bridge). -/
theorem not_hasIndicableLabelling_deleteSub_max (P : Presentation V) (hsep : P.CodeSeparates)
    (m : P.ι) (hm : ∀ i : P.ι, i ≤ m) (e : Quiver.Total V) (he : e ∈ (P.path m).arrowList)
    (hedge : ∀ i : P.ι, i ≠ m → edgeCount P.edgeOf (P.path i) e = 0)
    (hconn : Nonempty (dpath (P.keepCode (P.edgeOf e)) e.right e.left))
    (hnon : ¬ P.HasIndicableLabelling) :
    ¬ (P.deleteSub (P.keepCode (P.edgeOf e)) (fun i => i ≠ m)).HasIndicableLabelling := by
  classical
  set K : Keep V := P.keepCode (P.edgeOf e)
  have hKpred : ∀ g : Quiver.Total V, K.pred g ↔ P.edgeOf g ≠ P.edgeOf e := fun g =>
    (P.keepCode_pred (P.edgeOf e) g).to_iff
  rintro ⟨L', hL', x, β', hβ'⟩
  -- the extension of `L'` vanishes on the relators other than `m`
  have hvl : ∀ i : P.ι, i ≠ m → pathSum (extendLabelling K L').toFun (P.path i) = 0 := by
    intro i him
    have hKi : ∀ g ∈ (P.path i).arrowList, K.pred g := fun g hg =>
      (hKpred g).mpr ((edgeCount_eq_zero_iff P.edgeOf (P.path i) e).mp (hedge i him) g hg)
    rw [pathSum_extendLabelling K L' (P.path i) hKi]
    exact hL' ⟨i, him, hKi⟩
  have hβev : pathSum (extendLabelling K L').toFun (DelV.erasePath K x β') = pathSum L' β' :=
    (pathSum_erasePath K L' β').symm
  have hdel : ∀ i : P.ι, i ≠ m → pathSum (deltaLabelling P e).toFun (P.path i) = 0 := by
    intro i him
    refine pathSum_deltaLabelling_eq_zero P e (P.path i) ?_
    intro g hg
    have h1 : P.edgeOf g ≠ P.edgeOf e :=
      (edgeCount_eq_zero_iff P.edgeOf (P.path i) e).mp (hedge i him) g hg
    exact ⟨fun hge => h1 (by rw [hge]), fun hge => h1 (by rw [hge, P.edgeOf_reverse])⟩
  have hdelβ : pathSum (deltaLabelling P e).toFun (DelV.erasePath K x β') = 0 := by
    refine pathSum_deltaLabelling_eq_zero P e _ ?_
    intro g hg
    have h1 : P.edgeOf g ≠ P.edgeOf e :=
      code_ne_of_mem_erasePath P K e (fun g hg => (hKpred g).mp hg) β' hg
    exact ⟨fun hge => h1 (by rw [hge]), fun hge => h1 (by rw [hge, P.edgeOf_reverse])⟩
  set a : ℤ := pathSum (extendLabelling K L').toFun (P.path m)
  set k : ℤ := pathSum (deltaLabelling P e).toFun (P.path m)
  by_cases ha : a = 0
  · refine hnon ⟨extendLabelling K L', ?_, x, DelV.erasePath K x β', ?_⟩
    · intro i
      by_cases him : i = m
      · subst him; exact ha
      · exact hvl i him
    · rw [hβev]; exact hβ'
  · by_cases hk : k = 0
    · -- only `δₑ` is needed, and the connecting path gives a non-zero closed path
      obtain ⟨s⟩ := hconn
      have hW : pathSum (deltaLabelling P e).toFun (DelV.erasePath K e.right s) = 0 := by
        refine pathSum_deltaLabelling_eq_zero P e _ ?_
        intro g hg
        have h1 : P.edgeOf g ≠ P.edgeOf e :=
          code_ne_of_mem_erasePath P K e (fun g hg => (hKpred g).mp hg) s hg
        exact ⟨fun hge => h1 (by rw [hge]), fun hge => h1 (by rw [hge, P.edgeOf_reverse])⟩
      refine hnon ⟨Labelling.smul (-a) (deltaLabelling P e), ?_, e.left,
        e.hom.toPath.comp (DelV.erasePath K e.right s), ?_⟩
      · intro i
        rw [Labelling.pathSum_smul]
        by_cases him : i = m
        · subst him
          show -a * k = 0
          rw [hk]; ring
        · rw [hdel i him]; ring
      · rw [Labelling.pathSum_smul, pathSum_comp, pathSum_toPath, deltaLabelling_apply_self, hW]
        simp only [add_zero, mul_one]
        exact neg_ne_zero.mpr ha
    · -- the combination `k θ - a δₑ`
      refine hnon ⟨Labelling.comb k (-a) (extendLabelling K L') (deltaLabelling P e), ?_, x,
        DelV.erasePath K x β', ?_⟩
      · intro i
        rw [Labelling.pathSum_comb]
        by_cases him : i = m
        · subst him
          show k * a + (-a) * k = 0
          ring
        · rw [hvl i him, hdel i him]; ring
      · rw [Labelling.pathSum_comb, hβev, hdelβ]
        have hmain : k * pathSum L' β' ≠ 0 := mul_ne_zero hk hβ'
        simpa using hmain

/-! ## Subsingleton transfers -/

theorem subsingleton_of_surjective {α β : Type*} [Subsingleton α] (f : α → β)
    (hf : Function.Surjective f) : Subsingleton β :=
  ⟨fun a b => by
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    rw [Subsingleton.elim x y]⟩

theorem subsingleton_of_quotient_bot {G : Type*} [Group G]
    (h : Subsingleton (G ⧸ (⊥ : Subgroup G))) : Subsingleton G := by
  haveI := h
  exact ⟨fun a b =>
    (QuotientGroup.quotientBot (G := G)).symm.injective (Subsingleton.elim _ _)⟩

/-- A presentation without relators has free vertex groups, so a trivial presented vertex group
forces the free vertex group to be trivial. -/
theorem subsingleton_vertexGroup_of_isEmpty_iota (P : Presentation V) [IsEmpty P.ι] (x : V)
    (h : Subsingleton (P.vertexGroup x)) : Subsingleton (VertexGroup x) := by
  have hbot : P.relatorNormalClosure x = ⊥ := by
    show Subgroup.normalClosure (P.relatorSet x) = ⊥
    rw [Subgroup.normalClosure_eq_bot_iff]
    rintro y ⟨i, δ, hδ, hy⟩
    exact isEmptyElim i
  have h2 : Subsingleton (VertexGroup x ⧸ (⊥ : Subgroup (VertexGroup x))) := by
    rw [← hbot]
    exact h
  exact subsingleton_of_quotient_bot h2

/-! ## Index arithmetic for the induction -/

theorem card_subtype_ne {ι : Type u} (m : ι) [Finite ι] {N : ℕ} (hN : Nat.card ι = N) :
    Nat.card {i : ι // i ≠ m} = N - 1 := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have h1 : Nat.card {i : ι // i ≠ m} = Fintype.card {i : ι // i ≠ m} := Nat.card_eq_fintype_card
  have h2 : Fintype.card {i : ι // i ≠ m} =
      Fintype.card ι - Fintype.card {i : ι // i = m} :=
    Fintype.card_subtype_compl (fun i : ι => i = m)
  have h3 : Fintype.card {i : ι // i = m} = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨m, rfl⟩, fun b => Subtype.ext b.2⟩
  have h4 : Fintype.card ι = N := by rw [← Nat.card_eq_fintype_card]; exact hN
  rw [h1, h2, h3, h4]

theorem card_subtype_le_of_imp {ι : Type u} [Finite ι] {J Q : ι → Prop} (h : ∀ i, J i → Q i) :
    Nat.card {i : ι // J i} ≤ Nat.card {i : ι // Q i} := by
  classical
  haveI : Fintype {i : ι // J i} := Fintype.ofFinite _
  haveI : Fintype {i : ι // Q i} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_le_of_injective
    (fun a : {i : ι // J i} => (⟨a.1, h a.1 a.2⟩ : {i : ι // Q i})) ?_
  intro a b hab
  have h2 : a.1 = b.1 := by
    have h3 := congrArg (fun z : {i : ι // Q i} => z.1) hab
    simpa using h3
  exact Subtype.ext h2

theorem card_subtype_and_le {ι : Type u} [Finite ι] (J Q : ι → Prop) :
    Nat.card {i : ι // J i ∧ Q i} ≤ Nat.card {i : ι // J i} :=
  card_subtype_le_of_imp (J := fun i => J i ∧ Q i) (Q := J) fun i hi => hi.1

theorem card_deleteSub_iota_le (P : Presentation V) [Finite P.ι] (K : Keep V)
    (J : P.ι → Prop) :
    Nat.card (P.deleteSub K J).ι ≤ Nat.card {i : P.ι // J i} :=
  card_subtype_and_le J (fun i => ∀ g ∈ (P.path i).arrowList, K.pred g)

theorem card_deleteSub_lt (P : Presentation V) [Finite P.ι] (K : Keep V) (J : P.ι → Prop)
    (m : P.ι) (hJm : ∀ i, J i → i ≠ m) {N : ℕ} (hN : Nat.card P.ι = N) (hpos : 0 < N) :
    Nat.card (P.deleteSub K J).ι < N := by
  have h1 := card_deleteSub_iota_le P K J
  have h2 : Nat.card {i : P.ι // J i} ≤ Nat.card {i : P.ι // i ≠ m} :=
    card_subtype_le_of_imp hJm
  have h3 : Nat.card {i : P.ι // i ≠ m} = N - 1 := card_subtype_ne m hN
  omega

theorem pathMin_deleteSub (P : Presentation V) (K : Keep V) (J : P.ι → Prop)
    (i : P.ι) (hJ : J i) (hK : ∀ g ∈ (P.path i).arrowList, K.pred g) :
    pathMin (P.deleteSub K J).edgeOf ((P.deleteSub K J).path ⟨i, hJ, hK⟩) =
      pathMin P.edgeOf (P.path i) := by
  show pathMin (fun g => P.edgeOf (DelV.toTotal K g))
      (DelV.liftPath K (P.base i) (P.path i) hK) = pathMin P.edgeOf (P.path i)
  exact DelV.pathMin_liftPath K P.edgeOf (P.path i) hK

theorem pathMax_deleteSub (P : Presentation V) (K : Keep V) (J : P.ι → Prop)
    (i : P.ι) (hJ : J i) (hK : ∀ g ∈ (P.path i).arrowList, K.pred g) :
    pathMax (P.deleteSub K J).edgeOf ((P.deleteSub K J).path ⟨i, hJ, hK⟩) =
      pathMax P.edgeOf (P.path i) := by
  show pathMax (fun g => P.edgeOf (DelV.toTotal K g))
      (DelV.liftPath K (P.base i) (P.path i) hK) = pathMax P.edgeOf (P.path i)
  exact DelV.pathMax_liftPath K P.edgeOf (P.path i) hK

theorem dpath_eq_nil_of_subsingleton (K : Keep V) (x : V)
    (h : Subsingleton (VertexGroup (V := DelV K) x)) {q : dpath K x x} (hq : q.IsReduced) :
    q = Quiver.Path.nil := by
  haveI : Subsingleton {p : dpath K x x // p.IsReduced} := h
  have h1 : (⟨q, hq⟩ : {p : dpath K x x // p.IsReduced}) =
      (⟨(Quiver.Path.nil : dpath K x x),
        Quiver.Path.IsReduced.nil (V := DelV K) x⟩ : {p : dpath K x x // p.IsReduced}) :=
    Subsingleton.elim _ _
  simpa using congrArg Subtype.val h1


/-! ## Propagation of the two sides of a bridge -/

theorem reachRight_arrows (P : Presentation V) (e : Quiver.Total V) {a b : V}
    (q : Quiver.Path a b) (hq : Avoids P e q) (ha : ReachRight P e a) :
    (∀ g ∈ q.arrowList, ReachRight P e g.left ∧ ReachRight P e g.right) ∧ ReachRight P e b := by
  induction q with
  | nil => exact ⟨fun g hg => by simp at hg, ha⟩
  | cons p f ih =>
      obtain ⟨hp, hf⟩ := (avoids_cons_iff P e p f).mp hq
      obtain ⟨ihall, ihb⟩ := ih hp
      have hfl : ReachRight P e (Quiver.Total.mk _ _ f).left := ihb
      have hfr : ReachRight P e (Quiver.Total.mk _ _ f).right := by
        obtain ⟨ρ, hρ⟩ := hfl
        exact ⟨ρ.cons f, (avoids_cons_iff P e ρ f).mpr ⟨hρ, hf⟩⟩
      refine ⟨?_, hfr⟩
      intro g hg
      rw [Quiver.Path.arrowList_cons] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact ihall g hg
      · simp only [List.mem_singleton] at hg
        rw [hg]
        exact ⟨hfl, hfr⟩

theorem not_reachRight_arrows (P : Presentation V) (e : Quiver.Total V) :
    ∀ {a b : V} (q : Quiver.Path a b), Avoids P e q → ¬ ReachRight P e b →
      (∀ g ∈ q.arrowList, ¬ ReachRight P e g.left ∧ ¬ ReachRight P e g.right) ∧
        ¬ ReachRight P e a := by
  intro a b q
  induction q with
  | nil => intro _ hb; exact ⟨fun g hg => by simp at hg, hb⟩
  | cons p f ih =>
      intro hq hb
      obtain ⟨hp, hf⟩ := (avoids_cons_iff P e p f).mp hq
      have hx : ¬ ReachRight P e (Quiver.Total.mk _ _ f).left := by
        intro h
        obtain ⟨ρ, hρ⟩ := h
        exact hb ⟨ρ.cons f, (avoids_cons_iff P e ρ f).mpr ⟨hρ, hf⟩⟩
      obtain ⟨ihall, iha⟩ := ih hp hx
      refine ⟨?_, iha⟩
      intro g hg
      rw [Quiver.Path.arrowList_cons] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact ihall g hg
      · simp only [List.mem_singleton] at hg
        rw [hg]
        exact ⟨hx, hb⟩

/-! ## The two sides are exchanged by reversing the arrow -/

theorem reachLeft_totalReverse (P : Presentation V) (e : Quiver.Total V) (y : V) :
    ReachLeft P (Quiver.totalReverse e) y ↔ ReachRight P e y := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, fun g hg hc => hq g hg (hc.trans (P.edgeOf_reverse e).symm)⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, fun g hg hc => hq g hg (hc.trans (P.edgeOf_reverse e))⟩

theorem reachRight_totalReverse (P : Presentation V) (e : Quiver.Total V) (y : V) :
    ReachRight P (Quiver.totalReverse e) y ↔ ReachLeft P e y := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, fun g hg hc => hq g hg (hc.trans (P.edgeOf_reverse e).symm)⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, fun g hg hc => hq g hg (hc.trans (P.edgeOf_reverse e))⟩

theorem sideLoop_totalReverse (P : Presentation V) (e : Quiver.Total V) (side : V → Prop)
    {x y : V} (β : Quiver.Path x y) :
    SideLoop P (Quiver.totalReverse e) side β ↔ SideLoop P e side β := by
  constructor
  · intro h g hg
    obtain ⟨h1, h2, h3⟩ := h g hg
    exact ⟨h1, h2, fun hc => h3 (hc.trans (P.edgeOf_reverse e).symm)⟩
  · intro h g hg
    obtain ⟨h1, h2, h3⟩ := h g hg
    exact ⟨h1, h2, fun hc => h3 (hc.trans (P.edgeOf_reverse e))⟩

theorem sideIndicable_totalReverse (P : Presentation V) (m : P.ι) (e : Quiver.Total V)
    (side : V → Prop) :
    SideIndicable P m (Quiver.totalReverse e) side ↔ SideIndicable P m e side := by
  constructor
  · rintro ⟨L, x, β, h1, h2, h3⟩
    exact ⟨L, x, β, h1, (sideLoop_totalReverse P e side β).mp h2, h3⟩
  · rintro ⟨L, x, β, h1, h2, h3⟩
    exact ⟨L, x, β, h1, (sideLoop_totalReverse P e side β).mpr h2, h3⟩

theorem sideIndicable_congr_side (P : Presentation V) (m : P.ι) (e : Quiver.Total V)
    {side side' : V → Prop} (h : ∀ y : V, side y ↔ side' y) :
    SideIndicable P m e side ↔ SideIndicable P m e side' := by
  constructor
  · rintro ⟨L, x, β, h1, h2, h3⟩
    refine ⟨L, x, β, h1, ?_, h3⟩
    intro g hg
    obtain ⟨h4, h5, h6⟩ := h2 g hg
    exact ⟨(h _).mp h4, (h _).mp h5, h6⟩
  · rintro ⟨L, x, β, h1, h2, h3⟩
    refine ⟨L, x, β, h1, ?_, h3⟩
    intro g hg
    obtain ⟨h4, h5, h6⟩ := h2 g hg
    exact ⟨(h _).mpr h4, (h _).mpr h5, h6⟩

/-- L6 of `N4_LOCIND_LEAD.md`: Howie's Case 2, rewritten on a fixed vertex type with arrow deletion.

Suggested proof (see `N4_LOCIND_LEAD.md` §L6): strong induction on `N` generalising `V`; the
sub-presentations come from `Presentation.delete`/`Presentation.deleteInclVG` (defined by the
sibling file `Howie/vertexGroup_eliminate.lean`); the graph lemmas are
`hasIndicableLabelling_of_loop` (L5a), `edgeCount_even_of_bridge` (L5b),
`edgeCount_eq_one_of_forest` (L5c), `false_of_bridge_forest_side` (L5d), and the labelling lemmas
`indicable_of_labelling`, `hasIndicableLabelling_of_indicable`, `not_hasIndicableLabelling`,
`hasIndicableLabelling_of_bijective` (L3), all of which are being proved in sibling files in
`Submission/Work/ORLocInd/Howie/`. -/
theorem case2 : ∀ (N : ℕ) {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]
    (P : Work.ORLocInd.Howie.Presentation V), Nat.card P.ι = N → Finite P.ι →
    Finite (Quiver.Total V) → P.CodeSeparates → ¬ P.HasIndicableLabelling →
    (∀ x : V, Subsingleton (P.vertexGroup x)) ∧
      ∀ (i : P.ι) (g : Quiver.Total V), g ∈ (P.path i).arrowList →
        Work.ORLocInd.Howie.edgeCount P.edgeOf (P.path i) g = 1 := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro V _ _ _ P hcard hfin hfint hsep hnon
    classical
    haveI : Fintype P.ι := Fintype.ofFinite P.ι
    haveI : Finite P.ι := hfin
    haveI : Finite (Quiver.Total V) := hfint
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · -- No relators: the presented groupoid is the free groupoid, which is trivial
      haveI : IsEmpty P.ι := by
        rw [← Fintype.card_eq_zero_iff, ← Nat.card_eq_fintype_card]
        exact hcard.trans hN0
      refine ⟨?_, ?_⟩
      · intro x
        have htriv : ∀ p : Quiver.Path x x, p.IsReduced → p = Quiver.Path.nil := by
          intro p hp
          by_contra hpne
          have hne : p.length ≠ 0 := fun h0 => hpne (Quiver.Path.eq_nil_of_length_zero p h0)
          obtain ⟨L, y, q, hq⟩ := hasIndicableLabelling_of_loop (V := V) P.noSelfLoop p hp hne
          exact hnon ⟨L, (fun i => isEmptyElim i), y, q, hq⟩
        haveI : Subsingleton (VertexGroup x) :=
          ⟨fun a b => Subtype.ext (by rw [htriv a.1 a.2, htriv b.1 b.2])⟩
        refine Subsingleton.intro fun a b => ?_
        exact Quotient.inductionOn₂ a b fun p q => by rw [Subsingleton.elim p q]
      · intro i
        exact isEmptyElim i
    · -- At least one relator
      haveI : Nonempty P.ι := by
        rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card]
        omega
      obtain ⟨m, hm⟩ : ∃ m : P.ι, ∀ i, i ≤ m :=
        ⟨Finset.univ.max' Finset.univ_nonempty,
          fun i => Finset.le_max' _ _ (Finset.mem_univ i)⟩
      obtain ⟨e, he, hedge⟩ := exists_maxCode_arrow P m hm
      have hedgeA : ∀ i : P.ι, i ≠ m → Avoids P e (P.path i) := fun i hi g hg =>
        (edgeCount_eq_zero_iff P.edgeOf (P.path i) e).mp (hedge i hi) g hg
      set K : Keep V := P.keepCode (P.edgeOf e)
      have hKpred : ∀ g : Quiver.Total V, K.pred g ↔ P.edgeOf g ≠ P.edgeOf e := fun g =>
        (P.keepCode_pred (P.edgeOf e) g).to_iff
      by_cases hbridge : Nonempty (dpath K e.right e.left)
      · -- The deleted edge is not a bridge of `Γ ∖ e` (Howie's *connected* case)
        have hP' : ¬ (P.deleteSub K (fun i => i ≠ m)).HasIndicableLabelling :=
          not_hasIndicableLabelling_deleteSub_max P hsep m hm e he hedge hbridge hnon
        have hlt : Nat.card (P.deleteSub K (fun i => i ≠ m)).ι < N :=
          card_deleteSub_lt P K (fun i => i ≠ m) m (fun i hi => hi) hcard hNpos
        obtain ⟨hsub', hedge'⟩ :=
          ih _ hlt (P := P.deleteSub K (fun i => i ≠ m)) rfl
            (finite_deleteSub_iota P K (fun i => i ≠ m)) (finite_total_delV K)
            (deleteSub_codeSeparates P K (fun i => i ≠ m) hsep) hP'
        -- Step 2: the relators other than `m` already occur once through each edge
        have step2 : ∀ (i : P.ι) (him : i ≠ m) (g : Quiver.Total V),
            g ∈ (P.path i).arrowList → edgeCount P.edgeOf (P.path i) g = 1 := by
          intro i him g hg
          have himp : ∀ g ∈ (P.path i).arrowList, K.pred g := fun g hg =>
            (hKpred g).mpr (hedgeA i him g hg)
          rw [edgeCount_deleteSub P K (fun i => i ≠ m) i him himp g hg]
          exact hedge' ⟨i, him, himp⟩ (DelV.ofTotal K g (himp g hg))
            (DelV.ofTotal_mem_arrowList_liftPath K (P.path i) himp hg)
        rcases eq_or_ne N 1 with hN1 | hN2
        · -- `N = 1`: the deleted presentation has no relators, so `Γ ∖ e` is a forest
          subst hN1
          have hcard0 : Nat.card (P.deleteSub K (fun i => i ≠ m)).ι = 0 := by
            have h1 : Nat.card (P.deleteSub K (fun i => i ≠ m)).ι ≤
                Nat.card {i : P.ι // (fun i => i ≠ m) i} :=
              card_deleteSub_iota_le P K (fun i => i ≠ m)
            have h2 : Nat.card {i : P.ι // (fun i => i ≠ m) i} = 1 - 1 :=
              card_subtype_ne m hcard
            omega
          haveI : Finite (P.deleteSub K (fun i => i ≠ m)).ι :=
            finite_deleteSub_iota P K (fun i => i ≠ m)
          haveI : Fintype (P.deleteSub K (fun i => i ≠ m)).ι :=
            Fintype.ofFinite (P.deleteSub K (fun i => i ≠ m)).ι
          haveI : IsEmpty (P.deleteSub K (fun i => i ≠ m)).ι := by
            rw [← Fintype.card_eq_zero_iff, ← Nat.card_eq_fintype_card]
            exact hcard0
          have hfor : ∀ (y : V) (q : dpath K y y), q.IsReduced → q.length = 0 := by
            intro y q hq
            haveI : Subsingleton (VertexGroup (V := DelV K) y) :=
              subsingleton_vertexGroup_of_isEmpty_iota (P.deleteSub K (fun i => i ≠ m)) y
                (hsub' y)
            have h2 : q = (Quiver.Path.nil : dpath K y y) :=
              dpath_eq_nil_of_subsingleton K y ‹Subsingleton (VertexGroup (V := DelV K) y)› hq
            rw [h2]
            rfl
          have hm1 : ∀ g ∈ (P.path m).arrowList, edgeCount P.edgeOf (P.path m) g = 1 :=
            L5.edgeCount_eq_one_of_forest_del P hsep e hfor (P.path m) (P.reduced m)
              (P.cyclicallyReduced m) (P.notProperPower m) he
          have hbij : ∀ x : V, Function.Bijective (P.deleteSubInclVG K (fun i => i ≠ m) x) :=
            fun x => L4.deleteSubInclVG_bijective P hsep m e (hm1 e he) (fun i hi => hedge i hi) x
          refine ⟨fun x => ?_, fun i => ?_⟩
          · haveI := hsub' x
            exact subsingleton_of_surjective _ (hbij x).2
          · intro g hg
            by_cases him : i = m
            · rw [him] at hg ⊢
              exact hm1 g hg
            · exact step2 i him g hg
        · -- `N ≥ 2`: eliminate the minimal relator by the Tietze step
          obtain ⟨i₁, hi₁⟩ : ∃ i₁ : P.ι, ∀ i, i₁ ≤ i :=
            ⟨Finset.univ.min' Finset.univ_nonempty,
              fun i => Finset.min'_le _ _ (Finset.mem_univ i)⟩
          have hne : ∃ i : P.ι, i ≠ i₁ := by
            by_contra hcon
            push_neg at hcon
            have h1 : Fintype.card P.ι = 1 :=
              Fintype.card_eq_one_iff.mpr ⟨i₁, fun b => hcon b⟩
            rw [← Nat.card_eq_fintype_card] at h1
            omega
          have hi₁m : i₁ ≠ m := by
            intro h0
            obtain ⟨i, hi⟩ := hne
            refine hi (le_antisymm (le_trans (hm i) (le_of_eq h0.symm)) (hi₁ i))
          have hmne : m ≠ i₁ := fun hh => hi₁m hh.symm
          obtain ⟨f, hfmem, hfmin⟩ := exists_pathMin_eq P.edgeOf (arrowList_ne_nil P i₁)
          have hf₀ : edgeCount P.edgeOf (P.path i₁) f = 1 := step2 i₁ hi₁m f hfmem
          have hf : ∀ i : P.ι, i ≠ i₁ → edgeCount P.edgeOf (P.path i) f = 0 := by
            intro i hi
            have hlt : i₁ < i := lt_of_le_of_ne (hi₁ i) (Ne.symm hi)
            have hst := (P.staggered i₁ i hlt).2
            rw [hfmin] at hst
            refine edgeCount_eq_zero P.edgeOf (P.path i) f fun g hg hge => ?_
            have h2 := pathMin_le P.edgeOf hg
            rw [hge] at h2
            exact absurd (lt_of_lt_of_le hst h2) (lt_irrefl _)
          have hP₂ : ¬ (P.deleteSub (P.keepCode (P.edgeOf f)) (fun i => i ≠ i₁)).HasIndicableLabelling :=
            fun hcon =>
            hnon (hasIndicableLabelling_of_bijective P
              (P.deleteSub (P.keepCode (P.edgeOf f)) (fun i => i ≠ i₁)) (Equiv.refl V)
              (fun x => P.deleteSubInclVG (P.keepCode (P.edgeOf f)) (fun i => i ≠ i₁) x)
              (fun x => L4.deleteSubInclVG_bijective P hsep i₁ f hf₀ hf x) hcon)
          have hlt₂ : Nat.card (P.deleteSub (P.keepCode (P.edgeOf f)) (fun i => i ≠ i₁)).ι < N :=
            card_deleteSub_lt P (P.keepCode (P.edgeOf f)) (fun i => i ≠ i₁) i₁
              (fun i hi => hi) hcard hNpos
          obtain ⟨hsub₂, hedge₂⟩ :=
            ih _ hlt₂ (P := P.deleteSub (P.keepCode (P.edgeOf f)) (fun i => i ≠ i₁)) rfl
              (finite_deleteSub_iota P (P.keepCode (P.edgeOf f)) (fun i => i ≠ i₁))
              (finite_total_delV (P.keepCode (P.edgeOf f)))
              (deleteSub_codeSeparates P (P.keepCode (P.edgeOf f)) (fun i => i ≠ i₁) hsep) hP₂
          have hKm : ∀ g ∈ (P.path m).arrowList, (P.keepCode (P.edgeOf f)).pred g :=
            fun g hg => (P.keepCode_pred (P.edgeOf f) g).to_iff.mpr
              ((edgeCount_eq_zero_iff P.edgeOf (P.path m) f).mp (hf m hmne) g hg)
          have hbij₂ : ∀ x : V,
              Function.Bijective (P.deleteSubInclVG (P.keepCode (P.edgeOf f))
                (fun i => i ≠ i₁) x) :=
            fun x => L4.deleteSubInclVG_bijective P hsep i₁ f hf₀ hf x
          refine ⟨fun x => ?_, fun i => ?_⟩
          · haveI := hsub₂ x
            exact subsingleton_of_surjective _ (hbij₂ x).2
          · intro g hg
            by_cases him : i = m
            · rw [him] at hg ⊢
              rw [edgeCount_deleteSub P (P.keepCode (P.edgeOf f)) (fun i => i ≠ i₁) m hmne
                hKm g hg]
              exact hedge₂ ⟨m, hmne, hKm⟩ (DelV.ofTotal (P.keepCode (P.edgeOf f)) g (hKm g hg))
                (DelV.ofTotal_mem_arrowList_liftPath (P.keepCode (P.edgeOf f)) (P.path m) hKm hg)
            · exact step2 i him g hg
      · -- The deleted edge is a bridge of `Γ ∖ e` (Howie's *bridge* case)
        have hbr : ∀ q : Quiver.Path e.right e.left, Avoids P e q → False := fun q hq =>
          hbridge ⟨DelV.liftPath K e.right q (fun g hg => (hKpred g).mpr (hq g hg))⟩
        have hside : ¬ SideIndicable P m e (ReachLeft P e) ∨
            ¬ SideIndicable P m e (ReachRight P e) := by
          by_contra hcon
          push_neg at hcon
          exact hnon (C2.hasIndicableLabelling_of_both_sides P hsep m e hbr hedgeA hcon.2 hcon.1)
        have key : ∀ (e' : Quiver.Total V),
            (∃ g ∈ (P.path m).arrowList, P.edgeOf g = P.edgeOf e') →
            (∀ i : P.ι, i ≠ m → Avoids P e' (P.path i)) →
            (∀ q : Quiver.Path e'.right e'.left, Avoids P e' q → False) →
            ¬ SideIndicable P m e' (ReachLeft P e') → False := by
          intro e' he' hedge' hbr' hside'
          set K₃ : Keep V := keepRight P e'
          set J₃ : P.ι → Prop := bridgeRelator P m e'
          have hK₃pred : ∀ g : Quiver.Total V, K₃.pred g ↔
              (P.edgeOf g ≠ P.edgeOf e' ∧
                ¬ (ReachRight P e' g.left ∨ ReachRight P e' g.right)) := fun g => Iff.rfl
          have hJ₃iff : ∀ i : P.ι, J₃ i ↔ (i ≠ m ∧ ¬ ReachRight P e' (P.base i)) :=
            fun i => Iff.rfl
          haveI : Finite (P.deleteSub K₃ J₃).ι := finite_deleteSub_iota P K₃ J₃
          have hP₃ : ¬ (P.deleteSub K₃ J₃).HasIndicableLabelling :=
            C2.not_hasIndicableLabelling_bridgePresentation P hsep m e' he' hedge' hbr' hnon hside'
          have hlt₃ : Nat.card (P.deleteSub K₃ J₃).ι < N :=
            card_deleteSub_lt P K₃ J₃ m (fun i hi => ((hJ₃iff i).mp hi).1) hcard hNpos
          obtain ⟨hsub₃, hedge₃⟩ :=
            ih _ hlt₃ (P := P.deleteSub K₃ J₃) rfl (finite_deleteSub_iota P K₃ J₃)
              (finite_total_delV K₃) (deleteSub_codeSeparates P K₃ J₃ hsep) hP₃
          rcases isEmpty_or_nonempty (P.deleteSub K₃ J₃).ι with hemp | hnemp
          · -- `P₃` has no relators: `L5d` gives `False`
            haveI : IsEmpty (P.deleteSub K₃ J₃).ι := hemp
            have hforE : ∀ q : Quiver.Path e'.left e'.left, Avoids P e' q → q.IsReduced →
                q = Quiver.Path.nil := by
              intro q hq hqr
              have hnotL : ¬ ReachRight P e' e'.left := fun h => h.elim fun ρ hρ => hbr' ρ hρ
              obtain ⟨hall, -⟩ := not_reachRight_arrows P e' q hq hnotL
              have hkeep : ∀ g ∈ q.arrowList, K₃.pred g := fun g hg => (hK₃pred g).mpr
                ⟨hq g hg, fun hh => hh.elim (fun h => (hall g hg).1 h)
                  (fun h => (hall g hg).2 h)⟩
              have hqr' : (DelV.liftPath K₃ e'.left q hkeep).IsReduced :=
                (DelV.isReduced_liftPath K₃ q hkeep).mpr hqr
              have hss : Subsingleton (VertexGroup (V := DelV K₃) e'.left) :=
                subsingleton_vertexGroup_of_isEmpty_iota (P.deleteSub K₃ J₃) e'.left
                  (hsub₃ e'.left)
              have hnil : DelV.liftPath K₃ e'.left q hkeep = Quiver.Path.nil :=
                dpath_eq_nil_of_subsingleton K₃ e'.left hss hqr'
              have h3 := congrArg (DelV.erasePath K₃ e'.left) hnil
              rwa [DelV.erasePath_liftPath, DelV.erasePath_nil] at h3
            exact C2.false_of_bridge_forest_side_exists P hsep e' hbr' hforE (P.path m)
              (P.reduced m) (P.cyclicallyReduced m) he'
          · -- `P₃` has a relator: eliminate the minimal one by the Tietze step
            haveI : Nonempty (P.deleteSub K₃ J₃).ι := hnemp
            haveI : Fintype (P.deleteSub K₃ J₃).ι := Fintype.ofFinite _
            obtain ⟨i₃, hi₃⟩ : ∃ i₃ : (P.deleteSub K₃ J₃).ι, ∀ i, i₃ ≤ i :=
              ⟨Finset.univ.min' Finset.univ_nonempty,
                fun i => Finset.min'_le _ _ (Finset.mem_univ i)⟩
            obtain ⟨f₁, hf₁mem, hf₁min⟩ := exists_pathMin_eq (P.deleteSub K₃ J₃).edgeOf
              (arrowList_ne_nil (P.deleteSub K₃ J₃) i₃)
            have hfmem : DelV.toTotal K₃ f₁ ∈ (P.path i₃.1).arrowList :=
              (toTotal_mem_arrowList_liftPath K₃ (P.path i₃.1) i₃.2.2 hf₁mem).1
            have hKf : K₃.pred (DelV.toTotal K₃ f₁) :=
              (toTotal_mem_arrowList_liftPath K₃ (P.path i₃.1) i₃.2.2 hf₁mem).2
            have hminf : pathMin P.edgeOf (P.path i₃.1) =
                (P.edgeOf (DelV.toTotal K₃ f₁) : WithTop P.α) := by
              rw [← pathMin_deleteSub P K₃ J₃ i₃.1 i₃.2.1 i₃.2.2]
              exact hf₁min
            have hf₀ : edgeCount P.edgeOf (P.path i₃.1) (DelV.toTotal K₃ f₁) = 1 := by
              rw [edgeCount_deleteSub P K₃ J₃ i₃.1 i₃.2.1 i₃.2.2 (DelV.toTotal K₃ f₁) hfmem]
              rw [DelV.ofTotal_toTotal]
              exact hedge₃ i₃ f₁ hf₁mem
            have hi₃m : i₃.1 ≠ m := ((hJ₃iff i₃.1).mp i₃.2.1).1
            have hmne : m ≠ i₃.1 := fun hh => hi₃m hh.symm
            have hf : ∀ i : P.ι, i ≠ i₃.1 →
                edgeCount P.edgeOf (P.path i) (DelV.toTotal K₃ f₁) = 0 := by
              intro i hi
              refine edgeCount_eq_zero P.edgeOf (P.path i) (DelV.toTotal K₃ f₁)
                fun g hg hgc => ?_
              by_cases him : i = m
              · have hlt : i₃.1 < m := lt_of_le_of_ne (hm i₃.1) (fun hh => hi (him.trans hh.symm))
                have h1 : (P.edgeOf (DelV.toTotal K₃ f₁) : WithTop P.α) <
                    pathMin P.edgeOf (P.path m) := by
                  rw [← hminf]
                  exact (P.staggered i₃.1 m hlt).2
                have h2 := pathMin_le P.edgeOf hg
                rw [hgc, him] at h2
                exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
              · by_cases hbase : ReachRight P e' (P.base i)
                · obtain ⟨hRall, -⟩ := reachRight_arrows P e' (P.path i) (hedge' i him) hbase
                  have hR : ReachRight P e' g.left := (hRall g hg).1
                  rcases hsep g (DelV.toTotal K₃ f₁) hgc with hge | hge
                  · rw [hge] at hR
                    exact ((hK₃pred (DelV.toTotal K₃ f₁)).mp hKf).2 (Or.inl hR)
                  · rw [hge] at hR
                    exact ((hK₃pred (DelV.toTotal K₃ f₁)).mp hKf).2
                      (Or.inr (by simpa using hR))
                · have hKi : ∀ g ∈ (P.path i).arrowList, K₃.pred g := fun g hg =>
                    (hK₃pred g).mpr ⟨hedge' i him g hg, by
                      obtain ⟨hnl, -⟩ := not_reachRight_arrows P e' (P.path i)
                        (hedge' i him) hbase
                      exact fun hh => hh.elim (fun h => (hnl g hg).1 h) (fun h => (hnl g hg).2 h)⟩
                  have hJ₃i : J₃ i := (hJ₃iff i).mpr ⟨him, hbase⟩
                  have hle : i₃.1 ≤ i := hi₃ (⟨i, hJ₃i, hKi⟩ : (P.deleteSub K₃ J₃).ι)
                  have hlt : i₃.1 < i := lt_of_le_of_ne hle (fun hh => hi hh.symm)
                  have h1 : (P.edgeOf (DelV.toTotal K₃ f₁) : WithTop P.α) <
                      pathMin P.edgeOf (P.path i) := by
                    rw [← hminf]
                    exact (P.staggered i₃.1 i hlt).2
                  have h2 := pathMin_le P.edgeOf hg
                  rw [hgc] at h2
                  exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
            set K₂ : Keep V := P.keepCode (P.edgeOf (DelV.toTotal K₃ f₁))
            have hP₂ : ¬ (P.deleteSub K₂ (fun i => i ≠ i₃.1)).HasIndicableLabelling := fun hcon =>
              hnon (hasIndicableLabelling_of_bijective P (P.deleteSub K₂ (fun i => i ≠ i₃.1))
                (Equiv.refl V) (fun x => P.deleteSubInclVG K₂ (fun i => i ≠ i₃.1) x)
                (fun x => L4.deleteSubInclVG_bijective P hsep i₃.1 (DelV.toTotal K₃ f₁) hf₀ hf x)
                hcon)
            have hlt₂ : Nat.card (P.deleteSub K₂ (fun i => i ≠ i₃.1)).ι < N :=
              card_deleteSub_lt P K₂ (fun i => i ≠ i₃.1) i₃.1 (fun i hi => hi) hcard hNpos
            obtain ⟨hsub₂, hedge₂⟩ :=
              ih _ hlt₂ (P := P.deleteSub K₂ (fun i => i ≠ i₃.1)) rfl
                (finite_deleteSub_iota P K₂ (fun i => i ≠ i₃.1)) (finite_total_delV K₂)
                (deleteSub_codeSeparates P K₂ (fun i => i ≠ i₃.1) hsep) hP₂
            have hKm2 : ∀ g ∈ (P.path m).arrowList, K₂.pred g := fun g hg =>
              (P.keepCode_pred (P.edgeOf (DelV.toTotal K₃ f₁)) g).to_iff.mpr
                ((edgeCount_eq_zero_iff P.edgeOf (P.path m) (DelV.toTotal K₃ f₁)).mp
                  (hf m hmne) g hg)
            obtain ⟨g₀, hg₀mem, hg₀c⟩ := he'
            have h1 : edgeCount P.edgeOf (P.path m) g₀ = 1 := by
              rw [edgeCount_deleteSub P K₂ (fun i => i ≠ i₃.1) m hmne hKm2 g₀ hg₀mem]
              exact hedge₂ ⟨m, hmne, hKm2⟩ (DelV.ofTotal K₂ g₀ (hKm2 g₀ hg₀mem))
                (DelV.ofTotal_mem_arrowList_liftPath K₂ (P.path m) hKm2 hg₀mem)
            have h2 : Even (edgeCount P.edgeOf (P.path m) e') :=
              L5.edgeCount_even_of_bridge_del P hsep e' hbr' (P.path m)
            have h3 : edgeCount P.edgeOf (P.path m) g₀ = edgeCount P.edgeOf (P.path m) e' :=
              edgeCount_congr_code P.edgeOf (P.path m) hg₀c
            rw [h3] at h1
            rw [h1] at h2
            obtain ⟨k, hk⟩ := h2
            omega
        rcases hside with hside | hside
        · exact (key e ⟨e, he, rfl⟩ hedgeA hbr hside).elim
        · refine (key (Quiver.totalReverse e) ⟨e, he, (P.edgeOf_reverse e).symm⟩ ?_ ?_ ?_).elim
          · intro i hi g hg hc
            exact hedgeA i hi g hg (hc.trans (P.edgeOf_reverse e))
          · intro q hq
            exact hbr q.reverse (avoids_reverse P e
              (fun g hg hc => hq g hg (hc.trans (P.edgeOf_reverse e).symm)))
          · rw [sideIndicable_totalReverse P m e (ReachLeft P (Quiver.totalReverse e))]
            exact fun hh => hside
              ((sideIndicable_congr_side P m e (fun y => reachLeft_totalReverse P e y)).mp hh)

end Work.ORLocInd.Howie
