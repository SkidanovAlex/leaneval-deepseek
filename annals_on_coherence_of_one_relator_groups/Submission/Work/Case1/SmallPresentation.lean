/-
# The presentation of the small model

Given a skeleton `S : Skel V W` of a graph `V` (an indexing of its vertices and of its arrows), a
groupoid presentation `P` on `V` and a datum `D` in `P`,

* the *codes* of the unoriented edges of the small graph `S.Vx` are the distinct codes of the
  arrows used by `D`, reindexed by their rank in the sorted list of these codes, and
* the *relators* of the small graph are the relators of `P` occurring in `D`, reindexed by their
  rank in the sorted list of those indices

(the reindexing produces types in the universe `u` of `S.Vx`, which need not be the universe of
`P.α` or `P.ι`, so they are carried into `Type u` by `ULift`; the code type is `Fin (N + 1)` rather
than `Fin N` so that it is always inhabited, the extra value never being attained).

This file constructs that presentation `smallPresentation S P D hrel` and proves that its code
separates the unoriented edges as soon as `P.CodeSeparates` does.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.SpanPresentation
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.Case1.Skeleton
import Submission.Work.Case1.CastVG
import Submission.Work.Case1.dec_totalMap_injective
import Submission.Work.Case1.MaxMem
import Submission.Work.Case1.foldr_max_map_of_mono
import Submission.Work.Case1.foldr_min_map_of_mono
import Submission.Work.ORLocInd.Howie.isReduced_compPower_of_comp_self
import Submission.Work.ORLocInd.Howie.presentation_path_ne_nil

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Work.Case1

open _root_.Quiver
open Work.ORLocInd.Howie

namespace SmallPres

variable {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V] {W : Type u}

/-! ## The codes -/

/-- The codes of the arrows used by the datum. -/
noncomputable def codeList (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) : List P.α :=
  (D.usedArrowsList).map P.edgeOf

/-- The set of codes of the arrows used by the datum. -/
noncomputable def codeSet (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) : Finset P.α :=
  (codeList P D).toFinset

theorem mem_codeSet {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n} {c : P.α} :
    c ∈ codeSet P D ↔ ∃ e ∈ D.usedArrowsList, P.edgeOf e = c := by
  rw [codeSet, List.mem_toFinset, codeList, List.mem_map]

/-- The distinct codes of the arrows used by the datum, sorted. -/
noncomputable def cs (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) : List P.α :=
  (codeSet P D).sort

theorem cs_sorted (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) :
    (cs P D).SortedLT := Finset.sortedLT_sort (codeSet P D)

theorem mem_cs {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n} {c : P.α} :
    c ∈ cs P D ↔ ∃ e ∈ D.usedArrowsList, P.edgeOf e = c := by
  rw [cs, Finset.mem_sort]
  exact mem_codeSet

/-- The number of codes. -/
noncomputable def Nc (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) : ℕ :=
  (cs P D).length

/-- The order isomorphism between `Fin (Nc P D)` and the codes. -/
noncomputable def cIso (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) :
    Fin (Nc P D) ≃o {c : P.α // c ∈ cs P D} :=
  (cs_sorted P D).getIso (cs P D)

/-- The rank of a code, as an element of `Fin (Nc + 1)`; the extra value is not attained on the
codes used by the datum. -/
noncomputable def effRank (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) (c : P.α) :
    Fin (Nc P D + 1) :=
  if h : c ∈ cs P D then Fin.castSucc ((cIso P D).symm ⟨c, h⟩)
  else ⟨Nc P D, Nat.lt_succ_self _⟩

theorem effRank_cs {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n} {c : P.α}
    (hc : c ∈ cs P D) :
    effRank P D c = Fin.castSucc ((cIso P D).symm ⟨c, hc⟩) := dif_pos hc

theorem effRank_lt_iff {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n} {a b : P.α}
    (ha : a ∈ cs P D) (hb : b ∈ cs P D) :
    effRank P D a < effRank P D b ↔ a < b := by
  rw [effRank_cs ha, effRank_cs hb, Fin.castSucc_lt_castSucc_iff, (cIso P D).symm.lt_iff_lt,
    Subtype.mk_lt_mk]

theorem effRank_inj {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n} {a b : P.α}
    (ha : a ∈ cs P D) (hb : b ∈ cs P D) (h : effRank P D a = effRank P D b) : a = b := by
  have h' : (⟨a, ha⟩ : {c : P.α // c ∈ cs P D}) = ⟨b, hb⟩ := by
    have h2 : (cIso P D).symm ⟨a, ha⟩ = (cIso P D).symm ⟨b, hb⟩ := by
      rw [effRank_cs ha, effRank_cs hb] at h
      exact Fin.castSucc_inj.mp h
    exact (cIso P D).symm.injective h2
  exact congrArg Subtype.val h'

/-- The code of an arrow used by the datum is one of the codes. -/
theorem edgeOf_mem_cs {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n}
    {e : Quiver.Total V} (he : e ∈ D.usedArrowsList) : P.edgeOf e ∈ cs P D :=
  mem_cs.mpr ⟨e, he, rfl⟩

/-! ## The relators -/

/-- The relator indices occurring in the datum. -/
noncomputable def relList (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) : List P.ι :=
  (List.finRange n).flatMap (fun j => (D.terms j).map (fun t => t.i))

/-- The set of relator indices occurring in the datum. -/
noncomputable def relSet (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) : Finset P.ι :=
  (relList P D).toFinset

/-- The distinct relator indices occurring in the datum, sorted. -/
noncomputable def rels (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) : List P.ι :=
  (relSet P D).sort

theorem mem_rels {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n} {i : P.ι} :
    i ∈ rels P D ↔ ∃ (j : Fin n) (t : RelatorTerm P v), t ∈ D.terms j ∧ t.i = i := by
  simp only [rels, Finset.mem_sort, relSet, List.mem_toFinset, relList, List.mem_flatMap,
    List.mem_finRange, true_and, List.mem_map]

/-- The number of relators. -/
noncomputable def Nr (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) : ℕ :=
  (rels P D).length

theorem rels_sorted (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) :
    (rels P D).SortedLT := Finset.sortedLT_sort (relSet P D)

/-- The order isomorphism between `Fin (Nr P D)` and the relator indices. -/
noncomputable def rIso (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) :
    Fin (Nr P D) ≃o {i : P.ι // i ∈ rels P D} :=
  (rels_sorted P D).getIso (rels P D)

/-- The relator index of a position. -/
noncomputable def rel (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (i : Fin (Nr P D)) : P.ι := (rIso P D i).1

/-- The position of a relator index. -/
noncomputable def relInvOf (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) (x : P.ι)
    (hx : x ∈ rels P D) : Fin (Nr P D) := (rIso P D).symm ⟨x, hx⟩

theorem rel_relInvOf {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n} {x : P.ι}
    (hx : x ∈ rels P D) : rel P D (relInvOf P D x hx) = x :=
  congrArg Subtype.val ((rIso P D).apply_symm_apply ⟨x, hx⟩)

theorem rel_lt_iff (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (i j : Fin (Nr P D)) : rel P D i < rel P D j ↔ i < j :=
  (rIso P D).lt_iff_lt

/-- The index of a term of the datum is a relator index of the small presentation. -/
theorem term_i_mem_rels {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n} {j : Fin n}
    {t : RelatorTerm P v} (ht : t ∈ D.terms j) : t.i ∈ rels P D :=
  mem_rels.mpr ⟨j, t, ht, rfl⟩

/-- A relator occurring in the datum is a relator of the small presentation. -/
theorem exists_rel_of_usedRelator {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n}
    {i : P.ι} (hi : UsedRelator D i) : ∃ r : Fin (Nr P D), rel P D r = i := by
  obtain ⟨j, t, ht, hti⟩ := hi
  exact ⟨relInvOf P D t.i (term_i_mem_rels ht),
    (rel_relInvOf (term_i_mem_rels ht)).trans hti⟩

/-- The arrows of a relator occurring in the datum are used by the datum. -/
theorem edgeOf_mem_cs_of_relator {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n}
    {i : P.ι} (hi : UsedRelator D i) {e : Quiver.Total V} (he : e ∈ (P.path i).arrowList) :
    P.edgeOf e ∈ cs P D := by
  obtain ⟨j, t, ht, rfl⟩ := hi
  exact edgeOf_mem_cs (D.mem_usedArrowsList_of_mem_term ht (Or.inr he))

/-! ## The code of an arrow of the small graph -/

/-- The type of codes of the small presentation. -/
abbrev SmallCode (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n) : Type u :=
  ULift.{u,0} (Fin (Nc P D + 1))

/-- The code of a code of `P`, as a code of the small presentation. -/
noncomputable def effCode (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (c : P.α) : SmallCode S P D := ULift.up (effRank P D c)

/-- The code of an arrow of the small graph: the rank of the code of the arrow it decodes to. -/
noncomputable def edgeOf' (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (g : Quiver.Total S.Vx) : SmallCode S P D :=
  effCode S P D (P.edgeOf (PrefunctorAux.totalMap S.dec g))

theorem edgeOf'_reverse (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (g : Quiver.Total S.Vx) : edgeOf' S P D (Quiver.totalReverse g) = edgeOf' S P D g := by
  apply congrArg (fun c => ULift.up (effRank P D c))
  rw [PrefunctorAux.totalMap_totalReverse, P.edgeOf_reverse]

/-- `foldr_max_map_of_mono`, with the coercion `α → WithBot α` written as `WithBot.some` so that
both sides of the statement are in a form stable under elaboration (the coercion `↑` is
re-elaborated by Lean as `List.bind`/`List.map id` when it occurs under a `List.map`). -/
theorem foldr_max_map_some {α β : Type*} [LinearOrder α] [LinearOrder β] (f : α → β) (l : List α)
    (s : Set α) (hl : ∀ a ∈ l, a ∈ s) (hf : ∀ a ∈ s, ∀ b ∈ s, f a < f b ↔ a < b) :
    (l.map (fun a => WithBot.some (f a))).foldr max ⊥
      = WithBot.map f ((l.map WithBot.some).foldr max ⊥) := by
  rw [foldr_max_map_of_mono (f := f) (l := l) (s := s) hl hf]
  congr 1
  congr 1
  rw [List.map_id', List.bind_eq_flatMap]
  exact List.flatMap_pure_eq_map (f := WithBot.some) l

/-- `foldr_min_map_of_mono`, with the coercion `α → WithTop α` written as `WithTop.some`. -/
theorem foldr_min_map_some {α β : Type*} [LinearOrder α] [LinearOrder β] (f : α → β) (l : List α)
    (s : Set α) (hl : ∀ a ∈ l, a ∈ s) (hf : ∀ a ∈ s, ∀ b ∈ s, f a < f b ↔ a < b) :
    (l.map (fun a => WithTop.some (f a))).foldr min ⊤
      = WithTop.map f ((l.map WithTop.some).foldr min ⊤) := by
  rw [foldr_min_map_of_mono (f := f) (l := l) (s := s) hl hf]
  congr 1
  congr 1
  rw [List.map_id', List.bind_eq_flatMap]
  exact List.flatMap_pure_eq_map (f := WithTop.some) l

/-- The maximum of the code of a path of the small graph. -/
theorem pathMax_mapPath (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    {a b : V} (p : Quiver.Path a b) (hp : ∀ e ∈ p.arrowList, P.edgeOf e ∈ cs P D) :
    pathMax (edgeOf' S P D) (S.enc.mapPath p) =
      WithBot.map (effCode S P D) (pathMax P.edgeOf p) := by
  show ((S.enc.mapPath p).arrowList.map
      (fun g => (ULift.up (effRank P D (P.edgeOf (PrefunctorAux.totalMap S.dec g))) :
        WithBot (SmallCode S P D)))).foldr max ⊥ =
    WithBot.map (fun c => ULift.up (effRank P D c))
      ((p.arrowList.map (fun e => (P.edgeOf e : WithBot P.α))).foldr max ⊥)
  have hL : (S.enc.mapPath p).arrowList.map
        (fun g => (ULift.up (effRank P D (P.edgeOf (PrefunctorAux.totalMap S.dec g))) :
          WithBot (SmallCode S P D)))
      = (p.arrowList.map P.edgeOf).map
        (fun a : P.α => WithBot.some (ULift.up (effRank P D a))) := by
    rw [PrefunctorAux.mapPath_arrowList, List.map_map, List.map_map]
    exact List.map_congr_left (fun e _ => by
      simp only [Function.comp_apply, Skel.dec_totalMap_enc_totalMap, WithBot.some_eq_coe])
  have hR : (p.arrowList.map (fun e => (P.edgeOf e : WithBot P.α)))
      = (p.arrowList.map P.edgeOf).map WithBot.some := by
    rw [List.map_map]
    rfl
  rw [hL, hR]
  exact foldr_max_map_some (fun c => ULift.up (effRank P D c)) (p.arrowList.map P.edgeOf)
    {c | c ∈ cs P D} (fun a ha => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact hp e he)
    (fun a ha b hb => by
      show ULift.up (effRank P D a) < ULift.up (effRank P D b) ↔ a < b
      exact effRank_lt_iff ha hb)

/-- The minimum of the code of a path of the small graph. -/
theorem pathMin_mapPath (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    {a b : V} (p : Quiver.Path a b) (hp : ∀ e ∈ p.arrowList, P.edgeOf e ∈ cs P D) :
    pathMin (edgeOf' S P D) (S.enc.mapPath p) =
      WithTop.map (effCode S P D) (pathMin P.edgeOf p) := by
  show ((S.enc.mapPath p).arrowList.map
      (fun g => (ULift.up (effRank P D (P.edgeOf (PrefunctorAux.totalMap S.dec g))) :
        WithTop (SmallCode S P D)))).foldr min ⊤ =
    WithTop.map (fun c => ULift.up (effRank P D c))
      ((p.arrowList.map (fun e => (P.edgeOf e : WithTop P.α))).foldr min ⊤)
  have hL : (S.enc.mapPath p).arrowList.map
        (fun g => (ULift.up (effRank P D (P.edgeOf (PrefunctorAux.totalMap S.dec g))) :
          WithTop (SmallCode S P D)))
      = (p.arrowList.map P.edgeOf).map
        (fun a : P.α => WithTop.some (ULift.up (effRank P D a))) := by
    rw [PrefunctorAux.mapPath_arrowList, List.map_map, List.map_map]
    exact List.map_congr_left (fun e _ => by
      simp only [Function.comp_apply, Skel.dec_totalMap_enc_totalMap, WithTop.some_eq_coe])
  have hR : (p.arrowList.map (fun e => (P.edgeOf e : WithTop P.α)))
      = (p.arrowList.map P.edgeOf).map WithTop.some := by
    rw [List.map_map]
    rfl
  rw [hL, hR]
  exact foldr_min_map_some (fun c => ULift.up (effRank P D c)) (p.arrowList.map P.edgeOf)
    {c | c ∈ cs P D} (fun a ha => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact hp e he)
    (fun a ha b hb => by
      show ULift.up (effRank P D a) < ULift.up (effRank P D b) ↔ a < b
      exact effRank_lt_iff ha hb)

/-- The maximum of a relator occurring in the datum is a code. -/
theorem pathMax_mem_cs {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n}
    (hrel : ∀ i : P.ι, UsedRelator D i) {i : P.ι} (hne : (P.path i).arrowList ≠ []) {c : P.α}
    (hc : pathMax P.edgeOf (P.path i) = (c : WithBot P.α)) : c ∈ cs P D := by
  obtain ⟨g, hg, hge⟩ := exists_pathMax_eq P.edgeOf hne
  rw [hge] at hc
  have hgc : P.edgeOf g = c := WithBot.coe_eq_coe.mp hc
  rw [← hgc]
  exact edgeOf_mem_cs_of_relator (hrel i) hg

/-- The minimum of a relator occurring in the datum is a code. -/
theorem pathMin_mem_cs {P : Presentation V} {v : V} {n : ℕ} {D : Datum P v n}
    (hrel : ∀ i : P.ι, UsedRelator D i) {i : P.ι} (hne : (P.path i).arrowList ≠ []) {c : P.α}
    (hc : pathMin P.edgeOf (P.path i) = (c : WithTop P.α)) : c ∈ cs P D := by
  obtain ⟨g, hg, hge⟩ := exists_pathMin_eq P.edgeOf hne
  rw [hge] at hc
  have hgc : P.edgeOf g = c := WithTop.coe_eq_coe.mp hc
  rw [← hgc]
  exact edgeOf_mem_cs_of_relator (hrel i) hg

theorem map_effRank_lt_iff (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    {X Y : WithBot P.α}
    (hX : ∀ c : P.α, X = (c : WithBot P.α) → c ∈ cs P D)
    (hY : ∀ c : P.α, Y = (c : WithBot P.α) → c ∈ cs P D) :
    WithBot.map (effCode S P D) X < WithBot.map (effCode S P D) Y ↔ X < Y := by
  induction X using WithBot.recBotCoe with
  | bot =>
      induction Y using WithBot.recBotCoe with
      | bot =>
          simp only [WithBot.map_bot]
          exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩
      | coe b =>
          simp only [WithBot.map_bot, WithBot.map_coe]
          exact ⟨fun _ => WithBot.bot_lt_coe b, fun _ => WithBot.bot_lt_coe _⟩
  | coe a =>
      induction Y using WithBot.recBotCoe with
      | bot =>
          simp only [WithBot.map_bot, WithBot.map_coe]
          exact ⟨fun h => absurd h (WithBot.not_lt_bot _), fun h => absurd h (WithBot.not_lt_bot _)⟩
      | coe b =>
          simp only [WithBot.map_coe, WithBot.coe_lt_coe]
          exact effRank_lt_iff (hX a rfl) (hY b rfl)

theorem map_effRank_lt_iff' (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    {X Y : WithTop P.α}
    (hX : ∀ c : P.α, X = (c : WithTop P.α) → c ∈ cs P D)
    (hY : ∀ c : P.α, Y = (c : WithTop P.α) → c ∈ cs P D) :
    WithTop.map (effCode S P D) X < WithTop.map (effCode S P D) Y ↔ X < Y := by
  induction X using WithTop.recTopCoe with
  | top =>
      induction Y using WithTop.recTopCoe with
      | top =>
          simp only [WithTop.map_top]
          exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩
      | coe b =>
          simp only [WithTop.map_top, WithTop.map_coe]
          exact ⟨fun h => absurd h (WithTop.not_top_lt _),
            fun h => absurd h (WithTop.not_top_lt _)⟩
  | coe a =>
      induction Y using WithTop.recTopCoe with
      | top =>
          simp only [WithTop.map_top, WithTop.map_coe]
          exact ⟨fun _ => WithTop.coe_lt_top a, fun _ => WithTop.coe_lt_top _⟩
      | coe b =>
          simp only [WithTop.map_coe, WithTop.coe_lt_coe]
          exact effRank_lt_iff (hX a rfl) (hY b rfl)

/-! ## The presentation -/

/-- The relator paths of `P` are never empty. -/
theorem path_arrowList_ne_nil (P : Presentation V) (i : P.ι) : (P.path i).arrowList ≠ [] := by
  intro h
  refine presentation_path_ne_nil P i ?_
  have hlen : (P.path i).length = 0 := by
    rw [← Quiver.Path.arrowList_length_eq, h]
    rfl
  exact Quiver.Path.eq_nil_of_length_zero (P.path i) hlen

/-- There is no self-inverse loop in the small graph, because the decoding sends it to one in `V`
and there is none in `V`. -/
theorem noSelfLoop' (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (v' : S.Vx) (g : v' ⟶ v') : Quiver.reverse g ≠ g := by
  intro hg
  have h := congrArg S.dec.map hg
  rw [Prefunctor.map_reverse] at h
  exact P.noSelfLoop (S.decObj v') (S.dec.map g) h

/-- Each relator of the small presentation is reduced. -/
theorem reduced' (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (r : ULift.{u,0} (Fin (Nr P D))) :
    (S.enc.mapPath (P.path (rel P D r.down))).IsReduced :=
  PrefunctorAux.mapPath_isReduced S.enc S.encObj_injective (fun _ _ => S.enc_map_injective)
    (P.reduced (rel P D r.down))

/-- Each relator of the small presentation is cyclically reduced. -/
theorem cyclicallyReduced' (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (r : ULift.{u,0} (Fin (Nr P D))) :
    IsCyclicallyReduced (S.enc.mapPath (P.path (rel P D r.down))) := by
  have h2 : ((P.path (rel P D r.down)).comp (P.path (rel P D r.down))).IsReduced :=
    isReduced_comp_self_iff.mpr
      ⟨P.reduced (rel P D r.down), P.cyclicallyReduced (rel P D r.down),
        fun f _ => P.noSelfLoop (P.base (rel P D r.down)) f⟩
  have h3 : ((S.enc.mapPath (P.path (rel P D r.down))).comp
      (S.enc.mapPath (P.path (rel P D r.down)))).IsReduced := by
    rw [← Prefunctor.mapPath_comp]
    exact PrefunctorAux.mapPath_isReduced S.enc S.encObj_injective
      (fun _ _ => S.enc_map_injective) h2
  exact (isReduced_comp_self_iff.mp h3).2.1

/-- No relator of the small presentation is a proper power. -/
theorem notProperPower' (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (r : ULift.{u,0} (Fin (Nr P D))) :
    ¬ IsProperPower (S.enc.mapPath (P.path (rel P D r.down))) := by
  rintro ⟨q, m, hm, heq⟩
  refine P.notProperPower (rel P D r.down) ⟨
    (S.dec.mapPath q).cast (Skel.dO S (P.base (rel P D r.down))).symm
      (Skel.dO S (P.base (rel P D r.down))).symm, m, hm, ?_⟩
  have h1 : (P.path (rel P D r.down)).cast (Skel.dO S (P.base (rel P D r.down)))
      (Skel.dO S (P.base (rel P D r.down))) = (S.dec.mapPath q).compPower m := by
    rw [← Skel.dec_mapPath_enc_mapPath S (P.path (rel P D r.down)), heq,
      PrefunctorAux.mapPath_compPower]
  calc P.path (rel P D r.down)
      = ((P.path (rel P D r.down)).cast (Skel.dO S (P.base (rel P D r.down)))
          (Skel.dO S (P.base (rel P D r.down)))).cast
            (Skel.dO S (P.base (rel P D r.down))).symm
            (Skel.dO S (P.base (rel P D r.down))).symm :=
        (PathCast.cast_cast_symm _ _ _).symm
    _ = ((S.dec.mapPath q).compPower m).cast (Skel.dO S (P.base (rel P D r.down))).symm
          (Skel.dO S (P.base (rel P D r.down))).symm := by rw [← h1]
    _ = ((S.dec.mapPath q).cast (Skel.dO S (P.base (rel P D r.down))).symm
          (Skel.dO S (P.base (rel P D r.down))).symm).compPower m :=
        (PathCast.cast_compPower _ _ _ _).symm

/-- The staggered condition of the small presentation, transported from `P`. -/
theorem staggered' (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ} (D : Datum P v n)
    (hrel : ∀ i : P.ι, UsedRelator D i) :
    ∀ i j : ULift.{u,0} (Fin (Nr P D)), i < j →
      pathMax (edgeOf' S P D) (S.enc.mapPath (P.path (rel P D i.down))) <
        pathMax (edgeOf' S P D) (S.enc.mapPath (P.path (rel P D j.down))) ∧
      pathMin (edgeOf' S P D) (S.enc.mapPath (P.path (rel P D i.down))) <
        pathMin (edgeOf' S P D) (S.enc.mapPath (P.path (rel P D j.down))) := by
  intro i j hij
  have hlt : rel P D i.down < rel P D j.down := (rel_lt_iff P D i.down j.down).mpr hij
  obtain ⟨hmax, hmin⟩ := P.staggered (rel P D i.down) (rel P D j.down) hlt
  have hnei := path_arrowList_ne_nil P (rel P D i.down)
  have hnej := path_arrowList_ne_nil P (rel P D j.down)
  constructor
  · rw [pathMax_mapPath S P D _ (fun e he => edgeOf_mem_cs_of_relator (hrel _) he),
      pathMax_mapPath S P D _ (fun e he => edgeOf_mem_cs_of_relator (hrel _) he)]
    exact (map_effRank_lt_iff S P D (fun c hc => pathMax_mem_cs hrel hnei hc)
      (fun c hc => pathMax_mem_cs hrel hnej hc)).mpr hmax
  · rw [pathMin_mapPath S P D _ (fun e he => edgeOf_mem_cs_of_relator (hrel _) he),
      pathMin_mapPath S P D _ (fun e he => edgeOf_mem_cs_of_relator (hrel _) he)]
    exact (map_effRank_lt_iff' S P D (fun c hc => pathMin_mem_cs hrel hnei hc)
      (fun c hc => pathMin_mem_cs hrel hnej hc)).mpr hmin

/-- **The presentation of the small model.** -/
noncomputable def smallPresentation (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ}
    (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i) : Presentation S.Vx where
  α := SmallCode S P D
  linearOrder := inferInstance
  edgeOf := edgeOf' S P D
  edgeOf_reverse := edgeOf'_reverse S P D
  noSelfLoop := noSelfLoop' S P D
  ι := ULift.{u,0} (Fin (Nr P D))
  linearOrder_ι := inferInstance
  base r := S.encObj (P.base (rel P D r.down))
  path r := S.enc.mapPath (P.path (rel P D r.down))
  reduced := reduced' S P D
  cyclicallyReduced := cyclicallyReduced' S P D
  notProperPower := notProperPower' S P D
  staggered := staggered' S P D hrel

@[simp] theorem smallPresentation_α (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ}
    (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i) :
    (smallPresentation S P D hrel).α = SmallCode S P D := rfl

@[simp] theorem smallPresentation_base (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ}
    (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i)
    (r : ULift.{u,0} (Fin (Nr P D))) :
    (smallPresentation S P D hrel).base r = S.encObj (P.base (rel P D r.down)) := rfl

@[simp] theorem smallPresentation_path (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ}
    (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i)
    (r : ULift.{u,0} (Fin (Nr P D))) :
    (smallPresentation S P D hrel).path r = S.enc.mapPath (P.path (rel P D r.down)) := rfl

@[simp] theorem smallPresentation_edgeOf (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ}
    (D : Datum P v n) (hrel : ∀ i : P.ι, UsedRelator D i) (g : Quiver.Total S.Vx) :
    (smallPresentation S P D hrel).edgeOf g = edgeOf' S P D g := rfl

/-- **The code of the small presentation separates unoriented edges.** -/
theorem codeSeparates_smallPresentation (S : Skel V W) (P : Presentation V) {v : V} {n : ℕ}
    (D : Datum P v n) (hsep : P.CodeSeparates)
    (hpair : ∀ e : Quiver.Total V, e ∈ D.usedArrowsList)
    (hrel : ∀ i : P.ι, UsedRelator D i) :
    (smallPresentation S P D hrel).CodeSeparates := by
  rw [Presentation.CodeSeparates] at hsep ⊢
  intro e f h
  have hcode : P.edgeOf (PrefunctorAux.totalMap S.dec e) =
      P.edgeOf (PrefunctorAux.totalMap S.dec f) :=
    effRank_inj (edgeOf_mem_cs (hpair _)) (edgeOf_mem_cs (hpair _)) (congrArg ULift.down h)
  rcases hsep _ _ hcode with h' | h'
  · exact Or.inl (dec_totalMap_injective S h')
  · refine Or.inr ?_
    rw [← PrefunctorAux.totalMap_totalReverse S.dec f] at h'
    exact dec_totalMap_injective S h'

end SmallPres

end Work.Case1
