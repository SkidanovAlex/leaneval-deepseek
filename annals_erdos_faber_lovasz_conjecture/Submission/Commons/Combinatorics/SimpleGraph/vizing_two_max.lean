import Mathlib.Data.Set.Card
import Submission.Commons.Combinatorics.SimpleGraph.vizing

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# Vizing's theorem when at most two vertices have maximum degree

If `G` has maximum degree `D` and at most two vertices of degree `D`, then `G` is
`D`-edge-colourable, i.e. `G.lineGraph.Colorable D`.
-/

namespace Commons.Combinatorics.SimpleGraph

open Vizing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree does not depend on the `DecidableRel` instance of `G.Adj`. -/
lemma degree_inst_congr (G : SimpleGraph V) (v : V) (i1 i2 : Fintype (G.neighborSet v)) :
    @SimpleGraph.degree V G v i1 = @SimpleGraph.degree V G v i2 := by
  unfold SimpleGraph.degree
  rw [SimpleGraph.neighborFinset_def, SimpleGraph.neighborFinset_def]
  congr 1
  ext x
  simp

/-- `Nat.card` of the neighbour set equals the degree. -/
lemma natcard_neighborSet_eq_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Nat.card (G.neighborSet v) = G.degree v := by
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]

/-- `Nat.card` of the edge set equals the cardinality of the edge finset. -/
lemma natcard_edgeSet_eq_edgeFinset_card (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nat.card G.edgeSet = G.edgeFinset.card := by
  rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]

/-- If an edge `e0` at `x` is not coloured by `(S, c)` and `deg x ≤ k`, there is a colour of
`Fin k` missing at `x`. -/
theorem exists_missingAt_of_notMem (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    {S : Finset (Sym2 V)} (hS : ↑S ⊆ G.edgeSet) (c : Sym2 V → Fin k) {x : V}
    (hdeg : G.degree x ≤ k) {e0 : Sym2 V} (he0G : e0 ∈ G.edgeSet) (he0S : e0 ∉ S)
    (hxe0 : x ∈ e0) : ∃ a : Fin k, MissingAt S c x a := by
  classical
  set T : Finset (Fin k) := (S.filter (fun e => x ∈ e)).image c with hT
  have hcard1 : T.card ≤ (S.filter (fun e => x ∈ e)).card := Finset.card_image_le
  have hsub : S.filter (fun e => x ∈ e) ⊆ (G.neighborFinset x).image (fun y => s(x, y)) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heS, hxe⟩ := he
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
    refine Finset.mem_image.mpr ⟨y, ?_, rfl⟩
    rw [G.mem_neighborFinset]
    have := hS heS
    rwa [SimpleGraph.mem_edgeSet] at this
  have he0img : e0 ∈ (G.neighborFinset x).image (fun y => s(x, y)) := by
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe0
    refine Finset.mem_image.mpr ⟨y, ?_, rfl⟩
    rw [G.mem_neighborFinset]
    have := he0G
    rwa [SimpleGraph.mem_edgeSet] at this
  have hssub : S.filter (fun e => x ∈ e) ⊂ (G.neighborFinset x).image (fun y => s(x, y)) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hsub, fun heq => he0S ?_⟩
    have : e0 ∈ S.filter (fun e => x ∈ e) := (Finset.ext_iff.mp heq e0).mpr he0img
    exact (Finset.mem_filter.mp this).1
  have hcard2 : (S.filter (fun e => x ∈ e)).card < G.degree x := by
    calc (S.filter (fun e => x ∈ e)).card
        < ((G.neighborFinset x).image (fun y => s(x, y))).card := Finset.card_lt_card hssub
      _ = (G.neighborFinset x).card := Finset.card_image_of_injective _ (sym2_mk_left_injective x)
      _ = G.degree x := G.card_neighborFinset_eq_degree x
  have hlt : T.card < k := by omega
  have huniv : T.card < (Finset.univ : Finset (Fin k)).card := by simpa using hlt
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card huniv
  refine ⟨a, fun e he hx hcea => ha ?_⟩
  exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hx⟩, hcea⟩

/-- The fan-extension lemma without the `maxDegree < k` hypothesis: if `e0 = s(x,y0)` is an
uncoloured edge (`x` has a missing colour `α`) and the last vertex of a longest fan at `x` has a
missing colour `β`, we get a contradiction.  This is a transcript of
`Vizing.extends_of_maximal` with its two uses of `exists_missingAt` replaced by hypotheses. -/
theorem extends_of_missing (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    {S : Finset (Sym2 V)} {c : Sym2 V → Fin k}
    (hS : ↑S ⊆ G.edgeSet) (hc : IsProper S c)
    (hmax : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin k), ↑S' ⊆ G.edgeSet →
      IsProper S' c' → S'.card ≤ S.card)
    {x y0 : V} (heG : s(x, y0) ∈ G.edgeSet) (heS : s(x, y0) ∉ S)
    {α : Fin k} (hα : MissingAt S c x α)
    {yl : List V} (hhead : yl.head? = some y0) (hfan : IsFan G S c x yl)
    (hfanmax : ∀ (hne : yl ≠ []) (z : V), z ∉ yl → s(x, z) ∈ G.edgeSet →
        ¬ FanRel S c x (yl.getLast hne) z)
    (hylne : yl ≠ []) {β : Fin k} (hβ : MissingAt S c (yl.getLast hylne) β) : False := by
  classical
  have hpos : 0 < yl.length := List.length_pos_of_ne_nil hylne
  let t : ℕ := yl.length - 1
  have htl : t < yl.length := by omega
  have hlast : yl.getLast hylne = yl[t] := by
    rw [List.getLast_eq_getElem]
  have hy0 : yl[0] = y0 := head?_getElem_zero hhead hpos
  have he0S : s(x, yl[0]) ∉ S := by rw [hy0]; exact heS
  have he0G : s(x, yl[0]) ∈ G.edgeSet := by rw [hy0]; exact heG
  have hβt : MissingAt S c yl[t] β := hlast ▸ hβ
  let ck : Sym2 V → Fin k := shiftAlong x c (yl.take (t + 1))
  let Sk : Finset (Sym2 V) := holeSet S (s(x, yl[0])) (s(x, yl[t]))
  have hproperk : IsProper Sk ck := isProper_shiftAlong G htl hS hc hfan he0S
  have hmissxk : MissingAt Sk ck x α := missingAt_x_shiftAlong hfan htl hα
  have hmissyk : MissingAt Sk ck yl[t] β := missingAt_index_shiftAlong hfan htl hβt
  have hekS : s(x, yl[t]) ∉ Sk := Finset.notMem_erase _ _
  have hxyt : s(x, yl[t]) ∈ G.edgeSet := by
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · rw [sym2_snd_congr ht0 htl hpos]; exact he0G
    · exact hS (hfan.edge_mem_at htpos htl)
  have hSksub : ↑Sk ⊆ G.edgeSet := by
    intro e' he'
    rcases Finset.mem_insert.mp (Finset.mem_erase.mp he').2 with rfl | h
    · exact he0G
    · exact hS h
  have hSkcard : Sk.card = S.card := by
    show ((insert (s(x, yl[0])) S).erase (s(x, yl[t]))).card = S.card
    have hmem : s(x, yl[t]) ∈ insert (s(x, yl[0])) S := by
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · rw [sym2_snd_congr ht0 htl hpos]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hfan.edge_mem_at htpos htl)
    rw [Finset.card_erase_of_mem hmem, Finset.card_insert_of_notMem he0S]
    omega
  have hmaxk : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin k), ↑S' ⊆ G.edgeSet →
      IsProper S' c' → S'.card ≤ Sk.card := by
    intro S' c' hS' hc'
    rw [hSkcard]; exact hmax S' c' hS' hc'
  by_cases hmissxk' : MissingAt Sk ck x β
  · have hproper' : IsProper (insert (s(x, yl[t])) Sk) (Function.update ck (s(x, yl[t])) β) := by
      refine insert_proper hproperk hekS ?_
      intro e' he' _ hadj
      rcases hadj with ⟨u, hu, hu'⟩
      rcases Sym2.mem_iff.mp hu with rfl | rfl
      · exact hmissxk' e' he' hu'
      · exact hmissyk e' he' hu'
    have hsub' : ↑(insert (s(x, yl[t])) Sk) ⊆ G.edgeSet := by
      intro e' he'
      rcases Finset.mem_insert.mp he' with rfl | h
      · exact hxyt
      · exact hSksub h
    have hcard := hmaxk _ _ hsub' hproper'
    have hmem : s(x, yl[t]) ∈ insert (s(x, yl[0])) S := by
      rcases Nat.eq_zero_or_pos t with ht0 | htpos
      · rw [sym2_snd_congr ht0 htl hpos]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hfan.edge_mem_at htpos htl)
    have hins : insert (s(x, yl[t])) Sk = insert (s(x, yl[0])) S := by
      show insert (s(x, yl[t])) ((insert (s(x, yl[0])) S).erase (s(x, yl[t]))) = insert (s(x, yl[0])) S
      rw [Finset.insert_erase hmem]
    rw [hins, Finset.card_insert_of_notMem he0S] at hcard
    omega
  · unfold MissingAt at hmissxk'
    push_neg at hmissxk'
    obtain ⟨f, hfSk, hxf, hfc⟩ := hmissxk'
    obtain ⟨z, hfz⟩ := Sym2.mem_iff_exists.mp hxf
    have hfG : f ∈ G.edgeSet := hSksub hfSk
    by_cases hzyl : z ∈ yl
    · obtain ⟨j, hjl, hjz⟩ := List.getElem_of_mem hzyl
      have hfj : f = s(x, yl[j]) := by rw [hfz, ← hjz]
      have hjt : j ≠ t := by
        intro hjt
        have h1 : f = s(x, yl[t]) := hfj.trans (sym2_snd_congr hjt hjl htl)
        exact hekS (h1 ▸ hfSk)
      have hjt' : j < t := by omega
      have hckj : ck (s(x, yl[j])) = β := by rw [← hfj]; exact hfc
      have hsxjck : shiftAlong x c (yl.take (t+1)) (s(x, yl[j])) = β := hckj
      have hbeta : β = c (s(x, yl[j+1])) := by
        have h1 := hckj
        change shiftAlong x c (yl.take (t + 1)) (s(x, yl[j])) = β at h1
        rw [shiftAlong_take_getElem c x yl hfan.1 htl hjt'] at h1
        exact h1.symm
      have hmissj : MissingAt S c yl[j] β := by
        rw [hbeta]
        exact hfan.missing_at (m := j+1) (by omega) (by omega)
      exact fan_contradiction hS hc hmax hfan htl he0S he0G hα hβt hjt' hmissj hsxjck
    · exfalso
      have hfS : f ∈ S := by
        rcases Finset.mem_insert.mp (Finset.mem_erase.mp hfSk).2 with h | h
        · exfalso
          apply hzyl
          have h2 : z = yl[0] := sym2_mk_left_injective x (hfz.symm.trans h)
          rw [h2]
          exact List.getElem_mem (l := yl) hpos
        · exact h
      have hckf : ck f = c f := by
        have h1 : shiftAlong x c (yl.take (t+1)) f = c f := by
          rw [hfz]
          refine shiftAlong_take_eq_of_not (t := t) c x yl hfan.1 ?_
          intro m hm hmt hh
          exact hzyl (by
            have h2 : z = yl[m] := sym2_mk_left_injective x hh
            rw [h2]; exact List.getElem_mem (l := yl) hm)
        exact h1
      have hcf : c f = β := by rw [← hckf]; exact hfc
      refine hfanmax hylne z hzyl ?_ ⟨?_, ?_⟩
      · rw [← hfz]; exact hfG
      · rw [← hfz]; exact hfS
      · rw [hlast, ← hfz, hcf]; exact hβt

/-- If no colour of `Fin D` is missing at `z` for the colouring `(S, c)`, then `z` has degree `D`
and every edge at `z` lies in `S`. -/
theorem saturated_of_forall_not_missingAt (G : SimpleGraph V) [DecidableRel G.Adj] {D : ℕ}
    (hD : ∀ v, G.degree v ≤ D) {S : Finset (Sym2 V)} {c : Sym2 V → Fin D}
    (hS : ↑S ⊆ G.edgeSet) {z : V} (h : ∀ β : Fin D, ¬ MissingAt S c z β) :
    G.degree z = D ∧ ∀ e ∈ G.edgeSet, z ∈ e → e ∈ S := by
  classical
  set T : Finset (Sym2 V) := S.filter (fun e => z ∈ e) with hT
  have hchoice : ∀ β : Fin D, ∃ e, e ∈ S ∧ z ∈ e ∧ c e = β := by
    intro β
    have hh := h β
    rw [MissingAt] at hh
    push_neg at hh
    exact hh
  choose f hfS hfz hfc using hchoice
  have hfT : ∀ β, f β ∈ T := fun β => Finset.mem_filter.mpr ⟨hfS β, hfz β⟩
  let g : Fin D → ↥T := fun β => ⟨f β, hfT β⟩
  have hginj : Function.Injective g := by
    intro a b hab
    have hfab : f a = f b := congrArg Subtype.val hab
    rw [← hfc a, ← hfc b, hfab]
  have hcardD : D ≤ T.card := by
    have := Fintype.card_le_of_injective g hginj
    simpa using this
  have hsubT : T ⊆ G.incidenceFinset z := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heS, hze⟩ := he
    rw [G.mem_incidenceFinset]
    exact ⟨hS heS, hze⟩
  have hcard2 : T.card ≤ G.degree z := by
    calc T.card ≤ (G.incidenceFinset z).card := Finset.card_le_card hsubT
      _ = G.degree z := G.card_incidenceFinset_eq_degree z
  have hTdeg : T.card = G.degree z := le_antisymm hcard2 (le_trans (hD z) hcardD)
  have hdeg : G.degree z = D := le_antisymm (hD z) (le_trans hcardD hcard2)
  have hTeq : T = G.incidenceFinset z :=
    Finset.eq_of_subset_of_card_le hsubT
      (le_of_eq ((hTdeg.trans (G.card_incidenceFinset_eq_degree z).symm).symm))
  refine ⟨hdeg, fun e he hze => ?_⟩
  have heinc : e ∈ G.incidenceFinset z := by
    rw [G.mem_incidenceFinset]
    exact ⟨he, hze⟩
  have heT : e ∈ T := hTeq ▸ heinc
  exact (Finset.mem_filter.mp heT).1

/-- The last vertex of a longest fan at a hole has no missing colour. -/
theorem not_missingAt_fan_last (G : SimpleGraph V) [DecidableRel G.Adj] {D : ℕ}
    {S : Finset (Sym2 V)} {c : Sym2 V → Fin D}
    (hS : ↑S ⊆ G.edgeSet) (hc : IsProper S c)
    (hmax : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin D), ↑S' ⊆ G.edgeSet →
      IsProper S' c' → S'.card ≤ S.card)
    {x y0 : V} (heG : s(x, y0) ∈ G.edgeSet) (heS : s(x, y0) ∉ S)
    {α : Fin D} (hα : MissingAt S c x α)
    {yl : List V} (hhead : yl.head? = some y0) (hfan : IsFan G S c x yl)
    (hfanmax : ∀ (hne : yl ≠ []) (z : V), z ∉ yl → s(x, z) ∈ G.edgeSet →
        ¬ FanRel S c x (yl.getLast hne) z)
    (hylne : yl ≠ []) : ∀ β : Fin D, ¬ MissingAt S c (yl.getLast hylne) β :=
  fun β hβ => extends_of_missing G hS hc hmax heG heS hα hhead hfan hfanmax hylne hβ

/-- A longest fan rooted at an endpoint of an uncoloured edge ends at a saturated vertex `z ≠ x`
adjacent to `x`, whose every incident edge is coloured. -/
theorem exists_saturated_fan_end (G : SimpleGraph V) [DecidableRel G.Adj] {D : ℕ}
    (hD : ∀ v, G.degree v ≤ D) {S : Finset (Sym2 V)} {c : Sym2 V → Fin D}
    (hS : ↑S ⊆ G.edgeSet) (hc : IsProper S c)
    (hmax : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin D), ↑S' ⊆ G.edgeSet →
      IsProper S' c' → S'.card ≤ S.card)
    {x y0 : V} (heG : s(x, y0) ∈ G.edgeSet) (heS : s(x, y0) ∉ S)
    {α : Fin D} (hα : MissingAt S c x α) :
    ∃ z : V, z ≠ x ∧ G.degree z = D ∧ s(x, z) ∈ G.edgeSet ∧
      ∀ e ∈ G.edgeSet, z ∈ e → e ∈ S := by
  classical
  obtain ⟨yl, hhead, hfan, hfanmax⟩ := exists_longest_fan G S c x y0 heG
  have hylne : yl ≠ [] := by rintro rfl; simp at hhead
  have hno := not_missingAt_fan_last G hS hc hmax heG heS hα hhead hfan hfanmax hylne
  have hs := saturated_of_forall_not_missingAt G hD hS hno
  have hlastx : yl.getLast hylne ≠ x := by
    rw [List.getLast_eq_getElem]
    exact hfan.ne_x (j := yl.length - 1) (by
      have := List.length_pos_of_ne_nil hylne; omega)
  have hadj : s(x, yl.getLast hylne) ∈ G.edgeSet := hfan.2.1 _ (List.getLast_mem hylne)
  exact ⟨yl.getLast hylne, hlastx, hs.1, hadj, hs.2⟩

/-- A full proper edge colouring of `G.edgeFinset` gives a colouring of the line graph. -/
theorem colorable_of_isProper (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (c : Sym2 V → Fin k) (hc : IsProper G.edgeFinset c) : G.lineGraph.Colorable k := by
  refine ⟨SimpleGraph.Coloring.mk (fun e : G.edgeSet => c e.val) ?_⟩
  intro e1 e2 hadj
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  obtain ⟨hne, v, hv1, hv2⟩ := hadj
  exact hc e1.val (SimpleGraph.mem_edgeFinset.mpr e1.property) e2.val
    (SimpleGraph.mem_edgeFinset.mpr e2.property) (fun h => hne (Subtype.ext h)) ⟨v, hv1, hv2⟩

/-- A colouring of the line graph gives a function which is a proper colouring of `G.edgeFinset`. -/
theorem exists_isProper_of_colorable (H : SimpleGraph V) [DecidableRel H.Adj] {k : ℕ} [NeZero k]
    (hcol : H.lineGraph.Colorable k) : ∃ c : Sym2 V → Fin k, IsProper H.edgeFinset c := by
  classical
  obtain ⟨col⟩ := hcol
  let c : Sym2 V → Fin k := fun e => if h : e ∈ H.edgeSet then col ⟨e, h⟩ else 0
  refine ⟨c, ?_⟩
  intro e he e' he' hne hadj
  have heS : e ∈ H.edgeSet := SimpleGraph.mem_edgeFinset.mp he
  have he'S : e' ∈ H.edgeSet := SimpleGraph.mem_edgeFinset.mp he'
  have hce : c e = col ⟨e, heS⟩ := by simp only [c]; rw [dif_pos heS]
  have hce' : c e' = col ⟨e', he'S⟩ := by simp only [c]; rw [dif_pos he'S]
  rw [hce, hce']
  exact col.valid (by
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨fun hh => hne (congrArg Subtype.val hh), hadj⟩)

theorem vizing_two_max {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hD : ∀ v : V, G.degree v ≤ D)
    (hfew : {v : V | G.degree v = D}.ncard ≤ 2) : G.lineGraph.Colorable D := by
  classical
  have key : ∀ m : ℕ, ∀ (G : SimpleGraph V), Nat.card G.edgeSet = m →
      ∀ (D : ℕ), (∀ v : V, Nat.card (G.neighborSet v) ≤ D) →
      ({v : V | Nat.card (G.neighborSet v) = D}).ncard ≤ 2 →
      G.lineGraph.Colorable D := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro G hm D hDn hfewn
      have hm' : G.edgeFinset.card = m :=
        (natcard_edgeSet_eq_edgeFinset_card (G := G)).symm.trans hm
      have hD : ∀ v : V, G.degree v ≤ D := fun v => by
        rw [← natcard_neighborSet_eq_degree (G := G) v]; exact hDn v
      have hfew : ({v : V | G.degree v = D}).ncard ≤ 2 := by
        have hsetD : ({v : V | Nat.card (G.neighborSet v) = D} : Set V) =
            {v : V | G.degree v = D} := by
          ext v
          change Nat.card (G.neighborSet v) = D ↔ G.degree v = D
          constructor
          · intro hv
            rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at hv
            rwa [degree_inst_congr G v _ _] at hv
          · intro hv
            rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
            rwa [degree_inst_congr G v _ _]
        rw [← hsetD]; exact hfewn
      by_cases hempty : G.edgeFinset.card = 0
      · have hcard : Fintype.card G.edgeSet = 0 := by
          rw [← SimpleGraph.edgeFinset_card]; exact hempty
        haveI : IsEmpty G.edgeSet := Fintype.card_eq_zero_iff.mp hcard
        exact ⟨SimpleGraph.Coloring.ofIsEmpty (G := G.lineGraph)⟩
      · have hedge : 0 < G.edgeFinset.card := Nat.pos_of_ne_zero hempty
        by_cases hlt : G.maxDegree < D
        · exact (vizing G).mono (by omega)
        · have hmaxD : G.maxDegree = D :=
            le_antisymm (G.maxDegree_le_of_forall_degree_le D hD) (by omega)
          by_contra hnot
          obtain ⟨e0, he0⟩ := Finset.card_pos.mp hedge
          haveI : Nonempty V := by
            induction e0 using Sym2.ind with
            | h a b => exact ⟨a⟩
          have step : ∀ (x y : V), s(x, y) ∈ G.edgeSet →
              ∃ z : V, z ≠ x ∧ G.degree z = D ∧ s(x, z) ∈ G.edgeSet ∧
                ∀ e ∈ G.edgeSet, z ∈ e → e ∈ G.edgeFinset.erase s(x, y) := by
            intro x y hxy
            have hdel : (G.deleteEdges {s(x, y)}).edgeFinset = G.edgeFinset.erase s(x, y) := by
              apply Finset.ext
              intro e
              simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
                Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_erase]
              tauto
            have hDpos : 0 < D := by
              have hmz : G.maxDegree ≠ 0 := by
                intro h0
                rw [SimpleGraph.maxDegree_eq_zero_iff] at h0
                rw [h0] at hedge
                simp at hedge
              omega
            haveI : NeZero D := ⟨Nat.pos_iff_ne_zero.mp hDpos⟩
            have hD' : ∀ v : V, Nat.card ((G.deleteEdges {s(x, y)}).neighborSet v) ≤ D := by
              intro v
              rw [natcard_neighborSet_eq_degree]
              exact (SimpleGraph.degree_le_of_le (G := G.deleteEdges {s(x, y)}) (H := G)
                (SimpleGraph.deleteEdges_le {s(x, y)})).trans (hD v)
            have hfew' : ({v : V | Nat.card ((G.deleteEdges {s(x, y)}).neighborSet v) = D}).ncard
                ≤ 2 := by
              apply le_trans (Set.ncard_le_ncard ?_) hfew
              intro v hv
              change Nat.card ((G.deleteEdges {s(x, y)}).neighborSet v) = D at hv
              change G.degree v = D
              rw [natcard_neighborSet_eq_degree] at hv
              have hle : (G.deleteEdges {s(x, y)}).degree v ≤ G.degree v :=
                SimpleGraph.degree_le_of_le (G := G.deleteEdges {s(x, y)}) (H := G)
                  (SimpleGraph.deleteEdges_le {s(x, y)})
              exact le_antisymm (hD v) (hv ▸ hle)
            have hcard_lt : (G.deleteEdges {s(x, y)}).edgeFinset.card < m := by
              rw [hdel]
              rw [Finset.card_erase_of_mem (SimpleGraph.mem_edgeFinset.mpr hxy)]
              omega
            have hm'' : Nat.card (G.deleteEdges {s(x, y)}).edgeSet
                = (G.deleteEdges {s(x, y)}).edgeFinset.card :=
              natcard_edgeSet_eq_edgeFinset_card (G := G.deleteEdges {s(x, y)})
            have IHf : (G.deleteEdges {s(x, y)}).lineGraph.Colorable D :=
              ih _ hcard_lt (G.deleteEdges {s(x, y)}) hm'' D hD' hfew'
            obtain ⟨c, hc0⟩ := exists_isProper_of_colorable (G.deleteEdges {s(x, y)}) IHf
            have hc : IsProper (G.edgeFinset.erase s(x, y)) c := hdel ▸ hc0
            have hS : ↑(G.edgeFinset.erase s(x, y)) ⊆ G.edgeSet := by
              intro e he
              simp only [Finset.mem_coe, Finset.mem_erase] at he
              exact SimpleGraph.mem_edgeFinset.mp he.2
            have heS : s(x, y) ∉ G.edgeFinset.erase s(x, y) := Finset.notMem_erase _ _
            have hmax : ∀ (S' : Finset (Sym2 V)) (c' : Sym2 V → Fin D), ↑S' ⊆ G.edgeSet →
                IsProper S' c' → S'.card ≤ (G.edgeFinset.erase s(x, y)).card := by
              intro S' c' hS' hc'
              by_contra hcon
              rw [not_le] at hcon
              have hS'sub : S' ⊆ G.edgeFinset := fun f hf =>
                SimpleGraph.mem_edgeFinset.mpr (hS' hf)
              have hS'card : S'.card ≤ G.edgeFinset.card := Finset.card_le_card hS'sub
              have hSc := Finset.card_erase_of_mem (SimpleGraph.mem_edgeFinset.mpr hxy)
              rw [hSc] at hcon
              have hS'card_eq : S'.card = G.edgeFinset.card := by omega
              have hS'eq : S' = G.edgeFinset :=
                Finset.eq_of_subset_of_card_le hS'sub (le_of_eq hS'card_eq.symm)
              rw [hS'eq] at hc'
              exact hnot (colorable_of_isProper G c' hc')
            obtain ⟨a, ha⟩ :=
              exists_missingAt_of_notMem G hS c (hD x) hxy heS (Sym2.mem_mk_left x y)
            obtain ⟨z, hzx, hzD, hxz, hzS⟩ :=
              exists_saturated_fan_end G hD hS hc hmax hxy heS ha
            exact ⟨z, hzx, hzD, hxz, hzS⟩
          obtain ⟨u, hu⟩ := G.exists_maximal_degree_vertex
          have huD : G.degree u = D := hu.symm.trans hmaxD
          have hDpos : 0 < D := by
            have hmz : G.maxDegree ≠ 0 := by
              intro h0
              rw [SimpleGraph.maxDegree_eq_zero_iff] at h0
              rw [h0] at hedge
              simp at hedge
            omega
          obtain ⟨w, hw⟩ := Finset.card_pos.mp (by
            rw [G.card_neighborFinset_eq_degree, huD]; exact hDpos)
          have huw : G.Adj u w := by rwa [G.mem_neighborFinset] at hw
          have hsuw : s(u, w) ∈ G.edgeSet := by rw [SimpleGraph.mem_edgeSet]; exact huw
          obtain ⟨z, hzu, hzD, huz_mem, hzS⟩ := step u w hsuw
          obtain ⟨z', hz'u, hz'D, huz'_mem, hz'S⟩ := step u z huz_mem
          have hz'z : z' ≠ z := by
            intro hzz
            have hmem : s(u, z) ∈ G.edgeFinset.erase s(u, z) :=
              hz'S (s(u, z)) huz_mem (by rw [hzz]; exact Sym2.mem_mk_right u z)
            exact (Finset.notMem_erase s(u, z) G.edgeFinset) hmem
          have huz : u ≠ z := fun h => hzu h.symm
          have huz' : u ≠ z' := fun h => hz'u h.symm
          have hsub : ({u, z, z'} : Set V) ⊆ {v : V | G.degree v = D} := by
            intro v hv
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
            rcases hv with rfl | rfl | rfl
            · exact huD
            · exact hzD
            · exact hz'D
          have htriple : (3 : ℕ) ≤ ({u, z, z'} : Set V).ncard := by
            rw [show ({u, z, z'} : Set V) = insert u (insert z {z'}) from rfl,
              Set.ncard_insert_of_notMem (by simp [huz, huz']),
              Set.ncard_insert_of_notMem (by simp [hz'z.symm]),
              Set.ncard_singleton]
          have hcon := le_trans htriple (le_trans (Set.ncard_le_ncard hsub) hfew)
          omega
  have hDn : ∀ v : V, Nat.card (G.neighborSet v) ≤ D := fun v => by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
    rw [degree_inst_congr G v _ _]
    exact hD v
  have hfewn : ({v : V | Nat.card (G.neighborSet v) = D}).ncard ≤ 2 := by
    have hsetD : ({v : V | Nat.card (G.neighborSet v) = D} : Set V) = {v : V | G.degree v = D} := by
      ext v
      change Nat.card (G.neighborSet v) = D ↔ G.degree v = D
      constructor
      · intro hv
        rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at hv
        rwa [degree_inst_congr G v _ _] at hv
      · intro hv
        rw [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
        rwa [degree_inst_congr G v _ _]
    rw [hsetD]; exact hfew
  exact key (Nat.card G.edgeSet) G rfl D hDn hfewn

end Commons.Combinatorics.SimpleGraph