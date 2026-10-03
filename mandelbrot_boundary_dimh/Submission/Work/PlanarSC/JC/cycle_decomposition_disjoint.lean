import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.DartGraph
import Submission.Work.HornSC.CellBoundaryJordan.WallGraph
import Submission.Work.HornSC.CellBoundaryJordan.WallCycle.Defs
import Submission.Work.HornSC.CellBoundaryJordan.WallCycle.adjSeg_bridge
import Submission.Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_adjSeg_subset_wallSet

/-!
# Decomposition of `wallSet A` into disjoint simple grid cycles

`wallSet A` is the union of the unit grid segments separating a cell of `A` from a cell outside
`A`.  Every lattice point has an even number of incident wall segments (`wall_local_even`), so the
wall graph is an even graph, and the edges of a finite even graph decompose into edge-disjoint
simple cycles.

This file proves that decomposition and assembles the requested statement
`Work.PlanarSC.JC.cycle_decomposition_disjoint`.
-/

namespace Work.PlanarSC.JC

open Set
open Work.HornSC.CellBoundaryJordan

/-- The lattice points that can be an endpoint of a wall of `A`. -/
abbrev WallV (A : Finset (ℤ × ℤ)) : Type :=
  {v : ℤ × ℤ // v ∈ Work.HornSC.CellBoundaryJordan.WallCycle.wallVerts A}

/-- The dart set of the wall graph of `A`: all ordered pairs of lattice points whose segment is a
wall of `A`. -/
noncomputable def wallDartSet (A : Finset (ℤ × ℤ)) : Finset (WallV A × WallV A) :=
  (Finset.univ ×ˢ Finset.univ).filter
    (fun e => Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj A e.1.1 e.2.1)

lemma mem_wallDartSet {A : Finset (ℤ × ℤ)} {e : WallV A × WallV A} :
    e ∈ wallDartSet A ↔ Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj A e.1.1 e.2.1 := by
  classical
  simp [wallDartSet]

/-- The wall graph of `A`, as a dart graph. -/
noncomputable def wallDartGraph (A : Finset (ℤ × ℤ)) :
    Work.HornSC.CellBoundaryJordan.DartGraph (WallV A) where
  D := wallDartSet A
  symm := by
    intro e he
    rw [mem_wallDartSet] at he ⊢
    exact Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_symm he
  noLoop := by
    intro e he h
    rw [mem_wallDartSet] at he
    exact Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_irrefl (h ▸ he)

lemma WallDeg_eq_card_filter (A : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    Work.HornSC.CellBoundaryJordan.WallCycle.WallDeg A v
      = ((Work.HornSC.CellBoundaryJordan.WallCycle.nbhdPts v).filter
          (fun w => Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj A v w)).card := by
  rw [Work.HornSC.CellBoundaryJordan.WallCycle.WallDeg, Finset.card_filter]

lemma deg_wallDartGraph (A : Finset (ℤ × ℤ)) (x : WallV A) :
    (wallDartGraph A).deg x = Work.HornSC.CellBoundaryJordan.WallCycle.WallDeg A x.1 := by
  classical
  rw [Work.HornSC.CellBoundaryJordan.DartGraph.deg, WallDeg_eq_card_filter]
  have hD : (wallDartGraph A).D = wallDartSet A := rfl
  rw [hD]
  have himg : (wallDartSet A).filter (fun e => e.1 = x)
      = (Finset.univ.filter (fun w : WallV A =>
          Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj A x.1 w.1)).image
        (fun w => (x, w)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨he, he1⟩
      rw [mem_wallDartSet] at he
      refine ⟨e.2, ?_, ?_⟩
      · rw [← he1]; exact he
      · exact Prod.ext he1.symm rfl
    · rintro ⟨w, hw, hwe⟩
      rw [← hwe]
      exact ⟨mem_wallDartSet.mpr hw, rfl⟩
  rw [himg,
    Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.snd h)]
  have hsub : (Finset.univ.filter (fun w : WallV A =>
        Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj A x.1 w.1)).image Subtype.val
      = (Work.HornSC.CellBoundaryJordan.WallCycle.nbhdPts x.1).filter
          (fun w => Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj A x.1 w) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, hyw⟩
      rw [← hyw]
      exact ⟨Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_mem_nbhdPts hy, hy⟩
    · rintro ⟨hw, hadj⟩
      exact ⟨⟨w, Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_snd_mem_wallVerts hadj⟩,
        hadj, rfl⟩
  rw [← hsub, Finset.card_image_of_injective _ Subtype.val_injective]

lemma even_deg_wallDartGraph (A : Finset (ℤ × ℤ)) (x : WallV A) :
    Even ((wallDartGraph A).deg x) := by
  rw [deg_wallDartGraph]
  exact Work.HornSC.CellBoundaryJordan.WallCycle.even_WallDeg A x.1

/-! ## The graph-theoretic core: an even finite graph has a cycle -/

end Work.PlanarSC.JC

namespace Work.HornSC.CellBoundaryJordan

namespace DartGraph

variable {α : Type*} [DecidableEq α]

lemma deg_eq (G : DartGraph α) (a : α) : G.deg a = (G.D.filter (fun e => e.1 = a)).card := rfl

/-- One greedy step: move to a neighbour that has not been visited yet, if one exists. -/
noncomputable def nstep (G : DartGraph α) (s : α × Finset α) : α × Finset α := by
  classical
  exact if h : ∃ w : α, (s.1, w) ∈ G.D ∧ w ∉ s.2 then
    (Classical.choose h, insert (Classical.choose h) s.2) else s

lemma nstep_pos (G : DartGraph α) {s : α × Finset α}
    (h : ∃ w : α, (s.1, w) ∈ G.D ∧ w ∉ s.2) :
    (G.nstep s).1 = Classical.choose h ∧ (s.1, (G.nstep s).1) ∈ G.D ∧
      (G.nstep s).1 ∉ s.2 ∧ (G.nstep s).2 = insert (Classical.choose h) s.2 := by
  have hspec := Classical.choose_spec h
  rw [nstep, dite_eq_left h]
  exact ⟨rfl, hspec.1, hspec.2, rfl⟩

lemma nstep_neg (G : DartGraph α) {s : α × Finset α}
    (h : ¬ ∃ w : α, (s.1, w) ∈ G.D ∧ w ∉ s.2) : G.nstep s = s := by
  rw [nstep, dite_eq_right h]

/-- The greedy walk of `G` starting at `a`. -/
noncomputable def gwalk (G : DartGraph α) (a : α) (n : ℕ) : α × Finset α :=
  (G.nstep)^[n] (a, {a})

lemma gwalk_zero (G : DartGraph α) (a : α) : G.gwalk a 0 = (a, {a}) := rfl

lemma gwalk_succ (G : DartGraph α) (a : α) (n : ℕ) :
    G.gwalk a (n+1) = G.nstep (G.gwalk a n) := by
  rw [gwalk, Function.iterate_succ_apply']; rfl

/-- The walk can still be extended at time `n`. -/
def Live (G : DartGraph α) (a : α) (n : ℕ) : Prop :=
  ∃ w : α, ((G.gwalk a n).1, w) ∈ G.D ∧ w ∉ (G.gwalk a n).2

lemma gwalk_succ_of_live (G : DartGraph α) (a : α) (n : ℕ) (h : G.Live a n) :
    ((G.gwalk a (n+1)).1, (G.gwalk a n).1) ∈ G.D ∧ (G.gwalk a (n+1)).1 ∉ (G.gwalk a n).2 ∧
    (G.gwalk a (n+1)).2 = insert (G.gwalk a (n+1)).1 (G.gwalk a n).2 := by
  have h' : ∃ w : α, ((G.gwalk a n).1, w) ∈ G.D ∧ w ∉ (G.gwalk a n).2 := h
  obtain ⟨h1, h2, h3, h4⟩ := nstep_pos G h'
  have hgw : G.gwalk a (n+1) = G.nstep (G.gwalk a n) := gwalk_succ G a n
  have hx' : (G.gwalk a (n+1)).1 = (G.nstep (G.gwalk a n)).1 := by rw [hgw]
  have hV : (G.gwalk a (n+1)).2 = insert (Classical.choose h') (G.gwalk a n).2 := by rw [hgw, h4]
  exact ⟨by rw [hx']; exact G.symm _ h2, by rw [hx']; exact h3, by rw [hV, ← h1, hx']⟩

lemma gwalk_inv (G : DartGraph α) (a : α) : ∀ n, (∀ j < n, G.Live a j) →
    (G.gwalk a n).2 = (Finset.range (n+1)).image (fun j => (G.gwalk a j).1) ∧
    (∀ i < n+1, ∀ j < n+1, (G.gwalk a i).1 = (G.gwalk a j).1 → i = j) := by
  intro n
  induction n with
  | zero =>
    intro _
    constructor
    · simp [gwalk_zero]
    · intro i hi j hj _
      omega
  | succ n ih =>
    intro halive
    have hn : G.Live a n := halive n (by omega)
    obtain ⟨ihV, ihinj⟩ := ih (fun j hj => halive j (by omega))
    obtain ⟨hstep1, hstep2, hstep3⟩ := gwalk_succ_of_live G a n hn
    constructor
    · rw [hstep3, ihV]
      ext v
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (rfl | ⟨j, hj, hjv⟩)
        · exact ⟨n+1, by omega, rfl⟩
        · exact ⟨j, by omega, hjv⟩
      · rintro ⟨j, hj, hjv⟩
        rcases (show j ≤ n ∨ j = n + 1 from by omega) with h | h
        · exact Or.inr ⟨j, by omega, hjv⟩
        · exact Or.inl (by rw [← hjv, h])
    · intro i hi j hj hij
      have hi2 : i ≤ n + 1 := by omega
      have hj2 : j ≤ n + 1 := by omega
      rcases Nat.lt_or_eq_of_le hi2 with hi_lt | hi_eq
      · rcases Nat.lt_or_eq_of_le hj2 with hj_lt | hj_eq
        · exact ihinj i hi_lt j hj_lt hij
        · exfalso
          have hmem : (G.gwalk a i).1 ∈ (G.gwalk a n).2 := by
            rw [ihV]; exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi_lt, rfl⟩
          have heq : (G.gwalk a (n+1)).1 = (G.gwalk a i).1 := by rw [← hj_eq, hij]
          exact hstep2 (heq.symm ▸ hmem)
      · rcases Nat.lt_or_eq_of_le hj2 with hj_lt | hj_eq
        · exfalso
          have hmem : (G.gwalk a j).1 ∈ (G.gwalk a n).2 := by
            rw [ihV]; exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj_lt, rfl⟩
          have heq : (G.gwalk a (n+1)).1 = (G.gwalk a j).1 := by rw [← hi_eq, hij]
          exact hstep2 (heq.symm ▸ hmem)
        · rw [hi_eq, hj_eq]

lemma exists_live_false (G : DartGraph α) [Fintype α] (a : α) : ∃ n, ¬ G.Live a n := by
  by_contra hcon
  push_neg at hcon
  have hcard : ∀ n, ((G.gwalk a n).2).card = n + 1 := by
    intro n
    have hinv := gwalk_inv G a n (fun j _ => hcon j)
    rw [hinv.1]
    have hci : ((Finset.range (n+1)).image (fun j => (G.gwalk a j).1)).card
        = (Finset.range (n+1)).card := by
      refine Finset.card_image_of_injOn ?_
      intro x hx y hy hxy
      rw [Finset.mem_coe] at hx hy
      exact hinv.2 x (by rw [Finset.mem_range] at hx; omega)
        y (by rw [Finset.mem_range] at hy; omega) hxy
    rw [hci, Finset.card_range]
  have h1 := hcard (Fintype.card α)
  have h2 := Finset.card_le_univ (G.gwalk a (Fintype.card α)).2
  omega

/-- Every nonzero finite graph with all degrees even contains a simple cycle. -/
theorem exists_cycle_of_even_deg (G : DartGraph α) [Fintype α] (heven : ∀ a, Even (G.deg a))
    (hne : G.D.Nonempty) : ∃ C : G.Cycle, C.darts ⊆ G.D := by
  classical
  obtain ⟨e0, he0⟩ := hne
  set a := e0.1 with ha
  have hdega1 : 1 ≤ G.deg a := by
    rw [deg_eq]
    exact Finset.card_pos.mpr ⟨e0, Finset.mem_filter.mpr ⟨he0, by rw [ha]⟩⟩
  have hdeg2 : 2 ≤ G.deg a := by
    obtain ⟨k, hk⟩ := heven a
    omega
  have hlive0 : G.Live a 0 := by
    have hc : 0 < (G.D.filter (fun e => e.1 = a)).card := by
      rw [← deg_eq]
      exact hdega1
    obtain ⟨e, he⟩ := Finset.card_pos.mp hc
    rw [Finset.mem_filter] at he
    refine ⟨e.2, ?_, ?_⟩
    · rw [gwalk_zero, ← he.2]; exact he.1
    · rw [gwalk_zero, Finset.mem_singleton]
      intro h
      exact G.noLoop e he.1 (by rw [h, he.2])
  have hfind : ∃ n, ¬ G.Live a n := exists_live_false G a
  set n0 := Nat.find hfind with hn0def
  have hn0 : ¬ G.Live a n0 := Nat.find_spec hfind
  have halive : ∀ j < n0, G.Live a j := fun j hj => by
    by_contra hc
    exact Nat.find_min hfind hj hc
  have hv := (gwalk_inv G a n0 halive).1
  have hinj := (gwalk_inv G a n0 halive).2
  have hdead : ∀ w, ((G.gwalk a n0).1, w) ∈ G.D → w ∈ (G.gwalk a n0).2 := by
    intro w hw
    by_contra hc
    exact hn0 ⟨w, hw, hc⟩
  have hn0pos : 1 ≤ n0 := by
    rcases Nat.eq_zero_or_pos n0 with h | h
    · exact absurd (h.symm ▸ hlive0) hn0
    · exact h
  have hdegx : 2 ≤ G.deg (G.gwalk a n0).1 := by
    have hl : G.Live a (n0 - 1) := halive (n0-1) (by omega)
    have hs1 := (gwalk_succ_of_live G a (n0-1) hl).1
    rw [show (n0-1)+1 = n0 by omega] at hs1
    have hpos : 1 ≤ G.deg (G.gwalk a n0).1 := by
      rw [deg_eq]
      exact Finset.card_pos.mpr ⟨((G.gwalk a n0).1, (G.gwalk a (n0-1)).1),
        Finset.mem_filter.mpr ⟨hs1, rfl⟩⟩
    obtain ⟨k, hk⟩ := heven (G.gwalk a n0).1
    omega
  set S : Finset ℕ := (Finset.range n0).filter
      (fun i => ((G.gwalk a n0).1, (G.gwalk a i).1) ∈ G.D) with hSdef
  have hScard : S.card = G.deg (G.gwalk a n0).1 := by
    have hmap : (G.D.filter (fun e => e.1 = (G.gwalk a n0).1))
        = S.image (fun i => ((G.gwalk a n0).1, (G.gwalk a i).1)) := by
      ext e
      constructor
      · intro he
        rw [Finset.mem_filter] at he
        obtain ⟨heD, he1⟩ := he
        have hd : ((G.gwalk a n0).1, e.2) ∈ G.D := by
          have hEq : ((G.gwalk a n0).1, e.2) = e := Prod.ext he1.symm rfl
          rw [hEq]; exact heD
        have hw := hdead e.2 hd
        rw [hv] at hw
        obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hw
        have hir : i < n0 + 1 := Finset.mem_range.mp hi
        have hine : i ≠ n0 := by
          intro hie
          exact G.noLoop e heD (by rw [he1, ← hie]; exact hix)
        have hiS : i ∈ S := by
          rw [hSdef, Finset.mem_filter]
          exact ⟨Finset.mem_range.mpr (by omega), by rw [hix]; exact hd⟩
        exact Finset.mem_image.mpr ⟨i, hiS, Prod.ext he1.symm hix⟩
      · intro he
        rw [Finset.mem_image] at he
        obtain ⟨i, hi, rfl⟩ := he
        rw [hSdef, Finset.mem_filter] at hi
        exact Finset.mem_filter.mpr ⟨hi.2, rfl⟩
    rw [deg_eq, hmap]
    exact (Finset.card_image_of_injOn (f := fun i => ((G.gwalk a n0).1, (G.gwalk a i).1))
      (by
        intro x hx y hy hxy
        rw [Finset.mem_coe] at hx hy
        rw [hSdef, Finset.mem_filter, Finset.mem_range] at hx hy
        exact hinj x (by omega) y (by omega) (by simpa using congrArg Prod.snd hxy))).symm
  have hS2 : 2 ≤ S.card := hScard.symm ▸ hdegx
  have hSne : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hS2)
  set i := S.min' hSne with hidef
  have hiS : i ∈ S := Finset.min'_mem S hSne
  have hiSn : i < n0 ∧ ((G.gwalk a n0).1, (G.gwalk a i).1) ∈ G.D := by
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hiS
    exact hiS
  have hilt : i + 2 ≤ n0 := by
    obtain ⟨j, hjS, hji⟩ : ∃ j ∈ S, j ≠ i := by
      by_contra hc
      push_neg at hc
      have hsub : S ⊆ {i} := fun j hj => Finset.mem_singleton.mpr (hc j hj)
      have hcle : S.card ≤ 1 := by simpa using Finset.card_le_card hsub
      exact (not_le_of_gt (lt_of_lt_of_le Nat.one_lt_two hS2)) hcle
    have hle : S.min' hSne ≤ j := Finset.min'_le S j hjS
    have h1 : i < j := lt_of_le_of_ne hle (Ne.symm hji)
    have hj : j < n0 := by
      have h2 := hjS
      rw [hSdef, Finset.mem_filter, Finset.mem_range] at h2
      exact h2.1
    omega
  set L := n0 - i + 1 with hLdef
  have hiL : i + L - 1 = n0 := by omega
  have hL3 : 3 ≤ L := by omega
  refine ⟨{ L := L, hL := hL3, w := fun j => (G.gwalk a (i + j % L)).1,
            per := ?_, inj := ?_, adj := ?_ }, ?_⟩
  · intro j
    simp only [Nat.add_mod_right]
  · intro p q hp hq hpq
    rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at hpq
    have h2 := hinj (i + p) (by omega) (i + q) (by omega) hpq
    omega
  · intro j hj
    rw [Nat.mod_eq_of_lt hj]
    by_cases hjl : j + 1 < L
    · rw [Nat.mod_eq_of_lt hjl]
      have hl : G.Live a (i + j) := halive (i + j) (by omega)
      have hs1 := (gwalk_succ_of_live G a (i+j) hl).1
      have harg : i + (j + 1) = (i + j) + 1 := by omega
      rw [harg]
      exact G.symm _ hs1
    · have hj1 : j + 1 = L := by omega
      rw [hj1, Nat.mod_self, Nat.add_zero]
      have hij : i + j = n0 := by omega
      rw [hij]
      exact hiSn.2
  · exact Cycle.darts_subset _


/-- At every vertex, the number of darts of a cycle leaving it is even. -/
lemma Cycle.even_card_filter_fst (G : DartGraph α) (C : G.Cycle) (a : α) :
    Even ((C.darts.filter (fun e => e.1 = a)).card) := by
  classical
  set L := C.L with hL
  have hL3 : 3 ≤ L := C.hL
  set A := (Finset.range L).image (fun j => (C.w j, C.w (j+1))) with hA
  set B := (Finset.range L).image (fun j => (C.w (j+1), C.w j)) with hB
  have hdarts : C.darts = A ∪ B := rfl
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [hA, Finset.mem_image] at he
    rw [hB, Finset.mem_image] at he'
    obtain ⟨i, hi, hie⟩ := he
    obtain ⟨j, hj, hje⟩ := he'
    rw [Finset.mem_range] at hi hj
    have heq : (C.w i, C.w (i+1)) = (C.w (j+1), C.w j) := by rw [hie, hje]
    have h1 : C.w i = C.w (j+1) := congrArg Prod.fst heq
    have h2 : C.w (i+1) = C.w j := congrArg Prod.snd heq
    rcases lt_or_eq_of_le (show j + 1 ≤ L by omega) with hjl | hjl
    · have hij : i = j + 1 := C.inj i (j+1) hi hjl (by rw [h1])
      rw [hij] at h2
      rcases lt_or_eq_of_le (show j + 2 ≤ L by omega) with hj2 | hj2
      · exact absurd (C.inj (j+2) j hj2 hj h2) (by omega)
      · have h3 : C.w j = C.w 0 := by rw [← h2, hj2, C.w_period]
        have : j = 0 := C.inj j 0 hj (by omega) h3
        omega
    · have hi0 : i = 0 := by
        refine C.inj i 0 hi (by omega) ?_
        rw [h1, hjl, C.w_period]
      rw [hi0] at h2
      have : 1 = j := C.inj 1 j (by omega) hj h2
      omega
  have hAle : (A.filter (fun e => e.1 = a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro e he e' he'
    rw [hA, Finset.mem_filter, Finset.mem_image] at he he'
    obtain ⟨⟨i, hi, hie⟩, he1⟩ := he
    obtain ⟨⟨j, hj, hje⟩, he2⟩ := he'
    rw [Finset.mem_range] at hi hj
    have h1 : C.w i = a := (congrArg Prod.fst hie).trans he1
    have h2 : C.w j = a := (congrArg Prod.fst hje).trans he2
    have hij : i = j := C.inj i j hi hj (by rw [h1, h2])
    rw [← hie, ← hje, hij]
  have hBle : (B.filter (fun e => e.1 = a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro e he e' he'
    rw [hB, Finset.mem_filter, Finset.mem_image] at he he'
    obtain ⟨⟨i, hi, hie⟩, he1⟩ := he
    obtain ⟨⟨j, hj, hje⟩, he2⟩ := he'
    rw [Finset.mem_range] at hi hj
    have h1 : C.w (i+1) = a := (congrArg Prod.fst hie).trans he1
    have h2 : C.w (j+1) = a := (congrArg Prod.fst hje).trans he2
    have hij : i = j := by
      rcases lt_or_eq_of_le (show i+1 ≤ L by omega) with hiL | hiL
      · rcases lt_or_eq_of_le (show j+1 ≤ L by omega) with hjL | hjL
        · have h3 := C.inj (i+1) (j+1) hiL hjL (by rw [h1, h2])
          omega
        · rw [hjL, C.w_period] at h2
          have h3 := C.inj (i+1) 0 hiL (by omega) (by rw [h1, h2])
          omega
      · rcases lt_or_eq_of_le (show j+1 ≤ L by omega) with hjL | hjL
        · rw [hiL, C.w_period] at h1
          have h3 := C.inj (j+1) 0 hjL (by omega) (by rw [h2, h1])
          omega
        · omega
    rw [← hie, ← hje, hij]
  have hfwd : (A.filter (fun e => e.1 = a)).Nonempty →
      (B.filter (fun e => e.1 = a)).Nonempty := by
    rintro ⟨e, he⟩
    rw [hA, Finset.mem_filter, Finset.mem_image] at he
    obtain ⟨⟨i, hi, hie⟩, he1⟩ := he
    rw [Finset.mem_range] at hi
    have hia : C.w i = a := (congrArg Prod.fst hie).trans he1
    refine ⟨(C.w i, C.w (if i = 0 then L - 1 else i - 1)), ?_⟩
    rw [hB, Finset.mem_filter, Finset.mem_image]
    constructor
    · by_cases hi0 : i = 0
      · refine ⟨L - 1, by rw [Finset.mem_range]; omega, ?_⟩
        rw [hi0, show L - 1 + 1 = L by omega, C.w_period]
        simp
      · refine ⟨i - 1, by rw [Finset.mem_range]; omega, ?_⟩
        rw [show i - 1 + 1 = i by omega, if_neg hi0]
    · exact hia
  have hbwd : (B.filter (fun e => e.1 = a)).Nonempty →
      (A.filter (fun e => e.1 = a)).Nonempty := by
    rintro ⟨e, he⟩
    rw [hB, Finset.mem_filter, Finset.mem_image] at he
    obtain ⟨⟨i, hi, hie⟩, he1⟩ := he
    rw [Finset.mem_range] at hi
    have hia : C.w (i+1) = a := (congrArg Prod.fst hie).trans he1
    by_cases hiL : i + 1 < L
    · refine ⟨(C.w (i+1), C.w (i+2)), ?_⟩
      rw [hA, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨i+1, by rw [Finset.mem_range]; omega, rfl⟩, hia⟩
    · have hLL : i + 1 = L := by omega
      refine ⟨(C.w 0, C.w 1), ?_⟩
      rw [hA, Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨0, by rw [Finset.mem_range]; omega, rfl⟩, ?_⟩
      rw [← hia, hLL, C.w_period]
  have hd2 : Disjoint (A.filter (fun e => e.1 = a)) (B.filter (fun e => e.1 = a)) := by
    rw [Finset.disjoint_left] at hdisjAB ⊢
    intro e he he'
    exact hdisjAB (Finset.mem_of_mem_filter e he) (Finset.mem_of_mem_filter e he')
  have hcard : (C.darts.filter (fun e => e.1 = a)).card
      = (A.filter (fun e => e.1 = a)).card + (B.filter (fun e => e.1 = a)).card := by
    rw [hdarts, Finset.filter_union, Finset.card_union_of_disjoint hd2]
  rcases Finset.eq_empty_or_nonempty (C.darts.filter (fun e => e.1 = a)) with hemp | hne
  · rw [hemp]; exact ⟨0, rfl⟩
  · have hsum : (A.filter (fun e => e.1 = a)).card
        + (B.filter (fun e => e.1 = a)).card = 2 := by
      obtain ⟨e, he⟩ := hne
      have he' : e ∈ A.filter (fun e => e.1 = a) ∪ B.filter (fun e => e.1 = a) := by
        rw [← Finset.filter_union, ← hdarts]; exact he
      rcases Finset.mem_union.mp he' with hAe | hBe
      · have h1 : 1 ≤ (A.filter (fun e => e.1 = a)).card := Finset.card_pos.mpr ⟨e, hAe⟩
        have h2 : 1 ≤ (B.filter (fun e => e.1 = a)).card :=
          Finset.card_pos.mpr (hfwd ⟨e, hAe⟩)
        omega
      · have h1 : 1 ≤ (B.filter (fun e => e.1 = a)).card := Finset.card_pos.mpr ⟨e, hBe⟩
        have h2 : 1 ≤ (A.filter (fun e => e.1 = a)).card :=
          Finset.card_pos.mpr (hbwd ⟨e, hBe⟩)
        omega
    rw [hcard, hsum]
    exact ⟨1, rfl⟩

/-- Removing the darts of a cycle from an even graph leaves an even graph. -/
theorem exists_erase_cycle (G : DartGraph α) (heven : ∀ a, Even (G.deg a))
    (C : G.Cycle) (hC : C.darts ⊆ G.D) :
    ∃ G' : DartGraph α, G'.D = G.D \ C.darts ∧ (∀ a, Even (G'.deg a)) ∧
      G'.D.card < G.D.card := by
  classical
  refine ⟨⟨G.D \ C.darts, ?_, ?_⟩, rfl, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_sdiff] at he ⊢
    exact ⟨G.symm e he.1, fun hc => he.2 (C.swap_mem_darts hc)⟩
  · intro e he
    rw [Finset.mem_sdiff] at he
    exact G.noLoop e he.1
  · intro a
    show Even (((G.D \ C.darts).filter (fun e => e.1 = a)).card)
    have hsub : C.darts.filter (fun e => e.1 = a) ⊆ G.D.filter (fun e => e.1 = a) := by
      intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨hC he.1, he.2⟩
    have hiff : (G.D \ C.darts).filter (fun e => e.1 = a)
        = (G.D.filter (fun e => e.1 = a)) \ (C.darts.filter (fun e => e.1 = a)) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
    have hdeg : ((G.D \ C.darts).filter (fun e => e.1 = a)).card
        = (G.D.filter (fun e => e.1 = a)).card
          - (C.darts.filter (fun e => e.1 = a)).card := by
      rw [hiff, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    rw [hdeg]
    obtain ⟨k, hk⟩ := heven a
    have hk' : (G.D.filter (fun e => e.1 = a)).card = k + k := by
      rw [← deg_eq]; exact hk
    obtain ⟨m, hm⟩ := Cycle.even_card_filter_fst G C a
    have hle : (C.darts.filter (fun e => e.1 = a)).card
        ≤ (G.D.filter (fun e => e.1 = a)).card := Finset.card_le_card hsub
    exact ⟨k - m, by omega⟩
  · have hne : 0 < C.darts.card := by
      rw [Finset.card_pos]
      exact ⟨(C.w 0, C.w 1), C.mem_darts_forward (j := 0) (by have := C.hL; omega)⟩
    have hinter : C.darts ∩ G.D = C.darts := Finset.inter_eq_left.mpr hC
    have hle : C.darts.card ≤ G.D.card := Finset.card_le_card hC
    rw [Finset.card_sdiff, hinter]
    exact Nat.sub_lt (lt_of_lt_of_le hne hle) hne

/-- A simple closed walk, as raw data independent of the graph it lives in. -/
structure RawCycle (α : Type*) where
  L : ℕ
  hL : 3 ≤ L
  w : ℕ → α
  close : w L = w 0
  inj : ∀ i j, i < L → j < L → w i = w j → i = j

/-- `IsCycleDecomp G l` says that the dart set of `G` is the disjoint union of the oriented darts
of the cycles in the list `l`. -/
def IsCycleDecomp (G : DartGraph α) (l : List (RawCycle α)) : Prop :=
  l.Nodup ∧
  (∀ C ∈ l, ∀ j, j < C.L → (C.w j, C.w (j+1)) ∈ G.D) ∧
  (∀ C ∈ l, ∀ C' ∈ l, C ≠ C' → ∀ j j', j < C.L → j' < C'.L →
    (C.w j, C.w (j+1)) ≠ (C'.w j', C'.w (j'+1)) ∧
    (C.w j, C.w (j+1)) ≠ (C'.w (j'+1), C'.w j')) ∧
  (∀ e ∈ G.D, ∃ C ∈ l, ∃ j, j < C.L ∧ (e = (C.w j, C.w (j+1)) ∨ e = (C.w (j+1), C.w j)))

/-- A `G.Cycle` re-read as raw data. -/
def Cycle.toRaw {G : DartGraph α} (C : G.Cycle) : RawCycle α :=
  ⟨C.L, C.hL, C.w, C.w_period, C.inj⟩

lemma Cycle.toRaw_L {G : DartGraph α} (C : G.Cycle) : C.toRaw.L = C.L := rfl
lemma Cycle.toRaw_w {G : DartGraph α} (C : G.Cycle) (j : ℕ) : C.toRaw.w j = C.w j := rfl

lemma Cycle.toRaw_darts_forward {G : DartGraph α} (C : G.Cycle) {j : ℕ} (hj : j < C.L) :
    (C.toRaw.w j, C.toRaw.w (j+1)) ∈ C.darts := by
  rw [Cycle.toRaw_w C j, Cycle.toRaw_w C (j+1)]
  exact C.mem_darts_forward hj

lemma Cycle.toRaw_darts_backward {G : DartGraph α} (C : G.Cycle) {j : ℕ} (hj : j < C.L) :
    (C.toRaw.w (j+1), C.toRaw.w j) ∈ C.darts := by
  rw [Cycle.toRaw_w C j, Cycle.toRaw_w C (j+1)]
  exact C.swap_mem_darts (C.mem_darts_forward hj)

/-- The dart set of a finite even graph is the disjoint union of the darts of simple cycles. -/
theorem exists_raw_decomposition (G : DartGraph α) [Fintype α] (heven : ∀ a, Even (G.deg a)) :
    ∃ l : List (RawCycle α), IsCycleDecomp G l := by
  classical
  suffices h : ∀ n, ∀ (G : DartGraph α), G.D.card = n → (∀ a, Even (G.deg a)) →
      ∃ l : List (RawCycle α), IsCycleDecomp G l by
    exact h G.D.card G rfl heven
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G hcard heven
    by_cases hne : G.D.Nonempty
    · obtain ⟨C, hCsub⟩ := exists_cycle_of_even_deg G heven hne
      obtain ⟨G', hG'D, heven', hlt⟩ := exists_erase_cycle G heven C hCsub
      have hlt' : G'.D.card < n := by rw [← hcard]; exact hlt
      obtain ⟨l', hl'⟩ := ih G'.D.card hlt' G' rfl heven'
      obtain ⟨hnd', hmem', hdisj', hcov'⟩ := hl'
      have hLpos : 0 < C.L := by have := C.hL; omega
      have hsum : (C.toRaw.w 0, C.toRaw.w (0+1)) ∈ C.darts :=
        C.toRaw_darts_forward hLpos
      refine ⟨C.toRaw :: l', ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨?_, hnd'⟩
        intro hmem
        have h0 : 0 < C.toRaw.L := by rw [Cycle.toRaw_L C]; exact hLpos
        have hd := hmem' C.toRaw hmem 0 h0
        rw [hG'D, Finset.mem_sdiff] at hd
        exact hd.2 hsum
      · intro C' hC' j hj
        rcases List.mem_cons.mp hC' with rfl | hC'
        · have hjC : j < C.L := by rwa [Cycle.toRaw_L C] at hj
          rw [Cycle.toRaw_w C j, Cycle.toRaw_w C (j+1)]
          exact C.adj j hjC
        · exact (Finset.mem_sdiff.mp (hG'D ▸ hmem' C' hC' j hj)).1
      · intro C' hC' C'' hC'' hne' j j' hj hj'
        rcases List.mem_cons.mp hC' with rfl | hC'
        · rcases List.mem_cons.mp hC'' with rfl | hC''
          · exact absurd rfl hne'
          · have hjC : j < C.L := by rwa [Cycle.toRaw_L C] at hj
            have hd := Finset.mem_sdiff.mp (hG'D ▸ hmem' C'' hC'' j' hj')
            have hn := C.toRaw_darts_forward hjC
            have hn' := C.toRaw_darts_backward hjC
            have hd' : (C''.w (j'+1), C''.w j') ∉ C.darts := by
              intro hc
              exact hd.2 (by simpa using C.swap_mem_darts hc)
            constructor
            · intro heq; exact hd.2 (heq ▸ hn)
            · intro heq; exact hd' (heq ▸ hn)
        · rcases List.mem_cons.mp hC'' with rfl | hC''
          · have hj'' : j' < C.L := by rwa [Cycle.toRaw_L C] at hj'
            have hd := Finset.mem_sdiff.mp (hG'D ▸ hmem' C' hC' j hj)
            have hn := C.toRaw_darts_forward hj''
            have hn' := C.toRaw_darts_backward hj''
            constructor
            · intro heq; exact hd.2 (heq.symm ▸ hn)
            · intro heq; exact hd.2 (heq.symm ▸ hn')
          · exact hdisj' C' hC' C'' hC'' hne' j j' hj hj'
      · intro e he
        by_cases heC : e ∈ C.darts
        · have hdarts : C.darts = ((Finset.range C.L).image (fun j => (C.w j, C.w (j+1)))) ∪
              ((Finset.range C.L).image (fun j => (C.w (j+1), C.w j))) := rfl
          rw [hdarts, Finset.mem_union] at heC
          rcases heC with hA | hB
          · rw [Finset.mem_image] at hA
            obtain ⟨j, hj, hje⟩ := hA
            rw [Finset.mem_range] at hj
            refine ⟨C.toRaw, List.mem_cons_self, j, ?_, Or.inl ?_⟩
            · rwa [Cycle.toRaw_L C]
            · rw [Cycle.toRaw_w C j, Cycle.toRaw_w C (j+1)]; exact hje.symm
          · rw [Finset.mem_image] at hB
            obtain ⟨j, hj, hje⟩ := hB
            rw [Finset.mem_range] at hj
            refine ⟨C.toRaw, List.mem_cons_self, j, ?_, Or.inr ?_⟩
            · rwa [Cycle.toRaw_L C]
            · rw [Cycle.toRaw_w C j, Cycle.toRaw_w C (j+1)]; exact hje.symm
        · have he' : e ∈ G'.D := by rw [hG'D, Finset.mem_sdiff]; exact ⟨he, heC⟩
          obtain ⟨C', hC'l, j, hj, hej⟩ := hcov' e he'
          exact ⟨C', List.mem_cons_of_mem _ hC'l, j, hj, hej⟩
    · refine ⟨[], ?_, ?_, ?_, ?_⟩
      · exact List.nodup_nil
      · intro C hC; exact absurd hC (by simp)
      · intro C hC; exact absurd hC (by simp)
      · intro e he; exact absurd ⟨e, he⟩ hne

end DartGraph

end Work.HornSC.CellBoundaryJordan

namespace Work.HornSC.CellBoundaryJordan

open Set

private lemma hSeg_inj {u w : ℤ × ℤ} (h : hSeg u = hSeg w) : u = w := by
  have h1 : lpt u ∈ hSeg w := h ▸ lpt_mem_hSeg u
  have h2 : lpt (u.1 + 1, u.2) ∈ hSeg w := h ▸ lpt_add_one_mem_hSeg u
  simp only [mem_hSeg, lpt_re, lpt_im] at h1 h2
  have him : u.2 = w.2 := by
    have : ((u.2 : ℤ) : ℝ) = ((w.2 : ℤ) : ℝ) := h1.1
    exact_mod_cast this
  have hre : u.1 = w.1 := by
    have e1 : ((w.1 : ℤ) : ℝ) ≤ ((u.1 : ℤ) : ℝ) := h1.2.1
    have e2 : ((u.1 : ℤ) : ℝ) ≤ ((w.1 : ℤ) : ℝ) := by
      have h3 := h2.2.2
      push_cast at h3
      linarith
    have : ((u.1 : ℤ) : ℝ) = ((w.1 : ℤ) : ℝ) := le_antisymm e2 e1
    exact_mod_cast this
  exact Prod.ext hre him

private lemma vSeg_inj {u w : ℤ × ℤ} (h : vSeg u = vSeg w) : u = w := by
  have h1 : lpt u ∈ vSeg w := h ▸ lpt_mem_vSeg u
  have h2 : lpt (u.1, u.2 + 1) ∈ vSeg w := h ▸ lpt_add_one_mem_vSeg u
  simp only [mem_vSeg, lpt_re, lpt_im] at h1 h2
  have hre : u.1 = w.1 := by
    have : ((u.1 : ℤ) : ℝ) = ((w.1 : ℤ) : ℝ) := h1.1
    exact_mod_cast this
  have him : u.2 = w.2 := by
    have e1 : ((w.2 : ℤ) : ℝ) ≤ ((u.2 : ℤ) : ℝ) := h1.2.1
    have e2 : ((u.2 : ℤ) : ℝ) ≤ ((w.2 : ℤ) : ℝ) := by
      have h3 := h2.2.2
      push_cast at h3
      linarith
    have : ((u.2 : ℤ) : ℝ) = ((w.2 : ℤ) : ℝ) := le_antisymm e2 e1
    exact_mod_cast this
  exact Prod.ext hre him

private lemma hSeg_ne_vSeg (u w : ℤ × ℤ) : hSeg u ≠ vSeg w := by
  intro h
  have h1 : lpt u ∈ vSeg w := h ▸ lpt_mem_hSeg u
  have h2 : lpt (u.1 + 1, u.2) ∈ vSeg w := h ▸ lpt_add_one_mem_hSeg u
  simp only [mem_vSeg, lpt_re, lpt_im] at h1 h2
  have e1 : ((u.1 : ℤ) : ℝ) = (↑(u.1 + 1) : ℝ) := by rw [h1.1, h2.1]
  push_cast at e1
  linarith

lemma adjSeg_hSeg_or_vSeg {u v : ℤ × ℤ} (h : IsUnitAdj u v) :
    (u.2 = v.2 ∧ ∃ m : ℤ × ℤ, adjSeg u v = hSeg m ∧
        ((u = m ∧ v = (m.1 + 1, m.2)) ∨ (u = (m.1 + 1, m.2) ∧ v = m))) ∨
    (u.1 = v.1 ∧ ∃ m : ℤ × ℤ, adjSeg u v = vSeg m ∧
        ((u = m ∧ v = (m.1, m.2 + 1)) ∨ (u = (m.1, m.2 + 1) ∧ v = m))) := by
  rcases h with h | h | h | h
  · left
    refine ⟨by rw [h], u, ?_, Or.inl ⟨rfl, h⟩⟩
    rw [h]; exact adjSeg_east_wg u
  · left
    refine ⟨by rw [h], (u.1 - 1, u.2), ?_, Or.inr ⟨?_, ?_⟩⟩
    · rw [h]; exact Work.HornSC.CellBoundaryJordan.WallCycle.adjSeg_west u
    · ext <;> omega
    · rw [h]
  · right
    refine ⟨by rw [h], u, ?_, Or.inl ⟨rfl, h⟩⟩
    rw [h]; exact adjSeg_north_wg u
  · right
    refine ⟨by rw [h], (u.1, u.2 - 1), ?_, Or.inr ⟨?_, ?_⟩⟩
    · rw [h]; exact Work.HornSC.CellBoundaryJordan.WallCycle.adjSeg_south u
    · ext <;> omega
    · rw [h]

theorem adjSeg_determines_pair_of_unitAdj {u v u' v' : ℤ × ℤ}
    (h : IsUnitAdj u v) (h' : IsUnitAdj u' v') (heq : adjSeg u v = adjSeg u' v') :
    (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
  rcases adjSeg_hSeg_or_vSeg h with ⟨h2, m, hm, hshape⟩ | ⟨h1, m, hm, hshape⟩
  · rcases adjSeg_hSeg_or_vSeg h' with ⟨h2', m', hm', hshape'⟩ | ⟨h1', m', hm', hshape'⟩
    · have hmm : m = m' := hSeg_inj (by rw [← hm, heq, hm'])
      subst hmm
      rcases hshape with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> rcases hshape' with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
      · exact Or.inl ⟨by rw [hu, hu'], by rw [hv, hv']⟩
      · exact Or.inr ⟨by rw [hu, hv'], by rw [hv, hu']⟩
      · exact Or.inr ⟨by rw [hu, hv'], by rw [hv, hu']⟩
      · exact Or.inl ⟨by rw [hu, hu'], by rw [hv, hv']⟩
    · have hc : hSeg m = vSeg m' := by rw [← hm, heq, hm']
      exact absurd hc (hSeg_ne_vSeg m m')
  · rcases adjSeg_hSeg_or_vSeg h' with ⟨h2', m', hm', hshape'⟩ | ⟨h1', m', hm', hshape'⟩
    · have hc : vSeg m = hSeg m' := by rw [← hm, heq, hm']
      exact absurd hc.symm (hSeg_ne_vSeg m' m)
    · have hmm : m = m' := vSeg_inj (by rw [← hm, heq, hm'])
      subst hmm
      rcases hshape with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> rcases hshape' with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
      · exact Or.inl ⟨by rw [hu, hu'], by rw [hv, hv']⟩
      · exact Or.inr ⟨by rw [hu, hv'], by rw [hv, hu']⟩
      · exact Or.inr ⟨by rw [hu, hv'], by rw [hv, hu']⟩
      · exact Or.inl ⟨by rw [hu, hu'], by rw [hv, hv']⟩

end Work.HornSC.CellBoundaryJordan

namespace Work.PlanarSC.JC

open Set
open Work.HornSC.CellBoundaryJordan

/-- Every unit wall step of `A` is a wall in the `WallAdj` sense. -/
lemma wallAdj_of_mem_wallStepFinset {A : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)}
    (he : e ∈ Work.HornSC.CellBoundaryJordan.wallStepFinset A) :
    Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj A e.1 e.2 := by
  rcases Work.HornSC.CellBoundaryJordan.mem_wallStepFinset.mp he with
    ⟨u, h, rfl⟩ | ⟨u, h, rfl⟩
  · exact (Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_east A u).mpr h
  · exact (Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_north A u).mpr h

theorem cycle_decomposition_disjoint (A : Finset (ℤ × ℤ)) :
    ∃ (m : ℕ) (k : Fin m → ℕ) (u : Fin m → ℕ → ℤ × ℤ),
      (∀ i, 3 ≤ k i) ∧
      (∀ i, u i (k i) = u i 0) ∧
      (∀ i, ∀ j, j < k i → Work.HornSC.CellBoundaryJordan.IsUnitAdj (u i j) (u i (j + 1))) ∧
      (∀ i, ∀ j j', j < k i → j' < k i → u i j = u i j' → j = j') ∧
      (∀ i i', i ≠ i' → ∀ j j', j < k i → j' < k i' →
        Work.HornSC.CellBoundaryJordan.adjSeg (u i j) (u i (j + 1)) ≠
        Work.HornSC.CellBoundaryJordan.adjSeg (u i' j') (u i' (j' + 1))) ∧
      (⋃ i, ⋃ j ∈ {j : ℕ | j < k i},
        Work.HornSC.CellBoundaryJordan.adjSeg (u i j) (u i (j + 1))) =
        Work.HornSC.CellBoundaryJordan.wallSet A := by
  classical
  obtain ⟨l, hl⟩ := Work.HornSC.CellBoundaryJordan.DartGraph.exists_raw_decomposition
    (wallDartGraph A) (even_deg_wallDartGraph A)
  obtain ⟨hnd, hmem, hdisj, hcov⟩ := hl
  refine ⟨l.length, fun i => (l.get i).L, fun i j => ((l.get i).w j).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact (l.get i).hL
  · intro i; exact congrArg Subtype.val (l.get i).close
  · intro i j hj
    exact Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_unitAdj
      (mem_wallDartSet.mp (hmem _ (List.get_mem l i) j hj))
  · intro i j j' hj hj' h
    exact (l.get i).inj j j' hj hj' (Subtype.ext h)
  · intro i i' hne j j' hj hj' hseg
    have hget : l.get i ≠ l.get i' := by
      intro hh
      exact hne ((List.Nodup.get_inj_iff hnd).mp hh)
    have h1 := Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_unitAdj
      (mem_wallDartSet.mp (hmem _ (List.get_mem l i) j hj))
    have h2 := Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_unitAdj
      (mem_wallDartSet.mp (hmem _ (List.get_mem l i') j' hj'))
    have hpair := hdisj _ (List.get_mem l i) _ (List.get_mem l i') hget j j' hj hj'
    rcases Work.HornSC.CellBoundaryJordan.adjSeg_determines_pair_of_unitAdj h1 h2 hseg with
      ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact hpair.1 (Prod.ext (Subtype.ext e1) (Subtype.ext e2))
    · exact hpair.2 (Prod.ext (Subtype.ext e1) (Subtype.ext e2))
  · apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzi
      obtain ⟨hj, hzw⟩ := Set.mem_iUnion.mp hzj
      exact Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_adjSeg_subset_wallSet
        (mem_wallDartSet.mp (hmem (l.get i) (List.get_mem l i) j hj)) hzw
    · intro z hz
      obtain ⟨e, he, hze⟩ :=
        Work.HornSC.CellBoundaryJordan.wallSet_subset_wallStepFinset A hz
      have hwadj := wallAdj_of_mem_wallStepFinset he
      have hzw : z ∈ Work.HornSC.CellBoundaryJordan.adjSeg e.1 e.2 := by
        rwa [Work.HornSC.CellBoundaryJordan.adjSeg_stepSeg_of_mem_wallStepFinset he]
      have h1 : e.1 ∈ Work.HornSC.CellBoundaryJordan.WallCycle.wallVerts A :=
        Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_fst_mem_wallVerts hwadj
      have h2 : e.2 ∈ Work.HornSC.CellBoundaryJordan.WallCycle.wallVerts A :=
        Work.HornSC.CellBoundaryJordan.WallCycle.WallAdj_snd_mem_wallVerts hwadj
      have hd : (⟨e.1, h1⟩, ⟨e.2, h2⟩) ∈ (wallDartGraph A).D := mem_wallDartSet.mpr hwadj
      obtain ⟨C, hCl, j, hj, hcase⟩ := hcov _ hd
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hCl
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
      · show j < (l.get i).L
        rw [hi]
        exact hj
      · rcases hcase with hcase | hcase
        · have hx : e.1 = ((l.get i).w j).1 := by
            have h3 := congrArg (fun p : WallV A × WallV A => (p.1 : ℤ × ℤ)) hcase
            rw [hi]
            exact h3
          have hy : e.2 = ((l.get i).w (j+1)).1 := by
            have h3 := congrArg (fun p : WallV A × WallV A => (p.2 : ℤ × ℤ)) hcase
            rw [hi]
            exact h3
          rwa [hx, hy] at hzw
        · have hx : e.1 = ((l.get i).w (j+1)).1 := by
            have h3 := congrArg (fun p : WallV A × WallV A => (p.1 : ℤ × ℤ)) hcase
            rw [hi]
            exact h3
          have hy : e.2 = ((l.get i).w j).1 := by
            have h3 := congrArg (fun p : WallV A × WallV A => (p.2 : ℤ × ℤ)) hcase
            rw [hi]
            exact h3
          rw [hx, hy] at hzw
          rwa [Work.HornSC.CellBoundaryJordan.WallCycle.adjSeg_symm] at hzw

end Work.PlanarSC.JC
