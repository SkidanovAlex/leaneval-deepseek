import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Region
import Submission.Work.ORDunwoody.faceWalk_smul

set_option linter.unusedSectionVars false

namespace Work.ORDunwoody

open Cayley Dunwoody

universe u

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : Cayley.GeoData T t₀ P}

/-! ## Equivariance of the arc data

`arcIndex` records, for each old vertex of a walk, its position among the pattern points of the
walk.  Applying `g` to every vertex of the walk shifts the old vertices by `g` and leaves the
indices unchanged. -/

theorem arcIndexAux_map_smul (g : G) (l : List (Vertex D)) (k : ℕ) :
    arcIndexAux (l.map (fun v => g • v)) k =
      (arcIndexAux l k).map (fun p => (g • p.1, p.2)) := by
  induction l generalizing k with
  | nil => simp
  | cons v rest ih =>
      cases v with
      | inl u =>
          simp only [List.map_cons, vertex_smul_inl, arcIndexAux_inl]
          rw [ih k]
      | inr m =>
          simp only [List.map_cons, vertex_smul_inr, arcIndexAux_inr]
          rw [ih (k+1)]

theorem arcIndex_map_smul (g : G) (l : List (Vertex D)) :
    arcIndex (l.map (fun v => g • v)) =
      (arcIndex l).map (fun p => (g • p.1, p.2)) :=
  arcIndexAux_map_smul g l 0

/-! ## Equivariance of the visits of a walk

`visitTriples` extracts the pattern points of a walk together with the old vertices flanking
them.  Since the `G`-action preserves whether a vertex is old or a pattern point, it commutes
with `visitTriples`; the recursion of `visitTriples` looks three vertices ahead, so the
induction is on the length of the walk. -/

theorem visitTriplesAux_map_smul (g : G) (u : BaseV D) (l : List (Vertex D)) :
    visitTriplesAux (g • u) (l.map (fun v => g • v)) =
      (visitTriplesAux u l).map (fun t => (g • t.1, g • t.2.1, g • t.2.2)) := by
  have key : ∀ n, ∀ (u : BaseV D) (l : List (Vertex D)), l.length = n →
      visitTriplesAux (g • u) (l.map (fun v => g • v)) =
        (visitTriplesAux u l).map (fun t => (g • t.1, g • t.2.1, g • t.2.2)) := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih u l hl
    match l with
    | [] => simp
    | v :: rest =>
        cases v with
        | inl w =>
            have hlt : rest.length < n := by simp only [List.length_cons] at hl; omega
            have H := ih rest.length hlt w rest rfl
            simp only [List.map_cons, vertex_smul_inl, visitTriplesAux_inl, H]
        | inr m =>
            cases rest with
            | nil => simp
            | cons v' rest' =>
                cases v' with
                | inl w =>
                    have hlt : (Sum.inl w :: rest').length < n := by
                      simp only [List.length_cons] at hl ⊢; omega
                    have H := ih (Sum.inl w :: rest').length hlt w (Sum.inl w :: rest') rfl
                    simp only [List.map_cons, vertex_smul_inl, vertex_smul_inr,
                      visitTriplesAux_inl] at H
                    simp only [List.map_cons, vertex_smul_inl, vertex_smul_inr,
                      visitTriplesAux_inr, visitTriplesAux_inl, H]
                | inr m' =>
                    have hlt : (Sum.inr m' :: rest').length < n := by
                      simp only [List.length_cons] at hl ⊢; omega
                    have H := ih (Sum.inr m' :: rest').length hlt u (Sum.inr m' :: rest') rfl
                    simp only [List.map_cons, vertex_smul_inl, vertex_smul_inr,
                      visitTriplesAux_inr_inr] at H
                    simp only [List.map_cons, vertex_smul_inl, vertex_smul_inr,
                      visitTriplesAux_inr, visitTriplesAux_inr_inr, H]
  exact key l.length u l rfl

theorem visitTriples_map_smul (g : G) (l : List (Vertex D)) :
    visitTriples (l.map (fun v => g • v)) =
      (visitTriples l).map (fun t => (g • t.1, g • t.2.1, g • t.2.2)) := by
  induction l with
  | nil => simp
  | cons v rest ih =>
      cases v with
      | inl u =>
          simp only [List.map_cons, vertex_smul_inl, visitTriples_inl]
          exact visitTriplesAux_map_smul g u rest
      | inr m =>
          simp only [List.map_cons, vertex_smul_inr, visitTriples_inr]
          exact ih

/-! ## Equivariance of the labels, the fibres and the chords

The label of a pattern point is the (unordered) edge of `T` that its cell maps onto; applying
`g` replaces it by the `g`-translate of that edge.  The action on `V` is bijective, hence so is
the induced action on `Sym2 V`, and therefore the *partition* of the visits into fibres is
unchanged — which is all that `chords` and `pieceRel` see. -/

theorem label_smul (g : G) (p : MidV D) :
    (g • p).label = Sym2.map (fun v => g • v) p.label := by
  simp only [MidV.label, midV_smul, Sym2.map_mk]
  simp [mul_smul]

theorem smap_inj (g : G) : Function.Injective (Sym2.map (fun v : V => g • v)) :=
  Sym2.map.injective (MulAction.injective g)

theorem positionsOfLabelAux_smul (g : G) (l : List (MidV D)) (e : Sym2 V) (k : ℕ) :
    positionsOfLabelAux (l.map (fun p => g • p)) (Sym2.map (fun v => g • v) e) k =
      positionsOfLabelAux l e k := by
  induction l generalizing k with
  | nil => rfl
  | cons p rest ih =>
      have hiff : ((g • p).label = Sym2.map (fun v => g • v) e) ↔ (p.label = e) := by
        rw [label_smul]
        exact (smap_inj g).eq_iff
      simp only [List.map_cons, positionsOfLabelAux]
      rw [ih (k+1)]
      by_cases h : p.label = e
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]

theorem positionsOfLabel_smul (g : G) (l : List (MidV D)) (e : Sym2 V) :
    positionsOfLabel (l.map (fun p => g • p)) (Sym2.map (fun v => g • v) e) =
      positionsOfLabel l e :=
  positionsOfLabelAux_smul g l e 0

theorem labelSet_smul (g : G) (l : List (MidV D)) :
    labelSet (l.map (fun p => g • p)) = (labelSet l).map (Sym2.map (fun v => g • v)) := by
  unfold labelSet
  rw [List.map_map]
  have hfun : (MidV.label (D := D)) ∘ (fun p => g • p) =
      (Sym2.map (fun v => g • v)) ∘ (MidV.label (D := D)) := by
    funext p; exact label_smul g p
  rw [hfun, ← List.map_map]
  rw [List.dedup_map_of_injective (smap_inj g)]

theorem chords_smul (g : G) (l : List (MidV D)) :
    chords (l.map (fun p => g • p)) = chords l := by
  unfold chords
  rw [labelSet_smul, List.flatMap_map]
  refine List.flatMap_congr (fun e _ => ?_)
  rw [positionsOfLabel_smul]

theorem chordRel_smul (g : G) (l : List (MidV D)) :
    chordRel (l.map (fun p => g • p)) = chordRel l := by
  funext i j
  unfold chordRel
  rw [chords_smul]

theorem pieceRel_smul (g : G) (l : List (MidV D)) (i j : ℕ) :
    pieceRel (l.map (fun p => g • p)) i j ↔ pieceRel l i j := by
  unfold pieceRel
  rw [chordRel_smul]

/-! ## The face data of a translated face -/

theorem faceTriples_smul (g c : G) (w : List (Fin P.n × Bool)) :
    faceTriples D (g * c) w =
      (faceTriples D c w).map (fun t => (g • t.1, g • t.2.1, g • t.2.2)) := by
  unfold faceTriples
  rw [faceWalk_smul]
  rw [visitTriples_map_smul]

theorem faceVisits_smul (g c : G) (w : List (Fin P.n × Bool)) :
    faceVisits D (g * c) w = (faceVisits D c w).map (fun v => g • v) := by
  unfold faceVisits
  rw [faceTriples_smul, List.map_map, List.map_map]
  rfl

theorem regionRel_smul {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V] {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (g : G) {u w : Work.ORDunwoody.Dunwoody.BaseV D} (h : Work.ORDunwoody.Dunwoody.RegionRel D u w) : Work.ORDunwoody.Dunwoody.RegionRel D (g • u) (g • w) := by
  rcases h with ⟨a, j, hL, h1⟩ | ⟨r, c, i, j, hu, hw, hp⟩
  · refine Or.inl ⟨g * a, j, hL, ?_⟩
    rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [h1, h2]
      simp [baseV_smul, mul_assoc]
    · right
      rw [h1, h2]
      simp [baseV_smul, mul_assoc]
  · refine Or.inr ⟨r, g * c, i, j, ?_, ?_, ?_⟩
    · rw [faceWalk_smul, arcIndex_map_smul]
      exact List.mem_map.mpr ⟨(u, i), hu, rfl⟩
    · rw [faceWalk_smul, arcIndex_map_smul]
      exact List.mem_map.mpr ⟨(w, j), hw, rfl⟩
    · rw [faceVisits_smul]
      exact (pieceRel_smul g (faceVisits D c (FreeGroup.toWord r.1)) i j).mpr hp

end Work.ORDunwoody
