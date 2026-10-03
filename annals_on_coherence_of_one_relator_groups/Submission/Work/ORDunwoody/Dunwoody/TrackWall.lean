/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The regPair of a track, the incidence relation, and the dual graph

`Dunwoody/Track.lean` defines the tracks (the components of the chord graph on the pattern points)
and `Dunwoody/label_of_chord` / `Dunwoody/midPair_of_chord` show that a chord joins two pattern
points of the same *label* and of the same *pair of adjacent regions*.  Propagating along a track
gives:

* `Track.label` — the edge of `T` all cells of the track map onto (in `Dunwoody/Track.lean`);
* `Track.regPair` — the pair `s(Region.mk (src m), Region.mk (tgt m))` of regions adjacent to the
  track.  This is the geometric input that a track is incident with exactly two regions.

The incidence relation is then simply

    Inc τ R R'  :=  τ.regPair = s(R, R')

and the fact that a wall is incident with at most two regions — `few_inc`, in the form
`pair_eq_of_inc` — is immediate.  The **dual graph** `dualGraph` has the regions as vertices, two
regions being adjacent when some track is incident with the pair.

The remaining content of Dunwoody's construction is that `dualGraph` is a *tree*: it is connected
(a path in `graph` crosses finitely many pattern points, each giving an edge of the dual), and it
is acyclic.  Acyclicity is the hard part; see `DESIGN_N13.md` §8.5–8.8 for the discussion of the
two attacks (colour-based side function: fails; counting side function: needs the parity of the
passages, i.e. `H₁(Λ'';Z/2) = 0`).
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Track
import Submission.Work.ORDunwoody.midPair_of_chord
import Submission.Work.ORDunwoody.regionRel_smul

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley
open scoped Sym2

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- All the pattern points of a track have the same pair of adjacent regions. -/
theorem midPair_eq_of_reachable {m m' : MidV D} (h : (chordGraph D).Reachable m m') :
    midPair m = midPair m' := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
      refine ih.trans ?_
      obtain ⟨r, c, p, q, hpq, hb, hc⟩ := hbc.1
      rcases hpq with hpq | hpq
      · exact midPair_of_chord r c hpq hb hc
      · exact (midPair_of_chord r c hpq hc hb).symm

/-- **The pair of regions adjacent to a track.** -/
noncomputable def Track.regPair (τ : Track D) : Sym2 (Region D) :=
  Quot.lift (fun m : MidV D => midPair m) (fun _ _ h => midPair_eq_of_reachable h) τ

@[simp] theorem Track.regPair_trackOf (m : MidV D) : (trackOf m).regPair = midPair m := rfl

/-- **Incidence of a track and a pair of regions.** -/
def Track.Inc (τ : Track D) (R R' : Region D) : Prop := τ.regPair = s(R, R')

theorem Track.inc_symm {τ : Track D} {R R' : Region D} (h : τ.Inc R R') : τ.Inc R' R := by
  unfold Track.Inc at h ⊢
  rw [h, Sym2.eq_swap]

/-- **A track is incident with at most one pair of regions** (`few_inc`). -/
theorem pair_eq_of_inc {τ : Track D} {a b a' b' : Region D}
    (h : τ.Inc a b) (h' : τ.Inc a' b') : s(a, b) = s(a', b') := by
  unfold Track.Inc at h h'
  exact h.symm.trans h'

/-- **The dual graph**: regions for vertices, two regions adjacent when a track is incident with
the pair. -/
def dualGraph (D : GeoData T t₀ P) : SimpleGraph (Region D) where
  Adj R R' := R ≠ R' ∧ ∃ τ : Track D, τ.Inc R R'
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.choose, Track.inc_symm h.2.choose_spec⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem dualGraph_adj_iff {R R' : Region D} :
    (dualGraph D).Adj R R' ↔ R ≠ R' ∧ ∃ τ : Track D, τ.Inc R R' := Iff.rfl

/-! ## The action of `G` on the regions

`RegionRel` is `G`-invariant (`Work.ORDunwoody.regionRel_smul`), hence so is the equivalence
relation it generates, and the action descends to the quotient. -/

theorem regionRel_eqvGen_smul (g : G) {u w : BaseV D}
    (h : Relation.EqvGen (RegionRel D) u w) :
    Relation.EqvGen (RegionRel D) (g • u) (g • w) := by
  induction h with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (Work.ORDunwoody.regionRel_smul g hab)
  | refl => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

noncomputable instance instMulActionRegion : MulAction G (Region D) where
  smul g := Quotient.map (fun u : BaseV D => g • u)
    (fun _ _ h => regionRel_eqvGen_smul g h)
  one_smul R := by
    refine Quotient.inductionOn R (fun u => ?_)
    exact congrArg (Quotient.mk _) (one_smul G u)
  mul_smul g h R := by
    refine Quotient.inductionOn R (fun u => ?_)
    exact congrArg (Quotient.mk _) (mul_smul g h u)

@[simp] theorem Region.mk_smul (g : G) (u : BaseV D) :
    g • (Region.mk D u) = Region.mk D (g • u) := rfl

/-! ## Equivariance of the track data -/

@[simp] theorem MidV.src_smul (g : G) (m : MidV D) : (g • m).src = g • m.src := by
  simp only [MidV.src]
  rw [show (g • m).cell = g • m.cell from rfl, Cell.src_smul]

@[simp] theorem MidV.tgt_smul (g : G) (m : MidV D) : (g • m).tgt = g • m.tgt := by
  simp only [MidV.tgt]
  rw [show (g • m).cell = g • m.cell from rfl, Cell.tgt_smul]

theorem midPair_smul (g : G) (m : MidV D) :
    midPair (g • m) = Sym2.map (fun R : Region D => g • R) (midPair m) := by
  simp only [midPair, MidV.src_smul, MidV.tgt_smul, Region.mk_smul, Sym2.map_mk]

/-- The chord relation is `G`-invariant. -/
theorem ChordAdj_smul (g : G) {m m' : MidV D} (h : ChordAdj m m') :
    ChordAdj (g • m) (g • m') := by
  obtain ⟨r, c, p, q, hpq, hm, hm'⟩ := h
  refine ⟨r, g * c, p, q, ?_, ?_, ?_⟩
  · rw [Work.ORDunwoody.faceVisits_smul, Work.ORDunwoody.chords_smul]
    exact hpq
  · rw [Work.ORDunwoody.faceVisits_smul, List.getElem?_map, hm]
    rfl
  · rw [Work.ORDunwoody.faceVisits_smul, List.getElem?_map, hm']
    rfl

theorem chordGraph_smul_adj (g : G) {m m' : MidV D} (h : (chordGraph D).Adj m m') :
    (chordGraph D).Adj (g • m) (g • m') :=
  ⟨ChordAdj_smul g h.1, fun hc => h.2 (MulAction.injective g hc)⟩

theorem reachable_smul (g : G) {m m' : MidV D} (h : (chordGraph D).Reachable m m') :
    (chordGraph D).Reachable (g • m) (g • m') := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (chordGraph_smul_adj g hbc)

/-- Translation of a track by a group element. -/
noncomputable def trackSmul (g : G) : Track D → Track D :=
  Quot.map (fun m : MidV D => g • m) (fun _ _ h => reachable_smul g h)

noncomputable instance instMulActionTrack : MulAction G (Track D) where
  smul := trackSmul
  one_smul τ := by
    refine Quot.ind (β := fun q : Track D => trackSmul 1 q = q) (fun m => ?_) τ
    exact congrArg (Quot.mk (chordGraph D).Reachable) (one_smul G m)
  mul_smul g h τ := by
    refine Quot.ind (β := fun q : Track D =>
      trackSmul (g * h) q = trackSmul g (trackSmul h q)) (fun m => ?_) τ
    exact congrArg (Quot.mk (chordGraph D).Reachable) (mul_smul g h m)

@[simp] theorem trackOf_smul (g : G) (m : MidV D) : trackOf (g • m) = g • trackOf m := rfl

theorem Track.label_smul (g : G) (τ : Track D) :
    (g • τ).label = Sym2.map (fun v : V => g • v) τ.label := by
  refine Quot.ind (β := fun q : Track D => (g • q).label = Sym2.map (fun v : V => g • v) q.label)
    (fun m => ?_) τ
  change (g • trackOf m).label = Sym2.map (fun v : V => g • v) (trackOf m).label
  rw [← trackOf_smul, Track.label_trackOf, Track.label_trackOf]
  exact Work.ORDunwoody.label_smul g m

theorem Track.regPair_smul (g : G) (τ : Track D) :
    (g • τ).regPair = Sym2.map (fun R : Region D => g • R) τ.regPair := by
  refine Quot.ind
    (β := fun q : Track D => (g • q).regPair = Sym2.map (fun R : Region D => g • R) q.regPair)
    (fun m => ?_) τ
  change (g • trackOf m).regPair = Sym2.map (fun R : Region D => g • R) (trackOf m).regPair
  rw [← trackOf_smul, Track.regPair_trackOf, Track.regPair_trackOf]
  exact midPair_smul g m

/-- The dual graph is invariant under the action of `G`. -/
theorem dualGraph_smul_adj (g : G) {R R' : Region D} (h : (dualGraph D).Adj R R') :
    (dualGraph D).Adj (g • R) (g • R') := by
  obtain ⟨hne, τ, hτ⟩ := h
  refine ⟨fun hc => hne (by simpa using congrArg (fun S : Region D => g⁻¹ • S) hc), g • τ, ?_⟩
  unfold Track.Inc at hτ ⊢
  rw [Track.regPair_smul, hτ, Sym2.map_mk]

end Work.ORDunwoody.Dunwoody
