/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The last mile: from the counting side function to `dunwoodyResolution`

`Dunwoody/RegionAlpha.lean` proves (W1) (`alpha τ` vanishes on closed walks) and (W2) (the
counting side function `sideV τ` is constant on the classes of `RegionRel`, with the descent
`sideOfRegion τ : Region D → ZMod 2` and the two wall-system axioms
`resSideOfRegion_ne_of_inc`, `resSideOfRegion_eq_of_inc_of_ne`).

This file assembles the resolution tree from that data:

* `resSystem : WallSystem.System (Track D) (Region D)` — walls are the tracks, regions are the
  classes of `RegionRel`, incidence is `Track.Inc`, and the side function is `sideOfRegion`;
  `few_inc` is the fact that a track is incident with at most two regions.
* `resRegPair_injective`: **a track is determined by the pair of regions it separates.**  This is
  not formal: if `τ ≠ τ'` had the same pair `{R,R'}`, then `resSideOfRegion_ne_of_inc` for `τ` would
  say the two sides of `τ` differ while `resSideOfRegion_eq_of_inc_of_ne` for `τ'` would say they
  agree.  It is what makes the stabiliser of an *edge* of the dual tree accessible.
* `resDualGT : GTree G (Region D)`, the dual tree (regions for vertices, tracks for edges),
  derived from `System.isTree` and `dualGraph_connected`;
* `resDualGT_isCocompact` (finitely many orbits of regions and of oriented edges),
* `resDualGT_hasFGVertexStab` and `resDualGT_hasFGEdgeStab` (the stabiliser of an edge is the
  stabiliser of its track intersected with that of one of its regions, of index at most two),
* `resDualGT_dominates`, through the colour `colourRegion : Region D → V`;
* `resDunwoodyResolution`, the conclusion of GL17 Proposition 2.17 (constant case).
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.ResRegionSide
import Submission.Work.ORDunwoody.Dunwoody.Colour
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORDunwoody.WallSystem.Assembly
import Submission.Work.ORDunwoody.finite_orbits_region
import Submission.Work.ORDunwoody.dualGraph_connected
import Submission.Work.ORDunwoody.fg_stabilizer_region
import Submission.Work.ORDunwoody.fg_stabilizer_track

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

/-! ## Incidence and the pair of regions of an incidence -/

/-- **A track is never incident with a diagonal pair of regions**: the two regions on the two
sides of an incidence have opposite sides. -/
theorem Track.inc_ne {τ : Track D} {R R' : Region D} (h : τ.Inc R R') : R ≠ R' := fun hEq =>
  resSideOfRegion_ne_of_inc h (by rw [hEq])

/-- **The two regions of an incidence of a track are the ends of the cell of any of its pattern
points.** -/
theorem inc_pair_eq {τ : Track D} {m : MidV D} (hm : trackOf m = τ) {a b : Region D}
    (h : τ.Inc a b) :
    (a = Region.mk D (MidV.src m) ∧ b = Region.mk D (MidV.tgt m)) ∨
      (a = Region.mk D (MidV.tgt m) ∧ b = Region.mk D (MidV.src m)) := by
  have hreg : s(a, b) = s(Region.mk D (MidV.src m), Region.mk D (MidV.tgt m)) := by
    rw [show s(a, b) = τ.regPair from h.symm, ← hm]
    exact Track.regPair_trackOf m
  exact Sym2.eq_iff.mp hreg

/-! ## The wall system of the tracks -/

/-- **The wall system of the Dunwoody pattern**: the walls are the tracks, the regions are the
classes of `RegionRel`, a track is incident with the two regions of its pattern points, and the
side function is the descent `sideOfRegion` of the counting side function. -/
noncomputable def resSystem : Work.ORDunwoody.WallSystem.System (Track D) (Region D) where
  Inc := Track.Inc
  inc_symm := by
    intro w a b h
    exact Track.inc_symm h
  side := resSideOfRegion
  side_ne := by
    intro τ R R' h
    exact resSideOfRegion_ne_of_inc h
  side_other := by
    intro τ R R' h τ' hne
    exact resSideOfRegion_eq_of_inc_of_ne h (Ne.symm hne)
  few_inc := by
    intro τ a b c ⟨b', hb'⟩ ⟨c', hc'⟩ ⟨d', hd'⟩
    obtain ⟨m, hm⟩ := resExists_track_point τ
    have ha := inc_pair_eq (τ := τ) hm hb'
    have hb := inc_pair_eq (τ := τ) hm hc'
    have hc := inc_pair_eq (τ := τ) hm hd'
    rcases ha with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rcases hb with ⟨hb, -⟩ | ⟨hb, -⟩ <;>
      rcases hc with ⟨hc, -⟩ | ⟨hc, -⟩
    all_goals first
      | exact Or.inl (ha.trans hb.symm)
      | exact Or.inr (Or.inl (hb.trans hc.symm))
      | exact Or.inr (Or.inr (ha.trans hc.symm))

/-! ## A track is determined by its pair of regions -/

/-- **A track is determined by the pair of regions it separates.**  If two distinct tracks had the
same pair `{R,R'}` of adjacent regions, then the side function of the first would *differ* on the
two regions (`resSideOfRegion_ne_of_inc`) while that of the second would *agree*
(`resSideOfRegion_eq_of_inc_of_ne`). -/
theorem resRegPair_injective {τ τ' : Track D} (h : τ.regPair = τ'.regPair) : τ = τ' := by
  by_contra hne
  obtain ⟨m, hm⟩ := resExists_track_point τ
  have hinc : τ.Inc (Region.mk D (MidV.src m)) (Region.mk D (MidV.tgt m)) := by
    unfold Track.Inc
    rw [← hm]
    rfl
  have hinc' : τ'.Inc (Region.mk D (MidV.src m)) (Region.mk D (MidV.tgt m)) := by
    unfold Track.Inc
    rw [← h, ← hm]
    rfl
  exact resSideOfRegion_ne_of_inc hinc
    (resSideOfRegion_eq_of_inc_of_ne (τ := τ') (τ' := τ) hinc' (Ne.symm hne))

/-! ## The dual tree -/

/-- The incidence relation of the tracks is `G`-equivariant. -/
theorem resInc_smul (g : G) {τ : Track D} {R R' : Region D} (h : τ.Inc R R') :
    (g • τ).Inc (g • R) (g • R') := by
  unfold Track.Inc at h ⊢
  rw [Track.regPair_smul, h, Sym2.map_mk]

/-- The graph of the wall system of the tracks is the dual graph. -/
theorem resSystem_graph_eq_dualGraph : (resSystem (D := D)).graph = dualGraph D := by
  refine SimpleGraph.ext (funext (fun R => funext (fun R' => propext ?_)))
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨Track.inc_ne hτ, ⟨τ, hτ⟩⟩
  · rintro ⟨-, h⟩
    exact h

/-- The graph of the wall system of the tracks is connected. -/
theorem resSystem_connected : (resSystem (D := D)).graph.Connected := by
  rw [resSystem_graph_eq_dualGraph]
  exact dualGraph_connected D

/-- **The dual tree of the Dunwoody pattern**: the regions for vertices, the tracks for edges. -/
noncomputable def resDualGT : GTree G (Region D) where
  graph := (resSystem (D := D)).graph
  isTree := (resSystem (D := D)).isTree resSystem_connected
  smul_adj := by
    intro g u v huv
    obtain ⟨τ, hτ⟩ := huv
    exact ⟨g • τ, resInc_smul g hτ⟩

theorem resDualGT_adj_iff {R R' : Region D} :
    (resDualGT (D := D)).Adj R R' ↔ ∃ τ : Track D, τ.Inc R R' := Iff.rfl

/-- The label of a pattern point is an edge of `T`. -/
theorem MidV.label_mem_edgeSet (m : MidV D) : m.label ∈ T.graph.edgeSet := by
  have h1 := Cell.label_mem_edgeSet (D := D) (MidV.cell m)
  rwa [Cell.label_eq_MidV_label] at h1

/-- **The dual tree dominates `T`**, through the colour of a region. -/
theorem resDualGT_dominates : Dominates (resDualGT (D := D)) T :=
  ⟨{ toFun := colourRegion D
     map_smul' := fun g R => colourRegion_smul (D := D) g R
     map_adj' := by
       intro a b hab
       obtain ⟨τ, hτ⟩ := hab
       obtain ⟨m, hm⟩ := resExists_track_point τ
       have hcell : s(colourRegion D a, colourRegion D b) = MidV.label m := by
         rcases inc_pair_eq hm hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
         · exact colourRegion_pair m
         · rw [Sym2.eq_swap]
           exact colourRegion_pair m
       exact Or.inl ((T.graph.mem_edgeSet).mp (by
         rw [hcell]
         exact MidV.label_mem_edgeSet m)) }⟩

/-- The two orientations of the edge of the dual tree through a pattern point. -/
noncomputable def dualEdgeOf (m : MidV D) (b : Bool) : GTree.AdjPair (resDualGT (D := D)) :=
  if b then
    ⟨(Region.mk D (MidV.src m), Region.mk D (MidV.tgt m)),
      ⟨trackOf m, rfl⟩⟩
  else
    ⟨(Region.mk D (MidV.tgt m), Region.mk D (MidV.src m)),
      ⟨trackOf m, Track.inc_symm rfl⟩⟩

/-- The two orientations of a dual edge are equivariant. -/
theorem dualEdgeOf_smul (g : G) (m : MidV D) (b : Bool) :
    dualEdgeOf (D := D) (g • m) b = g • dualEdgeOf (D := D) m b := by
  cases b with
  | false =>
      apply Subtype.ext
      show (Region.mk D (MidV.tgt (g • m)), Region.mk D (MidV.src (g • m))) =
        g • (Region.mk D (MidV.tgt m), Region.mk D (MidV.src m))
      simp only [Prod.smul_mk, MidV.src_smul, MidV.tgt_smul, Region.mk_smul]
  | true =>
      apply Subtype.ext
      show (Region.mk D (MidV.src (g • m)), Region.mk D (MidV.tgt (g • m))) =
        g • (Region.mk D (MidV.src m), Region.mk D (MidV.tgt m))
      simp only [Prod.smul_mk, MidV.src_smul, MidV.tgt_smul, Region.mk_smul]

/-- Every oriented edge of the dual tree is one of the two orientations of the edge through some
pattern point. -/
theorem dualEdgeOf_surjective (p : GTree.AdjPair (resDualGT (D := D))) :
    ∃ (m : MidV D) (b : Bool), dualEdgeOf (D := D) m b = p := by
  obtain ⟨⟨R, R'⟩, hp⟩ := p
  obtain ⟨τ, hτ⟩ := hp
  obtain ⟨m, hm⟩ := resExists_track_point τ
  rcases inc_pair_eq hm hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨m, true, ?_⟩
    apply Subtype.ext
    simp only [dualEdgeOf, if_true]
    exact Prod.ext h1.symm h2.symm
  · refine ⟨m, false, ?_⟩
    apply Subtype.ext
    simp only [dualEdgeOf, Bool.false_eq_true, if_false]
    exact Prod.ext h1.symm h2.symm

/-- **The dual tree is cocompact**: finitely many orbits of regions (`finite_orbits_region`) and
of oriented edges, the latter because every oriented edge is a translate of one of the two
orientations of the edge through a pattern point `(1, i)` with `i` a finite index. -/
theorem resDualGT_isCocompact : (resDualGT (D := D)).IsCocompact := by
  haveI : Finite (MulAction.orbitRel.Quotient G (Region D)) := finite_orbits_region
  refine ⟨inferInstance, ?_⟩
  refine Finite.of_surjective
    (fun x : (Σ j : Fin P.n, Fin (D.L (j, true))) ⊕ (Σ j : Fin P.n, Fin (D.L (j, true))) =>
      (Quotient.mk (MulAction.orbitRel G (GTree.AdjPair (resDualGT (D := D))))
        (Sum.elim
          (fun i => dualEdgeOf (D := D) ((1 : G), (⟨i.1, i.2⟩ : MidIdx D)) true)
          (fun i => dualEdgeOf (D := D) ((1 : G), (⟨i.1, i.2⟩ : MidIdx D)) false) x) :
        MulAction.orbitRel.Quotient G (GTree.AdjPair (resDualGT (D := D))))) ?_
  intro q
  refine Quotient.inductionOn q (fun p => ?_)
  obtain ⟨m, b, hm⟩ := dualEdgeOf_surjective p
  have hmid : (m.1 : G)⁻¹ • m = ((1 : G), (⟨m.2.j, m.2.k⟩ : MidIdx D)) := by
    rw [show m = ((m.1 : G), m.2) from rfl, midV_smul, inv_mul_cancel]
  cases b with
  | false =>
      refine ⟨Sum.inr ⟨m.2.j, m.2.k⟩, ?_⟩
      apply Quotient.sound
      change (MulAction.orbitRel G (GTree.AdjPair (resDualGT (D := D))))
        (dualEdgeOf (D := D) ((1 : G), (⟨m.2.j, m.2.k⟩ : MidIdx D)) false) p
      rw [MulAction.orbitRel_apply]
      refine MulAction.mem_orbit_iff.mpr ⟨m.1⁻¹, ?_⟩
      rw [← hm, ← dualEdgeOf_smul, hmid]
  | true =>
      refine ⟨Sum.inl ⟨m.2.j, m.2.k⟩, ?_⟩
      apply Quotient.sound
      change (MulAction.orbitRel G (GTree.AdjPair (resDualGT (D := D))))
        (dualEdgeOf (D := D) ((1 : G), (⟨m.2.j, m.2.k⟩ : MidIdx D)) true) p
      rw [MulAction.orbitRel_apply]
      refine MulAction.mem_orbit_iff.mpr ⟨m.1⁻¹, ?_⟩
      rw [← hm, ← dualEdgeOf_smul, hmid]

/-! ## Finite generation of the stabilizers -/

/-- **Finitely many orbits and finite index.**  If `H ≤ K` are subgroups of `G`, `K` is finitely
generated, and `H` has finite index in `K`, then `H` is finitely generated. -/
theorem resFg_of_subgroup_finiteIndex {H K : Subgroup G} (hHK : H ≤ K)
    [h : (H.subgroupOf K).FiniteIndex] (hK : K.FG) : H.FG := by
  have hGK : Group.FG K := (Group.fg_iff_subgroup_fg K).2 hK
  have hsub : Group.FG ↥(H.subgroupOf K) := Subgroup.fg_of_index_ne_zero (H.subgroupOf K)
  have hGH : Group.FG H :=
    Group.fg_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hHK).surjective
  exact (Group.fg_iff_subgroup_fg H).1 hGH

/-- **The stabilizer of an edge of the dual tree is finitely generated.**  It is the stabilizer of
the track `τ` realising the edge intersected with the stabilizer of one of the two regions; the
latter is the stabilizer of that region for the action of `Stab τ`, and its orbit is contained in
the two-element set of regions of the edge, so its index is at most `2`. -/
theorem resDualGT_hasFGEdgeStab
    (hfgTrack : ∀ τ : Track D, (MulAction.stabilizer G τ).FG) :
    (resDualGT (D := D)).HasFGEdgeStab := by
  intro R R' hRR'
  rw [GTree.edgeStab_eq]
  obtain ⟨τ, hτ⟩ := hRR'
  have hne := Track.inc_ne hτ
  -- every element of `Stab τ` permutes the two regions of the edge
  have hswap : ∀ g : ↥(MulAction.stabilizer G τ),
      (g : G) • R = R ∨ (g : G) • R = R' := by
    intro g
    have hg : (g : G) • τ = τ := MulAction.mem_stabilizer_iff.mp g.2
    have hsym : Sym2.map (fun R : Region D => (g : G) • R) (s(R, R')) = s(R, R') := by
      rw [← hτ, ← Track.regPair_smul, hg]
    rcases Sym2.eq_iff.mp (by simpa only [Sym2.map_mk] using hsym) with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact Or.inl h2
    · exact Or.inr h2
  -- the stabilizer of the edge is `Stab τ ⊓ Stab R`
  have hHK : MulAction.stabilizer G R ⊓ MulAction.stabilizer G R' =
      MulAction.stabilizer G τ ⊓ MulAction.stabilizer G R := by
    refine le_antisymm ?_ ?_
    · intro g hg
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff] at hg
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      refine ⟨?_, hg.1⟩
      have hpair : s((g : G) • R, (g : G) • R') = s(R, R') := by rw [hg.1, hg.2]
      have hreg : (g • τ).regPair = τ.regPair := by
        rw [Track.regPair_smul, show τ.regPair = s(R, R') from hτ, Sym2.map_mk, hpair]
      exact resRegPair_injective hreg
    · intro g hg
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at hg
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
      refine ⟨hg.2, ?_⟩
      have hsym : Sym2.map (fun R : Region D => (g : G) • R) (s(R, R')) = s(R, R') := by
        rw [← hτ, ← Track.regPair_smul, hg.1]
      have hpair : s((g : G) • R, (g : G) • R') = s(R, R') := by
        simpa only [Sym2.map_mk] using hsym
      rw [hg.2] at hpair
      rcases Sym2.eq_iff.mp hpair with ⟨-, h2⟩ | ⟨h2, -⟩
      · exact h2
      · exact absurd h2 hne
  -- the orbit of `R` under `Stab τ` is contained in the two regions of the edge
  have horb : MulAction.orbit ↥(MulAction.stabilizer G τ) R ⊆ ({R, R'} : Set (Region D)) := by
    intro S hS
    rw [MulAction.mem_orbit_iff] at hS
    obtain ⟨g, hg⟩ := hS
    rw [← hg]
    change (g : G) • R ∈ ({R, R'} : Set (Region D))
    rcases hswap g with h | h
    · rw [h]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · rw [h]
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton R'))
  have horbfin : (MulAction.orbit ↥(MulAction.stabilizer G τ) R).Finite :=
    ((Set.finite_singleton R').insert R).subset horb
  -- the index of the edge stabilizer in `Stab τ` is at most two
  have hsub : (MulAction.stabilizer G R ⊓ MulAction.stabilizer G R').subgroupOf
        (MulAction.stabilizer G τ) =
      MulAction.stabilizer ↥(MulAction.stabilizer G τ) R := by
    rw [hHK, inf_comm (MulAction.stabilizer G τ) (MulAction.stabilizer G R),
      Subgroup.inf_subgroupOf_right]
    ext g
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    rfl
  have hfin : (MulAction.stabilizer ↥(MulAction.stabilizer G τ) R).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, MulAction.index_stabilizer]
    exact (Set.ncard_pos (hs := horbfin)).mpr ⟨R, MulAction.mem_orbit_self R⟩ |>.ne'
  have hfin' : ((MulAction.stabilizer G R ⊓ MulAction.stabilizer G R').subgroupOf
      (MulAction.stabilizer G τ)).FiniteIndex := by
    rw [hsub]
    exact hfin
  haveI := hfin'
  exact resFg_of_subgroup_finiteIndex (H := MulAction.stabilizer G R ⊓ MulAction.stabilizer G R')
    (K := MulAction.stabilizer G τ) (by rw [hHK]; exact inf_le_left) (hfgTrack τ)

/-- **The vertex stabilizers of the dual tree are finitely generated.** -/
theorem resDualGT_hasFGVertexStab :
    (resDualGT (D := D)).HasFGVertexStab :=
  fun R => fg_stabilizer_region R

/-- **The Dunwoody resolution**, given finite generation of the stabilizers of the tracks.  (All
the other inputs are theorems: (W1) and (W2) in `Dunwoody/RegionAlpha.lean`, finite generation of
the region stabilizers in `fg_stabilizer_region.lean`.) -/
theorem resDunwoodyResolution
    (hfgTrack : ∀ τ : Track D, (MulAction.stabilizer G τ).FG) :
    ∃ (W : Type u) (_ : MulAction G W) (S : GTree G W),
      S.IsCocompact ∧ S.HasFGStab ∧ Dominates S T :=
  ⟨Region D, instMulActionRegion, resDualGT (D := D), resDualGT_isCocompact,
    ⟨resDualGT_hasFGVertexStab, resDualGT_hasFGEdgeStab hfgTrack⟩,
    resDualGT_dominates⟩

/-! ## The Dunwoody resolution, unconditional -/

/-- **The Dunwoody resolution** (GL17 Proposition 2.17, constant case), for a group of the universe
of `G`: no hypothesis is left. -/
theorem resDunwoodyResolution_holds (G : Type u) [Group G] {V : Type u} [MulAction G V]
    (T : GTree G V) (hf : Group.IsFinitelyPresented G) (hc : T.IsCocompact) :
    ∃ (W : Type u) (_ : MulAction G W) (S : GTree G W),
      S.IsCocompact ∧ S.HasFGStab ∧ Dominates S T := by
  classical
  haveI : Nonempty V := T.isTree.1.2
  obtain ⟨t₀⟩ := ‹Nonempty V›
  obtain ⟨P⟩ := exists_finPresentation G hf
  obtain ⟨D⟩ := Cayley.geoData_nonempty T t₀ P
  exact resDunwoodyResolution (D := D) (fun τ => fg_stabilizer_track τ)

end Work.ORDunwoody.Dunwoody

namespace Work.ORDunwoody

/-- **`DunwoodyResolutionAll` is a theorem.**  This is the input `NodeInputs.dunwoody` of
`Submission/Work/ORAssembly`, and with it the theorems of `Theorem44.lean`, `Theorem45.lean` and
`Corollaries.lean` lose their `DunwoodyResolutionAll` hypothesis. -/
theorem resDunwoodyResolutionAll (X : Type u) : DunwoodyResolutionAll X := by
  intro G _ V _ T hf hc
  exact Dunwoody.resDunwoodyResolution_holds G T hf hc

end Work.ORDunwoody
