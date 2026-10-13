/-
  WilE7 (`Work.WilE7.sheetCoveringMap`): the sheet projection of a `Good` stratum `S` with
  `S.j = q` over a base set `C` which avoids the projections of the forbidden (frontier) points of
  the stratum is a **covering map**.

  Route.  `SheetProj : SheetE S C → C` is

  * a *local homeomorphism*: at a point `v` of the sheet domain, `sheetLocalPatch` (the
    implicit-function form of `Good`, made ambient by `hloc`) exhibits the stratum near `v` as the
    graph of a continuous map `y` over an open `U ∋ projFirst p q v`; on the open piece
    `src = {z ∈ SheetE S C | z ∈ V, projFirst p q z ∈ U}` the projection is injective (uniqueness
    of the graph) with image the open (in `C`) set `tgt = C ∩ U ∩ g ⁻¹' V`, `g x = (x, y x)`,
    whose inverse is the continuous graph map `g`;

  * a *closed map*: if `x ∈ C` is a limit of projections of stratum points `z_k`, compactness of
    the cube (`S.X.set ⊆ cubeC (p+q)`) produces a limit point `z ∈ closure S.X.set` over `x`; if
    `z ∉ S.X.set` then `z` is a frontier point, hence forbidden, contradicting `projFirst p q z = x
    ∈ C`.  (`Work.WilE7.sheetProj_closedMap`.)

  The fibres of `SheetProj` are finite (`sheetFiber_finite`, from `hfin`), so Mathlib's
  `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` concludes.
-/
import Mathlib
import Submission.Work.WilE7.SheetDefs
import Submission.Work.WilE7.fiberCluster
import Submission.Work.WilE7.sheetProj_closedMap

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-- **The projection of the sheet space is a local homeomorphism.**  At a point `w` of
`SheetE S C`, the local graph provided by `sheetLocalPatch` turns an open neighbourhood of `w` in
the sheet space into an open set of `C` (its image) homeomorphically. -/
theorem sheetProj_localHomeo {p q : ℕ} {S : Stratum p q} (hGood : S.Good) (hj : S.j = q)
    (C : Set (Fin p → ℝ))
    (hloc : ∀ z ∈ S.X.set, projFirst p q z ∈ C →
      ∀ᶠ z' in nhds z,
        (∀ a : Fin S.j, eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set) :
    IsLocalHomeomorphOn (SheetProj (p := p) (q := q) (S := S) (C := C)) Set.univ := by
  intro w _
  -- the local graph of the stratum through `w`
  obtain ⟨U, y, V, hUo, hxU, hVo, hwV, hycont, hy0, hgraphV, hgraphS, huniq⟩ :=
    sheetLocalPatch S hGood hj C hloc w.1 w.2.1 w.2.2
  let g : (Fin p → ℝ) → (Fin (p + q) → ℝ) := fun x => Fin.append x (y x)
  -- the base points of the graphs lying in `V`
  let T : Set (Fin p → ℝ) := {x | x ∈ U ∧ g x ∈ V}
  -- the piece of the sheet space over `T`
  let src : Set (SheetE S C) := {z | z.1 ∈ V ∧ projFirst p q z.1 ∈ U}
  let tgt : Set C := Subtype.val ⁻¹' T
  have hgU : ContinuousOn g U := continuousOn_append hycont
  have hTo : IsOpen T := hgU.isOpen_inter_preimage hUo hVo
  have hSo : IsOpen src := by
    rw [isOpen_induced_iff]
    exact ⟨{z : Fin (p + q) → ℝ | z ∈ V ∧ projFirst p q z ∈ U},
      hVo.inter ((continuous_projFirst p q).isOpen_preimage U hUo), rfl⟩
  have hTo' : IsOpen tgt := by
    rw [isOpen_induced_iff]
    exact ⟨T, hTo, rfl⟩
  -- the inverse of the projection on `src`: the graph map, with a junk value off `T`
  let invFn : C → SheetE S C := fun x =>
    if hx : x.1 ∈ T then
      ⟨g x.1, mem_SheetSpace.mpr ⟨hgraphS x.1 ⟨hx.1, x.2⟩,
        by rw [projFirst_append]; exact x.2⟩⟩
    else ⟨w.1, w.2⟩
  have hval' : ∀ x : C, x.1 ∈ T → (invFn x).1 = g x.1 := by
    intro x hx
    simp only [invFn, dite_eq_left hx]
  have hmemT : ∀ z : SheetE S C, z ∈ src → (SheetProj z).1 ∈ T := by
    intro z hz
    exact ⟨hz.2, by
      show g (projFirst p q z.1) ∈ V
      exact hgraphV (projFirst p q z.1) hz.2⟩
  refine ⟨{ toFun := SheetProj
            invFun := invFn
            source := src
            target := tgt
            map_source' := hmemT
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            open_source := hSo
            open_target := hTo'
            continuousOn_toFun := SheetProj_continuous.continuousOn
            continuousOn_invFun := ?_ }, ?_, rfl⟩
  · -- the graph point over `x ∈ tgt` lies in `src`
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [hval' x hx]; exact hx.2
    · rw [hval' x hx, projFirst_append]; exact hx.1
  · -- uniqueness of the graph: the projection is injective on `src`
    intro z hz
    refine Subtype.ext ?_
    rw [hval' (SheetProj z) (hmemT z hz)]
    show Fin.append (projFirst p q z.1) (y (projFirst p q z.1)) = z.1
    rw [← huniq z.1 hz.1 z.2.1 hz.2, append_proj]
  · -- the graph point projects back to its base
    intro x hx
    refine Subtype.ext ?_
    show projFirst p q (invFn x).1 = x.1
    rw [hval' x hx, projFirst_append]
  · -- the inverse is the continuous graph map
    rw [continuousOn_iff_continuous_domRestrict]
    have hgg : ContinuousOn (fun x : C => g x.1) tgt :=
      hgU.comp continuous_subtype_val.continuousOn (fun x hx => hx.1)
    have h1 : Continuous (fun p : tgt => g p.1.1) :=
      (continuousOn_iff_continuous_domRestrict).mp hgg
    have h2 : Continuous (fun p : tgt => (⟨g p.1.1, mem_SheetSpace.mpr ⟨hgraphS p.1.1 ⟨p.2.1, p.1.2⟩,
        by rw [projFirst_append]; exact p.1.2⟩⟩ : SheetE S C)) :=
      h1.subtype_mk _
    refine h2.congr ?_
    intro p
    apply Subtype.ext
    exact (hval' p.1 p.2).symm
  · exact ⟨hwV, hxU⟩

theorem sheetCoveringMap {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good) (hj : S.j = q)
    (C : Set (Fin p → ℝ)) (Forbidden : Set (Fin (p + q) → ℝ))
    (hForb : ∀ w ∈ Forbidden, WilkiesDesign.E.projFirst p q w ∉ C)
    (hFr : closure S.X.set \ S.X.set ⊆ Forbidden)
    (hloc : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p q z ∈ C →
      ∀ᶠ z' in nhds z,
        (∀ a : Fin S.j, WilkiesDesign.E.eaEval S.X.c (S.h a) z' = 0) → z' ∈ S.X.set)
    (hCsub : C ⊆ Set.image (WilkiesDesign.E.projFirst p q) S.X.set)
    (hfin : ∀ x : Fin p → ℝ, (WilkiesDesign.E.fiber S.X.set x).Finite) :
    IsCoveringMap (Work.WilE7.SheetProj (p := p) (q := q) (S := S) (C := C)) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine (sheetProj_closedMap S C Forbidden hForb hFr).isCoveringMapOn_of_isLocalHomeomorphOn
    (fun x _ => sheetFiber_finite hfin x) ?_
  simpa using sheetProj_localHomeo (S := S) hGood hj C hloc

end Work.WilE7
