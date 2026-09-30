import Mathlib
import Submission.Work.RTOwed.FillAtlas

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The disjointness of the chart families of the filling atlas of `M̂`

The filling atlas of `M̂` (`Work.RTOwed.FillAtlas`) consists of three families of charts attached to
the five *cusps* `v : Fin 5`, together with the fold charts of the hyperbolic piece:

* the **junction charts** `Work.RTOwed.jChart a D v P`;
* the **core charts** `Work.RTOwed.kChartOf a tor v W hW hsec`;
* the **collar charts** `Work.RTOwed.cChart a D v c δ hδ hne`;
* the **fold charts** `(Work.RTOwed.foldDataOf g).foldM i` of `M̄`.

All the charts of the first three families are attached to their cusp through the coordinate
inclusions, and the point of `M̂` that they describe lies in the corresponding filling piece
(`a.incW v`) unless it lies strictly below the ceiling of the cusp chart, in which case it lies in
the *un-glued* part `a.incMbar '' a.Tsetᶜ` of the hyperbolic piece.  The fold charts likewise take
their values in `a.incMbar '' a.Tsetᶜ` (their sources avoid the cusped boundary).

This file records the resulting *disjointness* of the sources of the charts of two distinct cusps
— the statement that the atlas is a genuine atlas of the *union* of the pieces rather than of the
pieces separately.  The main statement is `Work.RTOwed.atlas_empty`.
-/

noncomputable section

open Set Topology Function

namespace Work.RTOwed

variable (a : Work.Space.Assembly)

/-! ## The two complementary pieces of `M̂` -/

/-- Two points of *different* filling pieces can never agree in `M̂`: `a.incW` remembers the cusp. -/
theorem incW_ne_incW {v v' : Work.Space.Cusp} (h : v ≠ v')
    (p : Work.Space.SquarePt × a.Torus v) (p' : Work.Space.SquarePt × a.Torus v') :
    a.incW v p ≠ a.incW v' p' := by
  intro heq
  have h3 : (⟨v, p⟩ : a.Y) = ⟨v', p'⟩ := a.incY_injective heq
  exact h (congrArg Sigma.fst h3)

/-- The images of two distinct filling pieces in `M̂` are disjoint. -/
theorem range_incW_inter {v v' : Work.Space.Cusp} (h : v ≠ v') :
    (range (a.incW v) ∩ range (a.incW v') : Set a.Mhat) = ∅ := by
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
  rintro z ⟨p, hp⟩ ⟨p', hp'⟩
  exact incW_ne_incW a h p p' (by rw [hp, hp'])

/-- A point of the *un-glued* part of the hyperbolic piece is never in the image of a filling
piece: the identification of `M̄` with a filling piece takes place only on the cusped boundary
`a.Tset`. -/
theorem disjoint_range_incW_incMbar (v : Work.Space.Cusp) :
    Disjoint (range (a.incW v)) (a.incMbar '' a.Tsetᶜ) := by
  rw [Set.disjoint_left]
  rintro z ⟨p, hp⟩ ⟨x, hx, hxz⟩
  exact hx (Work.Cusp.incMbar_eq_incW_imp a v (by rw [hxz, hp])).1

/-! ## The values of the three coordinate inclusions

We show that every point of the source of one of the charts of the atlas is
`a.incW v`-valued for its cusp `v`, except for the collar chart, whose points below the ceiling are
`a.incMbar`-valued (and, being strictly below the ceiling, un-glued). -/

/-- If the value of a collar coordinate inclusion is at or above the ceiling of the cusp chart,
then it is a point of the filling piece of `v`. -/
theorem cuspCoordMTop_mem_range_incW (v : Work.Space.Cusp) (D : Work.Cusp.CuspGlueData a v)
    (c : Work.Cusp.E3) (δ : ℝ)
    (q : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    (h : ¬ q.1 3 < Work.Cusp.beta (Work.Cusp.xOf q.1)) :
    Work.Cusp.cuspCoordMTop a v D c δ q ∈ range (a.incW v) := by
  unfold Work.Cusp.cuspCoordMTop
  split_ifs with h'
  · exact absurd h' h
  · exact ⟨_, rfl⟩

/-- **Every value of a junction chart with the radial cut `rCut` lies in the filling piece of its
cusp.**  This is where the cut `rCut = 61/20 < R₀ − log (3/2)` enters: above the junction radius
`rJ = 3` the junction chart is the collar inclusion of the point `polarToUHS v q`, whose height
`e^{R₀ − q 0} > 3/2 ≥ β` exceeds the ceiling `β` of every cusp coordinate, so the collar inclusion
takes its filling branch. -/
theorem jCoordM_mem_range_incW (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2) (kx : Work.Cusp.E3)
    (δ : ℝ) (q : {q : Work.Cusp.E4 // q ∈ jBox v cU k W kx δ})
    (hcut : q.1 0 < rCut) :
    jCoordM a v (D v) cU k W kx δ q ∈ range (a.incW v) := by
  unfold jCoordM
  split_ifs with h
  · exact ⟨_, rfl⟩
  · have hr : Work.Cusp.rJ < q.1 0 := not_le.mp h
    unfold Work.Cusp.cuspCoordMTop
    split_ifs with h2
    · exfalso
      rw [Work.RTOwed.polarToUHS_three] at h2
      have hbeta := Work.Cusp.beta_le_max (Work.Cusp.xOf (Work.Cusp.polarToUHS v q.1))
      rw [← Work.RTOwed.lt_betaMax] at hbeta
      have hgt : (3 / 2 : ℝ) < Real.exp (Work.Cusp.R0 - q.1 0) := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
        apply Real.exp_lt_exp.mpr
        have hh := Work.RTOwed.rCut_lt_R0_sub_log
        simp only [Work.Cusp.rJ] at hr
        linarith
      linarith
    · exact ⟨_, rfl⟩

/-! ## The sources of the four chart families -/

/-- The source of a junction chart consists of points of the filling piece of its cusp. -/
theorem jChart_source_subset (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) :
    (jChart a D v P).source ⊆ range (a.incW v) := by
  intro z hz
  rw [jChart_source] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  exact jCoordM_mem_range_incW a D v P.cU P.k P.W P.kx P.δ q hq.2

/-- The source of a core chart consists of points of the filling piece of its cusp. -/
theorem kChart_source_subset (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    (kChartOf a tor v W hW hsec).source ⊆ range (a.incW v) := by
  intro z hz
  rw [kChartOf_source] at hz
  obtain ⟨q, -, rfl⟩ := hz
  unfold Work.Cusp.coreCoordM
  exact ⟨_, rfl⟩

/-- The source of a collar chart consists of points of the filling piece of its cusp, together
with points of the un-glued part of the hyperbolic piece (those strictly below the ceiling). -/
theorem cChart_source_subset (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1 / 2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    (cChart a D v c δ hδ hne).source ⊆ range (a.incW v) ∪ (a.incMbar '' a.Tsetᶜ) := by
  intro z hz
  rw [cChart_source] at hz
  obtain ⟨q, hq, rfl⟩ := hz
  unfold Work.Cusp.cuspCoordMTop
  split_ifs with h
  · exact Or.inr ⟨(D v).mbarLow q.1, (D v).mbarLow_not_TsetTop c δ q.2 h, rfl⟩
  · exact Or.inl ⟨_, rfl⟩

/-- The source of a transported fold chart consists of un-glued points of the hyperbolic piece. -/
theorem foldM_source_subset (F : Work.RTInstance.FoldData a) (i : Fin F.nF) :
    (F.foldM i).source ⊆ a.incMbar '' a.Tsetᶜ := by
  rw [Work.RTInstance.FoldData.foldM_source]
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, F.fold_source i hx, rfl⟩

/-! ## Empty intersections -/

/-- Sources of two charts of two distinct filling pieces are disjoint. -/
theorem inter_eq_empty_incW {S T : Set a.Mhat} {v v' : Work.Space.Cusp} (hne : v ≠ v')
    (hS : S ⊆ range (a.incW v)) (hT : T ⊆ range (a.incW v')) : S ∩ T = ∅ := by
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
  rintro z hz1 hz2
  obtain ⟨p, hp⟩ := hS hz1
  obtain ⟨p', hp'⟩ := hT hz2
  exact incW_ne_incW a hne p p' (by rw [hp, hp'])

/-- A source contained in one filling piece and a source contained in another filling piece or in
the un-glued part of the hyperbolic piece are disjoint. -/
theorem inter_eq_empty_incW_union {S T : Set a.Mhat} {v v' : Work.Space.Cusp} (hne : v ≠ v')
    (hS : S ⊆ range (a.incW v)) (hT : T ⊆ range (a.incW v') ∪ (a.incMbar '' a.Tsetᶜ)) :
    S ∩ T = ∅ := by
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
  rintro z hz1 hz2
  obtain ⟨p, hp⟩ := hS hz1
  rcases hT hz2 with ⟨p', hp'⟩ | ⟨x, hx, hxz⟩
  · exact incW_ne_incW a hne p p' (by rw [hp, hp'])
  · exact hx (Work.Cusp.incMbar_eq_incW_imp a v (by rw [hxz, hp])).1

/-- A source contained in the un-glued part of the hyperbolic piece and a source contained in a
filling piece are disjoint. -/
theorem inter_eq_empty_incMbar {S T : Set a.Mhat} {v : Work.Space.Cusp}
    (hS : S ⊆ a.incMbar '' a.Tsetᶜ) (hT : T ⊆ range (a.incW v)) : S ∩ T = ∅ := by
  rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
  rintro z hz1 hz2
  obtain ⟨x, hx, hxz⟩ := hS hz1
  obtain ⟨p, hp⟩ := hT hz2
  exact hx (Work.Cusp.incMbar_eq_incW_imp a v (by rw [hxz, hp])).1

/-! ## The statement -/

theorem atlas_empty (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) :
    (∀ (v v' : Work.Space.Cusp) (hne : v ≠ v') (P : Work.RTOwed.JPin a v)
        (Q : Work.RTOwed.JPin a v'),
        (Work.RTOwed.jChart a D v P).source ∩ (Work.RTOwed.jChart a D v' Q).source = ∅) ∧
    (∀ (v v' : Work.Space.Cusp) (hne : v ≠ v') (P : Work.RTOwed.JPin a v)
        (W : Set Work.Cusp.E2) (hW : IsOpen W)
        (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v' y ∈ W → Work.Cusp.wOf v' y' ∈ W →
          (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y'),
        (Work.RTOwed.jChart a D v P).source ∩ (Work.RTOwed.kChartOf a tor v' W hW hsec).source = ∅) ∧
    (∀ (v v' : Work.Space.Cusp) (hne : v ≠ v') (W W' : Set Work.Cusp.E2) (hW : IsOpen W)
        (hW' : IsOpen W')
        (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
          (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
        (hsec' : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v' y ∈ W' → Work.Cusp.wOf v' y' ∈ W' →
          (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y'),
        (Work.RTOwed.kChartOf a tor v W hW hsec).source ∩
          (Work.RTOwed.kChartOf a tor v' W' hW' hsec').source = ∅) ∧
    (∀ (v v' : Work.Space.Cusp) (hne : v ≠ v') (W : Set Work.Cusp.E2) (hW : IsOpen W)
        (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
          (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
        (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
        (hne' : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c δ}),
        (Work.RTOwed.kChartOf a tor v W hW hsec).source ∩
          (Work.RTOwed.cChart a D v' c δ hδ hne').source = ∅) ∧
    (∀ (v v' : Work.Space.Cusp) (hne : v ≠ v') (P : Work.RTOwed.JPin a v) (c : Work.Cusp.E3)
        (δ : ℝ) (hδ : δ ≤ 1/2)
        (hne' : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c δ}),
        (Work.RTOwed.jChart a D v P).source ∩ (Work.RTOwed.cChart a D v' c δ hδ hne').source = ∅) ∧
    (∀ (g : Work.RTInstance.GlueHomeo)
        (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
        (i : Fin (Work.RTOwed.foldDataOf g).nF) (v : Work.Space.Cusp)
        (P : Work.RTOwed.JPin (Work.RTInstance.assemblyOf g) v),
        ((Work.RTOwed.foldDataOf g).foldM i).source ∩
          (Work.RTOwed.jChart (Work.RTInstance.assemblyOf g) D v P).source = ∅) ∧
    (∀ (g : Work.RTInstance.GlueHomeo)
        (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
        (tor : ∀ v : Work.Space.Cusp, (Work.RTInstance.assemblyOf g).Torus v ≃ₜ
          (Fin 2 → AddCircle (1 : ℝ)))
        (i : Fin (Work.RTOwed.foldDataOf g).nF) (v : Work.Space.Cusp) (W : Set Work.Cusp.E2)
        (hW : IsOpen W)
        (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
          (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y'),
        ((Work.RTOwed.foldDataOf g).foldM i).source ∩
          (Work.RTOwed.kChartOf (Work.RTInstance.assemblyOf g) tor v W hW hsec).source = ∅) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v v' hne P Q
    exact inter_eq_empty_incW a hne (jChart_source_subset a D v P)
      (jChart_source_subset a D v' Q)
  · intro v v' hne P W hW hsec
    exact inter_eq_empty_incW a hne (jChart_source_subset a D v P)
      (kChart_source_subset a tor v' W hW hsec)
  · intro v v' hne W W' hW hW' hsec hsec'
    exact inter_eq_empty_incW a hne (kChart_source_subset a tor v W hW hsec)
      (kChart_source_subset a tor v' W' hW' hsec')
  · intro v v' hne W hW hsec c δ hδ hne'
    exact inter_eq_empty_incW_union a hne (kChart_source_subset a tor v W hW hsec)
      (cChart_source_subset a D v' c δ hδ hne')
  · intro v v' hne P c δ hδ hne'
    exact inter_eq_empty_incW_union a hne (jChart_source_subset a D v P)
      (cChart_source_subset a D v' c δ hδ hne')
  · intro g D i v P
    exact inter_eq_empty_incMbar (Work.RTInstance.assemblyOf g)
      (foldM_source_subset (Work.RTInstance.assemblyOf g) (foldDataOf g) i)
      (jChart_source_subset (Work.RTInstance.assemblyOf g) D v P)
  · intro g D tor i v W hW hsec
    exact inter_eq_empty_incMbar (Work.RTInstance.assemblyOf g)
      (foldM_source_subset (Work.RTInstance.assemblyOf g) (foldDataOf g) i)
      (kChart_source_subset (Work.RTInstance.assemblyOf g) tor v W hW hsec)

end Work.RTOwed
