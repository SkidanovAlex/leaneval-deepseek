import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfVanishing
import Submission.Work.Orient.Boundary.HalfRestrictIso
import Submission.Work.Orient.Boundary.HalfCover
import Submission.Work.Orient.Boundary.HalfCompactZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Gluing relative classes over a finite cover by coordinate half-balls

This file proves `Work.Orient.HalfCoverGlueProp`, i.e. the half-space analogue of
`Work.Orient.Port.coverGlue`: classes `ζ i ∈ H_{n+1}(W, W∖K_i)` over coordinate half-balls `K_i`
which agree at every point of the pairwise intersections `K_i ∩ K_j` are the restrictions of a
single class on the union.  It is the last component of the half-space port of Hatcher 3.27 used in
`Submission/Work/Orient/Boundary.lean`.

The proof is the literal transcription of the Euclidean argument (`Port/Hatcher2.lean`):

* the induction over the finite family of pieces uses the Mayer–Vietoris exactness of the
  "excluded set" functor (`Work.ThomBordism.excludedMV`) together with the vanishing above the
  dimension (`HalfVanishing`, the half-space Hatcher 3.27 (b)) and the localisation isomorphism out
  of a coordinate half-ball of the interior (`HalfRestrictIso`);
* the agreement of the two classes on the intersection `K_a ∩ ⋃_{i∈t} K_i` is obtained by
  uniqueness (Hatcher 3.27 (a)) for a class whose localisation vanishes everywhere
  (`halfCompactZeroInterior`), a statement which is `Work.Orient.Boundary.HalfCompactZero` with its
  `IsManifold` hypothesis — used there only to know that the boundary `∂W` is closed — replaced by
  `isClosed_boundary_halfSpace` below.

The interest of the last point is that a `ChartedSpace (EuclideanHalfSpace (n+1)) W` has no
manifold structure to speak of: the charts are unrelated homeomorphisms.  What makes `∂W` closed
anyway is that the interior/boundary dichotomy is *local homology*, hence chart independent: the
local group `H_{n+1}(W, W∖x)` is `ℤ` at an interior point and `0` at a boundary point
(`Work.Orient.Boundary.localHomology_corner`), so a point whose image in *some* chart has positive
last coordinate cannot be a boundary point (`chartAt_boundary_coord_zero_aux`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-! ## The restriction API, in the ORIENT names -/

private theorem resRelH_comp' (W : TopCat) (m : ℕ) {A B C : Set W} (h₁ : A ⊆ B) (h₂ : B ⊆ C)
    (h₃ : A ⊆ C) : (resRelH W m h₁).comp (resRelH W m h₂) = resRelH W m h₃ :=
  Work.Orient.Port.RelHmap_comp' W m h₁ h₂ h₃

private theorem resRelH_point_fac (W : TopCat) (m : ℕ) {A B : Set W} (h : A ⊆ B) {x : W}
    (hxA : x ∈ A) :
    resRelH W m (Set.singleton_subset_iff.mpr (h hxA))
      = (resRelH W m (Set.singleton_subset_iff.mpr hxA)).comp (resRelH W m h) :=
  Work.Orient.Port.RelHmap_point_fac W m h hxA

private theorem resRelH_congr_h (W : TopCat) (m : ℕ) {A B : Set W} (h h' : A ⊆ B) :
    resRelH W m h = resRelH W m h' :=
  Work.Orient.Port.RelHmap_congr_h W m h h'

/-! ## Chart independence of the interior, and closedness of the boundary -/

/-- **A chart identifies the local homology of `X` at `x` with the relative homology of the
half-space at the image of `x`** (the two-chart version of `Work.Orient.Boundary.locH_iso_halfspace`,
where the chart used is the one at `z` rather than the one at `x`). -/
theorem locH_iso_halfspace_chart (n k : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (z x : W)
    (hx : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).source) :
    Nonempty (LocH W k x ≅ (Work.Cohomology.relChains
      (TopCat.of (EuclideanHalfSpace (n + 1)))
      {y : EuclideanHalfSpace (n + 1) | y ≠ chartAt (EuclideanHalfSpace (n + 1)) z x}).homology
        k) := by
  haveI : T1Space (EuclideanHalfSpace (n + 1)) := t1Space_halfSpace n
  haveI : T1Space W := ChartedSpace.t1Space (EuclideanHalfSpace (n + 1)) W
  set c : EuclideanHalfSpace (n + 1) := chartAt (EuclideanHalfSpace (n + 1)) z x with hc
  obtain ⟨e1⟩ := relChains_chart_iso (chartAt (EuclideanHalfSpace (n + 1)) z) x hx k
  have hArg : IsOpen {y : EuclideanHalfSpace (n + 1) | y ≠ c} := isClosed_singleton.isOpen_compl
  have hcov : (chartAt (EuclideanHalfSpace (n + 1)) z).target ∪
      {y : EuclideanHalfSpace (n + 1) | y ≠ c} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases h : y = c
    · exact Or.inl (h ▸ (chartAt (EuclideanHalfSpace (n + 1)) z).map_source hx)
    · exact Or.inr h
  obtain ⟨e2⟩ := excision_iso (TopCat.of (EuclideanHalfSpace (n + 1)))
    (chartAt (EuclideanHalfSpace (n + 1)) z).target {y : EuclideanHalfSpace (n + 1) | y ≠ c}
    (chartAt (EuclideanHalfSpace (n + 1)) z).open_target hArg hcov k
  exact ⟨e1 ≪≫ e2⟩

/-- **Chart independence of the interior of the half-space model.**  If `x` is a boundary point of
`W` and lies in the source of the chart `chartAt H z`, then `chartAt H z` sends `x` onto the
hyperplane of the model.

This is the converse of `Work.Orient.Boundary.chartAt_interior_pos`: a point of the half-space whose
last coordinate is *positive* has a Euclidean neighbourhood inside the half-space, so its local
homology is `ℤ` (`Work.Orient.Boundary.halfspace_interior_top_iso`), which a boundary point — whose
local homology vanishes — cannot have. -/
theorem chartAt_boundary_coord_zero_aux {n : ℕ} {W : TopCat.{0}} [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] {z x : W}
    (hx : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) z).source)
    (hb : x ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    ((chartAt (EuclideanHalfSpace (n + 1)) z) x).1 0 = 0 := by
  classical
  by_contra hne
  have hpos : 0 < ((chartAt (EuclideanHalfSpace (n + 1)) z) x).1 0 :=
    lt_of_le_of_ne ((chartAt (EuclideanHalfSpace (n + 1)) z) x).2 (Ne.symm hne)
  obtain ⟨e1⟩ := locH_iso_halfspace_chart n (n + 1) W z x hx
  obtain ⟨e2⟩ := halfspace_interior_top_iso n ((chartAt (EuclideanHalfSpace (n + 1)) z) x) hpos
  have hzero : IsZero (LocH W (n + 1) x) := (localHomology_corner n W x).2 hb
  have hZ : IsZero (ModuleCat.of ℤ ℤ) := IsZero.of_iso hzero (e1 ≪≫ e2).symm
  have hsub : Subsingleton (ModuleCat.of ℤ ℤ) := ModuleCat.subsingleton_of_isZero hZ
  exact one_ne_zero (Subsingleton.elim (1 : ℤ) 0)

/-- **The boundary of a space charted by the half-space is closed.**  (This is
`ModelWithCorners.isClosed_boundary`, whose proof in Mathlib needs the space to be a `C^1`
manifold; for the half-space model it follows from the chart independence of the dichotomy
`chartAt_boundary_coord_zero_aux`, which is proved from the local homology.) -/
theorem isClosed_boundary_halfSpace (n : ℕ) (W : TopCat.{0}) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] :
    IsClosed ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) := by
  classical
  have hcompl : IsOpen (((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)ᶜ) := by
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    have hpos : 0 < ((chartAt (EuclideanHalfSpace (n + 1)) x) x).1 0 :=
      chartAt_interior_pos (n := n) (mem_chart_source _ x) hx
    refine ⟨(chartAt (EuclideanHalfSpace (n + 1)) x).source ∩
        (chartAt (EuclideanHalfSpace (n + 1)) x) ⁻¹'
          {y : EuclideanHalfSpace (n + 1) | 0 < y.1 0}, ?_, ?_, ?_⟩
    · intro y hy hyb
      have h0 := chartAt_boundary_coord_zero_aux (n := n) (W := W) (z := x) (x := y) hy.1 hyb
      have hlt : ¬ (0 < ((chartAt (EuclideanHalfSpace (n + 1)) x) y).1 0) := by
        rw [h0]
        exact lt_irrefl 0
      exact hlt hy.2
    · exact (chartAt (EuclideanHalfSpace (n + 1)) x).isOpen_inter_preimage
        (isOpen_lt continuous_const
          ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0).comp continuous_subtype_val))
    · exact ⟨mem_chart_source _ x, hpos⟩
  have h := isClosed_compl_iff.mpr hcompl
  simpa using h

/-! ## Uniqueness for a compact set of the interior -/

/-- **Uniqueness over a compact set of the interior, without a manifold structure on `W`.**

A class of `H_{n+1}(W, W∖A)`, with `A` compact and contained in the interior, whose localisation
vanishes at every point of `A`, is zero.  This is `Work.Orient.Boundary.HalfCompactZero`
(`Submission/Work/Orient/Boundary/HalfCompactZero.lean`) with the hypothesis
`[IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]` — which that proof uses only to know
that `∂W` is closed — replaced by `isClosed_boundary_halfSpace`, which is proved above. -/
theorem halfCompactZeroInterior (n : ℕ) (W : TopCat.{0}) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {A : Set W} (hA : IsCompact A)
    (hAint : ∀ x ∈ A, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (β : RelH W (n + 1) A)
    (hβ : ∀ (x : W) (hx : x ∈ A),
      resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx) β = 0) :
    β = 0 := by
  classical
  obtain ⟨m, z, r, hr, hgood, hzA, hint, hcov, γ, hγ⟩ :=
    halfExistsLift n W (isClosed_boundary_halfSpace n W) hA hAint β
  have hγ0 : γ = 0 := by
    refine halfUnionZero n W Finset.univ z r hr hgood hint γ ?_
    intro i _
    have h1 : resRelH W (n + 1) (Set.singleton_subset_iff.mpr (hcov (hzA i))) γ
        = resRelH W (n + 1) (Set.singleton_subset_iff.mpr (hzA i))
            (resRelH W (n + 1) hcov γ) := by
      rw [← LinearMap.comp_apply, ← resRelH_point_fac W (n + 1) hcov (hzA i)]
    rw [show (Set.singleton_subset_iff.mpr
          (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, mem_halfBallPiece_center (hr i)⟩))
        = Set.singleton_subset_iff.mpr (hcov (hzA i)) from Subsingleton.elim _ _,
      h1, hγ]
    exact hβ (z i) (hzA i)
  rw [← hγ, hγ0, map_zero]

/-! ## The gluing lemma -/

/-- **`Work.Orient.Boundary.HalfCoverGlue`** (the half-space analogue of
`Work.Orient.Port.coverGlue`): classes over coordinate half-balls lying in the interior of a
compact space `W` charted by the half-space, which agree at every point of the pairwise
intersections, are the restrictions of one class on the union. -/
theorem HalfCoverGlue (n : ℕ) (W : TopCat.{0}) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] {m : ℕ} (K : Fin m → Set W)
    (hK : ∀ i, Work.Orient.IsCoordHalfBall (n + 1) W (K i))
    (hint : ∀ (i : Fin m) (x : W), x ∈ K i →
      x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (ζ : ∀ i, Work.Orient.RelH W (n + 1) (K i))
    (hglue : ∀ (i j : Fin m) (x : W) (hx : x ∈ K i ∩ K j),
      Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx.1) (ζ i)
        = Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx.2) (ζ j)) :
    ∃ γ : Work.Orient.RelH W (n + 1) (⋃ i, K i), ∀ i,
      Work.Orient.resRelH W (n + 1) (Set.subset_iUnion K i) γ = ζ i := by
  classical
  have key : ∀ t : Finset (Fin m), ∃ γ : RelH W (n + 1) (⋃ i ∈ t, K i),
      ∀ i (hi : i ∈ t), resRelH W (n + 1) (Set.subset_biUnion_of_mem hi) γ = ζ i := by
    intro t
    refine Finset.induction_on t ?base ?step
    · exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · intro a t ha ih
      obtain ⟨γt, hγt⟩ := ih
      have hKa : IsCoordHalfBall (n + 1) W (K a) := hK a
      have hLcpt : IsCompact (⋃ i ∈ t, K i) :=
        Finset.isCompact_biUnion t (fun i _ => (hK i).isCompact)
      have hInt : IsCompact (K a ∩ ⋃ i ∈ t, K i) := hKa.isCompact.inter hLcpt
      have hWU : (K a ∪ ⋃ i ∈ t, K i) ⊆ (⋃ i ∈ insert a t, K i) := by
        intro y hy
        rcases hy with hy | hy
        · exact Set.mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a t, hy⟩
        · obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
          exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hyi⟩
      have hUW : (⋃ i ∈ insert a t, K i) ⊆ (K a ∪ ⋃ i ∈ t, K i) := by
        intro y hy
        obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Or.inl hyi
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hyi⟩)
      have hagree : resRelH W (n + 1) (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) (ζ a)
          = resRelH W (n + 1)
              (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) γt := by
        have hzero : resRelH W (n + 1)
              (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) (ζ a)
            - resRelH W (n + 1)
              (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) γt = 0 :=
          halfCompactZeroInterior n W (A := K a ∩ ⋃ i ∈ t, K i) hInt
            (fun x hx => hint a x hx.1)
            (resRelH W (n + 1)
                (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) (ζ a)
              - resRelH W (n + 1)
                (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) γt)
            (fun x hx => by
              have hxa : x ∈ K a := hx.1
              have hxi : x ∈ ⋃ i ∈ t, K i := hx.2
              obtain ⟨i, hi, hxKi⟩ := Set.mem_iUnion₂.mp hxi
              have e1 : resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxa) (ζ a)
                  = resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxKi) (ζ i) := by
                rw [hglue a i x ⟨hxa, hxKi⟩]
              have e2 : resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxKi) (ζ i)
                  = resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxi) γt := by
                rw [← hγt i hi, ← LinearMap.comp_apply, resRelH_comp' W (n + 1)
                  (Set.singleton_subset_iff.mpr hxKi) (Set.subset_biUnion_of_mem hi)
                  (Set.singleton_subset_iff.mpr hxi)]
                first
                 | rfl
                 | (congr 1; exact resRelH_congr_h W (n + 1) _ _)
              have key1 : resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx)
                    (resRelH W (n + 1)
                      (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a) (ζ a))
                  = resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxa) (ζ a) := by
                rw [← LinearMap.comp_apply, resRelH_comp' W (n + 1)
                  (Set.singleton_subset_iff.mpr hx)
                  (Set.inter_subset_left : K a ∩ ⋃ i ∈ t, K i ⊆ K a)
                  (Set.singleton_subset_iff.mpr hxa)]
              have key2 : resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx)
                    (resRelH W (n + 1)
                      (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i) γt)
                  = resRelH W (n + 1) (Set.singleton_subset_iff.mpr hxi) γt := by
                rw [← LinearMap.comp_apply, resRelH_comp' W (n + 1)
                  (Set.singleton_subset_iff.mpr hx)
                  (Set.inter_subset_right : K a ∩ ⋃ i ∈ t, K i ⊆ ⋃ i ∈ t, K i)
                  (Set.singleton_subset_iff.mpr hxi)]
              rw [map_sub, key1, key2, e1, e2, sub_self])
        exact sub_eq_zero.mp hzero
      obtain ⟨u, hu1, hu2⟩ := (Work.ThomBordism.excludedMV (n + 1) W (K a)
        (⋃ i ∈ t, K i) hKa.isClosed hLcpt.isClosed
        (HalfVanishing n W (K a ∩ ⋃ i ∈ t, K i) hInt ((n + 1) + 1) (by omega))).2
        (ζ a) γt hagree
      refine ⟨resRelH W (n + 1) hUW u, ?_⟩
      intro i hi
      have hsub : K i ⊆ K a ∪ ⋃ j ∈ t, K j := by
        rcases Finset.mem_insert.mp hi with hia | hi
        · intro y hy
          exact Or.inl (by rwa [hia] at hy)
        · intro y hy
          exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩)
      have h1 : resRelH W (n + 1) (Set.subset_biUnion_of_mem hi) (resRelH W (n + 1) hUW u)
          = resRelH W (n + 1) hsub u := by
        rw [show resRelH W (n + 1) (Set.subset_biUnion_of_mem hi) (resRelH W (n + 1) hUW u)
              = ((resRelH W (n + 1) (Set.subset_biUnion_of_mem hi)).comp
                  (resRelH W (n + 1) hUW)) u from rfl]
        rw [resRelH_comp' W (n + 1) (Set.subset_biUnion_of_mem hi) hUW hsub]
      rw [h1]
      rcases Finset.mem_insert.mp hi with hia | hi
      · have hcast := Work.Orient.Port.resRelH_aux (M := W) (n := n + 1)
          (B := K a ∪ ⋃ j ∈ t, K j) (B' := K a ∪ ⋃ j ∈ t, K j) (D := K a) (D' := K i)
          rfl (congrArg K hia.symm) (Set.subset_union_left : K a ⊆ K a ∪ ⋃ j ∈ t, K j) hsub u
        simp only [eqToIso_refl, Iso.refl_hom, CategoryTheory.id_apply] at hcast
        rw [hcast]
        have hstep : resRelH W (n + 1)
            (Set.subset_union_left : K a ⊆ K a ∪ ⋃ j ∈ t, K j) u = ζ a := hu1
        rw [hstep]
        exact Work.Orient.Port.eqToIso_congrArg_apply (M := W) (n := n + 1) ζ hia.symm
      · have h2 : resRelH W (n + 1) hsub u = resRelH W (n + 1) (Set.subset_biUnion_of_mem hi)
            (resRelH W (n + 1) (Set.subset_union_right :
              (⋃ j ∈ t, K j) ⊆ K a ∪ ⋃ j ∈ t, K j) u) := by
          rw [show resRelH W (n + 1) (Set.subset_biUnion_of_mem hi)
                (resRelH W (n + 1) (Set.subset_union_right :
                  (⋃ j ∈ t, K j) ⊆ K a ∪ ⋃ j ∈ t, K j) u)
              = ((resRelH W (n + 1) (Set.subset_biUnion_of_mem hi)).comp
                  (resRelH W (n + 1) (Set.subset_union_right :
                    (⋃ j ∈ t, K j) ⊆ K a ∪ ⋃ j ∈ t, K j))) u from rfl]
          rw [resRelH_comp' W (n + 1) (Set.subset_biUnion_of_mem hi)
            (Set.subset_union_right : (⋃ j ∈ t, K j) ⊆ K a ∪ ⋃ j ∈ t, K j) hsub]
        have hstep : resRelH W (n + 1)
            (Set.subset_union_right : (⋃ j ∈ t, K j) ⊆ K a ∪ ⋃ j ∈ t, K j) u = γt := hu2
        rw [h2, hstep, hγt i hi]
  obtain ⟨γ₀, hγ₀⟩ := key Finset.univ
  have hEq : (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i) = ⋃ i, K i := by
    ext x
    simp
  refine ⟨resRelH W (n + 1) (le_of_eq hEq.symm) γ₀, fun i => ?_⟩
  have hcomp : resRelH W (n + 1) (Set.subset_iUnion K i)
      (resRelH W (n + 1) (le_of_eq hEq.symm) γ₀)
      = resRelH W (n + 1) ((Set.subset_iUnion K i).trans (le_of_eq hEq.symm)) γ₀ :=
    LinearMap.congr_fun (resRelH_comp' W (n + 1) (Set.subset_iUnion K i)
      (le_of_eq hEq.symm) ((Set.subset_iUnion K i).trans (le_of_eq hEq.symm))) γ₀
  rw [hcomp, LinearMap.congr_fun (resRelH_congr_h W (n + 1)
    ((Set.subset_iUnion K i).trans (le_of_eq hEq.symm))
    (Set.subset_biUnion_of_mem (Finset.mem_univ i))) γ₀]
  exact hγ₀ i (Finset.mem_univ i)

end

end Work.Orient.Boundary
