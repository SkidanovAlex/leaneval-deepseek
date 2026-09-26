import Submission.Work.PlaneSlice.SliceRings
import Submission.Work.PlaneSlice.exists_arc_of_compactPreconnected_subset

/-!
# Building the rings of a plane slice from the classification of the level set

This file constructs a `Work.PlaneSlice.SliceRings` datum for a convex region `D` of a coordinate
plane `{y | y (σ 2) = l}` from the classification of the level set `F ∩ {y (σ 2) = l}` as a finite
disjoint union of embedded circles (`Work.Smooth.Morse.IsCircleUnion`), which the Sard +
`1`-manifold chapter supplies for almost every plane level
(`Work.PlaneSlice.ae_isCircleUnion_pardonSlice`).

The construction is where the geometry of the "open box slice" is used.  Let
`γ i : S¹ → F ∩ {plane}` be the circles of the level set.  The rings of `D` are those circles which
lie wholly inside `D`; for each of them:

* the *disc* is the Jordan disc of the circle, pushed into `ℝ³` along the chart
  `Work.Smooth.Plane.planeLift σ l` of the plane.  It lies in `D` because the bounded side of the
  projected curve lies in the convex set `planeProj σ '' D`
  (`Work.PlaneSlice.boundedSide_subset_of_convex`), and its interior is exactly the bounded side
  (`Work.Smooth.Jordan.plane_schoenflies_openDisc_eq`);
* a circle of the level set meeting the interior of that disc is *contained* in the disc
  (connectedness and the two-sidedness of a Jordan curve,
  `Work.Smooth.Jordan.plane_separation_preconnected_subset`), which gives `inside_subset`,
  `covers_interior` and the nesting rank `rank`;
* every *essential* loop of `F` inside `D` lies on one of the circles, and that circle lies in `D`:
  a loop lying in a circle of the level set but not on a circle contained in `D` misses a point of
  that circle (the part of the circle outside `D`), so it is contained in an arc of the circle
  (`Work.PlaneSlice.exists_arc_of_compactPreconnected_subset`) and is inessential
  (`Work.Smooth.Plane.Slicing.not_isEssential_of_range_subset_arc`).

## Main results

* `Work.PlaneSlice.nonempty_sliceRings_of_isCircleUnion` — the construction;
* `Work.PlaneSlice.sliceRings_pardonSlice` — the case of Pardon's box slice;
* `Work.PlaneSlice.ae_sliceRings_pardonSlice` — **the same for almost every plane level**, from
  item (1).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PlaneSlice

noncomputable section

variable {ψ : Submission.Diffeo} {σ : Equiv.Perm (Fin 3)} {l : ℝ} {D : Set R3}

/-- **The projection of a closed curve of the torus to the plane chart.** -/
def projCurve (σ : Equiv.Perm (Fin 3))
    (c : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)) :
    Work.Smooth.Jordan.PlaneCurve where
  γ := fun t => Work.Smooth.Plane.planeProj σ (c.γ t)
  cont := (Work.Smooth.Plane.continuous_planeProj σ).comp c.cont
  periodic := by
    intro t
    show Work.Smooth.Plane.planeProj σ (c.γ (t + 2 * Real.pi)) =
      Work.Smooth.Plane.planeProj σ (c.γ t)
    rw [c.periodic t]

@[simp] theorem projCurve_apply (σ : Equiv.Perm (Fin 3))
    (c : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)) (t : ℝ) :
    (projCurve σ c).γ t = Work.Smooth.Plane.planeProj σ (c.γ t) := rfl

/-- The projection of a simple closed curve of the plane `{y (σ 2) = l}` is a simple closed plane
curve. -/
theorem projCurve_isSimple {σ : Equiv.Perm (Fin 3)} {c : Work.CoreTopology.ClosedCurve
    (Work.Smooth.Morse.torus ψ)} (hc : Work.CoreTopology.IsSimple (Work.Smooth.Morse.torus ψ) c)
    (hmem : ∀ t : ℝ, c.γ t (σ 2) = l) : (projCurve σ c).IsSimple := by
  intro t ht t' ht' heq
  exact hc ht ht' (Work.Smooth.Plane.planeProj_injOn σ (hmem t) (hmem t') heq)

/-- Pushing a subset of the plane chart into `ℝ³` preserves images: the lift of the range of a
projected curve is the range of the curve. -/
theorem image_planeLift_range_projCurve {σ : Equiv.Perm (Fin 3)}
    {c : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)}
    (hmem : ∀ t : ℝ, c.γ t (σ 2) = l) :
    Work.Smooth.Plane.planeLift σ l '' Set.range (projCurve σ c).γ = Set.range c.γ := by
  ext y
  constructor
  · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, by
      rw [projCurve_apply]
      exact (Work.Smooth.Plane.planeLift_planeProj σ (hmem t)).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨(projCurve σ c).γ t, ⟨t, rfl⟩, ?_⟩
    simp only [projCurve_apply]
    exact Work.Smooth.Plane.planeLift_planeProj σ (hmem t)

end

end Work.PlaneSlice

namespace Work.PlaneSlice

noncomputable section

variable {ψ : Submission.Diffeo} {σ : Equiv.Perm (Fin 3)} {l : ℝ} {D : Set R3}

/-- The bounded side of a Schoenflies curve avoids the curve. -/
theorem boundedSide_subset_compl_trace {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies c) : S.V ⊆ c.traceᶜ := fun x hx => by
  rw [← S.union_eq]; exact Or.inr hx

/-- The range of a closed curve of the torus is compact. -/
theorem isCompact_range_closedCurve {P : Work.CoreTopology.ParamTorus}
    (c : Work.CoreTopology.ClosedCurve P) : IsCompact (Set.range c.γ) :=
  (isCompact_Icc.image_of_continuousOn c.cont.continuousOn).of_isClosed_subset
    (Work.InnermostDisk.isClosed_range_closedCurve c) (by
      rw [Work.CoreTopology.ClosedCurve.range_eq_image P c]
      exact Set.image_mono Set.Ico_subset_Icc_self)

/-- The two boundary parametrisations of the model disc agree. -/
theorem circlePoint_eq (θ : ℝ) :
    Work.CoreTopology.circlePoint θ = Work.Smooth.Jordan.circlePoint θ :=
  Subtype.ext rfl

/-- **The arc input of the construction** (proved in
`Submission/Work/PlaneSlice/exists_arc_of_compactPreconnected_subset.lean`): a compact preconnected
subset of a simple closed curve which misses a point of it is contained in an embedded arc of the
curve. -/
def ArcInput : Prop :=
  ∀ {c : ℝ → R3} (_ : Continuous c) (_ : Function.Periodic c (2 * Real.pi))
    (_ : Set.InjOn c (Set.Ico 0 (2 * Real.pi))) {K : Set R3}, IsCompact K → IsPreconnected K →
    K ⊆ Set.range c → ∀ {s : ℝ}, c s ∉ K →
    ∃ a : C(Work.Smooth.Plane.ArcInterval, R3), Function.Injective a ∧
      Set.range a ⊆ Set.range c ∧ K ⊆ Set.range a

/-- **The rings of the plane slice, from the classification of the level set.**

Let `D` be a convex subset of the coordinate plane `{y | y (σ 2) = l}` and let the level set
`F ∩ {y (σ 2) = l}` be a finite disjoint union of simple closed curves `γ i`.  Then `D` carries a
`Work.PlaneSlice.SliceRings` datum: the rings are the `γ i` that lie in `D`, each with its Jordan
disc inside `D`. -/
theorem nonempty_sliceRings_of_isCircleUnion_arc (harc : ArcInput) (hDconv : Convex ℝ D)
    (hplane : ∀ y ∈ D, y (σ 2) = l)
    (hCU : Work.Smooth.Morse.IsCircleUnion ψ
      (Work.Smooth.Morse.levelSet ψ (fun y : R3 => y (σ 2)) l)) :
    Nonempty (SliceRings ψ D) := by
  classical
  obtain ⟨n, γ, hγsimple, hγdisj, hγZ⟩ := hCU
  -- every circle of the level set lies in the cutting plane `{y (σ 2) = l}`
  have hplaneγ : ∀ (j : Fin n) (t : ℝ), (γ j).γ t (σ 2) = l := by
    intro j t
    have hmem : (γ j).γ t ∈ Work.Smooth.Morse.levelSet ψ (fun y : R3 => y (σ 2)) l := by
      rw [hγZ]
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_range_self t⟩
    exact hmem.2
  -- the projected curves
  let pc : Fin n → Work.Smooth.Jordan.PlaneCurve := fun j => projCurve σ (γ j)
  have hpc : ∀ j : Fin n, (pc j).IsSimple := fun j => projCurve_isSimple (hγsimple j) (hplaneγ j)
  let sch : (j : Fin n) → Work.Smooth.Jordan.PlaneSchoenflies (pc j) :=
    fun j => (Work.Smooth.Schoenflies.classicalInput (pc j) (hpc j)).some
  -- the index type of the rings
  let ι := {i : Fin n // ∀ t : ℝ, (γ i).γ t ∈ D}
  -- the convexity input: the bounded sides lie in `planeProj σ '' D`
  have hconv : Convex ℝ (Work.Smooth.Plane.planeProj σ '' D) :=
    Work.Smooth.Plane.planeProj_image_convex σ hDconv
  have htrace : ∀ i : ι, (pc i.1).trace ⊆ Work.Smooth.Plane.planeProj σ '' D := by
    rintro ⟨j, hj⟩ w hw
    obtain ⟨t, rfl⟩ := hw
    exact ⟨(γ j).γ t, hj t, rfl⟩
  have hVsub : ∀ i : ι, (sch i.1).V ⊆ Work.Smooth.Plane.planeProj σ '' D :=
    fun i => boundedSide_subset_of_convex (sch i.1) hconv (htrace i)
  -- the projected curves of distinct circles are disjoint
  have hdisj_proj : ∀ j k : Fin n, k ≠ j → Disjoint (Set.range (pc k).γ) (Set.range (pc j).γ) := by
    intro j k hkj
    rw [Set.disjoint_left]
    rintro w ⟨t, rfl⟩ ⟨t', ht'⟩
    have h1 : (γ j).γ t' = (γ k).γ t :=
      Work.Smooth.Plane.planeProj_injOn σ (hplaneγ j t') (hplaneγ k t) ht'
    exact Set.disjoint_left.mp (hγdisj k j hkj) (Set.mem_range_self t) ⟨t', h1⟩
  -- a circle of the level set meeting the bounded side of another lies in it
  have hsub_of_meets : ∀ j : Fin n, ∀ k : Fin n, k ≠ j →
      (Set.range (pc k).γ ∩ (sch j).V).Nonempty → Set.range (pc k).γ ⊆ (sch j).V := by
    intro j k hkj hmeet
    exact preconnected_subset_of_boundedSide (sch j).toPlaneSeparation
      (isPreconnected_range (pc k).cont) (hdisj_proj j k hkj) hmeet
  -- such a circle lies in `D`
  have hcurve_mem : ∀ i : ι, ∀ k : Fin n, Set.range (pc k).γ ⊆ (sch i.1).V →
      ∀ t : ℝ, (γ k).γ t ∈ D := by
    intro i k hsub t
    have h1 : (pc k).γ t ∈ Work.Smooth.Plane.planeProj σ '' D := hVsub i (hsub ⟨t, rfl⟩)
    have h2 := (Work.Smooth.Plane.planeLift_mem_iff σ hplane ((pc k).γ t)).mpr h1
    change Work.Smooth.Plane.planeLift σ l (Work.Smooth.Plane.planeProj σ ((γ k).γ t)) ∈ D at h2
    rw [Work.Smooth.Plane.planeLift_planeProj σ (hplaneγ k t)] at h2
    exact h2
  -- the pushed disc of a ring lies in `D`
  have hdisc_mem : ∀ i : ι, ∀ z : Work.InnermostDisk.Disc,
      Work.Smooth.Plane.planeLift σ l ((sch i.1).e z) ∈ D := by
    intro i z
    refine (Work.Smooth.Plane.planeLift_mem_iff σ hplane ((sch i.1).e z)).mpr ?_
    have hcl : (sch i.1).e z ∈ closure (sch i.1).V := by
      rw [← (sch i.1).range_e]; exact ⟨z, rfl⟩
    rw [closure_boundedSide_eq (sch i.1)] at hcl
    rcases hcl with h | h
    · exact hVsub i h
    · exact htrace i h
  -- the point of the bounded side, for an interior point `z`
  have hdisc_V : ∀ i : ι, ∀ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 →
      (sch i.1).e z ∈ (sch i.1).V := by
    intro i z hz
    rw [← image_openDisc_eq_boundedSide (sch i.1)]
    exact ⟨z, hz, rfl⟩
  -- membership of the pushed point in the projected range
  have hproj_eq : ∀ (k : Fin n) (t : ℝ) (w : ℂ),
      (γ k).γ t = Work.Smooth.Plane.planeLift σ l w → (pc k).γ t = w := by
    intro k t w hw
    change Work.Smooth.Plane.planeProj σ ((γ k).γ t) = w
    rw [hw]
    exact Work.Smooth.Plane.planeProj_planeLift σ l w
  let RANK : ι → ℕ := fun i =>
    (Finset.univ.filter (fun j : ι => Set.range (pc j.1).γ ⊆ (sch i.1).V)).card
  refine ⟨{
    ι := ι
    fintype := inferInstance
    c := fun i => γ i.1
    simple := fun i => hγsimple i.1
    disjoint := ?_
    mem := fun i => i.2
    disc := fun i => ⟨fun z => Work.Smooth.Plane.planeLift σ l ((sch i.1).e z),
      (Work.Smooth.Plane.continuous_planeLift σ l).comp (sch i.1).e.continuous⟩
    disc_inj := ?_
    disc_boundary := ?_
    disc_mem := ?_
    covers_interior := ?_
    covers_essential := ?_
    inside_subset := ?_
    rank := RANK
    inside := ?_ }⟩
  · -- distinct rings are disjoint
    intro i j hij
    exact hγdisj i.1 j.1 (fun h => hij (Subtype.ext h))
  · -- the disc is embedded
    intro i z z' hzz'
    exact (sch i.1).inj (Work.Smooth.Plane.planeLift_injective σ l hzz')
  · -- its boundary is the ring
    intro i θ
    show Work.Smooth.Plane.planeLift σ l ((sch i.1).e (Work.CoreTopology.circlePoint θ)) =
      (γ i.1).γ θ
    rw [circlePoint_eq θ, (sch i.1).boundary θ]
    exact Work.Smooth.Plane.planeLift_planeProj σ (hplaneγ i.1 θ)
  · -- the disc lies in `D`
    intro i z
    exact hdisc_mem i z
  · -- the interior of a disc meets `F` only along the rings
    intro i z hz hc
    have hzV : (sch i.1).e z ∈ (sch i.1).V := hdisc_V i z hz
    have hlev : Work.Smooth.Plane.planeLift σ l ((sch i.1).e z) ∈
        Work.Smooth.Morse.levelSet ψ (fun y : R3 => y (σ 2)) l :=
      ⟨hc, Work.Smooth.Plane.planeLift_apply_two σ l ((sch i.1).e z)⟩
    rw [hγZ] at hlev
    obtain ⟨k, t, hkt⟩ := Set.mem_iUnion.mp hlev
    have hki : k ≠ i.1 := by
      intro hEq
      rw [hEq] at hkt
      exact boundedSide_subset_compl_trace (sch i.1) hzV ⟨t, hproj_eq i.1 t _ hkt⟩
    have hmeet : (Set.range (pc k).γ ∩ (sch i.1).V).Nonempty :=
      ⟨(sch i.1).e z, ⟨⟨t, hproj_eq k t _ hkt⟩, hzV⟩⟩
    have hsub := hsub_of_meets i.1 k hki hmeet
    have hkD := hcurve_mem i k hsub
    exact ⟨⟨k, hkD⟩, ⟨t, hkt⟩⟩
  · -- an essential loop of `D` lies on a ring
    intro γ' hγ'ess hγ'D
    have hlev : ∀ t : ℝ, γ'.γ t ∈ Work.Smooth.Morse.levelSet ψ (fun y : R3 => y (σ 2)) l :=
      fun t => ⟨γ'.mem t, by simpa using hplane (γ'.γ t) (hγ'D t)⟩
    have hpre : IsPreconnected (Set.range γ'.γ) := isPreconnected_range γ'.cont
    have hne : (Set.range γ'.γ).Nonempty := ⟨γ'.γ 0, Set.mem_range_self 0⟩
    have hsub : Set.range γ'.γ ⊆ ⋃ j, Set.range (γ j).γ := by
      rintro x ⟨t, rfl⟩
      rw [← hγZ]
      exact hlev t
    obtain ⟨k, hk⟩ := Work.InnermostDisk.exists_subset_of_preconnected_iUnion hpre hne
      (fun j => Set.range (γ j).γ) (fun j => Work.InnermostDisk.isClosed_range_closedCurve (γ j))
      (fun j j' hjj' => hγdisj j j' hjj') hsub
    have hmemD : ∀ t : ℝ, (γ k).γ t ∈ D := by
      by_contra hcon
      push Not at hcon
      obtain ⟨t₀, ht₀⟩ := hcon
      have hmiss : (γ k).γ t₀ ∉ Set.range γ'.γ := by
        rintro ⟨t, ht⟩
        exact ht₀ (ht ▸ hγ'D t)
      obtain ⟨a, ha_inj, ha_sub, ha_cover⟩ :=
        harc (γ k).cont (γ k).periodic (hγsimple k) (isCompact_range_closedCurve γ') hpre hk hmiss
      exact absurd hγ'ess (Work.Smooth.Plane.Slicing.not_isEssential_of_range_subset_arc ha_inj
        (fun s => by
          obtain ⟨s', hs'⟩ := ha_sub (Set.mem_range_self s)
          rw [← hs']; exact (γ k).mem s')
        (fun t => ha_cover (Set.mem_range_self t)))
    exact ⟨⟨k, hmemD⟩, hk⟩
  · -- a ring meeting the interior of the disc of another is contained in it
    intro i j hcon
    obtain ⟨z, hz, hzj⟩ := hcon
    have hzV : (sch i.1).e z ∈ (sch i.1).V := hdisc_V i z hz
    obtain ⟨t, ht⟩ := hzj
    have hji : j.1 ≠ i.1 := by
      intro hEq
      rw [hEq] at ht
      exact boundedSide_subset_compl_trace (sch i.1) hzV ⟨t, hproj_eq i.1 t _ ht⟩
    have hmeet : (Set.range (pc j.1).γ ∩ (sch i.1).V).Nonempty :=
      ⟨(sch i.1).e z, ⟨⟨t, hproj_eq j.1 t _ ht⟩, hzV⟩⟩
    have hsub := hsub_of_meets i.1 j.1 hji hmeet
    intro y hy
    obtain ⟨t', rfl⟩ := hy
    have h1 : (pc j.1).γ t' ∈ Set.range (sch i.1).e := by
      rw [(sch i.1).range_e]
      exact subset_closure (hsub ⟨t', rfl⟩)
    obtain ⟨z', hz'⟩ := h1
    refine ⟨z', ?_⟩
    change Work.Smooth.Plane.planeLift σ l ((sch i.1).e z') = (γ j.1).γ t'
    rw [hz']
    change Work.Smooth.Plane.planeLift σ l (Work.Smooth.Plane.planeProj σ ((γ j.1).γ t')) =
      (γ j.1).γ t'
    exact Work.Smooth.Plane.planeLift_planeProj σ (hplaneγ j.1 t')
  · -- the nesting rank
    intro i j hcon
    obtain ⟨z, hz, hzj⟩ := hcon
    have hzV : (sch i.1).e z ∈ (sch i.1).V := hdisc_V i z hz
    obtain ⟨t, ht⟩ := hzj
    have hji : j.1 ≠ i.1 := by
      intro hEq
      rw [hEq] at ht
      exact boundedSide_subset_compl_trace (sch i.1) hzV ⟨t, hproj_eq i.1 t _ ht⟩
    have hmeet : (Set.range (pc j.1).γ ∩ (sch i.1).V).Nonempty :=
      ⟨(sch i.1).e z, ⟨⟨t, hproj_eq j.1 t _ ht⟩, hzV⟩⟩
    have hsub : Set.range (pc j.1).γ ⊆ (sch i.1).V := hsub_of_meets i.1 j.1 hji hmeet
    have hnest : (sch j.1).V ⊆ (sch i.1).V :=
      nested_boundedSide (sch i.1).toPlaneSeparation (sch j.1).toPlaneSeparation hsub
    have hjmem : j ∈ Finset.univ.filter (fun k : ι => Set.range (pc k.1).γ ⊆ (sch i.1).V) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hsub
    have hjnot : j ∉ Finset.univ.filter (fun k : ι => Set.range (pc k.1).γ ⊆ (sch j.1).V) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hmem
      exact boundedSide_subset_compl_trace (sch j.1) (hmem ⟨0, rfl⟩) ⟨0, rfl⟩
    show RANK j < RANK i
    refine Finset.card_lt_card ⟨?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hk.trans hnest
    · intro hcon'
      exact hjnot (hcon' hjmem)

/-- **The rings of the plane slice, from the classification of the level set**
(the unconditional form, with the arc input discharged). -/
theorem nonempty_sliceRings_of_isCircleUnion (hDconv : Convex ℝ D)
    (hplane : ∀ y ∈ D, y (σ 2) = l)
    (hCU : Work.Smooth.Morse.IsCircleUnion ψ
      (Work.Smooth.Morse.levelSet ψ (fun y : R3 => y (σ 2)) l)) :
    Nonempty (SliceRings ψ D) :=
  nonempty_sliceRings_of_isCircleUnion_arc
    (fun {c} hc hper hinj {K} hKc hKp hKs {s} hs =>
      exists_arc_of_compactPreconnected_subset hc hper hinj hKc hKp hKs hs)
    hDconv hplane hCU


end

end Work.PlaneSlice
