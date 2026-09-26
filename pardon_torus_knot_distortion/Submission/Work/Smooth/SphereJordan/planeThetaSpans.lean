import Mathlib
import Submission.Work.Smooth.SphereJordan.thetaSides
import Submission.Work.Smooth.SphereJordan.planeThetaCurves
import Submission.Work.Smooth.SphereJordan.half_spans_of_plane
import Submission.Work.SphereJordan.incrOn
import Submission.Work.SphereJordan.odd_windNumber_of_mem_V
import Submission.Work.Smooth.SphereJordan.DiscCurve
import Submission.Work.Smooth.SphereJordan.discCurveSpans
import Submission.Work.Smooth.SphereJordan.thetaTwoHalvesSphereOfPlane

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-- **The bounded side of a plane curve is independent of the Jordan separation datum.** -/
theorem planeSeparation_V_eq {c : Work.Smooth.Jordan.PlaneCurve}
    (d d' : Work.Smooth.Jordan.PlaneSeparation c) : d.V = d'.V := by
  rcases Work.Smooth.Jordan.plane_separation_eq d d' with ⟨-, h⟩ | ⟨-, h⟩
  · exact h
  · exfalso
    obtain ⟨C, hC⟩ := d.bounded_V.exists_norm_le
    obtain ⟨x, hxU, hxC⟩ := Work.Smooth.Jordan.plane_separation_unbounded d' (C + 1)
    have hxV : x ∈ d.V := by rw [h]; exact hxU
    exact absurd (hC x hxV) (by linarith)

/-- The target set of `planeThetaSpans` is the complement of the theta graph, read in `ℂ`. -/
theorem theta_complement_eq (D₁ D₂ : Set ℂ) (α β : C(Set.Icc (0 : ℝ) 1, ℂ)) :
    {x : ℂ | ((x : ℂ) : Work.Smooth.SphereJordan.RiemannSphere) ∉
        ((↑) '' D₁ ∪ (↑) '' D₂ ∪
          Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((α t : ℂ) : Work.Smooth.SphereJordan.RiemannSphere)) ∪
          Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((β t : ℂ) : Work.Smooth.SphereJordan.RiemannSphere)))} =
      (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ := by
  ext x
  have h1 : ((x : ℂ) : RiemannSphere) ∈ ((↑) : ℂ → RiemannSphere) '' D₁ ↔ x ∈ D₁ := by
    constructor
    · rintro ⟨z, hz, hzy⟩
      rw [← OnePoint.coe_injective hzy]
      exact hz
    · intro hx
      exact ⟨x, hx, rfl⟩
  have h2 : ((x : ℂ) : RiemannSphere) ∈ ((↑) : ℂ → RiemannSphere) '' D₂ ↔ x ∈ D₂ := by
    constructor
    · rintro ⟨z, hz, hzy⟩
      rw [← OnePoint.coe_injective hzy]
      exact hz
    · intro hx
      exact ⟨x, hx, rfl⟩
  have h3 : ((x : ℂ) : RiemannSphere) ∈
      Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((α t : ℂ) : RiemannSphere)) ↔
      x ∈ Set.range α := by
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, OnePoint.coe_injective ht⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
  have h4 : ((x : ℂ) : RiemannSphere) ∈
      Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((β t : ℂ) : RiemannSphere)) ↔
      x ∈ Set.range β := by
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, OnePoint.coe_injective ht⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
  simp only [Set.mem_setOf_eq, Set.mem_union, not_or, Set.mem_compl_iff, h1, h2, h3, h4]

/-! ## Remaining gap

The two lemmas below isolate the remaining geometric content (they are not yet proved):

* `closure_coe_unbounded_side` : from the two-disc datum `T` of `planeTwoDiscs` (a datum for the
  curve `t ↦ ↑(γ t)` in the Riemann sphere) one gets two disc maps `T.e`, `T.e'`; their open sides
  `T.openSide`, `T.openSide'` are preconnected, open, disjoint and cover the complement of the
  trace, hence (being `IsPreconnected`) each of them is contained in one of the two plane pieces
  `↑''S.U ∪ {∞}` and `↑''S.V`; since `S.U` is unbounded the point `∞` lies in `↑''S.U ∪ {∞}`,
  which decides which of `T.e`, `T.e'` has range `closure (↑''S.U)` (the range of either is the
  union of its open side with the trace, and the trace is contained in the closure of the side by
  the parametrisation).

* `thetaSideDetermination` (file `thetaSides.lean`): the side determination for the theta graph.
  The four four-arc curves are already constructed in `planeThetaCurves.lean`
  (`ThetaSetup.cur i j`, with `cur_isSimple`, `cur_range`, `cur_subset`, `range_α_subset_cur`,
  `range_β_subset_cur`), and `exists_thetaSetup` builds the configuration from the raw hypotheses.
  What remains is to decide, for each of the two discs, which of the two boundary arcs is the one
  that bounds the side of the chord curve `thetaPlaneJordanCurve` containing the disc; then the
  bounded side of the curve using the two inner arcs is the hole of the theta graph and the
  unbounded side of the curve using the two outer arcs is the unbounded component.  A purely
  metric way to decide it (no local topology) is to use the winding numbers `wd` of
  `radialWinding`: for `x ∈ int D₁` the two curves `cur false j`, `cur true j` have winding numbers
  about `x` differing by the winding number of the boundary circle of `D₁`, which is odd (and in
  particular non-zero) by the chord witness; while the winding number vanishes on the unbounded
  side.  -/

/-- The unbounded side of a plane separation is unbounded. -/
theorem not_isBounded_U {c : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation c) : ¬ Bornology.IsBounded S.U := by
  intro hb
  obtain ⟨C, hC⟩ := hb.subset_closedBall (0 : ℂ)
  obtain ⟨x, hxU, hxC⟩ := Work.Smooth.Jordan.plane_separation_unbounded S (C + 1)
  have h1 := hC hxU
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  linarith

/-- `∞` lies in the closure of the image of a set of `ℂ` exactly when that set is unbounded. -/
theorem mem_closure_infty_image_coe_iff (s : Set ℂ) :
    (OnePoint.infty : Work.Smooth.SphereJordan.RiemannSphere)
        ∈ closure (((↑) : ℂ → Work.Smooth.SphereJordan.RiemannSphere) '' s) ↔
      ¬ Bornology.IsBounded s := by
  constructor
  · intro h hb
    obtain ⟨C, hC⟩ := hb.subset_closedBall (0 : ℂ)
    have hV : (OnePoint.some '' (Metric.closedBall (0 : ℂ) C)ᶜ ∪
        {OnePoint.infty} : Set Work.Smooth.SphereJordan.RiemannSphere)
        ∈ nhds (OnePoint.infty : Work.Smooth.SphereJordan.RiemannSphere) :=
      OnePoint.hasBasis_nhds_infty.mem_iff.mpr
        ⟨Metric.closedBall (0 : ℂ) C, ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 C⟩,
          subset_rfl⟩
    obtain ⟨y, hyV, hyS⟩ := mem_closure_iff_nhds.mp h _ hV
    rcases hyV with ⟨w, hw, rfl⟩ | hw
    · obtain ⟨z, hz, hzw⟩ := hyS
      have hwz : w = z := OnePoint.coe_injective hzw.symm
      exact hw (by rw [hwz]; exact hC hz)
    · obtain ⟨z, hz, hzy⟩ := hyS
      have hyinf : y = OnePoint.infty := by simpa using hw
      exact OnePoint.coe_ne_infty z (by rw [hzy]; exact hyinf)
  · intro hb
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨K, ⟨hKc, hKcomp⟩, hKV⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hV
    obtain ⟨R, hR⟩ := hKcomp.isBounded.exists_norm_le
    have hex : ∃ x ∈ s, R < ‖x‖ := by
      by_contra hcon
      push Not at hcon
      exact hb (Metric.isBounded_closedBall.subset (fun x hx => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hcon x hx))
    obtain ⟨x, hx, hxR⟩ := hex
    refine ⟨(x : Work.Smooth.SphereJordan.RiemannSphere), hKV (Or.inl ⟨x, ?_, rfl⟩),
      ⟨x, hx, rfl⟩⟩
    intro hxK
    exact absurd (hR x hxK) (not_le.mpr hxR)

/-- The union of a preconnected set with a point of its closure is preconnected. -/
theorem isPreconnected_union_singleton_of_mem_closure {α : Type*} [TopologicalSpace α]
    {s : Set α} {x : α} (hs : IsPreconnected s) (hx : x ∈ closure s) :
    IsPreconnected (s ∪ {x}) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsub hdisj
  have hsu : s ⊆ u ∪ v := fun y hy => hsub (Or.inl hy)
  have hxn : s ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy, hyuv⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) y ⟨Or.inl hy, hyuv⟩
  have hxuv : x ∈ u ∪ v := hsub (Or.inr rfl)
  rcases isPreconnected_iff_subset_of_disjoint.mp hs u v hu hv hsu hxn with h | h
  · refine Or.inl ?_
    rcases hxuv with hxu | hxv
    · rintro y (hy | hy)
      · exact h hy
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hxu
    · exfalso
      obtain ⟨z, hzv, hzs⟩ := mem_closure_iff.mp hx v hv hxv
      exact (Set.eq_empty_iff_forall_notMem.mp hxn) z ⟨hzs, ⟨h hzs, hzv⟩⟩
  · refine Or.inr ?_
    rcases hxuv with hxu | hxv
    · exfalso
      obtain ⟨z, hzu, hzs⟩ := mem_closure_iff.mp hx u hu hxu
      exact (Set.eq_empty_iff_forall_notMem.mp hxn) z ⟨hzs, ⟨hzu, h hzs⟩⟩
    · rintro y (hy | hy)
      · exact h hy
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hxv

/-- **A preconnected set contained in the union of two disjoint open sets and meeting the first of
them is contained in the first, provided it misses the second somewhere.** -/
theorem subset_of_subset_union_of_mem_notMem {α : Type*} [TopologicalSpace α] {A u v : Set α}
    {x : α} (hA : IsPreconnected A) (hu : IsOpen u) (hv : IsOpen v) (hd : Disjoint u v)
    (hcov : A ⊆ u ∪ v) (hxA : x ∈ A) (hxv : x ∉ v) : A ⊆ u := by
  have hd' : A ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨-, hyu, hyv⟩
    exact (Set.disjoint_left.mp hd) hyu hyv
  rcases isPreconnected_iff_subset_of_disjoint.mp hA u v hu hv hcov hd' with h | h
  · exact h
  · exact absurd (h hxA) hxv

/-- **The disc of a two-disc datum that spans the unbounded side.**  Let `γ` be a simple closed
plane curve, `S` a Jordan separation of `γ` and `T` a two-disc decomposition of `γ` in the Riemann
sphere.  Then the disc of `T` whose image contains `∞` has range the closure of the image, under the
coercion `ℂ ↪ ℂ ∪ {∞}`, of the unbounded side `S.U`. -/
theorem exists_disc_spanning_unbounded {γ : ℝ → ℂ} {hcont : Continuous γ}
    {hper : Function.Periodic γ (2 * Real.pi)}
    (S : Work.Smooth.Jordan.PlaneSeparation ⟨γ, hcont, hper⟩)
    (T : TwoDiscs (fun t : ℝ => (γ t : RiemannSphere))) :
    ∃ Ψ : C(Disc, RiemannSphere), Function.Injective Ψ ∧
      Set.range Ψ = closure (((↑) : ℂ → RiemannSphere) '' S.U) := by
  classical
  have hUnb : ¬ Bornology.IsBounded S.U := not_isBounded_U S
  have hinfcl : (OnePoint.infty : RiemannSphere) ∈
      closure (((↑) : ℂ → RiemannSphere) '' S.U) :=
    (mem_closure_infty_image_coe_iff S.U).mpr hUnb
  have hApre : IsPreconnected (((↑) : ℂ → RiemannSphere) '' S.U) :=
    S.preconn_U.image _ OnePoint.continuous_coe.continuousOn
  have hA'pre : IsPreconnected (((↑) : ℂ → RiemannSphere) '' S.U ∪ {OnePoint.infty}) :=
    isPreconnected_union_singleton_of_mem_closure hApre hinfcl
  have hA'open : IsOpen (((↑) : ℂ → RiemannSphere) '' S.U ∪ {OnePoint.infty}) :=
    planeTwoDiscs_isOpen_coe_union_infty S.isOpen_U
      (planeTwoDiscs_norm_bound ⟨γ, hcont, hper⟩ S)
  have hBopen : IsOpen (((↑) : ℂ → RiemannSphere) '' S.V) :=
    OnePoint.isOpen_image_coe.mpr S.isOpen_V
  have hinftrace : (OnePoint.infty : RiemannSphere) ∉
      Set.range (fun t : ℝ => (γ t : RiemannSphere)) :=
    fun ⟨t, ht⟩ => OnePoint.coe_ne_infty (γ t) ht
  -- the two plane pieces with `∞` adjoined to the unbounded one
  have hUtrace : ∀ u ∈ S.U, u ∉ Set.range γ := by
    intro u hu hmem
    have h3 : u ∈ S.U ∪ S.V := Or.inl hu
    rw [S.union_eq] at h3
    exact h3 hmem
  have hVtrace : ∀ v ∈ S.V, v ∉ Set.range γ := by
    intro v hv hmem
    have h3 : v ∈ S.U ∪ S.V := Or.inr hv
    rw [S.union_eq] at h3
    exact h3 hmem
  have hcov : ((↑) : ℂ → RiemannSphere) '' S.U ∪ {OnePoint.infty} ∪
      ((↑) : ℂ → RiemannSphere) '' S.V =
      (Set.range (fun t : ℝ => (γ t : RiemannSphere)))ᶜ := by
    apply Set.Subset.antisymm
    · rintro y ((hy | hy) | hy)
      · rintro ⟨t, ht⟩
        obtain ⟨u, hu, hueq⟩ := hy
        refine hUtrace u hu ?_
        rw [OnePoint.coe_injective (hueq.trans ht.symm)]
        exact ⟨t, rfl⟩
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact fun ⟨t, ht⟩ => OnePoint.coe_ne_infty (γ t) ht
      · rintro ⟨t, ht⟩
        obtain ⟨v, hv, hveq⟩ := hy
        refine hVtrace v hv ?_
        rw [OnePoint.coe_injective (hveq.trans ht.symm)]
        exact ⟨t, rfl⟩
    · intro y hy
      by_cases hinf : y = OnePoint.infty
      · exact Or.inl (Or.inr (by rw [hinf]; rfl))
      · obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hinf
        have hz' : z ∉ Set.range γ := by
          intro hmem
          apply hy
          rw [← hz]
          obtain ⟨t, ht⟩ := hmem
          exact ⟨t, by show (γ t : RiemannSphere) = (z : RiemannSphere); rw [ht]⟩
        have hzUV : z ∈ S.U ∪ S.V := by
          rw [S.union_eq]
          exact hz'
        rcases hzUV with h | h
        · exact Or.inl (Or.inl ⟨z, h, hz⟩)
        · exact Or.inr ⟨z, h, hz⟩
  have hdisjA'B : Disjoint (((↑) : ℂ → RiemannSphere) '' S.U ∪ {OnePoint.infty})
      (((↑) : ℂ → RiemannSphere) '' S.V) := by
    rw [Set.disjoint_left]
    rintro y hy hz
    rcases hy with ⟨u, huU, hueq⟩ | hy
    · obtain ⟨v, hvV, hveq⟩ := hz
      have huv : u = v := OnePoint.coe_injective (hueq.trans hveq.symm)
      exact Set.disjoint_left.mp S.disjoint_UV huU (huv ▸ hvV)
    · rw [Set.mem_singleton_iff] at hy
      obtain ⟨v, hvV, hveq⟩ := hz
      exact OnePoint.coe_ne_infty v (hveq.trans hy)
  -- the two open sides of `T`
  have hSidesCov : T.outSide OnePoint.infty ∪ T.inSide OnePoint.infty =
      (Set.range (fun t : ℝ => (γ t : RiemannSphere)))ᶜ := by
    apply Set.Subset.antisymm
    · rintro y (h | h) hyc
      · exact (Set.disjoint_left.mp (T.disjoint_outSide_range OnePoint.infty)) h hyc
      · exact (Set.disjoint_left.mp (T.disjoint_inSide_range OnePoint.infty)) h hyc
    · intro y hy
      have h1 : y ∈ T.inSide OnePoint.infty ∪
          Set.range (fun t : ℝ => (γ t : RiemannSphere)) ∪ T.outSide OnePoint.infty := by
        rw [T.inSide_union_range_union_outSide OnePoint.infty]
        trivial
      rcases h1 with (h | h) | h
      · exact Or.inr h
      · exact absurd h hy
      · exact Or.inl h
  have hSidesDisj : Disjoint (T.outSide OnePoint.infty) (T.inSide OnePoint.infty) :=
    (T.disjoint_inSide_outSide OnePoint.infty).symm
  have hOutInf : OnePoint.infty ∈ T.outSide OnePoint.infty :=
    T.mem_outSide_self OnePoint.infty hinftrace
  have hInNotInf : OnePoint.infty ∉ T.inSide OnePoint.infty :=
    fun h => (Set.disjoint_left.mp (T.disjoint_inSide_outSide OnePoint.infty)) h hOutInf
  -- the two decompositions of the complement of the trace coincide
  have hA'cov : ((↑) : ℂ → RiemannSphere) '' S.U ∪ {OnePoint.infty} ⊆
      T.outSide OnePoint.infty ∪ T.inSide OnePoint.infty := by
    intro y hy
    have h1 : y ∈ (Set.range (fun t : ℝ => (γ t : RiemannSphere)))ᶜ := by
      rw [← hcov]
      exact Or.inl hy
    rw [← hSidesCov] at h1
    exact h1
  have hOutcov : T.outSide OnePoint.infty ⊆
      ((↑) : ℂ → RiemannSphere) '' S.U ∪ {OnePoint.infty} ∪
        ((↑) : ℂ → RiemannSphere) '' S.V := by
    intro y hy
    have h1 : y ∈ (Set.range (fun t : ℝ => (γ t : RiemannSphere)))ᶜ := by
      rw [← hSidesCov]
      exact Or.inl hy
    rw [← hcov] at h1
    exact h1
  have hA'sub : ((↑) : ℂ → RiemannSphere) '' S.U ∪ {OnePoint.infty} ⊆
      T.outSide OnePoint.infty :=
    subset_of_subset_union_of_mem_notMem hA'pre (T.isOpen_outSide OnePoint.infty)
      (T.isOpen_inSide OnePoint.infty) hSidesDisj hA'cov (Or.inr rfl) hInNotInf
  have hOutsub : T.outSide OnePoint.infty ⊆
      ((↑) : ℂ → RiemannSphere) '' S.U ∪ {OnePoint.infty} :=
    subset_of_subset_union_of_mem_notMem (T.outSide_preconnected OnePoint.infty) hA'open
      hBopen hdisjA'B hOutcov hOutInf OnePoint.infty_notMem_image_coe
  have hOutEq : T.outSide OnePoint.infty =
      ((↑) : ℂ → RiemannSphere) '' S.U ∪ {OnePoint.infty} :=
    Set.Subset.antisymm hOutsub hA'sub
  have hcl : closure (((↑) : ℂ → RiemannSphere) '' S.U ∪ {OnePoint.infty}) =
      closure (((↑) : ℂ → RiemannSphere) '' S.U) := by
    apply Set.Subset.antisymm
    · apply closure_minimal _ isClosed_closure
      intro y hy
      rcases hy with hy | hy
      · exact subset_closure hy
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hinfcl
    · exact closure_mono Set.subset_union_left
  have hr : closure (T.outSide OnePoint.infty) = Set.range (T.outer OnePoint.infty) := by
    rw [T.closure_outSide OnePoint.infty, T.compl_inSide OnePoint.infty, Set.union_comm,
      ← T.range_outer_eq OnePoint.infty]
  exact ⟨T.outer OnePoint.infty, T.outer_injective OnePoint.infty,
    by rw [← hr, hOutEq, ← hcl]⟩

/-- **The closure in the sphere of (the image of) the unbounded side of a plane separation is the
image of the model disc**, namely the outside disc of the two-disc datum of the curve: the
two-disc datum of `planeTwoDiscs` has one disc containing `∞`, and that disc is the outside one
(`exists_disc_spanning_unbounded`). -/
theorem closure_coe_unbounded_side (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : ℝ → ℂ} (hcont : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (S : Work.Smooth.Jordan.PlaneSeparation ⟨γ, hcont, hper⟩) :
    ∃ Ψ : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
      Function.Injective Ψ ∧
        Set.range Ψ = closure (((↑) : ℂ → Work.Smooth.SphereJordan.RiemannSphere) '' S.U) := by
  obtain ⟨T⟩ := planeTwoDiscs h hcont hper hinj
  exact exists_disc_spanning_unbounded S T

theorem planeThetaSpans (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {D₁ D₂ : Set ℂ}
    (hD₁ : ∃ f : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, ℂ)) (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩) :
    ∃ P₁ P₂ : Set ℂ,
      P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = {x : ℂ | ((x : ℂ) : Work.Smooth.SphereJordan.RiemannSphere) ∉
        ((↑) '' D₁ ∪ (↑) '' D₂ ∪ Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((α t : ℂ) : Work.Smooth.SphereJordan.RiemannSphere)) ∪
         Set.range (fun t : Set.Icc (0 : ℝ) 1 => ((β t : ℂ) : Work.Smooth.SphereJordan.RiemannSphere)))} ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ ∧
      (∃ Φ : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
        Function.Injective Φ ∧
          Set.range Φ = closure (((↑) : ℂ → Work.Smooth.SphereJordan.RiemannSphere) '' P₁)) ∧
      (∃ Ψ : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
        Function.Injective Ψ ∧
          Set.range Ψ = closure (((↑) : ℂ → Work.Smooth.SphereJordan.RiemannSphere) '' P₂)) := by
  obtain ⟨J₁, J₂, S₁, S₂, hJ₁, hJ₂, hsub₁, hsub₂, hα₁, hβ₁, hα₂, hβ₂, hAV, hAU, hdj, hun⟩ :=
    thetaSideDetermination h hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep
      hαβ₀ hαβ₁
  refine ⟨S₁.V, S₂.U, S₁.nonempty_V, S₂.nonempty_U, S₁.isOpen_V, S₂.isOpen_U, hdj, ?_,
    S₁.preconn_V, S₂.preconn_U, ?_, ?_⟩
  · rw [hun, theta_complement_eq]
  · -- the bounded side spans a disc
    obtain ⟨S₁'⟩ := h J₁ hJ₁
    have hV : S₁.V = S₁'.toPlaneSeparation.V :=
      planeSeparation_V_eq S₁ S₁'.toPlaneSeparation
    have hrange : Set.range (fun z : Disc => ((S₁'.e z : ℂ) : RiemannSphere))
        = closure (((↑) : ℂ → RiemannSphere) '' S₁.V) := by
      rw [range_coe_comp (F := S₁'.e)]
      have h1 : Set.range S₁'.e = closure S₁.V := by
        rw [S₁'.range_e]
        rw [hV]
      rw [h1]
      refine image_closure_coe_eq_closure_image ?_
      rw [Metric.isCompact_iff_isClosed_bounded]
      exact ⟨isClosed_closure, S₁.bounded_V.closure⟩
    exact ⟨⟨fun z => ((S₁'.e z : ℂ) : RiemannSphere),
      OnePoint.continuous_coe.comp S₁'.e.continuous⟩,
      fun a b hab => S₁'.inj (OnePoint.coe_injective hab), hrange⟩
  · exact closure_coe_unbounded_side h J₂.cont J₂.periodic hJ₂ S₂

end

end Work.Smooth.SphereJordan
