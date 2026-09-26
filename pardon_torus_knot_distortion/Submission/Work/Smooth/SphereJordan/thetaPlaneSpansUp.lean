import Mathlib
import Submission.Work.Smooth.SphereJordan.thetaFoundation
import Submission.Work.Smooth.SphereJordan.thetaOddCore
import Submission.Work.Smooth.SphereJordan.thetaFlip
import Submission.Work.Smooth.SphereJordan.planeThetaCurves
import Submission.Work.Smooth.SphereJordan.half_spans_of_plane
import Submission.Work.Smooth.SphereJordan.discCurveSpans
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.Jordan.plane_separation_eq

/-!
# The planar theta graph: two discs joined by two arcs bound two closed discs

A self-contained copy of the proof of `Work.Smooth.SphereJordan.planeThetaSpans`, with every
auxiliary result placed in the fresh namespace `Work.Smooth.SphereJordan.ThetaPlaneUp` so that it
can be imported by the target module without an import cycle.  See the file
history for the detailed description of the replacements used.
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

namespace ThetaPlaneUp

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
  simp only [Set.mem_ofPred_eq, Set.mem_union, not_or, Set.mem_compl_iff, h1, h2, h3, h4]

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


/-! ## The winding-number lemmas of the side determination

These are the copies of the corresponding lemmas of `thetaWinding.lean` with the two "diff" relations
replaced by their `thetaFlip` versions (`ThetaFlip.windNumber_cur_arcA_flip`,
`ThetaFlip.windNumber_cur_arcB_flip`) and `windNumber_eq_zero_or_odd` replaced by
`ThetaOdd.thetaWindZeroOrOdd`. -/

/-- **A point outside the image of a disc map is wound zero times round by its boundary curve.** -/
theorem windNumber_discCurve_eq_zero (h : PlaneHypothesis) {F : C(Disc, ℂ)}
    (hF : Function.Injective F) {z : ℂ} (hz : z ∉ Set.range F) :
    windNumber (discCurve F).γ (discCurve F).cont z = 0 := by
  obtain ⟨S⟩ := h (discCurve F) (discCurve_isSimple hF)
  obtain ⟨-, hopen⟩ := discCurveSpans hF S
  have hztrace : z ∉ (discCurve F).trace := by
    rintro ⟨θ, hθ⟩
    exact hz ⟨circlePoint θ, hθ⟩
  have hzV : z ∉ S.V := by
    rw [← hopen]
    rintro ⟨w, -, rfl⟩
    exact hz ⟨w, rfl⟩
  have hzU : z ∈ S.U := by
    have hmem : z ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hztrace
    rcases hmem with h | h
    · exact h
    · exact absurd h hzV
  exact windNumber_eq_zero_of_mem_U S.toPlaneSeparation hzU

/-- **The winding number of `cur i j` about a point outside `D₂` is independent of `j`.** -/
theorem windNumber_cur_indep_j {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (i j : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur i true).trace) (hx2 : x ∉ (T.cur i false).trace)
    (hxcirc : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ x)
    (hW : windNumber (discCurve T.g).γ (discCurve T.g).cont x = 0) :
    windNumber (T.cur i j).γ (T.cur i j).cont x
      = windNumber (T.cur i false).γ (T.cur i false).cont x := by
  cases j
  · rfl
  · have hd := ThetaFlip.windNumber_cur_arcB_flip T i hx1 hx2 hxcirc
    rw [hW] at hd
    linarith

/-- **The winding number of `cur i j` about a point outside `D₁` is independent of `i`.** -/
theorem windNumber_cur_indep_i {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (i j : Bool) {y : ℂ}
    (hy1 : y ∉ (T.cur true j).trace) (hy2 : y ∉ (T.cur false j).trace)
    (hycirc : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ y)
    (hW : windNumber (discCurve T.f).γ (discCurve T.f).cont y = 0) :
    windNumber (T.cur i j).γ (T.cur i j).cont y
      = windNumber (T.cur true j).γ (T.cur true j).cont y := by
  cases i
  · have hd := ThetaFlip.windNumber_cur_arcA_flip T j hy1 hy2 hycirc
    rw [hW] at hd
    linarith
  · rfl

/-- **Exactly one of the two curves `cur true j`, `cur false j` winds zero times about a point of
the interior of `D₁`.** -/
theorem exists_zero_index_arcA {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (h : PlaneHypothesis)
    (j : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur true j).trace) (hx2 : x ∉ (T.cur false j).trace)
    (hxcirc : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ x)
    (hW : Odd (windNumber (discCurve T.f).γ (discCurve T.f).cont x)) :
    ∃ i : Bool, windNumber (T.cur i j).γ (T.cur i j).cont x = 0 ∧
      ∀ i' : Bool, windNumber (T.cur i' j).γ (T.cur i' j).cont x = 0 → i' = i := by
  have h1 := ThetaOdd.thetaWindZeroOrOdd h (T.cur true j) (T.cur_isSimple true j) hx1
  have h2 := ThetaOdd.thetaWindZeroOrOdd h (T.cur false j) (T.cur_isSimple false j) hx2
  have hd := ThetaFlip.windNumber_cur_arcA_flip T j hx1 hx2 hxcirc
  have hne : windNumber (discCurve T.f).γ (discCurve T.f).cont x ≠ 0 := by
    obtain ⟨m, hm⟩ := hW
    rw [hm]
    omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have hzero : windNumber (discCurve T.f).γ (discCurve T.f).cont x = 0 := by
      rw [h1, h2, sub_zero] at hd
      exact hd.symm
    exact absurd hzero hne
  · refine ⟨true, h1, fun i' hi' => ?_⟩
    cases i' with
    | true => rfl
    | false =>
      obtain ⟨m, hm⟩ := h2
      rw [hi'] at hm
      omega
  · refine ⟨false, h2, fun i' hi' => ?_⟩
    cases i' with
    | true =>
      obtain ⟨m, hm⟩ := h1
      rw [hi'] at hm
      omega
    | false => rfl
  · exfalso
    obtain ⟨m, hm⟩ := h1
    obtain ⟨k, hk⟩ := h2
    obtain ⟨l, hl⟩ := hW
    rw [hm, hk, hl] at hd
    omega

/-- **Exactly one of the two curves `cur i true`, `cur i false` winds zero times about a point of
the interior of `D₂`.** -/
theorem exists_zero_index_arcB {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (h : PlaneHypothesis)
    (i : Bool) {y : ℂ}
    (hy1 : y ∉ (T.cur i true).trace) (hy2 : y ∉ (T.cur i false).trace)
    (hycirc : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ y)
    (hW : Odd (windNumber (discCurve T.g).γ (discCurve T.g).cont y)) :
    ∃ j : Bool, windNumber (T.cur i j).γ (T.cur i j).cont y = 0 ∧
      ∀ j' : Bool, windNumber (T.cur i j').γ (T.cur i j').cont y = 0 → j' = j := by
  have h1 := ThetaOdd.thetaWindZeroOrOdd h (T.cur i true) (T.cur_isSimple i true) hy1
  have h2 := ThetaOdd.thetaWindZeroOrOdd h (T.cur i false) (T.cur_isSimple i false) hy2
  have hd := ThetaFlip.windNumber_cur_arcB_flip T i hy1 hy2 hycirc
  have hne : windNumber (discCurve T.g).γ (discCurve T.g).cont y ≠ 0 := by
    obtain ⟨m, hm⟩ := hW
    rw [hm]
    omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have hzero : windNumber (discCurve T.g).γ (discCurve T.g).cont y = 0 := by
      rw [h1, h2, sub_zero] at hd
      exact hd.symm
    exact absurd hzero hne
  · refine ⟨true, h1, fun j' hj' => ?_⟩
    cases j' with
    | true => rfl
    | false =>
      obtain ⟨m, hm⟩ := h2
      rw [hj'] at hm
      omega
  · refine ⟨false, h2, fun j' hj' => ?_⟩
    cases j' with
    | true =>
      obtain ⟨m, hm⟩ := h1
      rw [hj'] at hm
      omega
    | false => rfl
  · exfalso
    obtain ⟨m, hm⟩ := h1
    obtain ⟨k, hk⟩ := h2
    obtain ⟨l, hl⟩ := hW
    rw [hm, hk, hl] at hd
    omega

/-- **Swapping the first index changes the winding number about a point outside `D₁` by at most
the sign of the winding number of `∂D₁`.**  (Here that number vanishes.) -/
theorem windNumber_cur_swap_i {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (i j : Bool) {y : ℂ}
    (hy1 : y ∉ (T.cur true j).trace) (hy2 : y ∉ (T.cur false j).trace)
    (hycirc : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ y)
    (hW : windNumber (discCurve T.f).γ (discCurve T.f).cont y = 0) :
    windNumber (T.cur i j).γ (T.cur i j).cont y
      = windNumber (T.cur (!i) j).γ (T.cur (!i) j).cont y := by
  cases i
  · simp only [Bool.not_false]
    have hd := ThetaFlip.windNumber_cur_arcA_flip T j hy1 hy2 hycirc
    rw [hW] at hd
    linarith
  · simp only [Bool.not_true]
    have hd := ThetaFlip.windNumber_cur_arcA_flip T j hy1 hy2 hycirc
    rw [hW] at hd
    linarith

/-- **Swapping the second index changes the winding number about a point outside `D₂` by at most
the sign of the winding number of `∂D₂`.**  (Here that number vanishes.) -/
theorem windNumber_cur_swap_j {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (i j : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur i true).trace) (hx2 : x ∉ (T.cur i false).trace)
    (hxcirc : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ x)
    (hW : windNumber (discCurve T.g).γ (discCurve T.g).cont x = 0) :
    windNumber (T.cur i j).γ (T.cur i j).cont x
      = windNumber (T.cur i (!j)).γ (T.cur i (!j)).cont x := by
  cases j
  · simp only [Bool.not_false]
    have hd := ThetaFlip.windNumber_cur_arcB_flip T i hx1 hx2 hxcirc
    rw [hW] at hd
    linarith
  · simp only [Bool.not_true]
    have hd := ThetaFlip.windNumber_cur_arcB_flip T i hx1 hx2 hxcirc
    rw [hW] at hd
    linarith


/-- **The side determination.**  In the theta configuration there are two four-arc curves `J₁`,
`J₂` (containing the two joining arcs) whose bounded, respectively unbounded, sides avoid the theta
graph and whose sides tile the complement. -/
theorem thetaSideDetermination (h : Work.Smooth.SphereJordan.PlaneHypothesis)
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
    ∃ (J₁ J₂ : Work.Smooth.Jordan.PlaneCurve)
      (S₁ : Work.Smooth.Jordan.PlaneSeparation J₁) (S₂ : Work.Smooth.Jordan.PlaneSeparation J₂),
      J₁.IsSimple ∧ J₂.IsSimple ∧
      Set.range J₁.γ ⊆ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β ∧
      Set.range J₂.γ ⊆ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β ∧
      Set.range α ⊆ J₁.trace ∧ Set.range β ⊆ J₁.trace ∧
      Set.range α ⊆ J₂.trace ∧ Set.range β ⊆ J₂.trace ∧
      (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∩ S₁.V = ∅ ∧
      (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∩ S₂.U = ∅ ∧
      Disjoint S₁.V S₂.U ∧
      S₁.V ∪ S₂.U = (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ := by
  obtain ⟨T, hTα, hTβ⟩ :=
    exists_thetaSetup h hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep
      hαβ₀ hαβ₁
  -- the Schoenflies discs of the two boundary curves of the theta graph
  obtain ⟨Sf⟩ := h (discCurve T.f) (discCurve_isSimple T.hf)
  obtain ⟨hfrange, hfopen⟩ := discCurveSpans T.hf Sf
  obtain ⟨Sg⟩ := h (discCurve T.g) (discCurve_isSimple T.hg)
  obtain ⟨hgrange, hgopen⟩ := discCurveSpans T.hg Sg
  have hfopen' : openImage T.f = Sf.V := hfopen
  have hfrange' : Set.range T.f = closure Sf.V := hfrange
  have hgopen' : openImage T.g = Sg.V := hgopen
  have hgrange' : Set.range T.g = closure Sg.V := hgrange
  -- the two interior points
  have hmem0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_zero]
    norm_num
  set z₀ : Disc := ⟨0, hmem0⟩ with hz₀def
  have hz₀norm : ‖(z₀ : ℂ)‖ < 1 := by
    rw [show (z₀ : ℂ) = 0 from rfl]
    norm_num
  set x₀ : ℂ := T.f z₀ with hx₀def
  set y₀ : ℂ := T.g z₀ with hy₀def
  have hx₀op : x₀ ∈ openImage T.f := ⟨z₀, hz₀norm, hx₀def.symm⟩
  have hy₀op : y₀ ∈ openImage T.g := ⟨z₀, hz₀norm, hy₀def.symm⟩
  have hx₀V : x₀ ∈ Sf.V := by rw [← hfopen']; exact hx₀op
  have hy₀V : y₀ ∈ Sg.V := by rw [← hgopen']; exact hy₀op
  have hx₀_odd : Odd (windNumber (discCurve T.f).γ (discCurve T.f).cont x₀) :=
    ThetaOdd.odd_windNumber_of_mem_V Sf hx₀V
  have hy₀_odd : Odd (windNumber (discCurve T.g).γ (discCurve T.g).cont y₀) :=
    ThetaOdd.odd_windNumber_of_mem_V Sg hy₀V
  -- the incidence facts
  have hx_trace : ∀ i j : Bool, x₀ ∉ (T.cur i j).trace := by
    intro i j
    rw [hx₀def]
    exact (ThetaFlip.center_notMem_cur_trace T z₀ hz₀norm i j).1
  have hy_trace : ∀ i j : Bool, y₀ ∉ (T.cur i j).trace := by
    intro i j
    rw [hy₀def]
    exact (ThetaFlip.center_notMem_cur_trace T z₀ hz₀norm i j).2
  have hxcirc_f : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ x₀ := by
    intro ψ
    rw [hx₀def]
    exact ThetaFlip.circlePoint_ne_of_norm_lt T hz₀norm ψ
  have hycirc_g : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ y₀ := by
    intro ψ
    rw [hy₀def]
    exact ThetaFlip.circlePoint_ne_of_norm_lt_g T hz₀norm ψ
  have hx₀D₁ : x₀ ∈ D₁ := by
    rw [hx₀def]
    have h1 : T.f z₀ ∈ Set.range T.f := ⟨z₀, rfl⟩
    rwa [T.hfr] at h1
  have hy₀D₂ : y₀ ∈ D₂ := by
    rw [hy₀def]
    have h1 : T.g z₀ ∈ Set.range T.g := ⟨z₀, rfl⟩
    rwa [T.hgr] at h1
  have hx₀_notD₂ : x₀ ∉ D₂ := fun hc => Set.disjoint_left.mp T.hdisj hx₀D₁ hc
  have hy₀_notD₁ : y₀ ∉ D₁ := fun hc => Set.disjoint_left.mp T.hdisj hc hy₀D₂
  have hycirc_f : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ y₀ := by
    intro ψ hcon
    have h1 : T.f (circlePoint ψ) ∈ D₁ := by
      have h2 : T.f (circlePoint ψ) ∈ Set.range T.f := ⟨circlePoint ψ, rfl⟩
      rwa [T.hfr] at h2
    exact Set.disjoint_left.mp T.hdisj h1 (by rw [hcon]; exact hy₀D₂)
  have hxcirc_g : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ x₀ := by
    intro ψ hcon
    have h1 : T.g (circlePoint ψ) ∈ D₂ := by
      have h2 : T.g (circlePoint ψ) ∈ Set.range T.g := ⟨circlePoint ψ, rfl⟩
      rwa [T.hgr] at h2
    exact Set.disjoint_left.mp T.hdisj (by rw [hcon]; exact hx₀D₁) h1
  have hWf_y : windNumber (discCurve T.f).γ (discCurve T.f).cont y₀ = 0 :=
    windNumber_discCurve_eq_zero h T.hf (fun hc => hy₀_notD₁ (by rwa [T.hfr] at hc))
  have hWg_x : windNumber (discCurve T.g).γ (discCurve T.g).cont x₀ = 0 :=
    windNumber_discCurve_eq_zero h T.hg (fun hc => hx₀_notD₂ (by rwa [T.hgr] at hc))
  -- the two indices
  obtain ⟨i₀, hi₀, hi₀uniq⟩ :=
    exists_zero_index_arcA T h false (hx_trace true false) (hx_trace false false) hxcirc_f hx₀_odd
  obtain ⟨j₀, hj₀, hj₀uniq⟩ :=
    exists_zero_index_arcB T h i₀ (hy_trace i₀ true) (hy_trace i₀ false) hycirc_g hy₀_odd
  have hJ₁s : (T.cur i₀ j₀).IsSimple := T.cur_isSimple i₀ j₀
  have hJ₂s : (T.cur (!i₀) (!j₀)).IsSimple := T.cur_isSimple (!i₀) (!j₀)
  obtain ⟨S₁⟩ := h (T.cur i₀ j₀) hJ₁s
  obtain ⟨S₂⟩ := h (T.cur (!i₀) (!j₀)) hJ₂s
  -- the winding numbers of the two curves
  have hJ₁x : windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont x₀ = 0 := by
    rw [windNumber_cur_indep_j T i₀ j₀ (hx_trace i₀ true) (hx_trace i₀ false) hxcirc_g hWg_x]
    exact hi₀
  have hJ₁y : windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont y₀ = 0 := hj₀
  have hne_swap_i : ¬ ((!i₀) = i₀) := by
    cases i₀ <;> simp
  have hne_swap_j : ¬ ((!j₀) = j₀) := by
    cases j₀ <;> simp
  have hJ₂x : windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont x₀ ≠ 0 := by
    rw [windNumber_cur_indep_j T (!i₀) (!j₀) (hx_trace (!i₀) true) (hx_trace (!i₀) false)
      hxcirc_g hWg_x]
    intro h0
    exact absurd (hi₀uniq (!i₀) h0) hne_swap_i
  have hJ₂y : windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont y₀ ≠ 0 := by
    have h1 : windNumber (T.cur i₀ (!j₀)).γ (T.cur i₀ (!j₀)).cont y₀ ≠ 0 := by
      intro h0
      exact absurd (hj₀uniq (!j₀) h0) hne_swap_j
    intro h0
    have h2 : windNumber (T.cur true (!j₀)).γ (T.cur true (!j₀)).cont y₀ = 0 := by
      rw [← windNumber_cur_indep_i T (!i₀) (!j₀) (hy_trace true (!j₀)) (hy_trace false (!j₀))
        hycirc_f hWf_y]
      exact h0
    exact h1 (by
      rw [windNumber_cur_indep_i T i₀ (!j₀) (hy_trace true (!j₀)) (hy_trace false (!j₀))
        hycirc_f hWf_y]
      exact h2)
  -- the open discs miss the traces of the two curves
  have hopen₁f : openImage T.f ⊆ (T.cur i₀ j₀).traceᶜ := by
    rintro u ⟨w, hw, rfl⟩
    exact ThetaFlip.f_notMem_cur_trace T w hw i₀ j₀
  have hopen₂f : openImage T.f ⊆ (T.cur (!i₀) (!j₀)).traceᶜ := by
    rintro u ⟨w, hw, rfl⟩
    exact ThetaFlip.f_notMem_cur_trace T w hw (!i₀) (!j₀)
  have hopen₁g : openImage T.g ⊆ (T.cur i₀ j₀).traceᶜ := by
    rintro u ⟨w, hw, rfl⟩
    exact ThetaFlip.g_notMem_cur_trace T w hw i₀ j₀
  have hopen₂g : openImage T.g ⊆ (T.cur (!i₀) (!j₀)).traceᶜ := by
    rintro u ⟨w, hw, rfl⟩
    exact ThetaFlip.g_notMem_cur_trace T w hw (!i₀) (!j₀)
  -- the sides of `S₁` contain the two discs
  have hxU₁ : x₀ ∈ S₁.U := by
    have hmem : x₀ ∈ S₁.U ∪ S₁.V := by rw [S₁.union_eq]; exact hx_trace i₀ j₀
    rcases hmem with h | h
    · exact h
    · exact absurd hJ₁x (windNumber_ne_zero_of_mem_V S₁ h)
  have hyU₁ : y₀ ∈ S₁.U := by
    have hmem : y₀ ∈ S₁.U ∪ S₁.V := by rw [S₁.union_eq]; exact hy_trace i₀ j₀
    rcases hmem with h | h
    · exact h
    · exact absurd hJ₁y (windNumber_ne_zero_of_mem_V S₁ h)
  have hopen_f_U₁ : openImage T.f ⊆ S₁.U := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S₁.toPlaneSeparation
      (openImage_preconnected T.f) hopen₁f with h | h
    · exact h
    · exact absurd (h hx₀op) (Set.disjoint_left.mp S₁.toPlaneSeparation.disjoint_UV hxU₁)
  have hopen_g_U₁ : openImage T.g ⊆ S₁.U := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S₁.toPlaneSeparation
      (openImage_preconnected T.g) hopen₁g with h | h
    · exact h
    · exact absurd (h hy₀op) (Set.disjoint_left.mp S₁.toPlaneSeparation.disjoint_UV hyU₁)
  have hclos₁ : closure (openImage T.f) = D₁ := by
    rw [hfopen', hfrange'.symm]
    exact T.hfr
  have hclos₂ : closure (openImage T.g) = D₂ := by
    rw [hgopen', hgrange'.symm]
    exact T.hgr
  have hV₁D₁ : S₁.V ∩ D₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huV, huD⟩
    have hucl : u ∈ closure (openImage T.f) := hclos₁.symm ▸ huD
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S₁.toPlaneSeparation.isOpen_V u huV
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp S₁.toPlaneSeparation.disjoint_UV (hopen_f_U₁ hvop) (hball hvball)
  have hV₁D₂ : S₁.V ∩ D₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huV, huD⟩
    have hucl : u ∈ closure (openImage T.g) := hclos₂.symm ▸ huD
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S₁.toPlaneSeparation.isOpen_V u huV
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp S₁.toPlaneSeparation.disjoint_UV (hopen_g_U₁ hvop) (hball hvball)
  have hA₁ : (D₁ ∪ D₂ ∪ Set.range T.α ∪ Set.range T.β) ∩ S₁.V = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huA, huV⟩
    have huVt : u ∉ (T.cur i₀ j₀).trace := by
      have hmem : u ∈ S₁.U ∪ S₁.V := Or.inr huV
      rwa [S₁.union_eq] at hmem
    rcases huA with ((h | h) | h) | h
    · exact (Set.eq_empty_iff_forall_notMem.mp hV₁D₁) u ⟨huV, h⟩
    · exact (Set.eq_empty_iff_forall_notMem.mp hV₁D₂) u ⟨huV, h⟩
    · exact huVt (T.range_α_subset_cur i₀ j₀ h)
    · exact huVt (T.range_β_subset_cur i₀ j₀ h)
  -- the sides of `S₂`
  have hxV₂ : x₀ ∈ S₂.V := by
    have hmem : x₀ ∈ S₂.U ∪ S₂.V := by rw [S₂.union_eq]; exact hx_trace (!i₀) (!j₀)
    rcases hmem with h | h
    · exact absurd (Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U S₂.toPlaneSeparation h)
        hJ₂x
    · exact h
  have hyV₂ : y₀ ∈ S₂.V := by
    have hmem : y₀ ∈ S₂.U ∪ S₂.V := by rw [S₂.union_eq]; exact hy_trace (!i₀) (!j₀)
    rcases hmem with h | h
    · exact absurd (Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U S₂.toPlaneSeparation h)
        hJ₂y
    · exact h
  have hopen_f_V₂ : openImage T.f ⊆ S₂.V := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S₂.toPlaneSeparation
      (openImage_preconnected T.f) hopen₂f with h | h
    · exact False.elim (Set.disjoint_left.mp S₂.toPlaneSeparation.disjoint_UV (h hx₀op) hxV₂)
    · exact h
  have hopen_g_V₂ : openImage T.g ⊆ S₂.V := by
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S₂.toPlaneSeparation
      (openImage_preconnected T.g) hopen₂g with h | h
    · exact False.elim (Set.disjoint_left.mp S₂.toPlaneSeparation.disjoint_UV (h hy₀op) hyV₂)
    · exact h
  have hU₂D₁ : S₂.U ∩ D₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huU, huD⟩
    have hucl : u ∈ closure (openImage T.f) := hclos₁.symm ▸ huD
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S₂.toPlaneSeparation.isOpen_U u huU
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp S₂.toPlaneSeparation.disjoint_UV (hball hvball) (hopen_f_V₂ hvop)
  have hU₂D₂ : S₂.U ∩ D₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huU, huD⟩
    have hucl : u ∈ closure (openImage T.g) := hclos₂.symm ▸ huD
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp S₂.toPlaneSeparation.isOpen_U u huU
    rw [Metric.mem_closure_iff] at hucl
    obtain ⟨v, hvop, hvd⟩ := hucl ε hε
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, dist_comm]
      exact hvd
    exact Set.disjoint_left.mp S₂.toPlaneSeparation.disjoint_UV (hball hvball) (hopen_g_V₂ hvop)
  have hA₂ : (D₁ ∪ D₂ ∪ Set.range T.α ∪ Set.range T.β) ∩ S₂.U = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro u ⟨huA, huU⟩
    have huUt : u ∉ (T.cur (!i₀) (!j₀)).trace := by
      have hmem : u ∈ S₂.U ∪ S₂.V := Or.inl huU
      rwa [S₂.union_eq] at hmem
    rcases huA with ((h | h) | h) | h
    · exact (Set.eq_empty_iff_forall_notMem.mp hU₂D₁) u ⟨huU, h⟩
    · exact (Set.eq_empty_iff_forall_notMem.mp hU₂D₂) u ⟨huU, h⟩
    · exact huUt (T.range_α_subset_cur (!i₀) (!j₀) h)
    · exact huUt (T.range_β_subset_cur (!i₀) (!j₀) h)
  -- outside the theta graph the two curves have the same winding number
  have hAgree : ∀ z : ℂ, z ∉ (D₁ ∪ D₂ ∪ Set.range T.α ∪ Set.range T.β) →
      windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont z
        = windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont z := by
    intro z hz
    have hzD₁ : z ∉ D₁ := fun h => hz (Or.inl (Or.inl (Or.inl h)))
    have hzD₂ : z ∉ D₂ := fun h => hz (Or.inl (Or.inl (Or.inr h)))
    have hzT₁ : z ∉ (T.cur i₀ j₀).trace := fun h => hz (T.cur_subset i₀ j₀ h)
    have hzT₂ : z ∉ (T.cur (!i₀) (!j₀)).trace := fun h => hz (T.cur_subset (!i₀) (!j₀) h)
    have hzt : ∀ i j : Bool, z ∉ (T.cur i j).trace := fun i j h => hz (T.cur_subset i j h)
    have hzf : windNumber (discCurve T.f).γ (discCurve T.f).cont z = 0 :=
      windNumber_discCurve_eq_zero h T.hf (fun hc => hzD₁ (by rwa [T.hfr] at hc))
    have hzg : windNumber (discCurve T.g).γ (discCurve T.g).cont z = 0 :=
      windNumber_discCurve_eq_zero h T.hg (fun hc => hzD₂ (by rwa [T.hgr] at hc))
    have hcirc_z_f : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ z := by
      intro ψ hcon
      exact hzD₁ (by
        have h3 : T.f (circlePoint ψ) ∈ Set.range T.f := ⟨circlePoint ψ, rfl⟩
        rw [T.hfr] at h3
        rwa [hcon] at h3)
    have hcirc_z_g : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ z := by
      intro ψ hcon
      exact hzD₂ (by
        have h3 : T.g (circlePoint ψ) ∈ Set.range T.g := ⟨circlePoint ψ, rfl⟩
        rw [T.hgr] at h3
        rwa [hcon] at h3)
    have e1 : windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont z
        = windNumber (T.cur (!i₀) j₀).γ (T.cur (!i₀) j₀).cont z :=
      windNumber_cur_swap_i T i₀ j₀ (hzt true j₀) (hzt false j₀) hcirc_z_f hzf
    have e2 : windNumber (T.cur (!i₀) j₀).γ (T.cur (!i₀) j₀).cont z
        = windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont z :=
      windNumber_cur_swap_j T (!i₀) j₀ (hzt (!i₀) true) (hzt (!i₀) false) hcirc_z_g hzg
    rw [e1, e2]
  have hcur₁ : Set.range (T.cur i₀ j₀).γ ⊆ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β := by
    rw [← hTα, ← hTβ]
    exact T.cur_subset i₀ j₀
  have hcur₂ : Set.range (T.cur (!i₀) (!j₀)).γ ⊆ D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β := by
    rw [← hTα, ← hTβ]
    exact T.cur_subset (!i₀) (!j₀)
  have hα₁' : Set.range α ⊆ (T.cur i₀ j₀).trace := by
    rw [← hTα]
    exact T.range_α_subset_cur i₀ j₀
  have hβ₁' : Set.range β ⊆ (T.cur i₀ j₀).trace := by
    rw [← hTβ]
    exact T.range_β_subset_cur i₀ j₀
  have hα₂' : Set.range α ⊆ (T.cur (!i₀) (!j₀)).trace := by
    rw [← hTα]
    exact T.range_α_subset_cur (!i₀) (!j₀)
  have hβ₂' : Set.range β ⊆ (T.cur (!i₀) (!j₀)).trace := by
    rw [← hTβ]
    exact T.range_β_subset_cur (!i₀) (!j₀)
  have hA₁' : (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∩ S₁.V = ∅ := by
    rw [← hTα, ← hTβ]
    exact hA₁
  have hA₂' : (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∩ S₂.U = ∅ := by
    rw [← hTα, ← hTβ]
    exact hA₂
  refine ⟨T.cur i₀ j₀, T.cur (!i₀) (!j₀), S₁.toPlaneSeparation, S₂.toPlaneSeparation,
    hJ₁s, hJ₂s, hcur₁, hcur₂, hα₁', hβ₁', hα₂', hβ₂', hA₁', hA₂', ?_, ?_⟩
  · -- the two sides are disjoint
    rw [Set.disjoint_left]
    rintro u huV₁ huU₂
    have huA : u ∉ (D₁ ∪ D₂ ∪ Set.range T.α ∪ Set.range T.β) :=
      fun hA => (Set.eq_empty_iff_forall_notMem.mp hA₁) u ⟨hA, huV₁⟩
    have hW₁ : windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont u ≠ 0 :=
      windNumber_ne_zero_of_mem_V S₁ huV₁
    have hW₂ : windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont u = 0 :=
      Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U S₂.toPlaneSeparation huU₂
    exact hW₁ (by rw [hAgree u huA]; exact hW₂)
  · -- the two sides exhaust the complement
    rw [← hTα, ← hTβ]
    refine Set.Subset.antisymm ?_ ?_
    · rintro u (huV₁ | huU₂)
      · exact fun hA => (Set.eq_empty_iff_forall_notMem.mp hA₁) u ⟨hA, huV₁⟩
      · exact fun hA => (Set.eq_empty_iff_forall_notMem.mp hA₂) u ⟨hA, huU₂⟩
    · intro u huA
      have huT₁ : u ∉ (T.cur i₀ j₀).trace := fun h => huA (T.cur_subset i₀ j₀ h)
      have huT₂ : u ∉ (T.cur (!i₀) (!j₀)).trace := fun h => huA (T.cur_subset (!i₀) (!j₀) h)
      by_cases hzero : windNumber (T.cur (!i₀) (!j₀)).γ (T.cur (!i₀) (!j₀)).cont u = 0
      · have hmem : u ∈ S₂.U ∪ S₂.V := by rw [S₂.union_eq]; exact huT₂
        rcases hmem with h | h
        · exact Or.inr h
        · exact absurd hzero (windNumber_ne_zero_of_mem_V S₂ h)
      · have hW₁ : windNumber (T.cur i₀ j₀).γ (T.cur i₀ j₀).cont u ≠ 0 := by
          rw [hAgree u huA]
          exact hzero
        have hmem : u ∈ S₁.U ∪ S₁.V := by rw [S₁.union_eq]; exact huT₁
        rcases hmem with h | h
        · exact absurd (Work.Smooth.SphereJordan.windNumber_eq_zero_of_mem_U
            S₁.toPlaneSeparation h) hW₁
        · exact Or.inl h


end ThetaPlaneUp

/-! ## The main theorem -/

theorem thetaPlaneSpansUp (h : Work.Smooth.SphereJordan.PlaneHypothesis)
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
    ThetaPlaneUp.thetaSideDetermination h hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint
      hβint hsep hαβ₀ hαβ₁
  refine ⟨S₁.V, S₂.U, S₁.nonempty_V, S₂.nonempty_U, S₁.isOpen_V, S₂.isOpen_U, hdj, ?_,
    S₁.preconn_V, S₂.preconn_U, ?_, ?_⟩
  · rw [hun, ThetaPlaneUp.theta_complement_eq]
  · obtain ⟨S₁'⟩ := h J₁ hJ₁
    have hV : S₁.V = S₁'.toPlaneSeparation.V :=
      ThetaPlaneUp.planeSeparation_V_eq S₁ S₁'.toPlaneSeparation
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
  · exact ThetaPlaneUp.closure_coe_unbounded_side h J₂.cont J₂.periodic hJ₂ S₂

end

end Work.Smooth.SphereJordan
