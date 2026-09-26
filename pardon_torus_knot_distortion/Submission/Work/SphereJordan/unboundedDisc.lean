import Mathlib
import Submission.Work.SphereJordan.chamberDefs
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.Schoenflies.Unconditional

/-!
# The disc spanning the unbounded side of a Jordan curve

For a simple closed plane curve `γ` with a Jordan separation `S` (`S.U` the unbounded side) we
produce an embedding `E : 𝔻 → ℂ ∪ {∞}` of the model disc whose boundary circle is the trace and
whose *open* disc maps exactly onto `S.U` (together with `∞`):

  `E '' {z : 𝔻 | ‖z‖ < 1} = (↑) '' S.U ∪ {∞}`.

This is the two-disc form of the Jordan–Schoenflies theorem (`planeTwoDiscs`) with the required
disc identified by connectedness: the open disc of `E` and that of the companion embedding `E'`
partition the complement of the trace in the sphere, as do `S.U ∪ {∞}` and `S.V`; comparing the
two partitions (all four sets are open, preconnected and non-empty) gives the claim.

The embedding `E` is the tool with which the local two-sidedness of the trace at a trace point is
proved in `Submission/Work/SphereJordan/germCellUnique.lean`.
-/

open Set Metric
open scoped Topology

namespace Work.SphereJordan

open Work.Smooth.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The image of the *open* model disc under an embedding of the closed disc. -/
def discInteriorImage (e : C(Disc, RiemannSphere)) : Set RiemannSphere :=
  e '' {z : Disc | ‖(z : ℂ)‖ < 1}

/-- The union `(↑) '' s ∪ {∞}` is open in the sphere when the complement of `s` is bounded. -/
theorem isOpen_coe_union_infty {s : Set ℂ} (hs : IsOpen s)
    (hb : ∃ R : ℝ, ∀ x : ℂ, x ∉ s → ‖x‖ ≤ R) :
    IsOpen (((↑) : ℂ → RiemannSphere) '' s ∪ {infty} : Set RiemannSphere) :=
  Work.Smooth.SphereJordan.planeTwoDiscs_isOpen_coe_union_infty hs hb

/-- The unbounded side lies off the trace. -/
theorem unboundedDisc_U_trace (S : Work.Smooth.Jordan.PlaneSeparation γ) :
    S.U ⊆ γ.traceᶜ := by
  intro u hu hmem
  have h3 : u ∈ S.U ∪ S.V := Or.inl hu
  rw [S.union_eq] at h3
  exact h3 hmem

/-- The bounded side lies off the trace. -/
theorem unboundedDisc_V_trace (S : Work.Smooth.Jordan.PlaneSeparation γ) :
    S.V ⊆ γ.traceᶜ := by
  intro u hu hmem
  have h3 : u ∈ S.U ∪ S.V := Or.inr hu
  rw [S.union_eq] at h3
  exact h3 hmem

/-- The complement of the trace in the sphere is the union of the two sides, `∞` joined to the
unbounded one. -/
theorem compl_trace_eq (S : Work.Smooth.Jordan.PlaneSeparation γ) :
    (((↑) : ℂ → RiemannSphere) '' S.U ∪ {infty} ∪ ((↑) : ℂ → RiemannSphere) '' S.V)
      = (((↑) : ℂ → RiemannSphere) '' γ.trace)ᶜ := by
  apply Set.Subset.antisymm
  · rintro x ((⟨u, hu, rfl⟩ | hx) | ⟨v, hv, rfl⟩)
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨t, ht⟩ := hy
      have hyu : y = u := OnePoint.coe_injective (hyx.trans rfl)
      exact unboundedDisc_U_trace S hu ⟨t, by rw [ht]; exact hyu⟩
    · rw [Set.mem_singleton_iff] at hx
      rintro ⟨y, hy, hyx⟩
      exact OnePoint.coe_ne_infty y (hyx.trans hx)
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨t, ht⟩ := hy
      have hyu : y = v := OnePoint.coe_injective (hyx.trans rfl)
      exact unboundedDisc_V_trace S hv ⟨t, by rw [ht]; exact hyu⟩
  · intro x hx
    by_cases hinf : x = infty
    · exact Or.inl (Or.inr hinf)
    · obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.mp hinf
      have hyt : y ∉ γ.trace := by
        intro hmem
        exact hx (by rw [← hy]; exact ⟨y, hmem, rfl⟩)
      have hyUV : y ∈ S.U ∪ S.V := by
        rw [S.union_eq]
        exact hyt
      rcases hyUV with h | h
      · exact Or.inl (Or.inl ⟨y, h, hy⟩)
      · exact Or.inr ⟨y, h, hy⟩

/-- The range of the curve in the sphere is the image of the trace. -/
theorem range_coe_curve (γ : Work.Smooth.Jordan.PlaneCurve) :
    Set.range (fun t : ℝ => ((γ.γ t : ℂ) : RiemannSphere))
      = ((↑) : ℂ → RiemannSphere) '' γ.trace := by
  show Set.range (((↑) : ℂ → RiemannSphere) ∘ γ.γ) = _
  rw [Set.range_comp]
  rfl

section TwoDiscsFacts

variable {T : TwoDiscs (fun t : ℝ => ((γ.γ t : ℂ) : RiemannSphere))}
variable {S : Work.Smooth.Jordan.PlaneSeparation γ}

/-- A disc point whose norm is not `1` is in the open disc. -/
theorem norm_lt_one_of_ne_one {z : Disc} (hz : ‖(z : ℂ)‖ ≠ 1) : ‖(z : ℂ)‖ < 1 := by
  have h : dist (z : ℂ) 0 ≤ 1 := z.2
  rw [dist_eq_norm, sub_zero] at h
  exact lt_of_le_of_ne h hz

/-- The open model disc is preconnected. -/
theorem isPreconnected_openDisc : IsPreconnected {z : Disc | ‖(z : ℂ)‖ < 1} := by
  haveI : PreconnectedSpace ↥(Metric.ball (0 : ℂ) 1) :=
    Subtype.preconnectedSpace isPreconnected_ball
  let f : ↥(Metric.ball (0 : ℂ) 1) → Disc :=
    fun w => ⟨(w : ℂ), Metric.ball_subset_closedBall w.2⟩
  have hcont : Continuous f := continuous_subtype_val.subtype_mk _
  have himg : f '' univ = {z : Disc | ‖(z : ℂ)‖ < 1} := by
    ext z
    constructor
    · rintro ⟨w, -, rfl⟩
      have hw : dist (w : ℂ) 0 < 1 := w.2
      rw [dist_eq_norm, sub_zero] at hw
      exact hw
    · intro hz
      have hz' : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact hz
      exact ⟨⟨(z : ℂ), hz'⟩, trivial, rfl⟩
  have h := (isPreconnected_univ (α := ↥(Metric.ball (0 : ℂ) 1))).image f hcont.continuousOn
  rw [himg] at h
  exact h

/-- The boundary circle of the disc maps onto the trace. -/
theorem boundary_image_eq_range :
    T.e '' {z : Disc | ‖(z : ℂ)‖ = 1}
      = Set.range (fun t : ℝ => ((γ.γ t : ℂ) : RiemannSphere)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨θ, rfl⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
    exact ⟨θ, by rw [T.boundary]⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨circlePoint t, by simp [Work.Smooth.Jordan.circlePoint_coe], T.boundary t⟩

/-- The boundary circle of the second disc maps onto the trace. -/
theorem boundary_image_eq_range' :
    T.e' '' {z : Disc | ‖(z : ℂ)‖ = 1}
      = Set.range (fun t : ℝ => ((γ.γ t : ℂ) : RiemannSphere)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨θ, rfl⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
    exact ⟨θ, by rw [T.boundary']⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨circlePoint t, by simp [Work.Smooth.Jordan.circlePoint_coe], T.boundary' t⟩

/-- The interior image of the first disc lies off the trace. -/
theorem discInteriorImage_subset_compl :
    discInteriorImage T.e ⊆ (Set.range (fun t : ℝ => ((γ.γ t : ℂ) : RiemannSphere)))ᶜ := by
  rintro x ⟨z, hz, rfl⟩ hmem
  rw [← boundary_image_eq_range (γ := γ)] at hmem
  obtain ⟨z', hz', hzz'⟩ := hmem
  have hzz : z' = z := T.inj hzz'
  have h1 : ‖(z : ℂ)‖ = 1 := hzz ▸ hz'
  have hzlt : ‖(z : ℂ)‖ < 1 := hz
  rw [h1] at hzlt
  exact absurd hzlt (lt_irrefl 1)

/-- The interior image of the second disc lies off the trace. -/
theorem discInteriorImage_subset_compl' :
    discInteriorImage T.e' ⊆ (Set.range (fun t : ℝ => ((γ.γ t : ℂ) : RiemannSphere)))ᶜ := by
  rintro x ⟨z, hz, rfl⟩ hmem
  rw [← boundary_image_eq_range' (γ := γ)] at hmem
  obtain ⟨z', hz', hzz'⟩ := hmem
  have hzz : z' = z := T.inj' hzz'
  have h1 : ‖(z : ℂ)‖ = 1 := hzz ▸ hz'
  have hzlt : ‖(z : ℂ)‖ < 1 := hz
  rw [h1] at hzlt
  exact absurd hzlt (lt_irrefl 1)

/-- The two interior images partition the complement of the trace. -/
theorem discInteriorImage_union :
    discInteriorImage T.e ∪ discInteriorImage T.e'
      = (Set.range (fun t : ℝ => ((γ.γ t : ℂ) : RiemannSphere)))ᶜ := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (discInteriorImage_subset_compl (γ := γ))
      (discInteriorImage_subset_compl' (γ := γ))
  · intro x hx
    have hx' : x ∈ Set.range T.e ∪ Set.range T.e' := by rw [T.cover]; trivial
    rcases hx' with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · refine Or.inl ⟨z, norm_lt_one_of_ne_one ?_, rfl⟩
      intro hz1
      exact hx (by rw [← boundary_image_eq_range (γ := γ)]; exact ⟨z, hz1, rfl⟩)
    · refine Or.inr ⟨z, norm_lt_one_of_ne_one ?_, rfl⟩
      intro hz1
      exact hx (by rw [← boundary_image_eq_range' (γ := γ)]; exact ⟨z, hz1, rfl⟩)

theorem disjoint_interiorImages :
    Disjoint (discInteriorImage T.e) (discInteriorImage T.e') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : x ∈ Set.range T.e ∩ Set.range T.e' := by
    refine ⟨?_, ?_⟩
    · obtain ⟨z, hz, hzx⟩ := hx; exact ⟨z, hzx⟩
    · obtain ⟨z, hz, hzx⟩ := hx'; exact ⟨z, hzx⟩
  rw [T.meet] at h1
  exact discInteriorImage_subset_compl (γ := γ) hx h1

theorem isPreconnected_discInteriorImage : IsPreconnected (discInteriorImage T.e) :=
  isPreconnected_openDisc.image T.e T.e.continuous.continuousOn

theorem isPreconnected_discInteriorImage' : IsPreconnected (discInteriorImage T.e') :=
  isPreconnected_openDisc.image T.e' T.e'.continuous.continuousOn

theorem discInteriorImage_nonempty : (discInteriorImage T.e).Nonempty :=
  ⟨T.e ⟨0, by simp [Metric.mem_closedBall]⟩,
    ⟨⟨0, by simp [Metric.mem_closedBall]⟩, by simp, rfl⟩⟩

theorem discInteriorImage_nonempty' : (discInteriorImage T.e').Nonempty :=
  ⟨T.e' ⟨0, by simp [Metric.mem_closedBall]⟩,
    ⟨⟨0, by simp [Metric.mem_closedBall]⟩, by simp, rfl⟩⟩

/-- **The disc spanning the unbounded side.**  For a simple closed plane curve `γ` and a Jordan
separation `S` of it there is an embedding `E : 𝔻 → ℂ ∪ {∞}` whose boundary circle is the trace
(in the parametrisation of `γ`) and whose open disc maps exactly onto `S.U ∪ {∞}`. -/
theorem exists_unboundedDisc (hs : γ.IsSimple) (S : Work.Smooth.Jordan.PlaneSeparation γ) :
    ∃ E : C(Disc, RiemannSphere), Function.Injective E ∧
      (∀ θ : ℝ, E (circlePoint θ) = ((γ.γ θ : ℂ) : RiemannSphere)) ∧
      discInteriorImage E = ((↑) : ℂ → RiemannSphere) '' S.U ∪ {infty} := by
  classical
  obtain ⟨T⟩ := Work.Smooth.SphereJordan.planeTwoDiscs
      Work.Smooth.Schoenflies.planeHypothesis γ.cont γ.periodic hs
  set P : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' S.U ∪ {infty} with hPdef
  set Q : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' S.V with hQdef
  have hPopen : IsOpen P := isOpen_coe_union_infty S.isOpen_U
      (Work.Smooth.SphereJordan.planeTwoDiscs_norm_bound γ S)
  have hQopen : IsOpen Q := OnePoint.isOpen_image_coe.mpr S.isOpen_V
  have hPQdisj : Disjoint P Q := by
    rw [Set.disjoint_left]
    rintro x (⟨u, hu, rfl⟩ | hx) ⟨v, hv, hveq⟩
    · exact Set.disjoint_left.mp S.disjoint_UV hu (OnePoint.coe_injective hveq ▸ hv)
    · rw [Set.mem_singleton_iff] at hx
      exact OnePoint.coe_ne_infty v (hveq.trans hx)
  have htrace : P ∪ Q = (Set.range (fun t : ℝ => ((γ.γ t : ℂ) : RiemannSphere)))ᶜ := by
    rw [hPdef, hQdef, range_coe_curve γ, ← compl_trace_eq S]
  have hAne : (discInteriorImage T.e).Nonempty := discInteriorImage_nonempty (γ := γ)
  have hAne' : (discInteriorImage T.e').Nonempty := discInteriorImage_nonempty' (γ := γ)
  have hPne : P.Nonempty := ⟨infty, Or.inr rfl⟩
  have hQne : Q.Nonempty := S.nonempty_V.elim (fun v hv => ⟨(v : RiemannSphere), ⟨v, hv, rfl⟩⟩)
  have hsub : discInteriorImage T.e ⊆ P ∪ Q := by
    rw [htrace]; exact discInteriorImage_subset_compl (γ := γ)
  have hsub' : discInteriorImage T.e' ⊆ P ∪ Q := by
    rw [htrace]; exact discInteriorImage_subset_compl' (γ := γ)
  have hcase : discInteriorImage T.e ⊆ P ∨ discInteriorImage T.e ⊆ Q := by
    by_cases hne : (discInteriorImage T.e ∩ P).Nonempty
    · exact Or.inl (IsPreconnected.subset_left_of_subset_union hPopen hQopen hPQdisj hsub hne
        (isPreconnected_discInteriorImage (γ := γ)))
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      have hne' : ∀ y, y ∉ discInteriorImage T.e ∩ P :=
        Set.eq_empty_iff_forall_notMem.mp hne
      refine Or.inr (IsPreconnected.subset_left_of_subset_union hQopen hPopen hPQdisj.symm
        (by rw [Set.union_comm]; exact hsub) ?_ (isPreconnected_discInteriorImage (γ := γ)))
      rcases hsub hAne.some_mem with h | h
      · exact absurd ⟨hAne.some_mem, h⟩ (hne' hAne.some)
      · exact ⟨hAne.some, hAne.some_mem, h⟩
  have hcase' : discInteriorImage T.e' ⊆ P ∨ discInteriorImage T.e' ⊆ Q := by
    by_cases hne : (discInteriorImage T.e' ∩ P).Nonempty
    · exact Or.inl (IsPreconnected.subset_left_of_subset_union hPopen hQopen hPQdisj hsub' hne
        (isPreconnected_discInteriorImage' (γ := γ)))
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      have hne' : ∀ y, y ∉ discInteriorImage T.e' ∩ P :=
        Set.eq_empty_iff_forall_notMem.mp hne
      refine Or.inr (IsPreconnected.subset_left_of_subset_union hQopen hPopen hPQdisj.symm
        (by rw [Set.union_comm]; exact hsub') ?_ (isPreconnected_discInteriorImage' (γ := γ)))
      rcases hsub' hAne'.some_mem with h | h
      · exact absurd ⟨hAne'.some_mem, h⟩ (hne' hAne'.some)
      · exact ⟨hAne'.some, hAne'.some_mem, h⟩
  -- the interior image of each disc is one of the two sets `P`, `Q`
  have key₁ : ∀ A A' : Set RiemannSphere, A ⊆ P → A' ⊆ Q → A ∪ A' = P ∪ Q → A = P := by
    intro A A' h1 h2 hunion
    apply Set.Subset.antisymm h1
    intro p hp
    have : p ∈ A ∪ A' := by rw [hunion]; exact Or.inl hp
    rcases this with h | h
    · exact h
    · exact absurd (h2 h) (fun hQ => Set.disjoint_left.mp hPQdisj hp hQ)
  have key₂ : ∀ A A' : Set RiemannSphere, A ⊆ Q → A' ⊆ P → A ∪ A' = P ∪ Q → A' = P :=
    fun A A' h1 h2 hunion => key₁ A' A h2 h1 (by rw [Set.union_comm]; exact hunion)
  have hunion : discInteriorImage T.e ∪ discInteriorImage T.e' = P ∪ Q := by
    rw [discInteriorImage_union (γ := γ), ← htrace]
  rcases hcase with h1 | h1 <;> rcases hcase' with h2 | h2
  · -- both in P: Q would be inside P
    exfalso
    have hQP : Q ⊆ P := by
      intro q hq
      have hq' : q ∈ discInteriorImage T.e ∪ discInteriorImage T.e' := by
        rw [hunion]; exact Or.inr hq
      rcases hq' with h | h
      · exact h1 h
      · exact h2 h
    obtain ⟨q, hq⟩ := hQne
    exact Set.disjoint_left.mp hPQdisj (hQP hq) hq
  · refine ⟨T.e, T.inj, T.boundary, key₁ _ _ h1 h2 hunion⟩
  · refine ⟨T.e', T.inj', T.boundary', key₂ _ _ h1 h2 hunion⟩
  · -- both in Q: P would be inside Q
    exfalso
    have hPQ : P ⊆ Q := by
      intro p hp
      have hp' : p ∈ discInteriorImage T.e ∪ discInteriorImage T.e' := by
        rw [hunion]; exact Or.inl hp
      rcases hp' with h | h
      · exact h1 h
      · exact h2 h
    obtain ⟨p, hp⟩ := hPne
    exact Set.disjoint_left.mp hPQdisj hp (hPQ hp)

/-- A disc embedding whose boundary circle is the curve (in the parametrisation) has the trace as
the image of its boundary circle. -/
theorem image_circle_of_boundary {E : C(Disc, RiemannSphere)}
    (hEbd : ∀ θ : ℝ, E (circlePoint θ) = ((γ.γ θ : ℂ) : RiemannSphere)) :
    E '' {x : Disc | ‖(x : ℂ)‖ = 1} = ((↑) : ℂ → RiemannSphere) '' γ.trace := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    obtain ⟨θ, rfl⟩ := Work.Smooth.Jordan.exists_circlePoint_eq x hx
    exact ⟨γ.γ θ, ⟨θ, rfl⟩, (hEbd θ).symm⟩
  · rintro z ⟨y, ⟨t, ht⟩, hyz⟩
    exact ⟨circlePoint t, by simp [Work.Smooth.Jordan.circlePoint_coe],
      by rw [hEbd t, ht]; exact hyz⟩

/-- The corner `{‖z‖ < 1} ∩ ball ξ ε` of the open disc is preconnected. -/
theorem isPreconnected_openDisc_inter (ξ : ℂ) (ε : ℝ) :
    IsPreconnected {v : Disc | ‖(v : ℂ)‖ < 1 ∧ dist (v : ℂ) ξ < ε} := by
  haveI : PreconnectedSpace ↥(Metric.ball (0 : ℂ) 1 ∩ Metric.ball ξ ε) :=
    Subtype.preconnectedSpace ((convex_ball (0 : ℂ) 1).inter (convex_ball ξ ε)).isPreconnected
  let f : ↥(Metric.ball (0 : ℂ) 1 ∩ Metric.ball ξ ε) → Disc :=
    fun w => ⟨(w : ℂ), Metric.ball_subset_closedBall w.2.1⟩
  have hcont : Continuous f := continuous_subtype_val.subtype_mk _
  have himg : f '' univ = {v : Disc | ‖(v : ℂ)‖ < 1 ∧ dist (v : ℂ) ξ < ε} := by
    ext v
    constructor
    · rintro ⟨w, -, rfl⟩
      have h1 : dist (w : ℂ) 0 < 1 := w.2.1
      rw [dist_eq_norm, sub_zero] at h1
      exact ⟨h1, w.2.2⟩
    · rintro ⟨h1, h2⟩
      have h1' : (v : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact h1
      exact ⟨⟨(v : ℂ), ⟨h1', h2⟩⟩, trivial, rfl⟩
  have h := (isPreconnected_univ (α := ↥(Metric.ball (0 : ℂ) 1 ∩ Metric.ball ξ ε))).image f
    hcont.continuousOn
  rw [himg] at h
  exact h

/-- Preconnectedness transports from the sphere back to the plane along the coercion, for subsets
of the finite part. -/
theorem isPreconnected_coe_preimage {Z : Set RiemannSphere} (hZ : IsPreconnected Z)
    (hZsub : Z ⊆ Set.range ((↑) : ℂ → RiemannSphere)) :
    IsPreconnected {c : ℂ | ((c : ℂ) : RiemannSphere) ∈ Z} := by
  set W : Set ℂ := {c : ℂ | ((c : ℂ) : RiemannSphere) ∈ Z} with hW
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv hdisj
  set U : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' u with hU
  set V : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' v with hV
  have hUopen : IsOpen U := OnePoint.isOpen_image_coe.mpr hu
  have hVopen : IsOpen V := OnePoint.isOpen_image_coe.mpr hv
  have hZsub' : Z ⊆ U ∪ V := by
    intro x hx
    obtain ⟨c, hc⟩ := hZsub hx
    have hcW : c ∈ W := by
      rw [hW]
      simp only [Set.mem_ofPred_eq]
      rw [hc]
      exact hx
    rcases huv hcW with h | h
    · exact Or.inl ⟨c, h, hc⟩
    · exact Or.inr ⟨c, h, hc⟩
  have hZdisj : Z ∩ (U ∩ V) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxZ, ⟨c, hcu, hcx⟩, ⟨c', hcv, hc'x⟩⟩
    have hcc' : c = c' := OnePoint.coe_injective (hcx.trans hc'x.symm)
    have hcW : c ∈ W := by
      rw [hW]
      simp only [Set.mem_ofPred_eq]
      rw [hcx]
      exact hxZ
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) c
      ⟨hcW, hcu, by rw [hcc']; exact hcv⟩
  rcases (isPreconnected_iff_subset_of_disjoint.mp hZ) U V hUopen hVopen hZsub' hZdisj with h | h
  · left
    intro c hc
    rw [hW] at hc
    simp only [Set.mem_ofPred_eq] at hc
    obtain ⟨c', hcu, hceq⟩ := h hc
    have hcc' : c' = c := OnePoint.coe_injective hceq
    rw [← hcc']
    exact hcu
  · right
    intro c hc
    rw [hW] at hc
    simp only [Set.mem_ofPred_eq] at hc
    obtain ⟨c', hcv, hceq⟩ := h hc
    have hcc' : c' = c := OnePoint.coe_injective hceq
    rw [← hcc']
    exact hcv

/-- **The key local lemma.**  Let `E` be a disc embedding spanning the unbounded side, `C` a
component of `Metric.ball z ρ \ γ.trace` contained in `S.U`, and `a` a trace point of the closure
of `C` lying in the ball.  Then a corner of the open model disc around `ξ = E⁻¹ a` maps into `C`:
two such components, both accumulating at a trace point, therefore meet. -/
theorem openDisc_image_subset_component {E : C(Disc, RiemannSphere)}
    (hEinj : Function.Injective E)
    (hEbd : ∀ θ : ℝ, E (circlePoint θ) = ((γ.γ θ : ℂ) : RiemannSphere))
    (hEint : discInteriorImage E = ((↑) : ℂ → RiemannSphere) '' S.U ∪ {infty})
    {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {w : ℂ} (hw : w ∈ Metric.ball z ρ \ γ.trace)
    {C : Set ℂ} (hC : C = connectedComponentIn (Metric.ball z ρ \ γ.trace) w)
    (hCU : C ⊆ S.U) {a : ℂ} (ha : a ∈ closure C) (hatr : a ∈ γ.trace)
    (hab : a ∈ Metric.ball z ρ) :
    ∃ ξ : Disc, E ξ = ((a : ℂ) : RiemannSphere) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ v : Disc, ‖(v : ℂ)‖ < 1 → dist (v : ℂ) (ξ : ℂ) < ε →
        ∃ c ∈ C, E v = ((c : ℂ) : RiemannSphere) := by
  classical
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Disc, E ξ = ((a : ℂ) : RiemannSphere) := by
    have htr : ((a : ℂ) : RiemannSphere) ∈ E '' {x : Disc | ‖(x : ℂ)‖ = 1} := by
      rw [image_circle_of_boundary (γ := γ) hEbd]
      exact ⟨a, hatr, rfl⟩
    obtain ⟨ξ, -, hξ⟩ := htr
    exact ⟨ξ, hξ⟩
  refine ⟨ξ, hξ, ?_⟩
  have hwC : w ∈ C := hC ▸ mem_connectedComponentIn hw
  have hCpre : IsPreconnected C := hC ▸ isPreconnected_connectedComponentIn
  have hCsub : C ⊆ Metric.ball z ρ \ γ.trace := hC ▸ connectedComponentIn_subset _ _
  have hCsubU : C ⊆ Metric.ball z ρ ∩ S.U := fun c hc => ⟨(hCsub hc).1, hCU hc⟩
  have hsub1 : Metric.ball z ρ ∩ S.U ⊆ Metric.ball z ρ \ γ.trace := by
    rintro c ⟨hc1, hc2⟩
    exact ⟨hc1, fun hct => (unboundedDisc_U_trace S hc2) hct⟩
  have hCcomp : C = connectedComponentIn (Metric.ball z ρ ∩ S.U) w := by
    apply Set.Subset.antisymm
    · exact hCpre.subset_connectedComponentIn (x := w) (F := Metric.ball z ρ ∩ S.U) hwC hCsubU
    · rw [hC]
      exact IsPreconnected.subset_connectedComponentIn
        (s := connectedComponentIn (Metric.ball z ρ ∩ S.U) w)
        (F := Metric.ball z ρ \ γ.trace) (x := w)
        isPreconnected_connectedComponentIn
        (mem_connectedComponentIn ⟨hw.1, hCU hwC⟩)
        ((connectedComponentIn_subset _ _).trans hsub1)
  have hUopen : IsOpen (((↑) : ℂ → RiemannSphere) '' Metric.ball z ρ) :=
    OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball
  have hξmemU : E ξ ∈ ((↑) : ℂ → RiemannSphere) '' Metric.ball z ρ := ⟨a, hab, hξ.symm⟩
  have hξmem : E ξ ∈ (((↑) : ℂ → RiemannSphere) '' Metric.ball z ρ) ∩ {infty}ᶜ :=
    ⟨hξmemU, by rw [hξ]; exact OnePoint.coe_ne_infty a⟩
  have hnbhd : E ⁻¹' ((((↑) : ℂ → RiemannSphere) '' Metric.ball z ρ) ∩ {infty}ᶜ) ∈ 𝓝 ξ :=
    E.continuous.continuousAt.preimage_mem_nhds
      ((hUopen.inter isClosed_singleton.isOpen_compl).mem_nhds hξmem)
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hnbhd
  refine ⟨ε, hεpos, ?_⟩
  have hball : ∀ v : Disc, dist (v : ℂ) (ξ : ℂ) < ε →
      E v ∈ (((↑) : ℂ → RiemannSphere) '' Metric.ball z ρ) ∩ {infty}ᶜ := fun v hv =>
    hεsub (by rw [Metric.mem_ball, Subtype.dist_eq]; exact hv)
  set Hs : Set Disc := {v : Disc | ‖(v : ℂ)‖ < 1 ∧ dist (v : ℂ) (ξ : ℂ) < ε} with hHs
  have hHspre : IsPreconnected Hs := isPreconnected_openDisc_inter (ξ : ℂ) ε
  have hEHpre : IsPreconnected (E '' Hs) := hHspre.image E E.continuous.continuousOn
  set Hc : Set ℂ := {c : ℂ | ((c : ℂ) : RiemannSphere) ∈ E '' Hs} with hHc
  have hHcpre : IsPreconnected Hc := by
    refine isPreconnected_coe_preimage hEHpre ?_
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨⟨c₀, -, hc₀eq⟩, -⟩ := hball v hv.2
    exact ⟨c₀, hc₀eq⟩
  have hHcsub : Hc ⊆ Metric.ball z ρ ∩ S.U := by
    rintro c ⟨v, hv, hveq⟩
    obtain ⟨⟨c₀, hc₀ball, hc₀eq⟩, hc₀ne⟩ := hball v hv.2
    have hcvc : c₀ = c := OnePoint.coe_injective (hc₀eq.trans hveq)
    have hEvIn : E v ∈ discInteriorImage E := ⟨v, hv.1, rfl⟩
    rw [hEint] at hEvIn
    rcases hEvIn with ⟨u, huU, hueq⟩ | hinf
    · have hcu : c = u := OnePoint.coe_injective (hveq.symm.trans hueq.symm)
      exact ⟨by rw [← hcvc]; exact hc₀ball, by rw [hcu]; exact huU⟩
    · exact absurd hinf hc₀ne
  have hHcmeets : (Hc ∩ C).Nonempty := by
    have hKcompact : IsCompact (E '' ((Metric.ball ξ ε)ᶜ : Set Disc)) :=
      (IsClosed.isCompact (isOpen_ball.isClosed_compl)).image E.continuous
    have hKclosed : IsClosed (E '' ((Metric.ball ξ ε)ᶜ : Set Disc)) := hKcompact.isClosed
    have hξK : E ξ ∉ E '' ((Metric.ball ξ ε)ᶜ : Set Disc) := by
      rintro ⟨v, hv, hveq⟩
      have hve : v = ξ := hEinj hveq
      rw [hve] at hv
      exact hv (Metric.mem_ball_self hεpos)
    obtain ⟨η, hηpos, hηsub⟩ :
        ∃ η > 0, Metric.ball a η ⊆
          ((↑) ⁻¹' (E '' ((Metric.ball ξ ε)ᶜ : Set Disc))ᶜ : Set ℂ) := by
      have hmem : (E '' ((Metric.ball ξ ε)ᶜ : Set Disc))ᶜ ∈ 𝓝 (((a : ℂ)) : RiemannSphere) := by
        rw [← hξ]
        exact hKclosed.isOpen_compl.mem_nhds hξK
      rw [OnePoint.nhds_coe_eq, Filter.mem_map] at hmem
      exact Metric.mem_nhds_iff.mp hmem
    obtain ⟨c, hcC, hcd⟩ := Metric.mem_closure_iff.mp ha η hηpos
    have hcU : ((c : ℂ) : RiemannSphere) ∈ (E '' ((Metric.ball ξ ε)ᶜ : Set Disc))ᶜ :=
      hηsub (by rw [Metric.mem_ball]; rwa [dist_comm])
    have hcRange : ((c : ℂ) : RiemannSphere) ∈ Set.range E := by
      have h1 : ((c : ℂ) : RiemannSphere) ∈ discInteriorImage E :=
        hEint.symm ▸ Or.inl ⟨c, hCU hcC, rfl⟩
      rw [discInteriorImage] at h1
      obtain ⟨v, -, hv⟩ := h1
      exact ⟨v, hv⟩
    obtain ⟨v, hv⟩ := hcRange
    have hvball : v ∈ Metric.ball ξ ε := by
      by_contra hv'
      exact hcU ⟨v, hv', hv⟩
    have hvHs : v ∈ Hs := by
      refine ⟨?_, by show dist v ξ < ε; exact Metric.mem_ball.mp hvball⟩
      have hvin : E v ∈ discInteriorImage E := by
        rw [hEint]; exact Or.inl ⟨c, hCU hcC, hv.symm⟩
      obtain ⟨u, hu1, hueq⟩ := hvin
      have huv : u = v := hEinj hueq
      rwa [huv] at hu1
    exact ⟨c, ⟨v, hvHs, hv⟩, hcC⟩
  obtain ⟨x, hxHc, hxC⟩ := hHcmeets
  have hsub : Hc ⊆ connectedComponentIn (Metric.ball z ρ ∩ S.U) x :=
    hHcpre.subset_connectedComponentIn hxHc hHcsub
  have heq : connectedComponentIn (Metric.ball z ρ ∩ S.U) x = C := by
    rw [hCcomp]
    exact (connectedComponentIn_eq (F := Metric.ball z ρ ∩ S.U) (x := w) (y := x)
      (hCcomp ▸ hxC)).symm
  rw [heq] at hsub
  intro v hv1 hv2
  have hvHs : v ∈ Hs := ⟨hv1, hv2⟩
  obtain ⟨c, hceq⟩ : ∃ c : ℂ, E v = ((c : ℂ) : RiemannSphere) := by
    obtain ⟨⟨c₀, -, hc₀eq⟩, -⟩ := hball v hv2
    exact ⟨c₀, hc₀eq.symm⟩
  exact ⟨c, hsub ⟨v, hvHs, hceq⟩, hceq⟩

end TwoDiscsFacts

end

end Work.SphereJordan
