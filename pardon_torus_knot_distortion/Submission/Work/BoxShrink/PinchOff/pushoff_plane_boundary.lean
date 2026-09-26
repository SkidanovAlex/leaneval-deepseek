
import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Span
import Submission.Work.BoxShrink.PinchOff.IB.Pieces
import Submission.Work.SurgeryInvariance.All
import Submission.Work.TorusCover.ParamTorus_exists_liftOf
import Submission.Work.Smooth.Schoenflies.Unconditional
import Submission.Work.Smooth.SphereJordan.RiemannSphere
import Submission.Work.SphereJordan.unboundedDisc
import Submission.Work.Smooth.JordanSeparation.spanningDisc
import Submission.Work.BoxShrink.PinchOff.jordan_push
import Submission.Work.BoxShrink.PinchOff.exists_periodic_push
import Submission.Work.BoxShrink.PinchOff.exists_periodic_push2
import Submission.Work.BoxShrink.PinchOff.exists_uniform_gap
import Submission.Work.BoxShrink.PinchOff.exists_nbd_of_compact_subset_open
import Submission.Work.BoxShrink.PinchOff.lifted_boundary_structure

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## Plane and torus preliminaries -/

/-- The standard circle point is `2π`-periodic. -/
theorem circlePoint_periodic (t : ℝ) :
    Work.Smooth.Jordan.circlePoint (t + 2 * Real.pi) = Work.Smooth.Jordan.circlePoint t := by
  apply Subtype.ext
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  have h : (((t + 2 * Real.pi : ℝ)) : ℂ) * Complex.I
      = (t : ℂ) * Complex.I + 2 * Real.pi * Complex.I := by push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The standard circle point is injective on one period. -/
theorem circlePoint_injOn {s t : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (ht : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (h : Work.Smooth.Jordan.circlePoint s = Work.Smooth.Jordan.circlePoint t) : s = t := by
  have h' : Circle.exp s = Circle.exp t := by
    apply Subtype.ext
    rw [Circle.coe_exp, Circle.coe_exp]
    exact congrArg Subtype.val h
  exact Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by linarith [Real.pi_pos]) hs ht h'

/-- The boundary circle `∂D` of an embedded disc, read as a closed curve of `P`. -/
def boundaryCurve {P : Work.CoreTopology.ParamTorus} (D : Work.SurgeryInvariance.DiscRegion P) :
    Work.CoreTopology.ClosedCurve P where
  γ := fun t => D.e (Work.Smooth.Jordan.circlePoint t)
  cont := D.e.continuous.comp Work.Smooth.JordanSeparation.continuous_circlePoint
  periodic := fun t => by rw [circlePoint_periodic]
  mem := fun t => D.mem _

@[simp] theorem boundaryCurve_apply {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) (t : ℝ) :
    (boundaryCurve D).γ t = D.e (Work.Smooth.Jordan.circlePoint t) := rfl

/-- The boundary curve of an embedded disc is simple. -/
theorem boundaryCurve_isSimple {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) :
    Work.CoreTopology.IsSimple P (boundaryCurve D) := by
  intro s hs t ht hst
  exact circlePoint_injOn hs ht (D.inj hst)

/-- The boundary curve of an embedded disc is inessential. -/
theorem boundaryCurve_not_isEssential {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) :
    ¬ Work.CoreTopology.IsEssential P (boundaryCurve D) :=
  Work.SurgeryInvariance.DiscRegion.not_isEssential D _ (fun t => ⟨_, rfl⟩)

/-- The carrier of an embedded disc is the union of its interior and its boundary circle. -/
theorem carrier_eq_union {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) :
    D.carrier = D.interior ∪ D.boundary := by
  ext x
  constructor
  · intro hx
    by_cases h : x ∈ D.interior
    · exact Or.inl h
    · refine Or.inr ?_
      obtain ⟨u, hu, rfl⟩ := hx
      have hu1 : ‖(u : ℂ)‖ ≤ 1 := by
        have := u.2; rwa [Metric.mem_closedBall, dist_zero_right] at this
      rcases lt_or_eq_of_le hu1 with hlt | heq
      · exact absurd ⟨u, hlt, rfl⟩ h
      · exact ⟨u, heq, rfl⟩
  · rintro (h | h)
    · exact Work.SurgeryInvariance.DiscRegion.interior_subset_carrier D h
    · exact Work.SurgeryInvariance.DiscRegion.boundary_subset_carrier D h

/-- The preimage of the boundary circle is the union of the lattice translates of the lifted
curve. -/
theorem Xtilde_boundaryCurve_eq {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P)
    (L : Work.CoreTopology.LiftOf P (boundaryCurve D)) :
    Xtilde P D.boundary =
      ⋃ ν ∈ periodLattice, {z : ℂ | z - ν ∈ Set.range (liftMap L)} := by
  ext z
  constructor
  · intro hz
    rw [mem_Xtilde] at hz
    obtain ⟨u, hu1, hu2⟩ := hz
    obtain ⟨φ, hφ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq u hu1
    have h1 : planePsi P (liftMap L φ) = planePsi P z := by
      rw [planePsi_liftMap, boundaryCurve_apply, hφ]
      exact hu2
    have hν : z - liftMap L φ ∈ periodLattice := sub_mem_periodLattice_of_planePsi_eq h1
    refine Set.mem_iUnion.mpr ⟨z - liftMap L φ, Set.mem_iUnion.mpr ⟨hν, ?_⟩⟩
    use φ
    ring
  · intro hz
    obtain ⟨ν, hmem⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hνmem, hνrange⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨φ, hφ⟩ := hνrange
    rw [mem_Xtilde]
    have h2 : z = liftMap L φ + ν := by rw [hφ]; ring
    have h3 : planePsi P z = D.e (Work.Smooth.Jordan.circlePoint φ) := by
      rw [h2, planePsi_add_periodLattice P _ ν hνmem, planePsi_liftMap]
      rfl
    rw [h3]
    exact ⟨Work.Smooth.Jordan.circlePoint φ, by simp, rfl⟩





/-- **Pushing a lifted curve off the boundary circles of the disc translates.** -/
theorem pushoff_plane_boundary
    {P : Work.CoreTopology.ParamTorus} {X : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.SurgeryInvariance.DiscRegion P)
    (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hsub : D.boundary ⊆ X)
    {a b : ℤ} {Λ : ℝ → ℂ}
    (hΛc : Continuous Λ)
    (hΛper : ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t + Work.BoxShrink.PinchOff.periodPt a b)
    (hΛmem : ∀ t : ℝ,
      Λ t ∈ Work.BoxShrink.PinchOff.Xtilde P X \
        Work.BoxShrink.PinchOff.Xtilde P D.interior) :
    ∃ c : ℝ → ℂ, Continuous c ∧
      (∀ t : ℝ, c (t + 2 * Real.pi) = c t + Work.BoxShrink.PinchOff.periodPt a b) ∧
      (∀ t : ℝ, c t ∈ Work.BoxShrink.PinchOff.Xtilde P (X \ D.carrier)) := by
  classical
  -- (0) the boundary curve, its lift and the plane curve
  set γ : Work.CoreTopology.ClosedCurve P := boundaryCurve D with hγdef
  have hγapply : ∀ t : ℝ, γ.γ t = D.e (Work.Smooth.Jordan.circlePoint t) :=
    fun t => by rw [hγdef]; rfl
  have hγsimple : Work.CoreTopology.IsSimple P γ := by
    rw [hγdef]; exact boundaryCurve_isSimple D
  have hγiness : ¬ Work.CoreTopology.IsEssential P γ := by
    rw [hγdef]; exact boundaryCurve_not_isEssential D
  set L : Work.CoreTopology.LiftOf P γ := chosenLift P γ with hLdef
  have hL : L.winding = (0, 0) := by
    by_contra hne
    exact hγiness ⟨L, hne⟩
  set c : Work.Smooth.Jordan.PlaneCurve :=
    { γ := liftMap L, cont := continuous_liftMap L, periodic := liftMap_periodic L hL }
    with hcdef
  have hcapply : ∀ t : ℝ, c.γ t = liftMap L t := fun t => rfl
  have hcsimple : c.IsSimple := by
    intro s hs t ht hst
    rw [hcapply s, hcapply t] at hst
    have h2 : γ.γ s = γ.γ t := by
      rw [← planePsi_liftMap L s, ← planePsi_liftMap L t, hst]
    have h3 : D.e (Work.Smooth.Jordan.circlePoint s) = D.e (Work.Smooth.Jordan.circlePoint t) := by
      rw [← hγapply s, ← hγapply t]; exact h2
    exact circlePoint_injOn hs ht (D.inj h3)
  -- (1) the Jordan separation datum
  obtain ⟨hsch⟩ : Nonempty (Work.Smooth.Jordan.PlaneSchoenflies c) :=
    Work.Smooth.Schoenflies.classicalInput c hcsimple
  set h : Work.Smooth.Jordan.PlaneSeparation c := hsch.toPlaneSeparation with hhdef
  have htrace : Set.range c.γ ⊆ closure h.V := by
    rintro _ ⟨t, rfl⟩
    have h1 : hsch.e (Work.Smooth.Jordan.circlePoint t) = c.γ t := hsch.boundary t
    rw [← h1, ← hsch.range_e]
    exact Set.mem_range_self _
  -- (2) the structure of the lifted discs
  obtain ⟨hstruct, hdisj⟩ := lifted_boundary_structure D γ hγapply L hL c hcapply h
  -- (3) the outer disc parametrisation
  obtain ⟨E, hEinj, hEb, hEint⟩ := Work.SphereJordan.exists_unboundedDisc hcsimple h
  have hEcont : Continuous E := E.continuous
  obtain ⟨u₀, hu₀lt, hu₀E⟩ : ∃ u₀ : Work.Smooth.Jordan.Disc,
      ‖(u₀ : ℂ)‖ < 1 ∧ E u₀ = OnePoint.infty := by
    have hmem : OnePoint.infty ∈ Work.SphereJordan.discInteriorImage E := by
      rw [hEint]; exact Or.inr rfl
    rcases hmem with ⟨w, hw, hwe⟩
    exact ⟨w, hw, hwe⟩
  have hEopen : ∀ w : Work.Smooth.Jordan.Disc, ‖(w : ℂ)‖ < 1 → w ≠ u₀ →
      ∃ z : ℂ, E w = (z : OnePoint ℂ) ∧ z ∈ h.U := by
    intro w hw hne
    have hmem : E w ∈ Work.SphereJordan.discInteriorImage E := ⟨w, hw, rfl⟩
    rw [hEint] at hmem
    rcases hmem with ⟨z, hzU, hzE⟩ | hinf
    · exact ⟨z, hzE.symm, hzU⟩
    · exact absurd (hEinj (by rw [hinf, hu₀E])) hne
  -- (4) the push, single-curve form
  have hpush : ∀ ε : ℝ, 0 < ε → ∃ ψ : ℂ → ℂ, Continuous ψ ∧
      (∀ z : ℂ, ‖ψ z - z‖ ≤ ε) ∧
      (∀ z : ℂ, ε ≤ Metric.infDist z (Set.range c.γ) → ψ z = z) ∧
      (∀ z : ℂ, (z ∈ h.U ∨ ∃ θ : ℝ, z = c.γ θ) → ψ z ∈ h.U) :=
    jordan_push h u₀ hu₀lt (⇑E) hEcont hEinj hEb hu₀E hEopen
  -- (5) estimates
  obtain ⟨ρ, hρpos, hgap⟩ := exists_uniform_gap h.bounded_V hdisj
  have hXtilde_open : IsOpen (Xtilde P X) := by
    have hopen : Work.SurgeryInvariance.IsOpenInCarrier P (X ∩ P.carrier) := by
      have hset : (Subtype.val ⁻¹' (X ∩ P.carrier) : Set P.carrier) = Subtype.val ⁻¹' X := by
        ext x; exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
      rw [Work.SurgeryInvariance.IsOpenInCarrier, hset]
      exact hX
    have h1 : IsOpen (Xtilde P (X ∩ P.carrier)) :=
      isOpen_Xtilde Set.inter_subset_right hopen
    rwa [show Xtilde P (X ∩ P.carrier) = Xtilde P X from by
      ext z; constructor
      · intro hz; exact hz.1
      · intro hz; exact ⟨hz, planePsi_mem_carrier P z⟩] at h1
  have hXtilde_per : ∀ w : ℂ, w ∈ periodLattice → ∀ z : ℂ,
      z ∈ Xtilde P X ↔ z + w ∈ Xtilde P X :=
    fun w hw z => (Xtilde_add_periodLattice P X z w hw).symm
  have hγinX : Set.range c.γ ⊆ Xtilde P X := by
    rintro _ ⟨t, rfl⟩
    rw [hcapply, mem_Xtilde, planePsi_liftMap, boundaryCurve_apply]
    exact hsub ⟨Work.Smooth.Jordan.circlePoint t, by simp, rfl⟩
  have hγcompact : IsCompact (Set.range c.γ) := by
    have h1 : IsCompact c.trace := by
      rw [Work.Smooth.Jordan.PlaneCurve.trace_eq_image_Icc]
      exact isCompact_Icc.image_of_continuousOn c.cont.continuousOn
    exact h1
  have hγne : (Set.range c.γ).Nonempty := ⟨c.γ 0, ⟨(0 : ℝ), rfl⟩⟩
  obtain ⟨rX, hrXpos, hrXnbd⟩ :=
    exists_nbd_of_compact_subset_open hXtilde_open (Set.range c.γ)
      hγcompact hγne hγinX hXtilde_per
  have hB := Xtilde_boundaryCurve_eq D L
  have hboundary_nbd : ∀ z : ℂ, Metric.infDist z (Xtilde P D.boundary) < rX →
      z ∈ Xtilde P X := by
    intro z hz; rw [hB] at hz; exact hrXnbd z hz
  -- (6) choose ε and build the periodic push
  set ε : ℝ := min (ρ / 2) (rX / 4) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hερ : ε < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεr : 2 * ε < rX := by
    have h1 : ε ≤ rX / 4 := min_le_right _ _
    linarith
  obtain ⟨ψ, hψc, hψ1, hψ2, hψ3⟩ := hpush ε hεpos
  obtain ⟨Ψ, hΨc, hΨ1, hΨ2, hΨ3, hΨ4⟩ :=
    exists_periodic_push2 h htrace hψc hεpos hψ1 hψ2 hψ3 hρpos hερ hgap
  -- (7) the memberships
  have hVtrace : h.V ⊆ c.traceᶜ := by
    intro z hz
    rw [← h.union_eq]
    exact Or.inr hz
  have hΛV : ∀ t : ℝ, ∀ μ : ℂ, μ ∈ periodLattice → Λ t - μ ∉ h.V := by
    intro t μ hμ hmem
    have h1 : planePsi P (Λ t) ∈ D.carrier := by
      have h2 : planePsi P (Λ t - μ) ∈ D.carrier := by
        have h3 : Λ t - μ ∈ Xtilde P D.carrier := by
          rw [hstruct]
          exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨zero_mem_periodLattice,
            show (Λ t - μ) - 0 ∈ closure h.V from by simpa using subset_closure hmem⟩⟩
        exact h3
      have h4 : Λ t - μ = Λ t + (-μ) := by ring
      rw [h4, planePsi_add_periodLattice P (Λ t) (-μ) (neg_mem_periodLattice hμ)] at h2
      exact h2
    have h5 : planePsi P (Λ t) ∈ D.boundary := by
      rw [carrier_eq_union D] at h1
      rcases h1 with hi | hb
      · exact absurd ((mem_Xtilde P D.interior (Λ t)).mpr hi) (hΛmem t).2
      · exact hb
    have h6 : Λ t ∈ ⋃ ν ∈ periodLattice, {z : ℂ | z - ν ∈ Set.range (liftMap L)} := by
      rw [← hB]; exact (mem_Xtilde P D.boundary (Λ t)).mpr h5
    obtain ⟨ν, hmemν⟩ := Set.mem_iUnion.mp h6
    obtain ⟨hνmem, hνr⟩ := Set.mem_iUnion.mp hmemν
    rcases eq_or_ne μ ν with hμν | hμν
    · subst hμν
      exact hVtrace hmem hνr
    · have h7 : Λ t - μ ∈ closure h.V := subset_closure hmem
      have h8 : (Λ t - μ) - (ν - μ) ∈ closure h.V := by
        have h9 : (Λ t - μ) - (ν - μ) = Λ t - ν := by ring
        rw [h9]
        exact htrace hνr
      have h10 : Disjoint ({z : ℂ | z - 0 ∈ closure h.V})
          ({z : ℂ | z - (ν - μ) ∈ closure h.V}) :=
        hdisj 0 (ν - μ) zero_mem_periodLattice (sub_mem_periodLattice hνmem hμ)
          (fun h0 => hμν (sub_eq_zero.mp h0.symm).symm)
      refine Set.disjoint_left.mp h10 ?_ h8
      show (Λ t - μ) - 0 ∈ closure h.V
      simpa using h7
  -- (8) the final curve
  refine ⟨fun t => Ψ (Λ t), hΨc.comp hΛc, ?_, ?_⟩
  · intro t
    change Ψ (Λ (t + 2 * Real.pi)) = Ψ (Λ t) + periodPt a b
    have hw : periodPt a b ∈ periodLattice := ⟨(a, b), rfl⟩
    rw [hΛper t, hΨ2 _ hw]
  · intro t
    by_cases hsupp : ∃ ν ∈ periodLattice, Metric.infDist (Λ t - ν) (Set.range c.γ) < ε
    · obtain ⟨ν, hνmem, hνdist⟩ := hsupp
      obtain ⟨⟨u, huU, hΨeq⟩, hdist, hnotcl⟩ := hΨ4 (Λ t) ν hνmem hνdist (hΛV t)
      have hX : planePsi P (Ψ (Λ t)) ∈ X := by
        apply hboundary_nbd
        obtain ⟨y, hy, hydist⟩ : ∃ y ∈ Set.range c.γ, dist (Λ t - ν) y < ε := by
          rw [Metric.infDist_lt_iff hγne] at hνdist
          exact hνdist
        obtain ⟨θ, hθy⟩ := hy
        have hθ : dist (Λ t - ν) (c.γ θ) < ε := by
          rw [hθy]; exact hydist
        have hmemB : c.γ θ + ν ∈ Xtilde P D.boundary := by
          rw [mem_Xtilde]
          have h1 : planePsi P (c.γ θ + ν) = planePsi P (c.γ θ) :=
            planePsi_add_periodLattice P _ ν hνmem
          rw [h1, hcapply θ, planePsi_liftMap, boundaryCurve_apply]
          exact ⟨Work.Smooth.Jordan.circlePoint θ, by simp, rfl⟩
        have h2 : Metric.infDist (Ψ (Λ t)) (Xtilde P D.boundary)
            ≤ dist (Ψ (Λ t)) (c.γ θ + ν) := Metric.infDist_le_dist_of_mem hmemB
        have h4 : dist (Ψ (Λ t)) (Λ t) ≤ ε := by
          simpa [dist_eq_norm, dist_comm, norm_sub_rev] using hΨ1 (Λ t)
        have h5 : dist (Λ t) (c.γ θ + ν) < ε := by
          rw [dist_eq_norm]
          have h6 : Λ t - (c.γ θ + ν) = (Λ t - ν) - c.γ θ := by ring
          rw [h6, ← dist_eq_norm]
          exact hθ
        have h3 : dist (Ψ (Λ t)) (c.γ θ + ν) < 2 * ε := by
          linarith [dist_triangle (Ψ (Λ t)) (Λ t) (c.γ θ + ν)]
        linarith
      have hnc : planePsi P (Ψ (Λ t)) ∉ D.carrier := by
        intro hc
        have hc' : Ψ (Λ t) ∈ Xtilde P D.carrier := (mem_Xtilde P D.carrier _).mpr hc
        rw [hstruct] at hc'
        obtain ⟨μ, hmemμ⟩ := Set.mem_iUnion.mp hc'
        obtain ⟨hμmem, hμcl⟩ := Set.mem_iUnion.mp hmemμ
        exact hnotcl ⟨μ, hμmem, hμcl⟩
      exact ⟨hX, hnc⟩
    · have hfix : Ψ (Λ t) = Λ t := by
        rcases hΨ3 (Λ t) with h | h
        · exact h
        · exact absurd h hsupp
      change Ψ (Λ t) ∈ Xtilde P (X \ D.carrier)
      rw [hfix]
      refine ⟨(hΛmem t).1, ?_⟩
      intro hc
      have hb : planePsi P (Λ t) ∈ D.boundary := by
        rw [carrier_eq_union D] at hc
        rcases hc with hi | hb
        · exact absurd ((mem_Xtilde P D.interior (Λ t)).mpr hi) (hΛmem t).2
        · exact hb
      have h1 : Λ t ∈ ⋃ ν ∈ periodLattice, {z : ℂ | z - ν ∈ Set.range (liftMap L)} := by
        rw [← hB]; exact (mem_Xtilde P D.boundary (Λ t)).mpr hb
      obtain ⟨ν, hmemν⟩ := Set.mem_iUnion.mp h1
      obtain ⟨hνmem, hνr⟩ := Set.mem_iUnion.mp hmemν
      have hmem : Λ t - ν ∈ Set.range c.γ := by
        have hrange : Set.range (liftMap L) = Set.range c.γ := by
          rw [show (liftMap L) = c.γ from funext (fun s => (hcapply s).symm)]
        rwa [← hrange]
      have h5 : Metric.infDist (Λ t - ν) (Set.range c.γ) < ε :=
        lt_of_le_of_lt (Metric.infDist_le_dist_of_mem (x := Λ t - ν) hmem)
          (by rw [dist_self]; exact hεpos)
      exact hsupp ⟨ν, hνmem, h5⟩

end

end Work.BoxShrink.PinchOff
