import Mathlib
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Work.SimplyConnected.ABS.region_with_sector_boundary
import Submission.Work.SimplyConnected.ABS.sectorCondition_of_chart_balls
import Submission.Work.SimplyConnected.ABS.green_reduction.kBallCone
import Submission.Work.SimplyConnected.ABS.exists_greenOn_of_sectorBoundary

/-!
# The sector condition for a finite family of chart balls at a point of free direction

The local theorem behind the construction of a barrier-regular region from a finite family of
chart balls: at a point p which lies on the spheres of the balls containing it and outside all the
others, a common free direction (a direction which, to first order, leaves every ball through p)
produces the sector condition at p.

The proof is the finite generalisation of the crossing lemma for two chart balls: a thin cone
around the free direction is built with the cone lemma exists_cone_of_finite_positive, and each
ball through p is shown to miss a smaller cone by the first-order Taylor estimate for its
transported defining function.
-/

namespace Work.SimplyConnected.ABS.green_reduction

open scoped _root_.Topology Manifold ContDiff ComplexConjugate
open Set Filter

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A subset with compact closure is never all of a non-compact space. -/
lemma ne_univ_of_compact_closure {U : Set X} (hX : ¬ CompactSpace X)
    (h : IsCompact (closure U)) : U ≠ Set.univ := by
  intro hU
  rw [hU, closure_univ] at h
  exact hX (isCompact_univ_iff.mp h)

/-- **The gap estimate at a point of a transported sphere.**

Let Psi be differentiable at z0 with derivative D, let a be a centre and rho > 0 with
norm (Psi z0 - a) = rho, and let kappa > 0.  Then for small u the membership
norm (Psi (z0 + u) - a) < rho forces the linear functional u |-> Re (conj (Psi z0 - a) * D * u) to
be at most kappa / 2 * norm u: moving a small amount u into the ball cannot make the conormal
functional large. -/
lemma exists_gap_of_hasDerivAt {Ψ : ℂ → ℂ} {D z₀ a : ℂ} {ρ κ : ℝ}
    (hD : HasDerivAt Ψ D z₀) (hρ : 0 < ρ) (hsph : ‖Ψ z₀ - a‖ = ρ) (hκ : 0 < κ) :
    ∃ δ > 0, ∀ u : ℂ, ‖u‖ < δ → ‖Ψ (z₀ + u) - a‖ < ρ →
      (starRingEnd ℂ (Ψ z₀ - a) * D * u).re ≤ κ / 2 * ‖u‖ := by
  have hlittle : (fun u : ℂ => Ψ (z₀ + u) - Ψ z₀ - u * D) =o[𝓝 0] (fun u : ℂ => u) := by
    have h := hD.isLittleO
    have htend : Tendsto (fun u : ℂ => z₀ + u) (𝓝 (0 : ℂ)) (𝓝 z₀) := by
      have h1 : Tendsto (fun _ : ℂ => z₀) (𝓝 (0 : ℂ)) (𝓝 z₀) := tendsto_const_nhds
      have h2 : Tendsto (fun u : ℂ => u) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := tendsto_id
      simpa using h1.add h2
    have hcomp := h.comp_tendsto htend
    simp only [Function.comp_def] at hcomp
    have hfun : (fun u : ℂ => Ψ (z₀ + u) - Ψ z₀ - (z₀ + u - z₀) • D)
        = fun u : ℂ => Ψ (z₀ + u) - Ψ z₀ - u * D := by
      funext u; rw [add_sub_cancel_left, smul_eq_mul]
    have hfun2 : (fun u : ℂ => z₀ + u - z₀) = fun u : ℂ => u := by
      funext u; rw [add_sub_cancel_left]
    rw [hfun, hfun2] at hcomp
    exact hcomp
  obtain ⟨δ, hδ, hδ'⟩ :=
    Metric.eventually_nhds_iff.mp (hlittle.bound (by positivity : 0 < κ / (2 * ρ)))
  refine ⟨δ, hδ, fun u hu hmem => ?_⟩
  set A : ℂ := Ψ z₀ - a with hA
  set R : ℂ := Ψ (z₀ + u) - Ψ z₀ - u * D with hR
  have hAρ : ‖A‖ = ρ := by rw [hA]; exact hsph
  have hRbd : ‖R‖ ≤ κ / (2 * ρ) * ‖u‖ := by
    refine hδ' ?_
    rw [dist_eq_norm, sub_zero]
    exact hu
  have hz : Ψ (z₀ + u) - a = (u * D + R) + A := by rw [hR, hA]; ring
  have hlt : ‖(u * D + R) + A‖ < ‖A‖ := by
    rw [← hz, hA, hsph]
    exact hmem
  have hexp : ‖(u * D + R) + A‖ ^ 2
      = ‖u * D + R‖ ^ 2 + 2 * inner ℝ (u * D + R) A + ‖A‖ ^ 2 :=
    norm_add_sq_real _ _
  have hinner : inner ℝ (u * D + R) A < 0 := by
    have h2 : ‖(u * D + R) + A‖ ^ 2 < ‖A‖ ^ 2 := by
      nlinarith [norm_nonneg ((u * D + R) + A), norm_nonneg A, hlt]
    nlinarith [hexp, h2, sq_nonneg ‖u * D + R‖]
  have hsplit : inner ℝ (u * D + R) A = inner ℝ (u * D) A + inner ℝ R A :=
    inner_add_left _ _ _
  have h1 : inner ℝ (u * D) A < -(inner ℝ R A) := by linarith [hsplit, hinner]
  have h2 : -(inner ℝ R A) ≤ κ / (2 * ρ) * ‖u‖ * ‖A‖ := by
    have h3 : |inner ℝ R A| ≤ κ / (2 * ρ) * ‖u‖ * ‖A‖ :=
      (abs_real_inner_le_norm R A).trans (mul_le_mul_of_nonneg_right hRbd (norm_nonneg A))
    linarith [(abs_le.mp h3).1]
  have h3 : κ / (2 * ρ) * ‖u‖ * ‖A‖ = κ / 2 * ‖u‖ := by
    rw [hAρ]
    field_simp
  have hgoal : reConjCLM (A * starRingEnd ℂ D) u ≤ κ / 2 * ‖u‖ := by
    rw [← inner_mul_right_eq A D u]
    linarith [h1.le, h2, h3]
  have hconv : reConjCLM (A * starRingEnd ℂ D) u = (starRingEnd ℂ A * D * u).re := by
    rw [reConjCLM_apply, map_mul]
    simp only [starRingEnd_apply, star_star]
  rwa [hconv] at hgoal

/-- **The sector condition for a finite family of chart balls with a common free direction.**

Let (cc i, a i, rho i) be finitely many chart balls, and let p lie on the sphere of every ball
whose closed ball contains it and outside all the others.  If there is a direction v which, to
first order, leaves every ball through p (that is, the transported conormal functional of each of
those balls is positive at v), then the union of the balls satisfies the sector condition at p. -/
theorem hasSectorBoundary_iUnion_chartBall_of_freeDirection
    {ι : Type*} [Fintype ι]
    (cc : ι → OpenPartialHomeomorph X ℂ) (hc : ∀ i, cc i ∈ atlas ℂ X)
    (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ (cc i).target)
    {p : X} (hp : p ∉ ⋃ i, Submission.chartBall (cc i) (a i) (ρ i))
    (hfree : ∃ v : ℂ, ∀ i, p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i) →
      0 < (starRingEnd ℂ ((cc i) p - a i) *
        deriv (fun z => (cc i) ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) * v).re) :
    Work.SimplyConnected.ABS.HasSectorBoundary
      (⋃ i, Submission.chartBall (cc i) (a i) (ρ i)) p := by
  classical
  set cp : OpenPartialHomeomorph X ℂ := chartAt ℂ p with hcp
  have hcp_atlas : cp ∈ atlas ℂ X := chart_mem_atlas ℂ p
  have hp_src : p ∈ cp.source := mem_chart_source ℂ p
  set U : Set X := ⋃ i, Submission.chartBall (cc i) (a i) (ρ i) with hU
  by_cases hne : ∃ i, p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i)
  · obtain ⟨i₀, hi₀⟩ := hne
    set J : Type _ := {i : ι // p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i)} with hJ
    haveI : Fintype J := by rw [hJ]; infer_instance
    haveI : Nonempty J := ⟨⟨i₀, hi₀⟩⟩
    have hsrc (i : J) : p ∈ (cc i.1).source := (Submission.mem_chartClosedBall.mp i.2).1
    have hcl (i : J) : (cc i.1) p ∈ Metric.closedBall (a i.1) (ρ i.1) :=
      (Submission.mem_chartClosedBall.mp i.2).2
    have hsph (i : J) : ‖(cc i.1) p - a i.1‖ = ρ i.1 := by
      have hle : ‖(cc i.1) p - a i.1‖ ≤ ρ i.1 := by
        have h := Metric.mem_closedBall.mp (hcl i)
        rwa [dist_eq_norm] at h
      have hge : ρ i.1 ≤ ‖(cc i.1) p - a i.1‖ := by
        by_contra hcon
        rw [not_le] at hcon
        have hball : (cc i.1) p ∈ Metric.ball (a i.1) (ρ i.1) := by
          rw [Metric.mem_ball, dist_eq_norm]
          exact hcon
        exact hp (Set.mem_iUnion.mpr ⟨i.1, Submission.mem_chartBall.mpr ⟨hsrc i, hball⟩⟩)
      exact le_antisymm hle hge
    have hAnal (i : J) : AnalyticAt ℂ (fun z => (cc i.1) (cp.symm z)) (cp p) := by
      have h1 : cp p ∈ cp.target := cp.map_source hp_src
      have h2 : cp.symm (cp p) ∈ (cc i.1).source := by
        rw [cp.left_inv hp_src]
        exact hsrc i
      exact Submission.analyticAt_transition_of_mem_atlas (c := cc i.1) (d := cp)
        (hc i.1) hcp_atlas (cp p) h1 h2
    have hHas (i : J) : HasDerivAt (fun z => (cc i.1) (cp.symm z))
        (deriv (fun z => (cc i.1) (cp.symm z)) (cp p)) (cp p) :=
      hasDerivAt_deriv_iff.mpr (hAnal i).differentiableAt
    obtain ⟨v, hv⟩ := hfree
    have hv' (i : J) : 0 < reConjCLM (((cc i.1) (cp.symm (cp p)) - a i.1) *
        starRingEnd ℂ (deriv (fun z => (cc i.1) (cp.symm z)) (cp p))) v := by
      have h := hv i.1 i.2
      have hconv : reConjCLM (((cc i.1) (cp.symm (cp p)) - a i.1) *
          starRingEnd ℂ (deriv (fun z => (cc i.1) (cp.symm z)) (cp p))) v
          = (starRingEnd ℂ ((cc i.1) (cp.symm (cp p)) - a i.1) *
              deriv (fun z => (cc i.1) (cp.symm z)) (cp p) * v).re := by
        rw [reConjCLM_apply, map_mul]
        simp only [starRingEnd_apply, star_star]
      rw [hconv, cp.left_inv hp_src]
      exact h
    obtain ⟨L₁, L₂, κ, hL₁, hL₂, hκ, ⟨w, hw₁, hw₂⟩, hbound⟩ :=
      exists_cone_of_finite_positive (N := fun i : J => reConjCLM
        (((cc i.1) (cp.symm (cp p)) - a i.1) *
          starRingEnd ℂ (deriv (fun z => (cc i.1) (cp.symm z)) (cp p)))) hv'
    have hgap (i : J) : ∃ δ > 0, ∀ u : ℂ, ‖u‖ < δ →
        ‖(cc i.1) (cp.symm (cp p + u)) - a i.1‖ < ρ i.1 →
        reConjCLM (((cc i.1) (cp.symm (cp p)) - a i.1) *
          starRingEnd ℂ (deriv (fun z => (cc i.1) (cp.symm z)) (cp p))) u ≤ κ / 2 * ‖u‖ := by
      have hsph' : ‖(fun z => (cc i.1) (cp.symm z)) (cp p) - a i.1‖ = ρ i.1 := by
        simpa only [cp.left_inv hp_src] using hsph i
      obtain ⟨δ, hδ, hmain⟩ := exists_gap_of_hasDerivAt (hHas i) (hρ i.1) hsph' hκ
      refine ⟨δ, hδ, fun u hu hmem => ?_⟩
      have h := hmain u hu hmem
      have hconv : reConjCLM (((cc i.1) (cp.symm (cp p)) - a i.1) *
          starRingEnd ℂ (deriv (fun z => (cc i.1) (cp.symm z)) (cp p))) u
          = (starRingEnd ℂ ((fun z => (cc i.1) (cp.symm z)) (cp p) - a i.1) *
              deriv (fun z => (cc i.1) (cp.symm z)) (cp p) * u).re := by
        rw [reConjCLM_apply, map_mul]
        simp only [starRingEnd_apply, star_star]
      rw [hconv]
      exact h
    choose δ hδpos hδ using hgap
    set δm : ℝ := Finset.univ.inf' Finset.univ_nonempty δ with hδm
    have hδmpos : 0 < δm := by
      rw [hδm, Finset.lt_inf'_iff]
      intro i _
      exact hδpos i
    have hδm_le (i : J) : δm ≤ δ i := by
      rw [hδm]; exact Finset.inf'_le _ (Finset.mem_univ i)
    set K₀ : Set X := Set.iUnion (fun i : {j : ι // ¬ p ∈ Submission.chartClosedBall (cc j) (a j) (ρ j)} =>
      Submission.chartClosedBall (cc i.1) (a i.1) (ρ i.1)) with hK₀
    have hK₀closed : IsClosed K₀ := by
      rw [hK₀]
      exact isClosed_iUnion_of_finite fun i =>
        (Submission.isCompact_chartClosedBall (hsub i.1)).isClosed
    set V : Set X := cp.source ∩ (cp ⁻¹' Metric.ball (cp p) δm) ∩ K₀ᶜ with hV
    have hVopen : IsOpen V := by
      rw [hV]
      exact (cp.continuousOn.isOpen_inter_preimage cp.open_source Metric.isOpen_ball).inter
        hK₀closed.isOpen_compl
    have hpV : p ∈ V := by
      rw [hV]
      refine ⟨⟨hp_src, Metric.mem_ball_self hδmpos⟩, ?_⟩
      rw [Set.mem_compl_iff, hK₀]
      rintro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact i.2 hi
    have hVsub : V ⊆ cp.source := fun x hx => hx.1.1
    refine ⟨cp, V, L₁, L₂, hcp_atlas, hVopen, hpV, hVsub, hp_src, hL₁, hL₂,
      ⟨w, hw₁, hw₂⟩, ?_⟩
    rintro x ⟨hxU, hxV⟩ ⟨h₁, h₂⟩
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxU
    have hjact : p ∈ Submission.chartClosedBall (cc j) (a j) (ρ j) := by
      by_contra hcon
      refine hxV.2 (Set.mem_iUnion.mpr ⟨⟨j, hcon⟩, ?_⟩)
      exact Submission.mem_chartClosedBall.mpr ⟨(Submission.mem_chartBall.mp hxj).1,
        Metric.ball_subset_closedBall (Submission.mem_chartBall.mp hxj).2⟩
    set u : ℂ := cp x - cp p with hu
    have hxsrc : x ∈ cp.source := hVsub hxV
    have hcone : κ * ‖u‖ ≤ reConjCLM (((cc j) (cp.symm (cp p)) - a j) *
        starRingEnd ℂ (deriv (fun z => (cc j) (cp.symm z)) (cp p))) u :=
      hbound ⟨j, hjact⟩ u h₁ h₂
    have hgapj : reConjCLM (((cc j) (cp.symm (cp p)) - a j) *
        starRingEnd ℂ (deriv (fun z => (cc j) (cp.symm z)) (cp p))) u ≤ κ / 2 * ‖u‖ := by
      refine hδ ⟨j, hjact⟩ u ?_ ?_
      · have h := Metric.mem_ball.mp hxV.1.2
        rw [dist_eq_norm] at h
        rw [hu]
        exact lt_of_lt_of_le h (hδm_le ⟨j, hjact⟩)
      · have hxmem : (cc j) x ∈ Metric.ball (a j) (ρ j) := (Submission.mem_chartBall.mp hxj).2
        have hxval : (cc j) (cp.symm (cp p + u)) = (cc j) x := by
          rw [hu]
          have harg : cp.symm (cp p + (cp x - cp p)) = cp.symm (cp x) := by
            congr 1
            ring
          rw [harg]
          exact congrArg (cc j) (cp.left_inv hxsrc)
        rw [hxval]
        simpa only [dist_eq_norm] using Metric.mem_ball.mp hxmem
    have hzero : ‖u‖ = 0 := by
      have := le_trans hcone hgapj
      nlinarith [hκ, norm_nonneg u]
    have hup : u = 0 := norm_eq_zero.mp hzero
    have hxp : x = p := by
      have h2 : cp x = cp p := by
        have h0 : cp x - cp p = 0 := by rw [← hu]; exact hup
        exact sub_eq_zero.mp h0
      have h3 := congrArg cp.symm h2
      rwa [cp.left_inv hxsrc, cp.left_inv hp_src] at h3
    exact hp (hxp ▸ hxU)
  · refine ⟨cp, cp.source ∩ (⋃ i, Submission.chartClosedBall (cc i) (a i) (ρ i))ᶜ,
      reConjCLM 1, reConjCLM Complex.I, hcp_atlas, ?_, ?_, ?_, hp_src, ?_, ?_, ?_, ?_⟩
    · exact cp.open_source.inter (isClosed_iUnion_of_finite fun i =>
        (Submission.isCompact_chartClosedBall (hsub i)).isClosed).isOpen_compl
    · exact ⟨hp_src, fun h => hne (Set.mem_iUnion.mp h)⟩
    · exact Set.inter_subset_left
    · exact reConjCLM_ne_zero one_ne_zero
    · exact reConjCLM_ne_zero Complex.I_ne_zero
    · refine ⟨1 + Complex.I, ?_, ?_⟩
      · rw [reConjCLM_apply, map_one, one_mul]
        simp only [Complex.add_re, Complex.one_re, Complex.I_re]
        norm_num
      · rw [reConjCLM_apply, Complex.conj_I]
        have h : (-Complex.I) * (1 + Complex.I) = 1 - Complex.I := by
          rw [mul_add, mul_one,
            show (-Complex.I) * Complex.I = -(Complex.I * Complex.I) by ring, Complex.I_mul_I]
          ring
        rw [h]
        simp only [Complex.sub_re, Complex.one_re, Complex.I_re]
        norm_num
    · rintro x ⟨hxU, hxV⟩ ⟨h₁, h₂⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
      have hmem := Submission.mem_chartBall.mp hi
      exact hxV.2 (Set.mem_iUnion.mpr ⟨i,
        Submission.mem_chartClosedBall.mpr ⟨hmem.1, Metric.ball_subset_closedBall hmem.2⟩⟩)

/-- **The target from a family of chart balls with a free direction everywhere on its boundary.**

If finitely many chart balls cover K union {x0}, have connected union, and every point of the
closed union outside the open union has a direction which to first order leaves every ball through
it, then the union is a witness for the target theorem: it is open, connected, precompact, proper,
and every frontier point carries the sector condition, hence a barrier. -/
theorem exists_barrier_regular_precompact_region_of_freeFamily
    [ConnectedSpace X] [SecondCountableTopology X]
    (hX : ¬ CompactSpace X) {K : Set X} (hK : IsCompact K) (x₀ : X)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (cc : ι → OpenPartialHomeomorph X ℂ) (hc : ∀ i, cc i ∈ atlas ℂ X)
    (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ (cc i).target)
    (hcov : K ∪ {x₀} ⊆ ⋃ i, Submission.chartBall (cc i) (a i) (ρ i))
    (hconn : IsConnected (⋃ i, Submission.chartBall (cc i) (a i) (ρ i)))
    (hfree : ∀ p ∈ (⋃ i, Submission.chartClosedBall (cc i) (a i) (ρ i)) \
        (⋃ i, Submission.chartBall (cc i) (a i) (ρ i)),
      ∃ v : ℂ, ∀ i, p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i) →
        0 < (starRingEnd ℂ ((cc i) p - a i) *
          deriv (fun z => (cc i) ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) * v).re) :
    ∃ Ω : Set X, IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ K ∪ {x₀} ⊆ Ω ∧
      Ω ≠ Set.univ ∧
      (∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
        Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
        ContinuousOn u V ∧ u p = 0) := by
  classical
  set Ω : Set X := ⋃ i, Submission.chartBall (cc i) (a i) (ρ i) with hΩ
  have hΩo : IsOpen Ω := isOpen_iUnion fun i => Submission.chartBall_isOpen (cc i) (a i) (ρ i)
  have hcompact : IsCompact (closure Ω) := by
    refine (isCompact_iUnion fun i =>
      Submission.isCompact_chartClosedBall (hsub i)).of_isClosed_subset isClosed_closure ?_
    rw [hΩ, closure_iUnion_of_finite (fun i => Submission.chartBall (cc i) (a i) (ρ i))]
    exact iUnion_mono fun i => Submission.closure_chartBall_subset_chartClosedBall (hsub i)
  refine ⟨Ω, hΩo, hconn, hcompact, hcov,
    ne_univ_of_compact_closure (X := X) hX hcompact, ?_⟩
  refine Work.SimplyConnected.ABS.barriers_of_sector_or_ray_of_open hΩo fun p hp => Or.inl ?_
  have hpU : p ∉ Ω := by
    have hf : frontier Ω = closure Ω \ Ω := hΩo.frontier_eq
    rw [hf] at hp
    exact hp.2
  have hpcl : p ∈ ⋃ i, Submission.chartClosedBall (cc i) (a i) (ρ i) := by
    have h1 : p ∈ closure Ω := hp.1
    rw [hΩ, closure_iUnion_of_finite (fun i => Submission.chartBall (cc i) (a i) (ρ i))] at h1
    exact (iUnion_mono fun i => Submission.closure_chartBall_subset_chartClosedBall (hsub i)) h1
  exact hasSectorBoundary_iUnion_chartBall_of_freeDirection cc hc a ρ hρ hsub hpU
    (hfree p ⟨hpcl, hpU⟩)

end Work.SimplyConnected.ABS.green_reduction