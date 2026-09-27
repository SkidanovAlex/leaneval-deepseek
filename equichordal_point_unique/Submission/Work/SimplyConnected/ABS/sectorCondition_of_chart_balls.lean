import Mathlib
import Submission.RiemannSurface
import Submission.DirichletX
import Submission.GreenFunction
import Submission.ChartBallDirichlet
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Work.SimplyConnected.ABS.ray_boundary_barrier
import Submission.Work.SimplyConnected.ABS.hasSectorBoundary_or_hasRayBoundary_of_two_chartBall

/-!
# The sector condition at a frontier point of a chart ball

`Work.SimplyConnected.ABS.sectorCondition_of_saturated_family` (`regularPiece_core.lean`) as stated
is *vacuous*: requiring the finite family `S` to contain every member of the cover meeting
`closure (⋃ i ∈ S, r i)` forces (with `r` closed and locally finite) the frontier of
`interior (⋃ i ∈ S, r i)` to be empty.  Saturation says nothing about two members *of* `S` merely
touching, and two members which are externally tangent at a frontier point produce a cusp, where no
sector exists: the usable hypothesis is therefore a **no-external-tangency condition**.

This file supplies the *base case* of the corrected assembly, for a single chart ball: at every
frontier point of `Submission.chartBall c a ρ` there is a sector in the complement.  The proof is
explicit: in the chart `c` the ball is Euclidean, and at a boundary point `q = c p` the outward
functional `z ↦ ⟪q - a, z⟫` is non-positive on the ball (because
`‖y - a‖² = ‖y - q‖² + 2⟪y - q, q - a⟫ + ‖q - a‖²` for `‖y - a‖ < ρ = ‖q - a‖`), while the
second functional `z ↦ ⟪I (q - a), z⟫` spans a genuine sector with it.  This is the same
construction as `Work.SimplyConnected.ABS.sectorComplement_of_single_ball`, but stated for the
canonical chart-ball API of `Submission.RiemannSurface` and independent of
`regularPiece_core.lean` (which currently does not compile).
-/

open Set Metric
open scoped Topology Manifold ContDiff

noncomputable section

open Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-! ## Elementary real-inner-product facts on `ℂ` -/

/-- The real inner-product pairing of `I * u` with `u` vanishes. -/
theorem inner_I_mul_left_self (u : ℂ) : inner ℝ (Complex.I * u) u = 0 := by
  rw [Complex.inner]
  rw [map_mul, Complex.conj_I]
  rw [show u * (-Complex.I * starRingEnd ℂ u) = -Complex.I * (u * starRingEnd ℂ u) by ring]
  rw [Complex.mul_conj]
  simp [Complex.mul_re]

/-- The real inner-product pairing of `u` with `I * u` vanishes. -/
theorem inner_I_mul_right_self (u : ℂ) : inner ℝ u (Complex.I * u) = 0 := by
  rw [real_inner_comm, inner_I_mul_left_self]

/-- Multiplication by `I` preserves the real inner product (it is an isometry). -/
theorem inner_I_mul_I_mul (u : ℂ) : inner ℝ (Complex.I * u) (Complex.I * u) = inner ℝ u u := by
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_mul, Complex.norm_I, one_mul]

/-- **The half-plane estimate.**  If `‖y - a‖ < ‖q - a‖` then the outward functional
`z ↦ ⟪q - a, z⟫_ℝ` is non-positive on `y - q`; equivalently, the Euclidean ball of centre `a` and
radius `‖q - a‖` lies in the closed half-plane beyond the tangent line at `q`. -/
theorem inner_le_zero_of_norm_lt {y q a : ℂ} (h : ‖y - a‖ < ‖q - a‖) :
    inner ℝ (q - a) (y - q) ≤ 0 := by
  have hpos : 0 < ‖q - a‖ :=
    lt_of_le_of_lt (norm_nonneg (y - a)) h
  have hsq : ‖y - a‖ ^ 2 < ‖q - a‖ ^ 2 := by
    nlinarith [norm_nonneg (y - a), norm_nonneg (q - a)]
  have key : ‖y - a‖ ^ 2 = ‖y - q‖ ^ 2 + 2 * inner ℝ (q - a) (y - q) + ‖q - a‖ ^ 2 := by
    rw [show y - a = (y - q) + (q - a) by ring, norm_add_sq_real, real_inner_comm]
  have hmain : 2 * inner ℝ (q - a) (y - q) < -‖y - q‖ ^ 2 := by linarith
  nlinarith [sq_nonneg ‖y - q‖]

/-! ## The sector condition for one chart ball -/

/-- **The sector condition at a frontier point of a chart ball.**

Let `c ∈ atlas ℂ X`, `a ∈ ℂ`, `ρ > 0`, with the closed Euclidean ball of centre `a` and radius `ρ`
inside the chart target, and let `p` be a frontier point of the chart ball `chartBall c a ρ`.  Then
`chartBall c a ρ` satisfies the sector (cone) condition at `p`.

This is the *usable* base case for the sector assembly of the ABS route (the sector condition is the
hypothesis of `Work.SimplyConnected.ABS.barrier_of_sector`, hence produces a barrier and then the
Green function of the region). -/
theorem hasSectorBoundary_chartBall {c : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X)
    {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsub : Metric.closedBall a ρ ⊆ c.target) :
    ∀ p ∈ frontier (Submission.chartBall c a ρ),
      HasSectorBoundary (Submission.chartBall c a ρ) p := by
  intro p hp
  -- `p` lies in the closed chart ball but not in the open one, hence on the chart sphere
  have hcl : p ∈ Submission.chartClosedBall c a ρ :=
    Submission.closure_chartBall_subset_chartClosedBall hsub hp.1
  have hint : p ∉ Submission.chartBall c a ρ := by
    rw [← (Submission.chartBall_isOpen c a ρ).interior_eq]
    exact hp.2
  obtain ⟨hpsrc, hpcl⟩ := Submission.mem_chartClosedBall.mp hcl
  have hpnb : c p ∉ Metric.ball a ρ := fun h =>
    hint (Submission.mem_chartBall.mpr ⟨hpsrc, h⟩)
  have hnorm : ‖c p - a‖ = ρ := by
    have h1 : ‖c p - a‖ ≤ ρ := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hpcl
    have h2 : ¬ (‖c p - a‖ < ρ) := by
      intro hlt
      exact hpnb (by simpa only [Metric.mem_ball, dist_eq_norm] using hlt)
    exact le_antisymm h1 (not_lt.mp h2)
  set u : ℂ := c p - a with hu
  have hu_ne : u ≠ 0 := by
    intro h
    have : ‖u‖ = 0 := by rw [h, norm_zero]
    rw [hu, hnorm] at this
    exact absurd this (ne_of_gt hρ)
  have hinner_u : 0 < inner ℝ u u := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hu_ne) 2
  -- the two functionals and the sector they span
  refine ⟨c, c.source, innerSL ℝ u, innerSL ℝ (Complex.I * u), hc, c.open_source, hpsrc,
    Subset.rfl, hpsrc, ?_, ?_, ?_, ?_⟩
  · -- the first functional is non-zero
    intro h
    have h0 : (innerSL ℝ u) u = 0 := by rw [h]; rfl
    rw [innerSL_apply_apply] at h0
    exact absurd hinner_u (not_lt.mpr (le_of_eq h0))
  · -- the second functional is non-zero
    intro h
    have h0 : (innerSL ℝ (Complex.I * u)) (Complex.I * u) = 0 := by rw [h]; rfl
    rw [innerSL_apply_apply, inner_I_mul_I_mul] at h0
    exact absurd hinner_u (not_lt.mpr (le_of_eq h0))
  · -- the sector is non-degenerate: `u + I * u` is in its interior
    refine ⟨u + Complex.I * u, ?_, ?_⟩
    · rw [innerSL_apply_apply, inner_add_right, inner_I_mul_right_self, add_zero]
      exact hinner_u
    · rw [innerSL_apply_apply, inner_add_right, inner_I_mul_left_self, zero_add,
        inner_I_mul_I_mul]
      exact hinner_u
  · -- the chart ball avoids the sector
    rintro x ⟨hxB, -⟩ hcon
    have hB : ‖c x - a‖ < ρ := by
      have := (Submission.mem_chartBall.mp hxB).2
      simpa only [Metric.mem_ball, dist_eq_norm] using this
    have hle : inner ℝ (c p - a) (c x - c p) ≤ 0 :=
      inner_le_zero_of_norm_lt (by rw [hnorm]; exact hB)
    have hcon' : 0 < inner ℝ (c p - a) (c x - c p) := by
      have := hcon.1
      rwa [innerSL_apply_apply] at this
    exact absurd hcon' (not_lt.mpr hle)

end Work.SimplyConnected.ABS

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The properties are local in `U` -/

/-- Both boundary conditions are local in `U`: they only test `U` inside a neighbourhood of the
point. -/
theorem hasSectorBoundary_of_inter_eq {U U' V : Set X} {p : X} (hVo : IsOpen V) (hpV : p ∈ V)
    (heq : U ∩ V = U' ∩ V) (h : HasSectorBoundary U' p) : HasSectorBoundary U p := by
  obtain ⟨c, V', L₁, L₂, hc, hV'o, hpV', hV'sub, hpsrc, hL₁, hL₂, hw, hsec⟩ := h
  refine ⟨c, V ∩ V', L₁, L₂, hc, hVo.inter hV'o, ⟨hpV, hpV'⟩,
    Set.inter_subset_right.trans hV'sub, hpsrc, hL₁, hL₂, hw, ?_⟩
  rintro x ⟨hxU, hxV⟩ hcon
  have hxV' : x ∈ V' := hxV.2
  have hxU' : x ∈ U' := by
    have hmem : x ∈ U ∩ V := ⟨hxU, hxV.1⟩
    rw [heq] at hmem
    exact hmem.1
  exact hsec x ⟨hxU', hxV'⟩ hcon

/-- The ray version of `hasSectorBoundary_of_inter_eq`. -/
theorem hasRayBoundary_of_inter_eq {U U' V : Set X} {p : X} (hVo : IsOpen V) (hpV : p ∈ V)
    (heq : U ∩ V = U' ∩ V) (h : HasRayBoundary U' p) : HasRayBoundary U p := by
  obtain ⟨c, V', d, hc, hV'o, hpV', hV'sub, hpsrc, hd, hsec⟩ := h
  refine ⟨c, V ∩ V', d, hc, hVo.inter hV'o, ⟨hpV, hpV'⟩,
    Set.inter_subset_right.trans hV'sub, hpsrc, hd, ?_⟩
  rintro x ⟨hxU, hxV⟩ t ht
  have hxV' : x ∈ V' := hxV.2
  have hxU' : x ∈ U' := by
    have hmem : x ∈ U ∩ V := ⟨hxU, hxV.1⟩
    rw [heq] at hmem
    exact hmem.1
  exact hsec x ⟨hxU', hxV'⟩ t ht

/-! ## The union of balls with a unique ball through the frontier point -/

/-- **The sector condition at a frontier point of a finite union of chart balls, when exactly one of
the closed balls contains the image of the point.**

`c ∈ atlas ℂ X` is a chart, `a i` the centres and `ρ i > 0` the radii of finitely many round balls
whose closed balls lie in `c.target`.  Let `U := ⋃ i, chartBall c (a i) (ρ i)` and let `p` be a
frontier point of `U` whose image `c p` lies in the closed ball of `i₀` and in no other closed ball.
Then `U` satisfies the sector condition at `p`.

This is the step the sector assembly of the ABS route uses at each frontier point: the members whose
closed ball misses `c p` are *away* from `p`, so the local picture is the single-ball one, to which
`Work.SimplyConnected.ABS.hasSectorBoundary_chartBall` applies. -/
theorem hasSectorBoundary_iUnion_chartBall_of_unique {c : OpenPartialHomeomorph X ℂ}
    (hc : c ∈ atlas ℂ X) {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℂ) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ c.target)
    {i₀ : ι} {p : X} (hp : p ∈ frontier (⋃ i, Submission.chartBall c (a i) (ρ i)))
    (hmem : c p ∈ Metric.closedBall (a i₀) (ρ i₀))
    (haway : ∀ i, i ≠ i₀ → c p ∉ Metric.closedBall (a i) (ρ i)) :
    HasSectorBoundary (⋃ i, Submission.chartBall c (a i) (ρ i)) p := by
  set U : Set X := ⋃ i, Submission.chartBall c (a i) (ρ i) with hUdef
  have hUo : IsOpen U := isOpen_iUnion fun i => Submission.chartBall_isOpen c (a i) (ρ i)
  have hpU : p ∉ U := by
    rw [← hUo.interior_eq]
    exact hp.2
  -- the closed chart discs are compact, hence closed
  have hclosed : IsClosed (⋃ i, Submission.chartClosedBall c (a i) (ρ i)) := by
    refine isClosed_iUnion_of_finite fun i => ?_
    rw [Submission.chartClosedBall_eq_image (hsub i)]
    exact ((isCompact_closedBall _ _).image_of_continuousOn
      (c.continuousOn_symm.mono (hsub i))).isClosed
  -- `p` lies in the source of the chart
  have hpsrc : p ∈ c.source := by
    have h1 : p ∈ ⋃ i, Submission.chartClosedBall c (a i) (ρ i) :=
      closure_minimal (fun x hx => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨i, Submission.chartBall_subset_chartClosedBall c (a i) (ρ i) hi⟩)
        hclosed hp.1
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
    exact Submission.chartClosedBall_subset_source c (a i) (ρ i) hi
  -- the image of `p` is on the sphere of the `i₀`-th ball
  have hnotball : c p ∉ Metric.ball (a i₀) (ρ i₀) := by
    intro hb
    exact hpU (Set.mem_iUnion.mpr ⟨i₀, Submission.mem_chartBall.mpr ⟨hpsrc, hb⟩⟩)
  have hsphere : c p ∈ Metric.sphere (a i₀) (ρ i₀) := by
    rw [Metric.mem_sphere]
    exact le_antisymm (by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hmem)
      (not_lt.mp (fun hlt => hnotball (by simpa only [Metric.mem_ball, dist_eq_norm] using hlt)))
  -- hence `p` is a frontier point of that single chart ball
  have hpf : p ∈ frontier (Submission.chartBall c (a i₀) (ρ i₀)) := by
    have hcl : p ∈ Submission.chartClosedBall c (a i₀) (ρ i₀) :=
      Submission.mem_chartClosedBall.mpr ⟨hpsrc, Metric.sphere_subset_closedBall hsphere⟩
    have hclo : p ∈ closure (Submission.chartBall c (a i₀) (ρ i₀)) :=
      Submission.chartClosedBall_subset_closure_chartBall (hρ i₀) (hsub i₀) hcl
    have hnb : p ∉ Submission.chartBall c (a i₀) (ρ i₀) := fun hb =>
      hpU (Set.mem_iUnion.mpr ⟨i₀, hb⟩)
    rw [IsOpen.frontier_eq (Submission.chartBall_isOpen c (a i₀) (ρ i₀))]
    exact ⟨hclo, hnb⟩
  -- the other balls are away from `p`
  have haway' : ∀ i, i ≠ i₀ → p ∉ Submission.chartClosedBall c (a i) (ρ i) :=
    fun i hi hmem' => haway i hi (Submission.mem_chartClosedBall.mp hmem').2
  -- the complement of their union is an open neighbourhood of `p`
  set V : Set X := (⋃ i : {i // i ≠ i₀}, Submission.chartClosedBall c (a i) (ρ i))ᶜ with hVdef
  have hVo : IsOpen V := by
    rw [hVdef]
    refine isOpen_compl_iff.mpr (isClosed_iUnion_of_finite fun i => ?_)
    rw [Submission.chartClosedBall_eq_image (hsub i)]
    exact ((isCompact_closedBall _ _).image_of_continuousOn
      (c.continuousOn_symm.mono (hsub i))).isClosed
  have hpV : p ∈ V := by
    rw [hVdef, Set.mem_compl_iff, Set.mem_iUnion]
    rintro ⟨i, hi⟩
    exact haway' i i.2 hi
  have hone : HasSectorBoundary (Submission.chartBall c (a i₀) (ρ i₀)) p :=
    hasSectorBoundary_chartBall hc (hρ i₀) (hsub i₀) p hpf
  refine hasSectorBoundary_of_inter_eq hVo hpV ?_ hone
  ext x
  constructor
  · rintro ⟨hxU, hxV⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
    have hi : i = i₀ := by
      by_contra hne
      refine hxV ?_
      exact Set.mem_iUnion.mpr ⟨⟨i, hne⟩,
        Submission.chartBall_subset_chartClosedBall c (a i) (ρ i) hxi⟩
    subst hi
    exact ⟨hxi, hxV⟩
  · rintro ⟨hx, hxV⟩
    exact ⟨Set.mem_iUnion.mpr ⟨i₀, hx⟩, hxV⟩

end Work.SimplyConnected.ABS

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The open chart ball is the image of the Euclidean ball (when the closed ball lies in the chart
target). -/
theorem chartBall_eq_image {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}
    (hsub : Metric.closedBall a ρ ⊆ c.target) :
    Submission.chartBall c a ρ = c.symm '' Metric.ball a ρ := by
  ext x
  constructor
  · rintro ⟨hx, hcx⟩
    exact ⟨c x, hcx, c.left_inv hx⟩
  · rintro ⟨w, hw, rfl⟩
    have hwcl : w ∈ Metric.closedBall a ρ := Metric.ball_subset_closedBall hw
    refine ⟨c.map_target (hsub hwcl), ?_⟩
    rw [Set.mem_preimage, c.right_inv (hsub hwcl)]
    exact hw

/-- A point of the closure of `U` which lies in an open `V` with `U ∩ V = U' ∩ V` is in the closure
of `U'`. -/
theorem mem_closure_of_inter_eq {U U' V : Set X} {p : X} (hVo : IsOpen V) (hpV : p ∈ V)
    (heq : U ∩ V = U' ∩ V) (h : p ∈ closure U) : p ∈ closure U' := by
  have hV : V ∈ 𝓝 p := hVo.mem_nhds hpV
  rw [_root_.mem_closure_iff_nhds] at h ⊢
  intro W hW
  obtain ⟨y, hyW, hyU⟩ := h (W ∩ V) (Filter.inter_mem hW hV)
  have hyU' : y ∈ U' := by
    have : y ∈ U ∩ V := ⟨hyU, hyW.2⟩
    rw [heq] at this
    exact this.1
  exact ⟨y, ⟨hyW.1, hyU'⟩⟩

/-- **The sector or ray condition at a frontier point of a finite union of chart balls, when at most
two of the closed balls meet there.**

`c ∈ atlas ℂ X` is a chart, `a i` the centres and `ρ i > 0` the radii of finitely many round balls
whose closed balls lie in `c.target`, and **at most two of the closed balls contain any given point
of `ℂ`** (the "general position" condition of the ABS route: it excludes the pinwheel
configurations, and it is exactly what makes the local picture at a frontier point either the
single-ball one or the two-ball one).  Then at every frontier point of
`U := ⋃ i, chartBall c (a i) (ρ i)` the union satisfies the sector condition or the ray condition.

This is the *corrected* form of `Work.SimplyConnected.ABS.sectorCondition_of_saturated_family`: the
sector condition is precisely what feeds `Work.SimplyConnected.ABS.barrier_of_sector`, the ray
condition what feeds `Work.SimplyConnected.ABS.barrier_of_ray`, and together they give the barrier
hypothesis of `exists_isGreenOn_of_barriers` for such a union. -/
theorem hasSectorBoundary_or_hasRayBoundary_iUnion_chartBall {c : OpenPartialHomeomorph X ℂ}
    (hc : c ∈ atlas ℂ X) {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℂ) (ρ : ι → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ c.target)
    (htwo : ∀ z : ℂ, ({i | z ∈ Metric.closedBall (a i) (ρ i)} : Set ι).ncard ≤ 2) :
    ∀ p ∈ frontier (⋃ i, Submission.chartBall c (a i) (ρ i)),
      HasSectorBoundary (⋃ i, Submission.chartBall c (a i) (ρ i)) p ∨
      HasRayBoundary (⋃ i, Submission.chartBall c (a i) (ρ i)) p := by
  intro p hp
  set U : Set X := ⋃ i, Submission.chartBall c (a i) (ρ i) with hUdef
  have hUo : IsOpen U := isOpen_iUnion fun i => Submission.chartBall_isOpen c (a i) (ρ i)
  have hpU : p ∉ U := by
    rw [← hUo.interior_eq]
    exact hp.2
  have hclosed : IsClosed (⋃ i, Submission.chartClosedBall c (a i) (ρ i)) := by
    refine isClosed_iUnion_of_finite fun i => ?_
    rw [Submission.chartClosedBall_eq_image (hsub i)]
    exact ((isCompact_closedBall _ _).image_of_continuousOn
      (c.continuousOn_symm.mono (hsub i))).isClosed
  have hpsrc : p ∈ c.source := by
    have h1 : p ∈ ⋃ i, Submission.chartClosedBall c (a i) (ρ i) :=
      closure_minimal (fun x hx => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨i, Submission.chartBall_subset_chartClosedBall c (a i) (ρ i) hi⟩)
        hclosed hp.1
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
    exact Submission.chartClosedBall_subset_source c (a i) (ρ i) hi
  -- the set of indices whose closed ball contains `c p`
  set T : Set ι := {i | c p ∈ Metric.closedBall (a i) (ρ i)} with hTdef
  have hTne : T.Nonempty := by
    have h1 : p ∈ ⋃ i, Submission.chartClosedBall c (a i) (ρ i) :=
      closure_minimal (fun x hx => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨i, Submission.chartBall_subset_chartClosedBall c (a i) (ρ i) hi⟩)
        hclosed hp.1
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
    exact ⟨i, (Submission.mem_chartClosedBall.mp hi).2⟩
  have hTcard : T.ncard ≤ 2 := htwo (c p)
  have hcases : T.ncard = 1 ∨ T.ncard = 2 := by
    have hfin : T.Finite := Set.finite_univ.subset (Set.subset_univ T)
    have hpos : 0 < T.ncard := (Set.ncard_pos (s := T) hfin).mpr hTne
    omega
  rcases hcases with h1 | h2
  · -- exactly one ball through `p`
    obtain ⟨i₀, hi₀⟩ := Set.ncard_eq_one.mp h1
    have hmem : c p ∈ Metric.closedBall (a i₀) (ρ i₀) := by
      have : i₀ ∈ T := by rw [hi₀]; exact Set.mem_singleton i₀
      exact this
    have haway : ∀ i, i ≠ i₀ → c p ∉ Metric.closedBall (a i) (ρ i) := by
      intro i hi hmem'
      have : i ∈ T := hmem'
      rw [hi₀, Set.mem_singleton_iff] at this
      exact hi this
    exact Or.inl (hasSectorBoundary_iUnion_chartBall_of_unique hc a ρ hρ hsub hp hmem haway)
  · -- exactly two balls through `p`
    obtain ⟨i₀, i₁, hne, hT⟩ := Set.ncard_eq_two.mp h2
    have hmem₀ : c p ∈ Metric.closedBall (a i₀) (ρ i₀) := by
      have : i₀ ∈ T := by rw [hT]; exact Set.mem_insert i₀ {i₁}
      exact this
    have hmem₁ : c p ∈ Metric.closedBall (a i₁) (ρ i₁) := by
      have : i₁ ∈ T := by
        rw [hT]
        exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton i₁))
      exact this
    have haway : ∀ i, i ≠ i₀ → i ≠ i₁ → c p ∉ Metric.closedBall (a i) (ρ i) := by
      intro i hi₀' hi₁' hmem'
      have : i ∈ T := hmem'
      rw [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h
      · exact hi₀' h
      · exact hi₁' h
    -- the complementary neighbourhood of `p`
    set V : Set X := (⋃ i : {i // i ≠ i₀ ∧ i ≠ i₁}, Submission.chartClosedBall c (a i) (ρ i))ᶜ
      with hVdef
    have hVo : IsOpen V := by
      rw [hVdef]
      refine isOpen_compl_iff.mpr (isClosed_iUnion_of_finite fun i => ?_)
      rw [Submission.chartClosedBall_eq_image (hsub i)]
      exact ((isCompact_closedBall _ _).image_of_continuousOn
        (c.continuousOn_symm.mono (hsub i))).isClosed
    have hpV : p ∈ V := by
      rw [hVdef, Set.mem_compl_iff, Set.mem_iUnion]
      rintro ⟨i, hi⟩
      exact haway i i.2.1 i.2.2 (Submission.mem_chartClosedBall.mp hi).2
    -- `U` agrees with the two-ball union near `p`
    have heq : U ∩ V = (Submission.chartBall c (a i₀) (ρ i₀) ∪
        Submission.chartBall c (a i₁) (ρ i₁)) ∩ V := by
      ext x
      constructor
      · rintro ⟨hxU, hxV⟩
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxU
        have hi : i = i₀ ∨ i = i₁ := by
          by_contra hcon
          push Not at hcon
          exact hxV (Set.mem_iUnion.mpr ⟨⟨i, hcon.1, hcon.2⟩,
            Submission.chartBall_subset_chartClosedBall c (a i) (ρ i) hxi⟩)
        rcases hi with h | h
        · subst h; exact ⟨Or.inl hxi, hxV⟩
        · subst h; exact ⟨Or.inr hxi, hxV⟩
      · rintro ⟨hx, hxV⟩
        exact ⟨Set.mem_iUnion.mpr (hx.elim (fun h => ⟨i₀, h⟩) (fun h => ⟨i₁, h⟩)), hxV⟩
    -- `p` is a frontier point of the two-ball union
    have hpf : p ∈ frontier (Submission.chartBall c (a i₀) (ρ i₀) ∪
        Submission.chartBall c (a i₁) (ρ i₁)) := by
      have hclo : p ∈ closure (Submission.chartBall c (a i₀) (ρ i₀) ∪
          Submission.chartBall c (a i₁) (ρ i₁)) :=
        mem_closure_of_inter_eq hVo hpV heq hp.1
      have hnb : p ∉ Submission.chartBall c (a i₀) (ρ i₀) ∪
          Submission.chartBall c (a i₁) (ρ i₁) := fun h =>
        hpU (Set.mem_iUnion.mpr (h.elim (fun h' => ⟨i₀, h'⟩) (fun h' => ⟨i₁, h'⟩)))
      rw [IsOpen.frontier_eq ((Submission.chartBall_isOpen c (a i₀) (ρ i₀)).union
        (Submission.chartBall_isOpen c (a i₁) (ρ i₁)))]
      exact ⟨hclo, hnb⟩
    -- the two-ball lemma of the workspace applies (restated with the chart balls)
    have htwo'' := hasSectorBoundary_or_hasRayBoundary_of_two_chartBall c hc (c₁ := a i₀)
      (c₂ := a i₁) (ρ₁ := ρ i₀) (ρ₂ := ρ i₁) (hρ i₀) (hρ i₁) (hsub i₀) (hsub i₁)
    simp only [← chartBall_eq_image (hsub i₀), ← chartBall_eq_image (hsub i₁)] at htwo''
    rcases htwo'' p hpf with hsec | hray
    · exact Or.inl (hasSectorBoundary_of_inter_eq hVo hpV heq hsec)
    · exact Or.inr (hasRayBoundary_of_inter_eq hVo hpV heq hray)

end Work.SimplyConnected.ABS
