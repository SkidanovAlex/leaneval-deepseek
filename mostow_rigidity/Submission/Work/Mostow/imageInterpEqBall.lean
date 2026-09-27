import Mathlib

/-!
# `Work.Mostow.imageInterpEqBall`

Let `E` be a finite-dimensional real inner product space and `f : E → E` a `C¹` map that sends
the closed unit ball into the unit sphere and fixes the sphere pointwise.  Put
`g_t x = (1 - t) • x + t • f x` for `0 < t < 1`.  If the derivative
`Dg_t(x) = (1 - t) • 1 + t • fderiv ℝ f x` is invertible (bijective) at every point of the open
unit ball, then `g_t` maps the closed unit ball *onto* the closed unit ball.

This is the analytic heart of the "no smooth retraction of the ball onto its boundary" step used
in the Besson–Courtois–Gallot route to Mostow rigidity.

The proof:
* `g_t` maps the closed ball into itself (triangle inequality) and is the identity on the sphere;
* on the open ball `g_t(B) ⊆ B` strictly, and by the inverse function theorem (`g_t` has a
  surjective strict derivative at every interior point) `g_t` is an open map on `B`, so `g_t(B)`
  is open;
* `g_t(B) ∪ S = g_t(closedBall)` is a continuous image of the compact closed ball, hence closed,
  so `g_t(B)` is closed inside `B`;
* `B` is convex, hence preconnected, so a nonempty clopen subset of `B` is all of `B`; thus
  `B ⊆ g_t(B)`;
* adding the sphere gives `g_t(closedBall) = closedBall`.
-/

set_option linter.style.haveILetI false

namespace Work.Mostow

open Metric Filter Set
open scoped Topology

/-! ## A general topology helper -/

/-- A nonempty subset of a preconnected set that is open and "closed inside the set" is the whole
set. -/
theorem subset_of_isPreconnected_of_isOpen_of_isClosedIn {X : Type*} [TopologicalSpace X]
    {B U : Set X} (hB : IsPreconnected B) (hUo : IsOpen U) (hUsub : U ⊆ B)
    (hUc : ∀ y ∈ closure U, y ∈ B → y ∈ U) (hne : U.Nonempty) : B ⊆ U := by
  letI : PreconnectedSpace ↥B := isPreconnected_iff_preconnectedSpace.mp hB
  set U' : Set B := Subtype.val ⁻¹' U with hU'
  have hopen' : IsOpen U' := hUo.preimage continuous_subtype_val
  have hclosed' : IsClosed U' := by
    rw [isClosed_induced_iff]
    refine ⟨closure U, isClosed_closure, ?_⟩
    ext x
    simp only [Set.mem_preimage]
    exact ⟨fun hx => hUc x hx x.2, fun hx => subset_closure hx⟩
  have hne' : U'.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, hUsub hx⟩, hx⟩
  have huniv : U' = Set.univ := IsClopen.eq_univ ⟨hclosed', hopen'⟩ hne'
  intro x hx
  have := huniv ▸ (Set.mem_univ (⟨x, hx⟩ : B))
  exact this

/-! ## Openness of the interpolant image on the open ball -/

/-- The inverse function theorem applied to the interpolant: since its derivative
`(1 - t) • 1 + t • fderiv ℝ f x` is bijective (hence surjective) at every interior point, the
interpolant is a local homeomorphism there, so the image of the open ball is open. -/
theorem isOpen_image_interp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → E) (hf : ContDiff ℝ 1 f) {t : ℝ}
    (hinv : ∀ x ∈ Metric.ball (0 : E) 1,
      Function.Bijective ((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x)) :
    IsOpen ((fun x => (1 - t) • x + t • f x) '' Metric.ball (0 : E) 1) := by
  have hgcd : ContDiff ℝ 1 (fun x => (1 - t) • x + t • f x) := by fun_prop
  have hnhds : ∀ x ∈ ball (0:E) 1,
      map (fun y => (1 - t) • y + t • f y) (nhds x) = nhds ((1 - t) • x + t • f x) := by
    intro x hx
    have hf' : HasFDerivAt f (fderiv ℝ f x) x := (hf.hasStrictFDerivAt one_ne_zero).hasFDerivAt
    have h1 : HasFDerivAt (fun y : E => (1 - t) • y) ((1 - t) • (1 : E →L[ℝ] E)) x :=
      ((1 - t) • (1 : E →L[ℝ] E)).hasFDerivAt
    have h2 : HasFDerivAt (fun y : E => t • f y) (t • fderiv ℝ f x) x := hf'.const_smul t
    have hFd : HasFDerivAt (fun y => (1 - t) • y + t • f y)
        ((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x) x := (h1.add h2).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun y => rfl)
    have hstrict : HasStrictFDerivAt (fun y => (1 - t) • y + t • f y)
        ((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x) x :=
      (hgcd.contDiffAt).hasStrictFDerivAt' hFd one_ne_zero
    have hsurj : (((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x : E →L[ℝ] E) : E →ₗ[ℝ] E).range = ⊤ := by
      rw [LinearMap.range_eq_top]; exact (hinv x hx).2
    exact hstrict.map_nhds_eq_of_surj hsurj
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  rw [← hnhds x hx, mem_map]
  exact Filter.mem_of_superset (isOpen_ball.mem_nhds hx) (fun z hz => ⟨z, hz, rfl⟩)

/-! ## The main statement -/

theorem imageInterpEqBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (hmaps : ∀ x ∈ Metric.closedBall (0 : E) 1, f x ∈ Metric.sphere (0 : E) 1)
    (hid : ∀ x ∈ Metric.sphere (0 : E) 1, f x = x) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hinv : ∀ x ∈ Metric.ball (0 : E) 1,
      Function.Bijective ((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x)) :
    (fun x => (1 - t) • x + t • f x) '' Metric.closedBall (0 : E) 1 = Metric.closedBall (0 : E) 1 := by
  have hgcont : Continuous (fun x : E => (1 - t) • x + t • f x) := by fun_prop
  have hnorm : ∀ x : E, ‖(1 - t) • x + t • f x‖ ≤ (1 - t) * ‖x‖ + t * ‖f x‖ := by
    intro x
    calc ‖(1 - t) • x + t • f x‖ ≤ ‖(1 - t) • x‖ + ‖t • f x‖ := norm_add_le _ _
      _ = (1 - t) * ‖x‖ + t * ‖f x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by linarith : (0:ℝ) < 1 - t), abs_of_pos ht]
  have hfx1 : ∀ x ∈ Metric.closedBall (0:E) 1, ‖f x‖ = 1 := by
    intro x hx
    have h := hmaps x hx
    rwa [mem_sphere_iff_norm, sub_zero] at h
  have hgfix : ∀ x ∈ Metric.sphere (0:E) 1, (1 - t) • x + t • f x = x := by
    intro x hx
    rw [hid x hx, ← add_smul, sub_add_cancel, one_smul]
  have himgS : (fun x => (1 - t) • x + t • f x) '' Metric.sphere (0:E) 1 = Metric.sphere (0:E) 1 := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, hyx⟩
      rw [← hyx]
      change (1 - t) • x + t • f x ∈ Metric.sphere (0:E) 1
      rw [hgfix x hx]
      exact hx
    · intro y hy; exact ⟨y, hy, hgfix y hy⟩
  have hmapC : ∀ x ∈ Metric.closedBall (0:E) 1, (1 - t) • x + t • f x ∈ Metric.closedBall (0:E) 1 := by
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    have hx1 : ‖x‖ ≤ 1 := by rwa [mem_closedBall, dist_zero_right] at hx
    calc ‖(1 - t) • x + t • f x‖ ≤ (1 - t) * ‖x‖ + t * ‖f x‖ := hnorm x
      _ = (1 - t) * ‖x‖ + t * 1 := by rw [hfx1 x hx]
      _ ≤ (1 - t) * 1 + t * 1 := by
            have h1t : (0:ℝ) ≤ 1 - t := by linarith
            nlinarith [hx1, h1t, ht, norm_nonneg x]
      _ = 1 := by ring
  have hmapB : ∀ x ∈ Metric.ball (0:E) 1, (1 - t) • x + t • f x ∈ Metric.ball (0:E) 1 := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    have hx1 : ‖x‖ < 1 := by rwa [mem_ball, dist_zero_right] at hx
    have hxcb : x ∈ Metric.closedBall (0:E) 1 := by
      rw [mem_closedBall, dist_zero_right]; exact le_of_lt hx1
    calc ‖(1 - t) • x + t • f x‖ ≤ (1 - t) * ‖x‖ + t * ‖f x‖ := hnorm x
      _ = (1 - t) * ‖x‖ + t * 1 := by rw [hfx1 x hxcb]
      _ < (1 - t) * 1 + t * 1 := by
            have h1t : (0:ℝ) < 1 - t := by linarith
            nlinarith [hx1, h1t, ht]
      _ = 1 := by ring
  have hopen : IsOpen ((fun x => (1 - t) • x + t • f x) '' Metric.ball (0:E) 1) :=
    isOpen_image_interp f hf hinv
  have hclosed : IsClosed ((fun x => (1 - t) • x + t • f x) '' Metric.ball (0:E) 1 ∪ Metric.sphere (0:E) 1) := by
    have heq : (fun x => (1 - t) • x + t • f x) '' Metric.closedBall (0:E) 1
        = (fun x => (1 - t) • x + t • f x) '' Metric.ball (0:E) 1 ∪ Metric.sphere (0:E) 1 := by
      rw [← ball_union_sphere (x := (0:E)) (ε := 1), image_union, himgS]
    rw [← heq]
    exact ((isCompact_closedBall (0:E) 1).image hgcont).isClosed
  have hball_sub : Metric.ball (0:E) 1 ⊆ (fun x => (1 - t) • x + t • f x) '' Metric.ball (0:E) 1 :=
    subset_of_isPreconnected_of_isOpen_of_isClosedIn
      (convex_ball (0:E) 1).isPreconnected hopen
      (by rintro y ⟨x, hx, hyx⟩; rw [← hyx]; exact hmapB x hx)
      (by
        intro y hy hyB
        have hyc : y ∈ closure ((fun x => (1 - t) • x + t • f x) '' Metric.ball (0:E) 1 ∪ Metric.sphere (0:E) 1) :=
          closure_mono Set.subset_union_left hy
        rw [hclosed.closure_eq] at hyc
        rcases hyc with hyc | hyc
        · exact hyc
        · exfalso
          rw [mem_ball, dist_zero_right] at hyB
          rw [mem_sphere_iff_norm, sub_zero] at hyc
          linarith)
      ⟨(fun x => (1 - t) • x + t • f x) 0, 0, Metric.mem_ball_self (by norm_num : (0:ℝ) < 1), rfl⟩
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, hyx⟩
    rw [← hyx]; exact hmapC x hx
  · intro y hy
    have hy' : y ∈ Metric.ball (0:E) 1 ∪ Metric.sphere (0:E) 1 := by
      rw [ball_union_sphere]; exact hy
    rcases hy' with hyb | hys
    · exact Set.image_mono Metric.ball_subset_closedBall (hball_sub hyb)
    · exact ⟨y, Metric.sphere_subset_closedBall hys, hgfix y hys⟩

end Work.Mostow
