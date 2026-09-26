import Mathlib
import Submission.Work.CoreTopology.Disk

/-!
# A disc parametrisation of the union of two convex planar sets

`Work.Drive.Mono.exists_discParam_of_two_convex`: if `A`, `B` are open, convex, bounded subsets of
the plane with `A ∩ B ≠ ∅`, then `closure (A ∪ B)` is the image of the closed unit disc `𝔻 ⊂ ℂ`
under an injective continuous map whose boundary circle maps onto `frontier (A ∪ B)`.

The construction is completely explicit.  Pick `p ∈ A ∩ B`; then `closure (A ∪ B)` is star-shaped
with respect to `p`, and in fact is described by a "gauge"

`G x = min (gauge (closure (A - p)) (x - p)) (gauge (closure (B - p)) (x - p))`

which is continuous, satisfies `G x ≤ 1 ↔ x ∈ closure (A ∪ B)`, `G x < 1 ↔ x ∈ interior (A ∪ B)`
and is positively homogeneous.  The map

`e z = p + (‖z‖ / G (z)) • z`   (`z` read in `ℂ ≅ ℝ²` via an orthonormal basis)

is then a homeomorphism from `𝔻` onto `closure (A ∪ B)` carrying the unit circle onto the frontier.

## Main results

* `Work.Drive.Mono.continuous_radial`, `Work.Drive.Mono.radial_image_closedBall`,
  `Work.Drive.Mono.radial_image_sphere` — the radial map of a gauge-like function.
* `Work.Drive.Mono.exists_discParam_of_two_convex_zero` — the case `0 ∈ A ∩ B`.
* `Work.Drive.Mono.exists_discParam_of_two_convex` — the general case.
-/

namespace Work.Drive.Mono

open Set Metric
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The radial map of a gauge-like function -/

/-- The radial map associated with a "gauge" `G`: `radial G x` is the multiple of `x` lying on the
level set `{G = ‖x‖}`.  When `G ≤ 1` describes a star-shaped bounded set, this retracts the closed
unit ball onto that set, keeping the unit sphere on the boundary. -/
def radial (G : E → ℝ) (x : E) : E := (‖x‖ / G x) • x

theorem radial_zero (G : E → ℝ) (hG0 : G 0 = 0) : radial G 0 = 0 := by
  simp [radial, hG0]

theorem norm_radial {G : E → ℝ} (hG0 : G 0 = 0) (hpos : ∀ x, x ≠ 0 → 0 < G x) (x : E) :
    ‖radial G x‖ = ‖x‖ * (‖x‖ / G x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radial, hG0]
  · rw [radial, norm_smul, mul_comm, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (hpos x hx).le)]

/-- The radial map of a continuous, positive definite, positively homogeneous function which is
bounded below by `‖x‖ / C` is continuous. -/
theorem continuous_radial {G : E → ℝ} (hGc : Continuous G) (hG0 : G 0 = 0)
    (hpos : ∀ x, x ≠ 0 → 0 < G x) {C : ℝ} (hbound : ∀ x, ‖x‖ / G x ≤ C) :
    Continuous (radial G) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, radial_zero G hG0]
    refine squeeze_zero_norm (a := fun y => C * ‖y‖) (fun y => ?_) ?_
    · rw [norm_radial hG0 hpos y]
      calc ‖y‖ * (‖y‖ / G y) ≤ ‖y‖ * C := mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _)
        _ = C * ‖y‖ := by ring
    · simpa using (continuous_norm.tendsto (0:E)).const_mul C
  · exact ((continuous_norm.continuousAt.div hGc.continuousAt (hpos x hx).ne').smul
      continuousAt_id)

/-! ## The gauge function of a union of two convex sets -/

/-- The minimum of the gauges of the closures of `A` and `B`.  When `0` is an interior point of
both `A` and `B` this is a positive definite, positively homogeneous continuous function whose
unit sublevel set is `closure A ∪ closure B`. -/
def twoConvexG (A B : Set E) : E → ℝ := fun x => min (gauge (closure A) x) (gauge (closure B) x)

theorem twoConvexG_smul {A B : Set E} {c : ℝ} (hc : 0 ≤ c) (x : E) :
    twoConvexG A B (c • x) = c * twoConvexG A B x := by
  have h1 := gauge_smul_of_nonneg (s := closure A) hc x
  have h2 := gauge_smul_of_nonneg (s := closure B) hc x
  simp only [twoConvexG, h1, h2, smul_eq_mul]
  exact (mul_min_of_nonneg _ _ hc).symm

theorem twoConvexG_zero (A B : Set E) : twoConvexG A B 0 = 0 := by
  simp [twoConvexG]

theorem twoConvexG_pos {A B : Set E} (hAb : Bornology.IsBounded A) (hAn : closure A ∈ 𝓝 (0:E))
    (hBb : Bornology.IsBounded B) (hBn : closure B ∈ 𝓝 (0:E)) {x : E} (hx : x ≠ 0) :
    0 < twoConvexG A B x := by
  rw [twoConvexG]
  exact lt_min ((gauge_pos (absorbent_nhds_zero hAn)
      (NormedSpace.isVonNBounded_of_isBounded ℝ hAb.closure)).2 hx)
    ((gauge_pos (absorbent_nhds_zero hBn)
      (NormedSpace.isVonNBounded_of_isBounded ℝ hBb.closure)).2 hx)

theorem twoConvexG_le_one_iff {A B : Set E} (hAc : Convex ℝ A) (hAn : closure A ∈ 𝓝 (0:E))
    (hBc : Convex ℝ B) (hBn : closure B ∈ 𝓝 (0:E)) (x : E) :
    twoConvexG A B x ≤ 1 ↔ x ∈ closure A ∪ closure B := by
  rw [twoConvexG, min_le_iff, gauge_le_one_iff_mem_closure hAc.closure hAn,
    gauge_le_one_iff_mem_closure hBc.closure hBn, closure_closure, closure_closure,
    mem_union]

/-- The gauge of two convex sets: `interior (closure A ∪ closure B)` is exactly `{G < 1}`.  The
non-trivial inclusion is the one from the interior: a point at level `≥ 1` can be scaled slightly
outwards, and the scaled point still lies outside the union. -/
theorem twoConvexG_lt_one_iff {A B : Set E} (hAc : Convex ℝ A) (hAn : closure A ∈ 𝓝 (0:E))
    (hBc : Convex ℝ B) (hBn : closure B ∈ 𝓝 (0:E)) (x : E) :
    twoConvexG A B x < 1 ↔ x ∈ interior (closure A ∪ closure B) := by
  constructor
  · intro h
    rw [twoConvexG, min_lt_iff] at h
    rcases h with h | h
    · exact interior_mono subset_union_left ((gauge_lt_one_iff_mem_interior hAc.closure hAn).1 h)
    · exact interior_mono subset_union_right ((gauge_lt_one_iff_mem_interior hBc.closure hBn).1 h)
  · intro hx
    by_contra hcon
    rw [not_lt] at hcon
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
    obtain ⟨ε, hε, hεsub⟩ := hx
    have hxne : x ≠ 0 := by
      rintro rfl
      rw [twoConvexG_zero] at hcon
      linarith
    have hnorm : 0 < ‖x‖ := norm_pos_iff.2 hxne
    set δ := ε / (2 * ‖x‖) with hδdef
    have hδpos : 0 < δ := by positivity
    have hδnorm : δ * ‖x‖ = ε / 2 := by rw [hδdef]; field_simp
    have hy : (1 + δ) • x ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : (1 + δ) • x - x = δ • x := by module
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos, hδnorm]
      linarith
    have hyK : (1 + δ) • x ∈ closure A ∪ closure B := hεsub hy
    have hyle : twoConvexG A B ((1 + δ) • x) ≤ 1 :=
      (twoConvexG_le_one_iff hAc hAn hBc hBn _).2 hyK
    have hhom : twoConvexG A B ((1 + δ) • x) = (1 + δ) * twoConvexG A B x :=
      twoConvexG_smul (by linarith) x
    rw [hhom] at hyle
    nlinarith [hyle, hcon]

theorem twoConvexG_radial {A B : Set E} (hpos : ∀ x : E, x ≠ 0 → 0 < twoConvexG A B x) (x : E) :
    twoConvexG A B (radial (twoConvexG A B) x) = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radial, twoConvexG_zero]
  · rw [radial, twoConvexG_smul (div_nonneg (norm_nonneg _) (hpos x hx).le),
      div_mul_cancel₀ _ (hpos x hx).ne']

/-- The gauge is bounded below by `‖x‖ / R` when the union is contained in the ball of radius `R`
about the origin. -/
theorem norm_le_mul_gauge {C : Set E} {R : ℝ} (hR : 0 < R)
    (hsub : C ⊆ Metric.closedBall (0:E) R) (habs : Absorbent ℝ C) (x : E) :
    ‖x‖ ≤ R * gauge C x := by
  by_contra hcon
  rw [not_le] at hcon
  have hlt : gauge C x < ‖x‖ / R := by
    rw [lt_div_iff₀ hR]; simpa [mul_comm] using hcon
  obtain ⟨r, hgr, hr⟩ := exists_between hlt
  obtain ⟨b, hb0, hbr, hxb⟩ := exists_lt_of_gauge_lt habs hgr
  obtain ⟨y, hyC, hyx⟩ := hxb
  have hyR : ‖y‖ ≤ R := by
    have := hsub hyC
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hxnorm : ‖x‖ = b * ‖y‖ := by
    rw [← hyx, norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
  have hbre : b * R < r * R := mul_lt_mul_of_pos_right hbr hR
  have hrx : r * R < ‖x‖ := by
    have := (lt_div_iff₀ hR).mp hr
    simpa [mul_comm] using this
  have hle : b * ‖y‖ ≤ b * R := mul_le_mul_of_nonneg_left hyR hb0.le
  have : b * ‖y‖ < ‖x‖ := lt_trans (lt_of_le_of_lt hle hbre) hrx
  rw [hxnorm] at this
  exact lt_irrefl _ this

theorem twoConvexG_bound {A B : Set E} (hAb : Bornology.IsBounded A) (hAn : closure A ∈ 𝓝 (0:E))
    (hBb : Bornology.IsBounded B) (hBn : closure B ∈ 𝓝 (0:E)) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : E, ‖x‖ / twoConvexG A B x ≤ R := by
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0:E)).mp
    (hAb.closure.union hBb.closure)
  refine ⟨max R₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x => ?_⟩
  set R := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsubA : closure A ⊆ Metric.closedBall (0:E) R := fun y hy =>
    Metric.closedBall_subset_closedBall (le_max_left _ _) (hR₀ (Or.inl hy))
  have hsubB : closure B ⊆ Metric.closedBall (0:E) R := fun y hy =>
    Metric.closedBall_subset_closedBall (le_max_left _ _) (hR₀ (Or.inr hy))
  have hbA := norm_le_mul_gauge hRpos hsubA (absorbent_nhds_zero hAn) x
  have hbB := norm_le_mul_gauge hRpos hsubB (absorbent_nhds_zero hBn) x
  rcases eq_or_ne x 0 with rfl | hx
  · have h : ‖(0:E)‖ / twoConvexG A B 0 = 0 := by simp [twoConvexG]
    rw [h]; exact hRpos.le
  · rw [div_le_iff₀ (twoConvexG_pos hAb hAn hBb hBn hx)]
    rw [twoConvexG, mul_min_of_nonneg _ _ hRpos.le]
    exact le_min hbA hbB

/-! ## The radial retraction onto the union -/

theorem radial_smul {A B : Set E} (hpos : ∀ x : E, x ≠ 0 → 0 < twoConvexG A B x)
    {c : ℝ} (hc : 0 ≤ c) (x : E) :
    radial (twoConvexG A B) (c • x) = c • radial (twoConvexG A B) x := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp [radial]
  · rcases eq_or_ne x 0 with rfl | hx
    · simp [radial]
    · rw [radial, radial, twoConvexG_smul hc x, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      rw [mul_div_mul_left _ _ hc0]
      rw [smul_smul, smul_smul, mul_comm]

theorem radial_inv_smul {A B : Set E} (hpos : ∀ x : E, x ≠ 0 → 0 < twoConvexG A B x)
    {x : E} (hx : x ≠ 0) :
    (twoConvexG A B x / ‖x‖) • radial (twoConvexG A B) x = x := by
  have hGx : twoConvexG A B x ≠ 0 := (hpos x hx).ne'
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have h1 : twoConvexG A B x / ‖x‖ * (‖x‖ / twoConvexG A B x) = 1 := by
    field_simp
  rw [radial, smul_smul, h1, one_smul]

theorem radial_injective {A B : Set E} (hpos : ∀ x : E, x ≠ 0 → 0 < twoConvexG A B x) :
    Function.Injective (radial (twoConvexG A B)) := by
  intro x y hxy
  have hpos' : ∀ x : E, x ≠ 0 → 0 < twoConvexG A B x := hpos
  rcases eq_or_ne x 0 with rfl | hx
  · have hy0 : y = 0 := by
      have h1 := twoConvexG_radial (A := A) (B := B) hpos' y
      rw [← hxy, radial_zero _ (twoConvexG_zero A B), twoConvexG_zero] at h1
      exact norm_eq_zero.1 h1.symm
    rw [hy0]
  · rcases eq_or_ne y 0 with rfl | hy
    · have hx0 : x = 0 := by
        have h1 := twoConvexG_radial (A := A) (B := B) hpos' x
        rw [hxy, radial_zero _ (twoConvexG_zero A B), twoConvexG_zero] at h1
        exact norm_eq_zero.1 h1.symm
      exact hx0
    · have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
      have h1 := radial_inv_smul (A := A) (B := B) hpos' hx
      have h2 := radial_inv_smul (A := A) (B := B) hpos' hy
      rw [hxy] at h1
      have ht : ‖x‖ = ‖y‖ := by
        have h3 := twoConvexG_radial (A := A) (B := B) hpos' x
        rw [hxy, twoConvexG_radial (A := A) (B := B) hpos' y] at h3
        exact h3.symm
      have hpne : radial (twoConvexG A B) y ≠ 0 := by
        intro hp
        have h3 := twoConvexG_radial (A := A) (B := B) hpos' y
        rw [hp, twoConvexG_zero] at h3
        exact hy (norm_eq_zero.1 h3.symm)
      have hnp : 0 < ‖radial (twoConvexG A B) y‖ := norm_pos_iff.2 hpne
      have hG : twoConvexG A B x = twoConvexG A B y := by
        have e1 : ‖x‖ = (twoConvexG A B x / ‖x‖) * ‖radial (twoConvexG A B) y‖ := by
          conv_lhs => rw [← h1]
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (hpos' x hx).le (norm_nonneg _))]
        have e2 : ‖y‖ = (twoConvexG A B y / ‖y‖) * ‖radial (twoConvexG A B) y‖ := by
          conv_lhs => rw [← h2]
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (hpos' y hy).le (norm_nonneg _))]
        have hcancel : twoConvexG A B x / ‖x‖ = twoConvexG A B y / ‖y‖ :=
          mul_right_cancel₀ (ne_of_gt hnp) (by rw [← e1, ← e2, ht])
        rw [← div_mul_cancel₀ (twoConvexG A B x) hx0, hcancel, ht,
          div_mul_cancel₀ (twoConvexG A B y) hy0]
      rw [hG, ht] at h1
      rw [← h1, h2]

theorem frontier_eq_gauge_eq_one {A B : Set E} (hAc : Convex ℝ A) (hAn : closure A ∈ 𝓝 (0:E))
    (hBc : Convex ℝ B) (hBn : closure B ∈ 𝓝 (0:E)) :
    frontier (closure A ∪ closure B) = {x : E | twoConvexG A B x = 1} := by
  have hcl : closure (closure A ∪ closure B) = closure A ∪ closure B := by simp
  rw [← closure_sdiff_interior, hcl]
  ext x
  simp only [mem_sdiff, mem_ofPred_eq]
  rw [← twoConvexG_le_one_iff hAc hAn hBc hBn x, ← twoConvexG_lt_one_iff hAc hAn hBc hBn x]
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h1 (not_lt.1 h2)
  · intro h; exact ⟨h.le, by rw [h]; norm_num⟩

theorem radial_image_closedBall {A B : Set E} (hAc : Convex ℝ A) (hAn : closure A ∈ 𝓝 (0:E))
    (hAb : Bornology.IsBounded A) (hBc : Convex ℝ B) (hBn : closure B ∈ 𝓝 (0:E))
    (hBb : Bornology.IsBounded B) :
    radial (twoConvexG A B) '' Metric.closedBall (0:E) 1 = closure A ∪ closure B := by
  have hpos : ∀ x : E, x ≠ 0 → 0 < twoConvexG A B x := fun x hx =>
    twoConvexG_pos hAb hAn hBb hBn hx
  refine Subset.antisymm ?_ ?_
  · rintro p ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rw [← twoConvexG_le_one_iff hAc hAn hBc hBn, twoConvexG_radial (A := A) (B := B) hpos x]
    exact hx
  · intro x hxK
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨0, by simp, by rw [radial_zero _ (twoConvexG_zero A B)]⟩
    · have hGx : 0 < twoConvexG A B x := hpos x hx0
      have hnorm : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hGxle : twoConvexG A B x ≤ 1 := (twoConvexG_le_one_iff hAc hAn hBc hBn x).2 hxK
      have hu_one : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hnorm.le),
          inv_mul_cancel₀ hnorm.ne']
      refine ⟨twoConvexG A B x • (‖x‖⁻¹ • x), ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hGx.le, hu_one, mul_one]
        exact hGxle
      · have hGu : twoConvexG A B (‖x‖⁻¹ • x) = ‖x‖⁻¹ * twoConvexG A B x :=
          twoConvexG_smul (inv_nonneg.2 hnorm.le) x
        have hr : radial (twoConvexG A B) (‖x‖⁻¹ • x)
            = (1 / (‖x‖⁻¹ * twoConvexG A B x)) • (‖x‖⁻¹ • x) := by
          rw [radial, hu_one, hGu]
        rw [radial_smul hpos hGx.le, hr, smul_smul, smul_smul]
        have h2 : twoConvexG A B x * (1 / (‖x‖⁻¹ * twoConvexG A B x)) * ‖x‖⁻¹ = 1 := by
          field_simp
        rw [h2, one_smul]

theorem radial_image_sphere {A B : Set E} (hAc : Convex ℝ A) (hAn : closure A ∈ 𝓝 (0:E))
    (hAb : Bornology.IsBounded A) (hBc : Convex ℝ B) (hBn : closure B ∈ 𝓝 (0:E))
    (hBb : Bornology.IsBounded B) :
    radial (twoConvexG A B) '' Metric.sphere (0:E) 1 = frontier (closure A ∪ closure B) := by
  have hpos : ∀ x : E, x ≠ 0 → 0 < twoConvexG A B x := fun x hx =>
    twoConvexG_pos hAb hAn hBb hBn hx
  rw [frontier_eq_gauge_eq_one hAc hAn hBc hBn]
  refine Subset.antisymm ?_ ?_
  · rintro p ⟨x, hx, rfl⟩
    rw [Metric.mem_sphere, dist_zero_right] at hx
    rw [mem_ofPred_eq, twoConvexG_radial (A := A) (B := B) hpos x, hx]
  · intro x hx
    rw [mem_ofPred_eq] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [twoConvexG_zero] at hx
      norm_num at hx
    have hnorm : 0 < ‖x‖ := norm_pos_iff.2 hx0
    refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
    · rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.2 hnorm.le), inv_mul_cancel₀ hnorm.ne']
    · have hu_one : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hnorm.le),
          inv_mul_cancel₀ hnorm.ne']
      rw [radial, hu_one, twoConvexG_smul (inv_nonneg.2 hnorm.le) x, hx, mul_one,
        one_div, inv_inv]
      rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]

/-- The interior of the union of the closures is the union of the interiors. -/
theorem interior_closure_union_eq {A B : Set E} (hAc : Convex ℝ A) (hAn : closure A ∈ 𝓝 (0:E))
    (hBc : Convex ℝ B) (hBn : closure B ∈ 𝓝 (0:E)) :
    interior (closure A ∪ closure B) = interior (closure A) ∪ interior (closure B) := by
  refine Subset.antisymm ?_ ?_
  · intro x hx
    have h1 : twoConvexG A B x < 1 := (twoConvexG_lt_one_iff hAc hAn hBc hBn x).2 hx
    rw [twoConvexG, min_lt_iff] at h1
    rcases h1 with h1 | h1
    · exact Or.inl ((gauge_lt_one_iff_mem_interior hAc.closure hAn).1 h1)
    · exact Or.inr ((gauge_lt_one_iff_mem_interior hBc.closure hBn).1 h1)
  · exact union_subset (interior_mono subset_union_left) (interior_mono subset_union_right)

/-- For open convex `A`, `B` containing `0` in their closure, the frontier of `A ∪ B` is the
frontier of `closure A ∪ closure B` (the difference between the two being only the open sets
`A`, `B`, which are the interiors of their closures). -/
theorem frontier_union_eq_frontier_closure_union {A B : Set E}
    (hAo : IsOpen A) (hAc : Convex ℝ A) (hneA : (interior A).Nonempty) (hAn : closure A ∈ 𝓝 (0:E))
    (hBo : IsOpen B) (hBc : Convex ℝ B) (hneB : (interior B).Nonempty) (hBn : closure B ∈ 𝓝 (0:E)) :
    frontier (A ∪ B) = frontier (closure A ∪ closure B) := by
  have hAint : interior (closure A) = A :=
    (hAc.interior_closure_eq_interior_of_nonempty_interior hneA).trans hAo.interior_eq
  have hBint : interior (closure B) = B :=
    (hBc.interior_closure_eq_interior_of_nonempty_interior hneB).trans hBo.interior_eq
  have hcl : closure (closure A ∪ closure B) = closure A ∪ closure B := by simp
  have hint : interior (closure A ∪ closure B) = A ∪ B := by
    rw [interior_closure_union_eq hAc hAn hBc hBn, hAint, hBint]
  rw [← closure_sdiff_interior (A ∪ B), ← closure_sdiff_interior (closure A ∪ closure B),
    closure_union, (hAo.union hBo).interior_eq, hcl, hint]

/-- Every point of the unit sphere of `ℂ` is of the form `circlePoint θ`. -/
theorem range_circlePoint :
    Set.range (fun θ : ℝ => ((Work.CoreTopology.circlePoint θ : Metric.closedBall (0:ℂ) 1) : ℂ))
      = Metric.sphere (0:ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨θ, rfl⟩
    simp only [Work.CoreTopology.circlePoint_coe, Metric.mem_sphere, dist_zero_right]
    exact Complex.norm_exp_ofReal_mul_I θ
  · intro hz
    rw [Metric.mem_sphere, dist_zero_right] at hz
    refine ⟨Complex.arg z, ?_⟩
    simp only [Work.CoreTopology.circlePoint_coe]
    have h := Complex.norm_mul_exp_arg_mul_I z
    simpa [hz] using h

/-! ## The core case `0 ∈ A ∩ B` -/

/-- The planar disc parametrisation of `closure (A ∪ B)` for two convex open bounded sets `A`, `B`
containing the origin. -/
theorem exists_discParam_of_two_convex_zero (A B : Set (EuclideanSpace ℝ (Fin 2)))
    (hAo : IsOpen A) (hAc : Convex ℝ A) (hAb : Bornology.IsBounded A)
    (hBo : IsOpen B) (hBc : Convex ℝ B) (hBb : Bornology.IsBounded B)
    (h0A : (0 : EuclideanSpace ℝ (Fin 2)) ∈ A) (h0B : (0 : EuclideanSpace ℝ (Fin 2)) ∈ B) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = closure (A ∪ B) ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (A ∪ B) := by
  have hAn : closure A ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)) :=
    Filter.mem_of_superset (hAo.mem_nhds h0A) subset_closure
  have hBn : closure B ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 2)) :=
    Filter.mem_of_superset (hBo.mem_nhds h0B) subset_closure
  have hpos : ∀ x : EuclideanSpace ℝ (Fin 2), x ≠ 0 → 0 < twoConvexG A B x :=
    fun x hx => twoConvexG_pos hAb hAn hBb hBn hx
  obtain ⟨R, hRpos, hbound⟩ := twoConvexG_bound hAb hAn hBb hBn
  have hGc : Continuous (twoConvexG A B) :=
    (continuous_gauge hAc.closure hAn).min (continuous_gauge hBc.closure hBn)
  have hρc : Continuous (radial (twoConvexG A B)) :=
    continuous_radial hGc (twoConvexG_zero A B) hpos hbound
  have hneA : (interior A).Nonempty := ⟨0, by rw [hAo.interior_eq]; exact h0A⟩
  have hneB : (interior B).Nonempty := ⟨0, by rw [hBo.interior_eq]; exact h0B⟩
  set Φ : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr with hΦdef
  have hΦ0 : Φ 0 = 0 := map_zero Φ
  set f : Metric.closedBall (0 : ℂ) 1 → EuclideanSpace ℝ (Fin 2) :=
    fun z => radial (twoConvexG A B) (Φ (z : ℂ)) with hfdef
  have hfc : Continuous f := hρc.comp (Φ.continuous.comp continuous_subtype_val)
  refine ⟨⟨f, hfc⟩, ?_, ?_, ?_⟩
  · intro z w hzw
    exact Subtype.ext (Φ.injective (radial_injective (A := A) (B := B) hpos hzw))
  · show Set.range f = closure (A ∪ B)
    have hφ : Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => Φ (z : ℂ))
        = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [show (fun z : Metric.closedBall (0 : ℂ) 1 => Φ (z : ℂ))
          = Φ ∘ (Subtype.val : Metric.closedBall (0 : ℂ) 1 → ℂ) from rfl, Set.range_comp,
        Subtype.range_coe, LinearIsometryEquiv.image_closedBall, hΦ0]
    rw [show f = (radial (twoConvexG A B)) ∘ (fun z : Metric.closedBall (0 : ℂ) 1 => Φ (z : ℂ))
        from rfl, Set.range_comp, hφ, radial_image_closedBall hAc hAn hAb hBc hBn hBb,
      closure_union]
  · show Set.range (fun θ : ℝ => f (Work.CoreTopology.circlePoint θ)) = frontier (A ∪ B)
    have hφ : Set.range (fun θ : ℝ => Φ (((Work.CoreTopology.circlePoint θ :
        Metric.closedBall (0 : ℂ) 1) : ℂ)))
        = Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [show (fun θ : ℝ => Φ (((Work.CoreTopology.circlePoint θ :
            Metric.closedBall (0 : ℂ) 1) : ℂ)))
          = Φ ∘ (fun θ : ℝ => ((Work.CoreTopology.circlePoint θ :
              Metric.closedBall (0 : ℂ) 1) : ℂ)) from rfl, Set.range_comp,
        range_circlePoint, LinearIsometryEquiv.image_sphere, hΦ0]
    rw [show (fun θ : ℝ => f (Work.CoreTopology.circlePoint θ))
        = (radial (twoConvexG A B)) ∘ (fun θ : ℝ => Φ (((Work.CoreTopology.circlePoint θ :
            Metric.closedBall (0 : ℂ) 1) : ℂ))) from rfl, Set.range_comp, hφ,
      radial_image_sphere hAc hAn hAb hBc hBn hBb,
      frontier_union_eq_frontier_closure_union hAo hAc hneA hAn hBo hBc hneB hBn]

/-! ## The general case -/

theorem exists_discParam_of_two_convex (A B : Set (EuclideanSpace ℝ (Fin 2)))
    (hAo : IsOpen A) (hAc : Convex ℝ A) (hAb : Bornology.IsBounded A)
    (hBo : IsOpen B) (hBc : Convex ℝ B) (hBb : Bornology.IsBounded B)
    (hne : (A ∩ B).Nonempty) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = closure (A ∪ B) ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (A ∪ B) := by
  obtain ⟨p, hpA, hpB⟩ := hne
  set τ : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) := Homeomorph.subRight p with hτdef
  set σ : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2) := Homeomorph.addLeft p with hσdef
  set A' : Set (EuclideanSpace ℝ (Fin 2)) := τ '' A with hA'def
  set B' : Set (EuclideanSpace ℝ (Fin 2)) := τ '' B with hB'def
  have hA'o : IsOpen A' := by
    rw [hA'def]; exact (Homeomorph.isOpen_image τ).mpr hAo
  have hB'o : IsOpen B' := by
    rw [hB'def]; exact (Homeomorph.isOpen_image τ).mpr hBo
  have hA'c : Convex ℝ A' := by
    rw [hA'def, hτdef, Homeomorph.coe_subRight]
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ u v hu hv huv
    refine ⟨u • a + v • b, hAc ha hb hu hv huv, ?_⟩
    have hv' : v = 1 - u := by linarith
    rw [hv']
    module
  have hB'c : Convex ℝ B' := by
    rw [hB'def, hτdef, Homeomorph.coe_subRight]
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ u v hu hv huv
    refine ⟨u • a + v • b, hBc ha hb hu hv huv, ?_⟩
    have hv' : v = 1 - u := by linarith
    rw [hv']
    module
  have hA'b : Bornology.IsBounded A' := by
    rw [hA'def, hτdef, Homeomorph.coe_subRight]
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall p).mp hAb
    refine (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 2))).mpr ⟨R, ?_⟩
    rintro x ⟨a, ha, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR ha
  have hB'b : Bornology.IsBounded B' := by
    rw [hB'def, hτdef, Homeomorph.coe_subRight]
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall p).mp hBb
    refine (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 2))).mpr ⟨R, ?_⟩
    rintro x ⟨a, ha, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hR ha
  have h0A' : (0 : EuclideanSpace ℝ (Fin 2)) ∈ A' := by
    rw [hA'def, hτdef, Homeomorph.coe_subRight]; exact ⟨p, hpA, by simp⟩
  have h0B' : (0 : EuclideanSpace ℝ (Fin 2)) ∈ B' := by
    rw [hB'def, hτdef, Homeomorph.coe_subRight]; exact ⟨p, hpB, by simp⟩
  obtain ⟨e₀, he₀inj, he₀range, he₀circ⟩ :=
    exists_discParam_of_two_convex_zero A' B' hA'o hA'c hA'b hB'o hB'c hB'b h0A' h0B'
  have hσA : σ '' A' = A := by
    rw [hA'def, hσdef, hτdef, Homeomorph.coe_addLeft, Homeomorph.coe_subRight]
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      simpa using ha
    · intro hx
      exact ⟨x - p, ⟨x, hx, rfl⟩, by simp⟩
  have hσB : σ '' B' = B := by
    rw [hB'def, hσdef, hτdef, Homeomorph.coe_addLeft, Homeomorph.coe_subRight]
    ext x
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      simpa using ha
    · intro hx
      exact ⟨x - p, ⟨x, hx, rfl⟩, by simp⟩
  have hσAB : σ '' (A' ∪ B') = A ∪ B := by
    rw [image_union, hσA, hσB]
  refine ⟨⟨fun z => σ (e₀ z), σ.continuous.comp e₀.continuous⟩, ?_, ?_, ?_⟩
  · intro z w hzw
    exact he₀inj (σ.injective hzw)
  · show Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => σ (e₀ z)) = closure (A ∪ B)
    have hrange : Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => σ (e₀ z))
        = σ '' Set.range e₀ :=
      Set.range_comp σ e₀
    rw [hrange, he₀range, Homeomorph.image_closure, hσAB]
  · show Set.range (fun θ : ℝ => σ (e₀ (Work.CoreTopology.circlePoint θ)))
        = frontier (A ∪ B)
    have hcirc : Set.range (fun θ : ℝ => σ (e₀ (Work.CoreTopology.circlePoint θ)))
        = σ '' Set.range (fun θ : ℝ => e₀ (Work.CoreTopology.circlePoint θ)) :=
      Set.range_comp σ (fun θ : ℝ => e₀ (Work.CoreTopology.circlePoint θ))
    rw [hcirc, he₀circ, Homeomorph.image_frontier, hσAB]

end

end Work.Drive.Mono
