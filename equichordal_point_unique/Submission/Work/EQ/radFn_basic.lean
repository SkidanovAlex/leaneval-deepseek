import Mathlib
import Submission.Work.EQ.normDefs

/-!
# Basic properties of the radial function `radFn`

`radFn K O v = 1 / gauge (K - O) v` is the distance from the interior point `O` to the
frontier of `K` along the direction `v`.  This file establishes the three facts used
everywhere downstream:

* `0 < radFn K O v` for `v ≠ 0`;
* for `t > 0` and `v ≠ 0`, the point `O + t • v` lies on `frontier K` **iff** `t = radFn K O v`
  (so every ray from `O` meets the frontier exactly once);
* `Y ∈ frontier K` iff `Y` is the point reached from `O` at distance `radFn K O v` in some
  unit direction `v` (so the frontier is the polar graph of `radFn` about `O`).

The proofs are a direct translation of the Minkowski-functional ("gauge") theory about the
translated convex body `shiftSet K O = K - O` (for which `0` is an interior point).
-/

namespace Work.EQ

open LeanEval.Geometry.Equichordal
open Set Metric
open scoped Topology

/-- Membership in the translation `shiftSet K O = K - O`: a point `z` lies in `K - O` exactly
when `z + O` lies in `K`. -/
lemma mem_shiftSet (K : Set Plane) (O z : Plane) : z ∈ shiftSet K O ↔ z + O ∈ K := by
  rw [shiftSet, Set.mem_image]
  constructor
  · rintro ⟨x, hx, hxz⟩
    rw [Homeomorph.coe_addLeft] at hxz
    have hx' : x = z + O := by
      have h := congrArg (fun w : Plane => w + O) hxz
      simpa using h
    simpa [hx'] using hx
  · intro hz
    exact ⟨z + O, hz, by rw [Homeomorph.coe_addLeft]; abel_nf⟩

/-- If `O` is an interior point of `K` then `0` is an interior point of `K - O`, i.e.
`K - O` is a neighbourhood of the origin. -/
lemma shiftSet_mem_nhds (K : Set Plane) (O : Plane) (hO : O ∈ interior K) :
    shiftSet K O ∈ 𝓝 (0 : Plane) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hO
  obtain ⟨ε, hε, hεK⟩ := hO
  rw [Metric.mem_nhds_iff]
  refine ⟨ε, hε, fun z hz => ?_⟩
  rw [mem_shiftSet]
  refine hεK ?_
  rw [Metric.mem_ball] at hz ⊢
  simpa [dist_eq_norm] using hz

theorem radFn_basic {K : Set (EuclideanSpace ℝ (Fin 2))}
    {O : EuclideanSpace ℝ (Fin 2)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hO : O ∈ interior K) :
    (∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 → 0 < radFn K O v) ∧
    (∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 → ∀ t : ℝ, 0 < t →
      (O + t • v ∈ frontier K ↔ t = radFn K O v)) ∧
    (∀ Y : EuclideanSpace ℝ (Fin 2), Y ∈ frontier K ↔
      ∃ v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, Y = O + radFn K O v • v) := by
  -- `K - O` is convex, a neighbourhood of `0`, and bounded (it is compact).
  have hSconv : Convex ℝ (shiftSet K O) := hconv.translate (-O)
  have hSnhds : shiftSet K O ∈ 𝓝 (0 : Plane) := shiftSet_mem_nhds K O hO
  have hSabs : Absorbent ℝ (shiftSet K O) := absorbent_nhds_zero hSnhds
  have hSbdd : Bornology.IsVonNBounded ℝ (shiftSet K O) :=
    (hK.image (Homeomorph.addLeft (-O)).continuous).isVonNBounded ℝ
  have hgauge_pos : ∀ v : Plane, v ≠ 0 → 0 < gauge (shiftSet K O) v :=
    fun v hv => (gauge_pos hSabs hSbdd).2 hv
  -- The frontier translates with `K - O`.
  have hfront : ∀ y : Plane, y ∈ frontier K ↔ y - O ∈ frontier (shiftSet K O) := by
    intro y
    have himg : frontier (shiftSet K O) = (Homeomorph.addLeft (-O)) '' frontier K := by
      rw [shiftSet]
      exact (Homeomorph.image_frontier (Homeomorph.addLeft (-O)) K).symm
    rw [himg, show y - O = ⇑(Homeomorph.addLeft (-O)) y by
      rw [Homeomorph.coe_addLeft]; abel_nf]
    exact ((Homeomorph.addLeft (-O)).injective.mem_set_image (s := frontier K) (a := y)).symm
  -- The ray from `O` in direction `v` meets the frontier exactly at `radFn K O v`.
  have hchar : ∀ v : Plane, v ≠ 0 → ∀ t : ℝ, 0 < t →
      (O + t • v ∈ frontier K ↔ t = radFn K O v) := by
    intro v hv t ht
    have hiff1 : O + t • v ∈ frontier K ↔ t • v ∈ frontier (shiftSet K O) := by
      have := hfront (O + t • v)
      simpa using this
    rw [hiff1, ← gauge_eq_one_iff_mem_frontier hSconv hSnhds,
      gauge_smul_of_nonneg ht.le v, smul_eq_mul, radFn]
    exact mul_eq_one_iff_eq_inv₀ (ne_of_gt (hgauge_pos v hv))
  have hpos : ∀ v : Plane, v ≠ 0 → 0 < radFn K O v := by
    intro v hv
    rw [radFn, inv_pos]
    exact hgauge_pos v hv
  refine ⟨hpos, hchar, fun Y => ?_⟩
  constructor
  · -- every frontier point is reached from `O` in a unit direction at distance `radFn`
    intro hY
    have hw_front : Y - O ∈ frontier (shiftSet K O) := (hfront Y).1 hY
    have hw_ne : Y - O ≠ 0 := by
      intro h0
      have h1 : gauge (shiftSet K O) (Y - O) = 1 :=
        (gauge_eq_one_iff_mem_frontier hSconv hSnhds).2 hw_front
      rw [h0, gauge_zero] at h1
      exact one_ne_zero h1.symm
    have ht : (0 : ℝ) < ‖Y - O‖ := norm_pos_iff.mpr hw_ne
    have htv : ‖Y - O‖ • (‖Y - O‖⁻¹ • (Y - O)) = Y - O := by
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw_ne), one_smul]
    have hvne : ‖Y - O‖⁻¹ • (Y - O) ≠ 0 := fun h =>
      hw_ne (by rw [← htv, h, smul_zero])
    refine ⟨‖Y - O‖⁻¹ • (Y - O), ?_, ?_⟩
    · rw [Metric.mem_sphere, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw_ne)
    · have hmem : O + ‖Y - O‖ • (‖Y - O‖⁻¹ • (Y - O)) ∈ frontier K := by
        have : O + ‖Y - O‖ • (‖Y - O‖⁻¹ • (Y - O)) = Y := by rw [htv]; abel_nf
        rw [this]; exact hY
      have hteq := (hchar _ hvne (‖Y - O‖) ht).1 hmem
      rw [← hteq, htv]
      abel_nf
  · -- conversely, the polar graph of `radFn` lies on the frontier
    rintro ⟨v, hv, rfl⟩
    rw [Metric.mem_sphere, dist_zero_right] at hv
    have hvne : v ≠ 0 := by
      intro h
      rw [h, norm_zero] at hv
      exact one_ne_zero hv.symm
    exact (hchar v hvne (radFn K O v) (hpos v hvne)).2 rfl

end Work.EQ
