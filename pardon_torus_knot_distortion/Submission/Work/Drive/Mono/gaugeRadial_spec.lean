import Mathlib
import Submission.Work.Drive.Mono.GaugeRadialDefs

/-!
# The radial gauge map of a convex body and its inverse

Let `K ⊆ E` be convex, closed and bounded and let `p ∈ interior K`.  Mathlib constructs, for a
convex set `s` containing `0` in its interior and a second such set `t`, the "gauge rescale" map
`gaugeRescale s t x = (gauge s x / gauge t x) • x`, which is a homeomorphism `E ≃ₜ E` mapping
`interior s` to `interior t`, `closure s` to `closure t` and `frontier s` to `frontier t`
(`Mathlib.Analysis.Convex.GaugeRescale`).

The maps `gaugeRadial K p` and `gaugeRadialInv K p` of `GaugeRadialDefs` are exactly this
construction with `s = K - {p}` (a translate of `K`, convex, closed, bounded, with `0` in its
interior) and `t = closedBall 0 1` (whose gauge is the norm); this file records the two
identifications and then transfers the whole `gaugeRescale` API through them.
-/

namespace Work.Drive.Mono

open Set Metric
open scoped Pointwise Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Translating `K` to the origin -/

/-- The translate of `K` by `-p` is the pointwise set difference `K - {p}` (which is the set
appearing in the definitions of `gaugeRadial` and `gaugeRadialInv`). -/
lemma sub_singleton_eq_vadd_neg (K : Set E) (p : E) : K - {p} = -p +ᵥ K := by
  ext x
  rw [Set.mem_sub, Set.mem_vadd_set]
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, h, hh, hkh⟩
    rw [hh] at hkh
    exact ⟨k, hk, by rw [vadd_eq_add]; rw [← hkh]; abel⟩
  · rintro ⟨k, hk, hkk⟩
    rw [vadd_eq_add] at hkk
    exact ⟨k, hk, p, rfl, by rw [← hkk]; abel⟩

/-- Membership in the translate `K - {p}`. -/
lemma mem_sub_singleton (K : Set E) (p z : E) : z - p ∈ K - {p} ↔ z ∈ K := by
  rw [Set.mem_sub]
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, h, hh, hkh⟩
    rw [hh] at hkh
    have hkz : k = z := by
      have h := congrArg (fun t => t + p) hkh
      simpa using h
    exact hkz ▸ hk
  · exact fun hz => ⟨z, hz, p, rfl, by abel⟩

/-- The closure of the translate is the translate of the closure. -/
lemma mem_sub_singleton_closure (K : Set E) (p z : E) :
    z - p ∈ closure (K - {p}) ↔ z ∈ closure K := by
  rw [sub_singleton_eq_vadd_neg, closure_vadd, Set.mem_vadd_set_iff_neg_vadd_mem]
  simp [vadd_eq_add]

/-- The interior of the translate is the translate of the interior. -/
lemma mem_sub_singleton_interior (K : Set E) (p z : E) :
    z - p ∈ interior (K - {p}) ↔ z ∈ interior K := by
  rw [sub_singleton_eq_vadd_neg, interior_vadd, Set.mem_vadd_set_iff_neg_vadd_mem]
  simp [vadd_eq_add]

/-- The frontier of the translate is the translate of the frontier. -/
lemma mem_sub_singleton_frontier (K : Set E) (p z : E) :
    z - p ∈ frontier (K - {p}) ↔ z ∈ frontier K := by
  have h₁ : z - p ∈ frontier (K - {p}) ↔ z - p ∈ closure (K - {p}) \ interior (K - {p}) := by
    rw [closure_sdiff_interior]
  have h₂ : z ∈ frontier K ↔ z ∈ closure K \ interior K := by
    rw [closure_sdiff_interior]
  rw [h₁, h₂, Set.mem_sdiff, Set.mem_sdiff, mem_sub_singleton_closure, mem_sub_singleton_interior]

/-- Membership of `p + y` in `K` is membership of `y` in the translate `K - {p}`. -/
lemma vadd_mem_iff (K : Set E) (p y : E) : p + y ∈ K ↔ y ∈ K - {p} :=
  (mem_sub_singleton K p (p + y)).symm.trans (by rw [add_sub_cancel_left])

/-- Membership of `p + y` in the frontier of `K` is membership of `y` in the frontier of the
translate `K - {p}`. -/
lemma vadd_mem_frontier_iff (K : Set E) (p y : E) :
    p + y ∈ frontier K ↔ y ∈ frontier (K - {p}) :=
  (mem_sub_singleton_frontier K p (p + y)).symm.trans (by rw [add_sub_cancel_left])

/-! ## Structural properties of the translate -/

lemma convex_sub_singleton {K : Set E} (hKc : Convex ℝ K) (p : E) : Convex ℝ (K - {p}) :=
  hKc.sub (convex_singleton p)

lemma isClosed_sub_singleton {K : Set E} (hK : IsClosed K) (p : E) : IsClosed (K - {p}) := by
  rw [sub_singleton_eq_vadd_neg]
  exact hK.vadd (-p)

lemma zero_mem_interior_sub_singleton {K : Set E} {p : E} (hp : p ∈ interior K) :
    (0 : E) ∈ interior (K - {p}) := by
  rw [sub_singleton_eq_vadd_neg, interior_vadd, Set.mem_vadd_set_iff_neg_vadd_mem]
  simpa using hp

lemma mem_nhds_zero_sub_singleton {K : Set E} {p : E} (hp : p ∈ interior K) :
    (K - {p}) ∈ 𝓝 0 :=
  mem_interior_iff_mem_nhds.mp (zero_mem_interior_sub_singleton hp)

lemma isVonNBounded_sub_singleton {K : Set E} {p : E} (hKb : Bornology.IsBounded K) :
    Bornology.IsVonNBounded ℝ (K - {p}) := by
  rw [sub_singleton_eq_vadd_neg]
  exact (NormedSpace.isVonNBounded_of_isBounded ℝ hKb).vadd (-p)

/-! ## The gauge of the translate detects `K` and its frontier -/

lemma gauge_le_one_iff_mem_of_convex_closed {K : Set E} {p : E} (hKc : Convex ℝ K)
    (hKcl : IsClosed K) (hp : p ∈ interior K) (z : E) :
    gauge (K - {p}) (z - p) ≤ 1 ↔ z ∈ K :=
  (gauge_le_one_iff_mem_closure (convex_sub_singleton hKc p)
      (mem_nhds_zero_sub_singleton hp)).trans
    ((mem_sub_singleton_closure K p z).trans (by rw [hKcl.closure_eq]))

lemma gauge_eq_one_iff_mem_frontier_of_convex_closed {K : Set E} {p : E} (hKc : Convex ℝ K)
    (hp : p ∈ interior K) (z : E) :
    gauge (K - {p}) (z - p) = 1 ↔ z ∈ frontier K :=
  (gauge_eq_one_iff_mem_frontier (convex_sub_singleton hKc p)
      (mem_nhds_zero_sub_singleton hp)).trans (mem_sub_singleton_frontier K p z)

/-! ## The two constructions agree -/

/-- `gaugeRadial K p` is the gauge rescale map from the translate of `K` to the unit ball. -/
lemma gaugeRadial_eq_gaugeRescale (K : Set E) (p z : E) :
    gaugeRadial K p z = gaugeRescale (K - {p}) (closedBall (0 : E) 1) (z - p) := by
  rw [gaugeRadial, gaugeRescale, gauge_closedBall (zero_le_one : (0 : ℝ) ≤ 1), div_one,
    smul_smul, div_eq_mul_inv]

/-- `gaugeRadialInv K p` is the inverse gauge rescale map, translated back to `p`. -/
lemma gaugeRadialInv_eq_gaugeRescale (K : Set E) (p w : E) :
    gaugeRadialInv K p w = p + gaugeRescale (closedBall (0 : E) 1) (K - {p}) w := by
  rw [gaugeRadialInv, gaugeRescale, gauge_closedBall (zero_le_one : (0 : ℝ) ≤ 1), div_one,
    gauge_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg w)), smul_eq_mul]
  congr 1
  rw [mul_inv_rev, inv_inv, div_eq_mul_inv]
  ring_nf

/-- The gauge rescale map to the unit ball has norm the gauge of the source set. -/
lemma norm_gaugeRescale_closedBall (s : Set E) (x : E) :
    ‖gaugeRescale s (closedBall (0 : E) 1) x‖ = gauge s x := by
  have hB0 : (closedBall (0 : E) 1) ∈ 𝓝 (0 : E) := closedBall_mem_nhds 0 one_pos
  have hBabs : Absorbent ℝ (closedBall (0 : E) 1) := absorbent_nhds_zero hB0
  have hBb : Bornology.IsVonNBounded ℝ (closedBall (0 : E) 1) :=
    NormedSpace.isVonNBounded_closedBall ℝ E 1
  have h : ‖gaugeRescale s (closedBall (0 : E) 1) x‖
      = gauge (closedBall (0 : E) 1) (gaugeRescale s (closedBall (0 : E) 1) x) := by
    rw [gauge_closedBall (zero_le_one : (0 : ℝ) ≤ 1), div_one]
  rw [h, gauge_gaugeRescale (s := s) hBabs hBb]

/-- The norm of the radial gauge map is the gauge of `z - p` with respect to the translate. -/
lemma norm_gaugeRadial (K : Set E) (p z : E) :
    ‖gaugeRadial K p z‖ = gauge (K - {p}) (z - p) := by
  rw [gaugeRadial_eq_gaugeRescale, norm_gaugeRescale_closedBall]

/-! ## The specification -/

theorem gaugeRadial_spec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {p : E} (hKc : Convex ℝ K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hp : p ∈ interior K) :
    Continuous (Work.Drive.Mono.gaugeRadial K p) ∧
    Continuous (Work.Drive.Mono.gaugeRadialInv K p) ∧
    (∀ z, Work.Drive.Mono.gaugeRadial K p z ∈ Metric.closedBall (0 : E) 1 ↔ z ∈ K) ∧
    (∀ z, Work.Drive.Mono.gaugeRadial K p z ∈ Metric.sphere (0 : E) 1 ↔ z ∈ frontier K) ∧
    (∀ w, Work.Drive.Mono.gaugeRadialInv K p (Work.Drive.Mono.gaugeRadial K p w) = w) ∧
    (∀ z, Work.Drive.Mono.gaugeRadial K p (Work.Drive.Mono.gaugeRadialInv K p z) = z) ∧
    (∀ w, ‖w‖ ≤ 1 → Work.Drive.Mono.gaugeRadialInv K p w ∈ K) ∧
    (∀ w, ‖w‖ = 1 → Work.Drive.Mono.gaugeRadialInv K p w ∈ frontier K) := by
  have hAc : Convex ℝ (K - {p}) := convex_sub_singleton hKc p
  have hA0 : (K - {p}) ∈ 𝓝 0 := mem_nhds_zero_sub_singleton hp
  have hAb : Bornology.IsVonNBounded ℝ (K - {p}) := isVonNBounded_sub_singleton hKb
  have hAabs : Absorbent ℝ (K - {p}) := absorbent_nhds_zero hA0
  have hAcl : IsClosed (K - {p}) := isClosed_sub_singleton hKcl p
  have hB0 : (closedBall (0 : E) 1) ∈ 𝓝 (0 : E) := closedBall_mem_nhds 0 one_pos
  have hBc : Convex ℝ (closedBall (0 : E) 1) := convex_closedBall 0 1
  have hBabs : Absorbent ℝ (closedBall (0 : E) 1) := absorbent_nhds_zero hB0
  have hBb : Bornology.IsVonNBounded ℝ (closedBall (0 : E) 1) :=
    NormedSpace.isVonNBounded_closedBall ℝ E 1
  have hA0mem : (0 : E) ∈ K - {p} := mem_of_mem_nhds hA0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show gaugeRadial K p = fun z => gaugeRescale (K - {p}) (closedBall (0 : E) 1) (z - p)
      from funext fun z => gaugeRadial_eq_gaugeRescale K p z]
    exact (continuous_gaugeRescale hAc hA0 hBc hB0 hBb).comp
      (continuous_id.sub continuous_const)
  · rw [show gaugeRadialInv K p = fun w => p + gaugeRescale (closedBall (0 : E) 1) (K - {p}) w
      from funext fun w => gaugeRadialInv_eq_gaugeRescale K p w]
    exact continuous_const.add (continuous_gaugeRescale hBc hB0 hAc hA0 hAb)
  · intro z
    rw [mem_closedBall_zero_iff, norm_gaugeRadial]
    exact gauge_le_one_iff_mem_of_convex_closed hKc hKcl hp z
  · intro z
    rw [mem_sphere_zero_iff_norm, norm_gaugeRadial]
    exact gauge_eq_one_iff_mem_frontier_of_convex_closed hKc hp z
  · intro w
    rw [gaugeRadial_eq_gaugeRescale K p w, gaugeRadialInv_eq_gaugeRescale,
      gaugeRescale_gaugeRescale hBabs hBb, gaugeRescale_self_apply hAabs hAb]
    abel
  · intro z
    rw [gaugeRadialInv_eq_gaugeRescale K p z,
      gaugeRadial_eq_gaugeRescale K p (p + gaugeRescale (closedBall (0 : E) 1) (K - {p}) z),
      add_sub_cancel_left,
      gaugeRescale_gaugeRescale (s := closedBall (0 : E) 1) (t := K - {p})
        (u := closedBall (0 : E) 1) hAabs hAb z,
      gaugeRescale_self_apply hBabs hBb z]
  · intro w hw
    rw [gaugeRadialInv_eq_gaugeRescale, vadd_mem_iff]
    have hmem : gaugeRescale (closedBall (0 : E) 1) (K - {p}) w ∈ closure (K - {p}) :=
      mapsTo_gaugeRescale_closure hBc hB0 hAc hA0mem hAabs
        (by rw [closure_closedBall]; simpa [mem_closedBall_zero_iff] using hw)
    rwa [hAcl.closure_eq] at hmem
  · intro w hw
    rw [gaugeRadialInv_eq_gaugeRescale, vadd_mem_frontier_iff,
      ← gauge_eq_one_iff_mem_frontier hAc hA0,
      gauge_gaugeRescale (s := closedBall (0 : E) 1) hAabs hAb,
      gauge_closedBall (zero_le_one : (0 : ℝ) ≤ 1), div_one, hw]

end

end Work.Drive.Mono
