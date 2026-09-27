import Mathlib
import Submission.Work.EQ.normDefs

namespace Work.EQ

open Metric Set

/-- **Common chord length.**  Two distinct equichordal points `P`, `Q` of the same planar domain
`K` share the same chord constant `L`, and the chord through `P` and `Q` is common, so that
`‖Q - P‖ < L`.

The hypotheses `hRP`, `hRQ` record that `radFn K O v` is the unique positive parameter `t` with
`O + t • v` on the frontier; this is exactly the radial-function form of the equichordal condition
for a convex body.  With it, the `IsEquichordalPoint` data for `P` and `Q` gives
`radFn K P u + radFn K P (-u) = Lp` and `radFn K Q u + radFn K Q (-u) = Lq` for every unit `u`.
Along the direction `u = (Q - P)/‖Q - P‖` the two radial functions are related by
`radFn K Q u = radFn K P u - ‖Q - P‖` and `radFn K Q (-u) = radFn K P (-u) + ‖Q - P‖`
(the order `‖Q - P‖ < radFn K P u` following from convexity, since otherwise the frontier point
`P + radFn K P u • u` would lie on the open segment joining the two interior points `P`, `Q`),
whence the two chord constants agree. -/
theorem chord_common {K : Set (EuclideanSpace ℝ (Fin 2))}
    {P Q : EuclideanSpace ℝ (Fin 2)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hPQ : P ≠ Q) (hP : LeanEval.Geometry.Equichordal.IsEquichordalPoint K P)
    (hQ : LeanEval.Geometry.Equichordal.IsEquichordalPoint K Q)
    (hRP : ∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 → ∀ t : ℝ, 0 < t →
      (P + t • v ∈ frontier K ↔ t = radFn K P v))
    (hRQ : ∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 → ∀ t : ℝ, 0 < t →
      (Q + t • v ∈ frontier K ↔ t = radFn K Q v)) :
    ∃ L : ℝ, 0 < L ∧ (∀ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        radFn K P u + radFn K P (-u) = L) ∧
      (∀ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        radFn K Q u + radFn K Q (-u) = L) ∧ ‖Q - P‖ < L := by
  obtain ⟨hPint, Lp, hLp, hPchord⟩ := hP
  obtain ⟨hQint, Lq, hLq, hQchord⟩ := hQ
  -- Step 1: the opposite radial distances about `P` sum to the chord constant `Lp`.
  have hPsum : ∀ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      radFn K P u + radFn K P (-u) = Lp := by
    intro u hu
    have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
    obtain ⟨a, b, ha, hb, hfa, hfb, hseg, hdist⟩ := hPchord u hu
    have hne : (-u : EuclideanSpace ℝ (Fin 2)) ≠ 0 := neg_ne_zero.mpr hu0
    have hra : radFn K P u = a := ((hRP u hu0 a ha).mp hfa).symm
    have hfb' : P + b • (-u) ∈ frontier K := by
      simpa only [smul_neg, sub_eq_add_neg] using hfb
    have hrb : radFn K P (-u) = b := ((hRP (-u) hne b hb).mp hfb').symm
    have hdist' : dist (P + a • u) (P - b • u) = a + b := by
      rw [dist_eq_norm]
      have hvec : P + a • u - (P - b • u) = (a + b) • u := by module
      rw [hvec, norm_smul, hu1, mul_one, Real.norm_of_nonneg (by linarith)]
    rw [hra, hrb, ← hdist']; exact hdist
  -- Step 2: the same about `Q`, with chord constant `Lq`.
  have hQsum : ∀ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      radFn K Q u + radFn K Q (-u) = Lq := by
    intro u hu
    have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
    obtain ⟨a, b, ha, hb, hfa, hfb, hseg, hdist⟩ := hQchord u hu
    have hne : (-u : EuclideanSpace ℝ (Fin 2)) ≠ 0 := neg_ne_zero.mpr hu0
    have hra : radFn K Q u = a := ((hRQ u hu0 a ha).mp hfa).symm
    have hfb' : Q + b • (-u) ∈ frontier K := by
      simpa only [smul_neg, sub_eq_add_neg] using hfb
    have hrb : radFn K Q (-u) = b := ((hRQ (-u) hne b hb).mp hfb').symm
    have hdist' : dist (Q + a • u) (Q - b • u) = a + b := by
      rw [dist_eq_norm]
      have hvec : Q + a • u - (Q - b • u) = (a + b) • u := by module
      rw [hvec, norm_smul, hu1, mul_one, Real.norm_of_nonneg (by linarith)]
    rw [hra, hrb, ← hdist']; exact hdist
  -- Step 3: work along the direction from `P` to `Q`.
  have hd : 0 < ‖Q - P‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr (Ne.symm hPQ)
  set d : ℝ := ‖Q - P‖ with hd_def
  have hd_pos : 0 < d := by rw [hd_def]; exact hd
  set u : EuclideanSpace ℝ (Fin 2) := d⁻¹ • (Q - P) with hu_def
  have hu_norm : ‖u‖ = 1 := by
    rw [hu_def, hd_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd),
        inv_mul_cancel₀ (ne_of_gt hd)]
  have hu_sphere : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    mem_sphere_zero_iff_norm.mpr hu_norm
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu_norm; simp at hu_norm
  have hQPu : Q = P + d • u := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hd_pos), one_smul]
    exact (add_sub_cancel P Q).symm
  obtain ⟨a, b, ha, hb, hfa, hfb, hseg, hdist⟩ := hPchord u hu_sphere
  have hra : radFn K P u = a := ((hRP u hu0 a ha).mp hfa).symm
  have hne : (-u : EuclideanSpace ℝ (Fin 2)) ≠ 0 := neg_ne_zero.mpr hu0
  have hrb : radFn K P (-u) = b := by
    have hfb' : P + b • (-u) ∈ frontier K := by
      simpa only [smul_neg, sub_eq_add_neg] using hfb
    exact ((hRP (-u) hne b hb).mp hfb').symm
  have hab : a + b = Lp := by
    have h := hPsum u hu_sphere
    rw [hra, hrb] at h
    exact h
  -- `Q` lies strictly between `P` and the frontier point `P + a • u`.
  have hlt : d < a := by
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with h_eq | h_lt
    · -- `d = a` would put the interior point `Q` on the frontier
      have hQfr : Q ∈ frontier K := by rw [hQPu, ← h_eq]; exact hfa
      exact (Set.disjoint_left.mp (disjoint_interior_frontier (s := K)) hQint) hQfr
    · -- `d > a`: the frontier point would be on the open segment of two interior points
      have hθ : a / d ∈ Set.Ioo (0:ℝ) 1 :=
        ⟨div_pos ha hd_pos, (div_lt_one hd_pos).mpr h_lt⟩
      have hcombo : (1 - a/d) • P + (a/d) • Q = P + a • u := by
        rw [hQPu, smul_add, smul_smul]
        rw [show a / d * d = a by rw [div_mul_cancel₀ _ (ne_of_gt hd_pos)]]
        module
      have hmem : P + a • u ∈ openSegment ℝ P Q := by
        rw [openSegment_eq_image]
        exact ⟨a/d, hθ, hcombo⟩
      have hint : P + a • u ∈ interior K :=
        (hconv.openSegment_interior_self_subset_interior hPint (interior_subset hQint)) hmem
      exact (Set.disjoint_left.mp (disjoint_interior_frontier (s := K)) hint) hfa
  -- Step 4: the two radial functions about `Q` along `±u`.
  have hraq : radFn K Q u = a - d := by
    have hpos : 0 < a - d := sub_pos.mpr hlt
    have hmem : Q + (a - d) • u ∈ frontier K := by
      have : Q + (a - d) • u = P + a • u := by rw [hQPu]; module
      rw [this]; exact hfa
    exact ((hRQ u hu0 (a - d) hpos).mp hmem).symm
  have hrbq : radFn K Q (-u) = b + d := by
    have hpos : 0 < b + d := by linarith
    have hmem : Q + (b + d) • (-u) ∈ frontier K := by
      have : Q + (b + d) • (-u) = P - b • u := by rw [hQPu, smul_neg]; module
      rw [this]; exact hfb
    exact ((hRQ (-u) hne (b + d) hpos).mp hmem).symm
  have hLq_eq : Lq = a + b := by
    have h := hQsum u hu_sphere
    rw [hraq, hrbq] at h
    linarith
  refine ⟨Lq, hLq, ?_, hQsum, ?_⟩
  · intro u' hu'
    rw [hPsum u' hu']
    rw [hab.symm, hLq_eq]
  · rw [hLq_eq]; linarith

end Work.EQ
