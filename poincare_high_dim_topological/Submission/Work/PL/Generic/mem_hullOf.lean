import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.Hull

namespace Work.PL.Generic

/-- The points expressible as a convex combination of the vertices `y v`, `v ∈ s`. -/
private def combSet {n : ℕ} {ι : Type*} (y : ι → PL.E n) (s : Finset ι) : Set (PL.E n) :=
  {x | ∃ w : ι → ℝ, (∀ v ∈ s, 0 ≤ w v) ∧ (∑ v ∈ s, w v = 1) ∧ (∑ v ∈ s, w v • y v = x)}

/-- `combSet` is convex: convex combinations of the two weight families. -/
private theorem convex_combSet {n : ℕ} {ι : Type*} (y : ι → PL.E n) (s : Finset ι) :
    Convex ℝ (combSet y s) := by
  rintro x ⟨w1, h10, h11, h1x⟩ x' ⟨w2, h20, h21, h2x⟩ a b ha hb hab
  refine ⟨fun v => a * w1 v + b * w2 v, ?_, ?_, ?_⟩
  · intro v hv
    exact add_nonneg (mul_nonneg ha (h10 v hv)) (mul_nonneg hb (h20 v hv))
  · have h : ∑ v ∈ s, (a * w1 v + b * w2 v)
        = a * (∑ v ∈ s, w1 v) + b * (∑ v ∈ s, w2 v) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [h, h11, h21, mul_one, mul_one, hab]
  · have h : ∑ v ∈ s, (a * w1 v + b * w2 v) • y v
        = a • (∑ v ∈ s, w1 v • y v) + b • (∑ v ∈ s, w2 v • y v) := by
      rw [Finset.sum_congr rfl (fun v _ => by rw [add_smul, mul_smul, mul_smul]),
        Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
    rw [h, h1x, h2x]

/-- Each vertex `y v`, `v ∈ s`, lies in `combSet y s` (its weight is the indicator of `{v}`). -/
private theorem image_subset_combSet {n : ℕ} {ι : Type*} (y : ι → PL.E n) (s : Finset ι) :
    y '' (s : Set ι) ⊆ combSet y s := by
  classical
  rintro p ⟨v, hv, rfl⟩
  have hv' : v ∈ s := hv
  refine ⟨fun u => if u = v then (1 : ℝ) else 0, ?_, ?_, ?_⟩
  · intro u _
    by_cases h : u = v <;> simp [h]
  · rw [Finset.sum_ite_eq' s v (fun _ => (1 : ℝ)), ite_eq_left hv']
  · have h1 : ∑ u ∈ s, (if u = v then (1 : ℝ) else 0) • y u
        = ∑ u ∈ s, (if u = v then y u else 0) :=
      Finset.sum_congr rfl (fun u _ => by by_cases h : u = v <;> simp [h])
    rw [h1, Finset.sum_ite_eq' s v (fun u => y u), ite_eq_left hv']

/-- Membership in `hullOf` as a finite convex combination of the vertices.  Proof: the `⇐` direction
is `Finset.centerMass_mem_convexHull` (`∑ v ∈ s, w v • y v = s.centerMass w y` when the weights sum
to `1`); for `⇒` use `convexHull_eq` and reindex (each point of the convex combination is `y v` for
some `v ∈ s`, accumulate the weights). -/
theorem mem_hullOf {n : ℕ} {ι : Type*} (y : ι → PL.E n) (s : Finset ι) (x : PL.E n) :
    x ∈ Work.PL.Generic.hullOf y s ↔ ∃ w : ι → ℝ, (∀ v ∈ s, 0 ≤ w v) ∧ (∑ v ∈ s, w v = 1) ∧
      (∑ v ∈ s, w v • y v = x) := by
  constructor
  · intro hx
    exact convexHull_min (image_subset_combSet y s) (convex_combSet y s)
      (by simpa [hullOf] using hx)
  · rintro ⟨w, hw0, hw1, hw2⟩
    have hpos : 0 < ∑ v ∈ s, w v := by rw [hw1]; norm_num
    have hmem : ∀ v ∈ s, y v ∈ y '' (s : Set ι) := fun v hv => ⟨v, by simpa using hv, rfl⟩
    have hcm : s.centerMass w y ∈ convexHull ℝ (y '' (s : Set ι)) :=
      Finset.centerMass_mem_convexHull s hw0 hpos hmem
    rw [hullOf, ← hw2, ← Finset.centerMass_eq_of_sum_1 s y hw1]
    exact hcm

end Work.PL.Generic
