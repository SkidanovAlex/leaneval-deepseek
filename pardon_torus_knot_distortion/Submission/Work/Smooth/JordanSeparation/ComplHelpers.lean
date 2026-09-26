import Mathlib

/-!
# Elementary connectedness helpers for complements in `ℂ`

* `isPreconnected_iff_connectedComponentIn_eq`: a set is preconnected iff the `connectedComponentIn`
  of each of its points is the whole set.
* `connectedComponentIn_eq_of_mem`: two points of the same `connectedComponentIn` have equal
  components.
* `isPreconnected_lt_norm_compl`: the complement of a closed ball in `ℂ` is preconnected (in
  particular all points of sufficiently large norm lie in one component of any set `Kᶜ` with `K`
  bounded).
-/

open Set Metric
open scoped Topology

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- A set is preconnected exactly when the connected component (inside it) of each of its points
is the whole set. -/
theorem isPreconnected_iff_connectedComponentIn_eq {α : Type*} [TopologicalSpace α] {s : Set α} :
    IsPreconnected s ↔ ∀ x ∈ s, connectedComponentIn s x = s := by
  constructor
  · intro hs x hx
    exact Subset.antisymm (connectedComponentIn_subset s x)
      (hs.subset_connectedComponentIn (F := s) (x := x) hx (Subset.refl s))
  · intro h
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact isPreconnected_empty
    · rw [← h x hx]
      exact isPreconnected_connectedComponentIn

/-- Two points of a connected component (inside a set `F`) have the same component. -/
theorem connectedComponentIn_eq_of_mem {α : Type*} [TopologicalSpace α] {F : Set α} {x y : α}
    (hy : y ∈ connectedComponentIn F x) :
    connectedComponentIn F y = connectedComponentIn F x := by
  have hxF : x ∈ F := connectedComponentIn_nonempty_iff.mp ⟨y, hy⟩
  have h1 : connectedComponentIn F x ⊆ connectedComponentIn F y :=
    (isPreconnected_connectedComponentIn (F := F) (x := x)).subset_connectedComponentIn
      (F := F) (x := y) hy (connectedComponentIn_subset F x)
  have hxy : x ∈ connectedComponentIn F y := h1 (mem_connectedComponentIn hxF)
  have h2 : connectedComponentIn F y ⊆ connectedComponentIn F x :=
    (isPreconnected_connectedComponentIn (F := F) (x := y)).subset_connectedComponentIn
      (F := F) (x := x) hxy (connectedComponentIn_subset F y)
  exact Subset.antisymm h2 h1

/-- The complement of a closed ball of non-negative radius in `ℂ` is preconnected. -/
theorem isPreconnected_lt_norm_compl (R : ℝ) (hR : 0 ≤ R) :
    IsPreconnected {z : ℂ | R < ‖z‖} := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hsphere : IsPreconnected (Metric.sphere (0 : ℂ) 1) := isPreconnected_sphere hrank 0 1
  have hprod : IsPreconnected ((Set.Ioi R) ×ˢ (Metric.sphere (0 : ℂ) 1)) :=
    isPreconnected_Ioi.prod hsphere
  have hcont : Continuous (fun q : ℝ × ℂ => q.1 • q.2) := by fun_prop
  have himg := hprod.image (fun q : ℝ × ℂ => q.1 • q.2) hcont.continuousOn
  have heq : (fun q : ℝ × ℂ => q.1 • q.2) '' ((Set.Ioi R) ×ˢ (Metric.sphere (0 : ℂ) 1))
      = {z : ℂ | R < ‖z‖} := by
    ext z; constructor
    · rintro ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩
      show R < ‖r • u‖
      rw [Metric.mem_sphere, dist_zero_right] at hu
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hR hr), hu, mul_one]
      exact hr
    · intro hz
      have hR1 : (0 : ℝ) < ‖z‖ := lt_of_le_of_lt hR hz
      refine ⟨(‖z‖, (‖z‖)⁻¹ • z), ⟨hz, ?_⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos hR1, inv_mul_cancel₀ (ne_of_gt hR1)]
      · show ‖z‖ • (‖z‖⁻¹ • z) = z
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hR1), one_smul]
  rwa [heq] at himg

end

end Work.Smooth.JordanSeparation
