/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area

# A coordinate-support bound for the von Neumann dimension

Let `K ⊆ ⊕_{i : Fin M} ℓ²(G) = HSum M` be a closed subspace with an orthogonal projection,
and let `S : Finset (Fin M)` be a set of coordinates such that every unit vector
`hdelta c = e_c ⊗ δ₁` with `c ∉ S` lies in the orthogonal complement `Kᗮ`.  Then

  `hdim K ≤ S.card`.

This is the elementary "support" estimate used in the Følner/Lück argument: the von Neumann
dimension `hdim K = ∑ i, ‖K.starProjection (hdelta i)‖ ^ 2` is computed on the single vectors
`hdelta i`, and each of them contributes at most `‖hdelta i‖ ^ 2 = 1`; the ones outside `S`
contribute nothing at all, since a vector of `Kᗮ` is killed by `K.starProjection`.

## Main result

* `Work.ORP311.hdim_le_card_of_orthogonal_delta` — the bound `hdim K ≤ S.card`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore
import Submission.Work.ORVonNeumann.Rep.vnHdimCompl

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORP311

/-- A vector lying in the orthogonal complement `Kᗮ` is killed by the orthogonal projection
onto `K`. -/
theorem starProjection_eq_zero_of_mem_orthogonal {G : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ}
    (K : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)) [K.HasOrthogonalProjection]
    {x : Work.ORVonNeumann.Rep.HSum (G := G) n} (hx : x ∈ Kᗮ) : K.starProjection x = 0 := by
  have h1 : Kᗮ.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have h2 := Submodule.starProjection_add_starProjection_orthogonal (K := K) x
  rw [h1, add_eq_right] at h2
  exact h2

theorem hdim_le_card_of_orthogonal_delta {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {M : ℕ} (K : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) M)) [K.HasOrthogonalProjection] (S : Finset (Fin M)) (hS : ∀ c : Fin M, c ∉ S → Work.ORVonNeumann.Rep.hdelta (G := G) M c ∈ Kᗮ) : Work.ORVonNeumann.Rep.hdim (G := G) K ≤ (S.card : ℝ) := by
  classical
  -- The coordinates outside `S` contribute nothing.
  have hzero : ∀ c : Fin M, c ∉ S →
      K.starProjection (Work.ORVonNeumann.Rep.hdelta (G := G) M c) = 0 :=
    fun c hc => starProjection_eq_zero_of_mem_orthogonal K (hS c hc)
  rw [Work.ORVonNeumann.Rep.hdim]
  -- Restrict the sum to `S`.
  have hsub : ∑ i ∈ S, ‖K.starProjection (Work.ORVonNeumann.Rep.hdelta (G := G) M i)‖ ^ 2
      = ∑ i : Fin M, ‖K.starProjection (Work.ORVonNeumann.Rep.hdelta (G := G) M i)‖ ^ 2 :=
    Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => by
      rw [hzero x hx, norm_zero]; norm_num)
  rw [← hsub]
  -- Each surviving coordinate contributes at most one.
  have hbound : ∑ i ∈ S, ‖K.starProjection (Work.ORVonNeumann.Rep.hdelta (G := G) M i)‖ ^ 2
      ≤ ∑ _i ∈ S, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection
      (Work.ORVonNeumann.Rep.hdelta (G := G) M i) K
    have hv := Work.ORVonNeumann.Rep.vnNormSqHdelta (G := G) M i
    nlinarith [sq_nonneg ‖Kᗮ.starProjection (Work.ORVonNeumann.Rep.hdelta (G := G) M i)‖]
  calc ∑ i ∈ S, ‖K.starProjection (Work.ORVonNeumann.Rep.hdelta (G := G) M i)‖ ^ 2
      ≤ ∑ _i ∈ S, (1 : ℝ) := hbound
    _ = (S.card : ℝ) := by simp

end Work.ORP311
