/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# Additivity of the von Neumann dimension on an orthogonal decomposition

The von Neumann dimension `Work.ORVonNeumann.Rep.hdim K` of a subspace
`K ⊆ ⊕_{i : Fin n} ℓ²(G)` is, by definition, `∑ i, ‖K.starProjection (δ i)‖ ^ 2`.  Since an
orthogonal projection decomposes every vector into an orthogonal sum
`x = K.starProjection x + Kᗮ.starProjection x`, Pythagoras
(`Submodule.norm_sq_eq_add_norm_sq_starProjection`) gives

`‖K.starProjection δ i‖ ^ 2 + ‖Kᗮ.starProjection δ i‖ ^ 2 = ‖δ i‖ ^ 2 = 1`,

and summing over `i` yields the complement identity

* `Work.ORVonNeumann.Rep.vnHdimCompl` — `hdim K + hdim Kᗮ = n`.

This is the normalisation making `hdim` a dimension function: `hdim ⊤ = n`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace

namespace Work.ORVonNeumann.Rep

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The vector `δ i = e i ⊗ δ₁` is a unit vector: `⟪δ i, δ i⟫ = 1`. -/
theorem vnInnerHdeltaSelf (n : ℕ) (i : Fin n) :
    inner ℂ (hdelta (G := G) n i) (hdelta (G := G) n i) = 1 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · rw [← hcoord_apply (G := G) n i (hdelta (G := G) n i), hcoord_hdelta, if_pos rfl]
    exact inner_delta1_self
  · intro j _ hj
    rw [← hcoord_apply (G := G) n j (hdelta (G := G) n i), hcoord_hdelta, if_neg hj]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The vector `δ i = e i ⊗ δ₁` has squared norm `1`. -/
theorem vnNormSqHdelta (n : ℕ) (i : Fin n) : ‖hdelta (G := G) n i‖ ^ 2 = 1 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hdelta (G := G) n i)
  rw [vnInnerHdeltaSelf] at h
  norm_num at h
  exact_mod_cast h.symm

/-- **Complement identity for the von Neumann dimension**: the dimensions of a subspace and
of its orthogonal complement add up to `n`, the "rank" of `⊕_{i : Fin n} ℓ²(G)`. -/
theorem vnHdimCompl {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} (K : Submodule ℂ (Work.ORVonNeumann.Rep.HSum (G := G) n)) [K.HasOrthogonalProjection] : Work.ORVonNeumann.Rep.hdim K + Work.ORVonNeumann.Rep.hdim Kᗮ = n := by
  rw [hdim, hdim, ← Finset.sum_add_distrib]
  have h : ∀ i : Fin n, ‖K.starProjection (hdelta (G := G) n i)‖ ^ 2
      + ‖Kᗮ.starProjection (hdelta (G := G) n i)‖ ^ 2 = 1 := by
    intro i
    rw [← Submodule.norm_sq_eq_add_norm_sq_starProjection (hdelta (G := G) n i) K]
    exact vnNormSqHdelta n i
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  simp

end Work.ORVonNeumann.Rep
