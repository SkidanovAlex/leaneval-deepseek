/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area

# Elementary facts about the window-supported subspaces `ell2Sub`

`Work.ORP311.ell2Sub m Z` is the closed span of the vectors `e_i ⊗ δ_g`, `g ∈ Z`, of
`HSum m = ⊕_{i : Fin m} ℓ²(G)`.  This file records the three elementary structural facts used by
the lowest-coset induction for the two-term Laurent operator
(`Work.ORP311.twoTerm_window_injective_normal`):

* `ell2Sub_orthogonal_compl` — `(ell2Sub m Z)ᗮ = ell2Sub m Zᶜ`;
* `ell2Sub_empty` — `ell2Sub m ∅ = ⊥`;
* `ell2Sub_map_subset_of_generators` — if a continuous linear map `A` sends every basis vector
  `e_i ⊗ δ_g`, `g ∈ Z`, into a closed submodule `U`, then `A '' ell2Sub m Z ⊆ U`.
-/
import Mathlib
import Submission.Work.ORP311.BlockShift
import Submission.Work.ORP311.ell2Sub_mono
import Submission.Work.ORP311.ell2Sub_inf
import Submission.Work.ORP311.ell2Sub_orthogonal
import Submission.Work.ORP311.mem_ell2Sub_iff

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct
open Work.ORVonNeumann

namespace Work.ORP311

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The orthogonal complement of `ell2Sub m Z` is `ell2Sub m Zᶜ`. -/
theorem ell2Sub_orthogonal_compl (m : ℕ) (Z : Set G) :
    (ell2Sub (G := G) m Z)ᗮ = ell2Sub (G := G) m Zᶜ := by
  have hc : IsClosed ((ell2Sub (G := G) m Zᶜ : Submodule ℂ (Rep.HSum (G := G) m)) :
      Set (Rep.HSum (G := G) m)) := by
    unfold ell2Sub
    exact Submodule.isClosed_topologicalClosure _
  rw [ell2Sub_orthogonal (G := G) m Z, Submodule.orthogonal_orthogonal_eq_closure]
  exact hc.submodule_topologicalClosure_eq

/-- `ell2Sub m ∅ = ⊥`. -/
theorem ell2Sub_empty (m : ℕ) : ell2Sub (G := G) m (∅ : Set G) = ⊥ := by
  unfold ell2Sub
  simp

/-- **Preservation.**  If a continuous linear map `A` sends every basis vector
`e_i ⊗ δ_g`, `g ∈ Z`, into a closed submodule `U`, then it maps `ell2Sub m Z` into `U`. -/
theorem ell2Sub_map_subset_of_generators (m : ℕ)
    (A : Rep.HSum (G := G) m →L[ℂ] Rep.HSum (G := G) m) (Z : Set G)
    (U : Submodule ℂ (Rep.HSum (G := G) m)) (hU : IsClosed (U : Set (Rep.HSum (G := G) m)))
    (hgen : ∀ g ∈ Z, ∀ i : Fin m,
      A (Rep.hinclude (G := G) m i (Rep.deltaG g)) ∈ U) :
    ∀ x ∈ ell2Sub (G := G) m Z, A x ∈ U := by
  intro x hx
  have hS : Submodule.span ℂ {w | ∃ g ∈ Z, ∃ i : Fin m,
        w = Rep.hinclude (G := G) m i (Rep.deltaG g)}
      ≤ Submodule.comap A.toLinearMap U := by
    rw [Submodule.span_le]
    rintro w ⟨g, hg, i, rfl⟩
    exact hgen g hg i
  have hc : IsClosed ((Submodule.comap A.toLinearMap U :
      Submodule ℂ (Rep.HSum (G := G) m)) : Set (Rep.HSum (G := G) m)) :=
    hU.preimage A.continuous
  have hcl := Submodule.topologicalClosure_minimal
    (s := Submodule.span ℂ {w | ∃ g ∈ Z, ∃ i : Fin m,
      w = Rep.hinclude (G := G) m i (Rep.deltaG g)}) hS hc
  exact hcl (by simpa only [ell2Sub] using hx)

end Work.ORP311
