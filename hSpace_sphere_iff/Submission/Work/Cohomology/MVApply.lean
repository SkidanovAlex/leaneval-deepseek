/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# The Mayer–Vietoris connecting map, instantiated

`Work.Cohomology.mvBeta_ker_eq_range` provides the exactness of the two maps of the
Mayer–Vietoris sequence of a covering pair of subcomplexes `A, B ⊆ S` in every degree, so the
connecting map of `Submission.Cohomology.mvDelta` is available as an honest linear map

`mvConnecting S A B hAB k : H (A ∩ B) ℚ k ⟶ H S ℚ (k+1)`.

This file records that instantiation, its computation rule on the class of a cocycle, and the
elementary fact that a vanishing cohomology group in positive degree means that every cocycle is a
coboundary.
-/
import Mathlib
import Submission.Work.Cohomology.MayerVietoris
import Submission.Work.Cohomology.mvBeta_ker_eq_range

open CategoryTheory Simplicial Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Submission.Cohomology

noncomputable section

/-- The exactness of the Mayer–Vietoris sequence, in all degrees, for a covering pair. -/
theorem mvExact (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (j : ℕ) :
    LinearMap.ker (mvBeta S A B j) = (mvAlpha S A B j).range :=
  Work.Cohomology.mvBeta_ker_eq_range S A B hAB j

/-- **The connecting map of the Mayer–Vietoris sequence** of a covering pair of subcomplexes. -/
def mvConnecting (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ) :
    H (A ⊓ B : S.Subcomplex) ℚ k →ₗ[ℚ] H S ℚ (k+1) :=
  mvDelta S A B hAB k fun j => mvExact S A B hAB j

/-- The computation rule for the connecting map on the class of a cocycle. -/
lemma mvConnecting_mk (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    {c : Cochain (A ⊓ B : S.Subcomplex) ℚ k} (hc : c ∈ cycles (A ⊓ B : S.Subcomplex) ℚ k) :
    mvConnecting S A B hAB k (H.mk c hc)
      = H.mk (mvDeltaRep S A B hAB k c) (mvDeltaRep_mem_cycles S A B hAB k
          (fun j => mvExact S A B hAB j) hc) :=
  mvDelta_mk S A B hAB k (fun j => mvExact S A B hAB j) hc

/-- A cohomology group all of whose elements are equal in degree `k` makes every `k`-cocycle a
coboundary. -/
lemma mem_boundaries_of_subsingleton (S : SSet.{0}) {k : ℕ} (h : Subsingleton (H S ℚ k))
    {z : Cochain S ℚ k} (hz : z ∈ cycles S ℚ k) : z ∈ boundaries S ℚ k := by
  have hz0 : H.mk z hz = 0 := Subsingleton.elim _ _
  have h0 : (0 : Cochain S ℚ k) ∈ cycles S ℚ k := Submodule.zero_mem _
  rw [show (0 : H S ℚ k) = H.mk 0 h0 from rfl] at hz0
  have := (H.mk_eq_mk_iff z 0 hz h0).mp hz0
  simpa using this

end

end Submission.Cohomology
