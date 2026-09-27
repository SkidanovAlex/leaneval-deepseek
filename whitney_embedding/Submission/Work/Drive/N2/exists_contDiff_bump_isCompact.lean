import Mathlib

open Set Metric Topology
open scoped Manifold ContDiff Topology

namespace Work.Drive.N2

/-- Smooth bump function around a compact set: for a compact `K` contained in an open `O` in a
finite-dimensional Euclidean space, there is a `C^∞` function `χ` with compact support, whose
(topological) support is contained in `O` and which equals `1` on a neighbourhood of `K`.

This is obtained from the manifold partition-of-unity theory: choose an open `U` with
`K ⊆ U`, `closure U` compact and `closure U ⊆ O`, and apply
`exists_contMDiffMap_one_nhds_of_subset_interior` to the closed set `K` and the open set `U`. -/
theorem exists_contDiff_bump_isCompact {N : ℕ} {K O : Set (EuclideanSpace ℝ (Fin N))}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ χ : EuclideanSpace ℝ (Fin N) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
        K ⊆ interior {x | χ x = 1} := by
  -- Shrink `O` to an open `U` with compact closure contained in `O`.
  obtain ⟨U, hUop, hKU, hUclO, hUcomp⟩ :=
    exists_open_between_and_isCompact_closure hK hO hKO
  -- Smooth function equal to `1` near `K` and vanishing outside `U`.
  obtain ⟨f, hf1, hf2, hf3⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, EuclideanSpace ℝ (Fin N))) (n := ⊤)
      hK.isClosed (by rw [hUop.interior_eq]; exact hKU)
  have hsupp : tsupport (f : EuclideanSpace ℝ (Fin N) → ℝ) ⊆ closure U := by
    rw [tsupport]
    exact closure_mono (Function.support_subset_iff'.mpr hf2)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · exact contMDiff_iff_contDiff.mp f.contMDiff
  · exact IsCompact.of_isClosed_subset hUcomp (isClosed_tsupport _) hsupp
  · exact hsupp.trans hUclO
  · exact subset_interior_iff_mem_nhdsSet.mpr hf1

end Work.Drive.N2
