import Mathlib
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.SingularTopFreeDefs
import Submission.Work.Cohomology.homology_zero_free

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `(N-1)`-st homology of the one-point compactification of `ℝ^N` is free

The one-point compactification `OnePointSpace N = OnePoint (ℝ^N)` is homeomorphic to the unit
sphere `S^N ⊆ ℝ^{N+1}` (`onePointEquivSphereOfFinrankEq`).  Its singular homology in degree `N-1`
is therefore that of `S^N`: it is `ℤ` for `N = 1` (`H₀` of any space is free,
`Work.Cohomology.homology_zero_free`) and `0` for `N ≥ 2` (`N - 1 ≠ 0, N`, so
`Work.Cohomology.sphereVanishing` applies); in both cases it is a free `ℤ`-module.

## Main result

* `homology_onePointSpace_free` — `H_{N-1}(OnePointSpace N; ℤ)` is a free `ℤ`-module.
-/

set_option linter.style.haveILetI false

namespace Work.Cohomology

open CategoryTheory

noncomputable section

/-- **`H_{N-1}` of the one-point compactification of `ℝ^N` is a free `ℤ`-module.** -/
theorem homology_onePointSpace_free (N : ℕ) (hN : 1 ≤ N) :
    Module.Free ℤ ↥((singularChains ℤ (TopCat.of (OnePointSpace N))).homology (N - 1)) := by
  by_cases hN1 : N = 1
  · -- `N = 1`: the degree is `0`, and `H₀` of any space is free.
    subst hN1
    exact homology_zero_free (TopCat.of (OnePointSpace 1))
  · -- `N ≥ 2`: the degree `N - 1` is neither `0` nor `N`, so the homology vanishes.
    have hN2 : 2 ≤ N := by omega
    -- The homeomorphism `OnePointSpace N ≃ₜ S^N`.
    let e : OnePointSpace N ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1 :=
      onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin N)) (ι := Fin (N + 1)) (by simp)
    obtain ⟨iso⟩ := homologyIso_of_homotopyEquiv e.toHomotopyEquiv (N - 1)
    -- `H_{N-1}(S^N) = 0`.
    have hzero : CategoryTheory.Limits.IsZero
        ((singularChains ℤ
          (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1))).homology
            (N - 1)) :=
      sphereVanishing N (N - 1) hN (by omega) (by omega)
    -- transport along the homology isomorphism, and use that a zero module is free
    have hz : CategoryTheory.Limits.IsZero
        ((singularChains ℤ (TopCat.of (OnePointSpace N))).homology (N - 1)) :=
      CategoryTheory.Limits.IsZero.of_iso hzero iso
    haveI : Subsingleton
        ↥((singularChains ℤ (TopCat.of (OnePointSpace N))).homology (N - 1)) :=
      ModuleCat.subsingleton_of_isZero hz
    exact Module.Free.of_subsingleton ℤ _

end

end Work.Cohomology
