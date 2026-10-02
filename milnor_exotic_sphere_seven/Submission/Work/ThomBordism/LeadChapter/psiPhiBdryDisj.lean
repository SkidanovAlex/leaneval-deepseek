import Mathlib
import Submission.Work.ThomBordism.LeadChapter.bdryAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary/hyperplane dichotomy of the `ψ`-collapse

Let `ψ` be a half-space chart of `W` around whose source the boundary of `W` is detected by the
vanishing of the `0`-th coordinate (`hbd`), and let `y`, `z` both lie on the boundary and in
`ψ.source`.  Then the collapse value

  `psiPhi ψ y τ χ z = profile2 0 (χ z) (τ • (ψ z - ψ y))`

either still lies in the hyperplane `{· 0 = 0}` (the third, "shift" phase of `profile2`) or is a
unit vector of `ℝ^{n+1}` (the constant "north pole" phase and the spherical phase — the latter
being the unit sphere because the argument `τ • (ψ z - ψ y)` lies in the hyperplane).

The only degenerate case is `z = y`: then `τ • (ψ z - ψ y) = 0`, and the spherical phase would
have norm `< 1`; but `χ y = 1` forces the third phase, which keeps the `0`-th coordinate at `0`.

The `ψ`-independent content is isolated in `profile2_bdry_dichotomy`; the transport from `W` to the
model half-space is `psiVa_coord_eq_zero_of_boundary` plus `psiVa_eq_zero_iff`.
-/

set_option linter.unusedVariables false

open scoped Manifold

namespace Work.ThomBordism.LeadChapter

open Work.ThomBordism

/-- **The `ψ`-free dichotomy of the seam-free profile on the hyperplane.**  If the `0`-th
coordinates of `e` and `v` vanish, then a value of `profile2 e t v` either keeps the `0`-th
coordinate equal to `0` (the shift phase) or is a unit vector (the north-pole and spherical
phases).  The only escape is the spherical phase applied to `v = 0`, which is excluded by `hvt`. -/
theorem profile2_bdry_dichotomy {m : ℕ} (e v : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ)
    (he : e 0 = 0) (hv : v 0 = 0) (hvt : v = 0 → 3 / 4 < t) :
    (BCU.profile2 e t v) 0 = 0 ∨ ‖BCU.profile2 e t v‖ = 1 := by
  rw [BCU.profile2]
  by_cases h1 : t ≤ 1 / 2
  · rw [if_pos h1]
    exact Or.inr (BCU.bcu_northPole_norm m)
  · rw [if_neg h1]
    by_cases h2 : t ≤ 3 / 4
    · rw [if_pos h2]
      refine Or.inr (BCU.bcu_sphPhase_norm_eq_one _ _ ?_ ?_ ?_ (le_of_eq hv.symm))
      · intro h
        exact absurd h2 (not_le.mpr (hvt h))
      · exact (BCU.bcu_phase2_nonneg h1 h2).1
      · exact (BCU.bcu_phase2_nonneg h1 h2).2
    · rw [if_neg h2]
      exact Or.inl (BCU.bcu_shift2_coord_eq_zero ((1 - t) * 4) e v he hv)

theorem psiPhiBdryDisj (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    (hbd : ∀ q ∈ ψ.source,
      q ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W ↔ (ψ q).1 0 = 0)
    {y : W} (hyψ : y ∈ ψ.source)
    (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {z : W} (hzψ : z ∈ ψ.source)
    (hz : z ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    {τ : ℝ} (hτ : 0 < τ) {χ : W → ℝ}
    (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hout : ∀ z, z ∉ ψ.source → χ z = 0)
    (hy1 : χ y = 1) :
    (Work.ThomBordism.LeadChapter.psiPhi ψ y τ χ z) 0 = 0 ∨
      ‖Work.ThomBordism.LeadChapter.psiPhi ψ y τ χ z‖ = 1 := by
  have hv0 : (psiVa ψ y τ z) 0 = 0 :=
    psiVa_coord_eq_zero_of_boundary ψ hbd hyψ hy hzψ hz
  have hvt : psiVa ψ y τ z = 0 → 3 / 4 < χ z := by
    intro hvz
    have hzy : z = y := (psiVa_eq_zero_iff ψ (ne_of_gt hτ) hyψ hzψ).mp hvz
    have h1 : χ z = 1 := by rw [hzy, hy1]
    rw [h1]; norm_num
  rw [psiPhi_apply]
  exact profile2_bdry_dichotomy 0 (psiVa ψ y τ z) (χ z) (by simp) hv0 hvt

end Work.ThomBordism.LeadChapter
