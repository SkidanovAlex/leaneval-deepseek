import Mathlib
import Submission.Work.Drive.oddClassLift
import Submission.Work.Drive.isClassLift_rotCapping

/-!
# The homotopy clauses of `HasClassLinearization` for the design's three planes

`Work.Drive.HasClassLinearization P` (`Submission/Work/Drive/classTripleOdd.lean`) asks, for the design's
triple of planes `P k = rotPresentation Q (u k)` (three rotations of the chart's plane), for

* a homotopy `H k` from `planeClassMap (P k)` to the disk model
  `planeClassMap (diskPlane (linPlaneChart (φ k) c hc))` of a *linear* plane, through class maps of the
  square, and
* the three `Meet3Hyp` admissibility clauses of the encoded chains.

This file produces the **homotopy clauses** (the first two bullets) from the checkable inputs of
`Work.Drive.exists_diskClassHomotopy_linear_of_neg`, uniformly in `k`:
the chart's lift is carried to the rotated charts by `Work.Drive.isClassLift_rotCapping`, its oddness is
produced by `Work.Drive.exists_odd_classLift`, and the homotopy is
`Work.Drive.exists_diskClassHomotopy_linear_of_neg`.

The remaining input for `HasClassLinearization` is the *admissibility* (the three `Meet3Hyp` clauses):
smoothness of the three chains is available
(`Work.Drive.contMDiff_chain_projTimesLine`, `Work.Drive.contMDiff_chain_projTimesLine_plane`), while
transversality at the triple points and the face condition are genericity statements about the same
parameter `p` that produces the homotopy — for which `Work.Drive.dense_diskGood` is the ingredient
(the set of admissible `p` is *dense*, so it meets the nonempty open set that the Sard argument yields).
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- **The homotopy clauses of `HasClassLinearization` for the design's three planes.**  The chart
(`Q`, with a smooth nonvanishing lift `V` of its class map, parallel to `V (-·)` on the boundary circle
and with negative factor at one point — the essentiality), the three rotation angles `u`, the three
linear plane charts `φ k` of the level `c`, and the three weights `χ k` (smooth, odd on the circle, with
the non-collision condition at their zeros) produce three homotopies with

* `H k (0, ·) = planeClassMap (rotPresentation Q (u k))` — the design's plane,
* `H k (1, ·) = planeClassMap (diskPlane (linPlaneChart (φ k) c hc))` — the linear disk model,
* the seam invariance `H k (t, seamInv2 y) = H k (t, y)` for `onSeam2 y` (the `Meet3Hyp.seam` condition
  of the encoded chain),
* continuity, and `C^∞` of each chain `x ↦ H k (x 2, (x 0, x 1))` into `ℝP³`. -/
theorem exists_homotopyClauses_rotPresentation
    (Q : ℂ → CappingSpace) (V : ℂ → Eucl 3)
    (hVne : ∀ z, V z ≠ 0) (hVsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hQcls : IsClassLift Q V hVne)
    (hVpar : ∀ z : ℂ, ‖z‖ = 1 → ∃ cc : ℝ, V (-z) = cc • V z)
    {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1)
    (hneg : ∃ cc : ℝ, V (-z₀) = cc • V z₀ ∧ cc < 0)
    (u : Fin 3 → ℝ) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (χ : Fin 3 → ℂ → ℝ) (hχsmooth : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ k))
    (hχodd : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 → χ k (-z) = - χ k z)
    (hgood : ∀ (k : Fin 3) (z : ℂ), ‖z‖ ≤ 1 → χ k z = 0 →
      ¬ ∃ lam : ℝ, (φ k (linVecC z)) = lam • (diagRotL (u k) (V z)) ∧ lam < 0) :
    ∃ H : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3),
      (∀ k, (fun y => H k (0, y))
          = planeClassMap (rotPresentation Q ((u k : ℝ) : UnitAddCircle))) ∧
      (∀ k, (fun y => H k (1, y))
          = planeClassMap (diskPlane (linPlaneChart (φ k) c hc))) ∧
      (∀ (k : Fin 3) (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
        onSeam2 y → H k (t, seamInv2 y) = H k (t, y)) ∧
      (∀ k, Continuous (H k)) ∧
      (∀ k, ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => H k (x 2, mk2 (x 0) (x 1)))) := by
  classical
  have hkey : ∀ k : Fin 3,
      ∃ p : Eucl 3,
        ∃ H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3),
          (∀ y, H (0, y) = planeClassMap (diskPlane fun z =>
              rotCapping ((u k : ℝ) : UnitAddCircle) (Q z)) y) ∧
          (∀ y, H (1, y) = planeClassMap (diskPlane (linPlaneChart (φ k) c hc)) y) ∧
          (∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
            onSeam2 y → H (t, seamInv2 y) = H (t, y)) ∧
          Continuous H ∧
          ContMDiff (𝓡 3) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
            ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : EuclideanSpace ℝ (Fin 3) => H (x 2, mk2 (x 0) (x 1))) := by
    intro k
    obtain ⟨hWne, hWcls⟩ :=
      isClassLift_rotCapping hVne hQcls (u k)
    have hWsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℂ => diagRotL (u k) (V z)) :=
      ((diagRotL (u k) : Eucl 3 →L[ℝ] Eucl 3)).contDiff.comp hVsmooth
    have hWpar : ∀ z : ℂ, ‖z‖ = 1 →
        ∃ cc : ℝ, (fun z : ℂ => diagRotL (u k) (V z)) (-z)
          = cc • (fun z : ℂ => diagRotL (u k) (V z)) z := by
      intro z hz
      obtain ⟨cc, hcc⟩ := hVpar z hz
      exact ⟨cc, by simp only [hcc, map_smul]⟩
    have hWneg : ∃ cc : ℝ, (fun z : ℂ => diagRotL (u k) (V z)) (-z₀)
        = cc • (fun z : ℂ => diagRotL (u k) (V z)) z₀ ∧ cc < 0 := by
      obtain ⟨cc, hcc, hccneg⟩ := hneg
      exact ⟨cc, by simp only [hcc, map_smul], hccneg⟩
    obtain ⟨p, H, h0, h1, h2, h3, h4⟩ :=
      exists_diskClassHomotopy_linear_of_neg (fun z => rotCapping ((u k : ℝ) : UnitAddCircle) (Q z))
        (fun z => diagRotL (u k) (V z)) hWne hWsmooth hWcls hWpar hz₀ hWneg (φ k) c hc
        (χ k) (hχsmooth k) (hχodd k) (hgood k)
    exact ⟨p, H, h0, h1, h2, h3, h4⟩
  choose p H h0 h1 h2 h3 h4 using hkey
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    funext y
    rw [h0 k y]
    rfl
  · intro k
    funext y
    exact h1 k y
  · intro k t y hy
    exact h2 k t y hy
  · intro k
    exact h3 k
  · intro k
    exact h4 k

end

end Work.Drive
