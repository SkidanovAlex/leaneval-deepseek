import Mathlib
import Submission.Work.Drive.meet3Generic_trans_clampedSweeps
import Submission.Work.Drive.clampedSweepCommonDir

/-!
# The face field of `Meet3Generic` for three radial sweeps

`Work.Drive.Meet3Generic.face` asks, at every boundary triple point `x` of the three parameter cubes,
for a *unique* face coordinate and a common tangent direction transversal to it.  For radial sweeps

* the common direction is the *radial* one, rescaled by the radial coefficients
  (`Work.Drive.tripleCommonDir_clampedSweeps`), so transversality forces the unique face coordinate to
  be `x k 2`;
* the uniqueness itself is a genericity condition on the triple-point set (no two coordinates on a
  face), which this file takes as the hypothesis `hface`.

The conclusion of `Work.Drive.meet3Generic_face_clampedSweeps` is *exactly* the type of the `face`
field of `Work.Drive.Meet3Generic` for `D k = clampedSweep (c k) ψ (P k)`, so it can be combined with
`Work.Drive.meet3Generic_trans_clampedSweeps` (the `trans` field) into the structure.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold Topology Filter

noncomputable section

set_option maxHeartbeats 8000000

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

/-- **The `face` field of `Meet3Generic` for three radial sweeps.** -/
theorem meet3Generic_face_clampedSweeps
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (ha : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, deriv ψ (x k 2) * (Real.log (c k) - Real.log
          (Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1))))) ≠ 0)
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
        ∃ k : Fin 3, (x k 2 = 0 ∨ x k 2 = 1) ∧
          (∀ j : Fin 3, j ≠ 2 → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1)) :
    ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
        = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
      Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
        = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
      (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
      ∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
          TripleCommonDir
            (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 0) ψ (P 0)) (x 0))
            (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 1) ψ (P 1)) (x 1))
            (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 2) ψ (P 2)) (x 2)) v ∧
          v k i ≠ 0 := by
  intro x hbox h01 h02 hbdry
  obtain ⟨k, hk2, hkother, hothers⟩ := hface x hbox h01 h02 hbdry
  have hA0 : ∀ k' : Fin 3, deriv ψ (x k' 2) * (Real.log (c k') - Real.log
      (Work.Drive.levelOf (P k' (Work.Drive.mk2 (x k' 0) (x k' 1))))) ≠ 0 :=
    ha x hbox h01 h02
  refine ⟨k, 2, hk2, (fun j hj => hkother j hj), hothers,
    (fun k' => (1 / (deriv ψ (x k' 2) * (Real.log (c k') - Real.log
      (Work.Drive.levelOf (P k' (Work.Drive.mk2 (x k' 0) (x k' 1)))))))
        • EuclideanSpace.single 2 (1 : ℝ)), ?_, ?_⟩
  · refine Work.Drive.tripleCommonDir_clampedSweeps c ψ P hψ hP x ?_ _ (fun k' => rfl) hA0
    intro k'
    fin_cases k'
    · rfl
    · exact h01.symm
    · exact h02.symm
  · show ((1 / (deriv ψ (x k 2) * (Real.log (c k) - Real.log
      (Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1)))))))
        • EuclideanSpace.single 2 (1 : ℝ)) 2 ≠ 0
    rw [PiLp.smul_apply, EuclideanSpace.single_apply, if_pos rfl, smul_eq_mul, mul_one]
    exact div_ne_zero one_ne_zero (hA0 k)

/-- **The full genericity data of three radial sweeps**, assembled from the plane conditions (`ha`,
`hc`, `hV`) and the genericity of the triple-point set at the boundary (`hface`). -/
theorem meet3Generic_clampedSweeps
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (ha : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, deriv ψ (x k 2) * (Real.log (c k) - Real.log
          (Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1))))) ≠ 0)
    (hc : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, Function.Injective (Work.Drive.planeClassDeriv c ψ P k x))
    (hV : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        (Work.Drive.planeClassDeriv c ψ P 0 x).range
          ⊓ (Work.Drive.planeClassDeriv c ψ P 1 x).range
          ⊓ (Work.Drive.planeClassDeriv c ψ P 2 x).range = ⊥)
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
        ∃ k : Fin 3, (x k 2 = 0 ∨ x k 2 = 1) ∧
          (∀ j : Fin 3, j ≠ 2 → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1)) :
    Work.Drive.Meet3Generic Work.Drive.CappingSpace
      (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) :=
  ⟨Work.Drive.meet3Generic_trans_clampedSweeps c ψ P hψ hP ha hc hV,
    meet3Generic_face_clampedSweeps c ψ P hψ hP ha hface⟩

/-- **The parity identity `Σ_k top_k ≡ Σ_k bottom_k` for three radial sweeps, from plane conditions.**
This is `Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped` with its genericity input
`Meet3Generic` produced from the plane conditions (`ha`, `hc`, `hV`) and the genericity of the
triple-point set at the boundary (`hface`). -/
theorem even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace) (c : Fin 3 → ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y))
    (ha : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, deriv ψ (x k 2) * (Real.log (c k) - Real.log
          (Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1))))) ≠ 0)
    (hc : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, Function.Injective (Work.Drive.planeClassDeriv c ψ P k x))
    (hV : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        (Work.Drive.planeClassDeriv c ψ P 0 x).range
          ⊓ (Work.Drive.planeClassDeriv c ψ P 1 x).range
          ⊓ (Work.Drive.planeClassDeriv c ψ P 2 x).range = ⊥)
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
        ∃ k : Fin 3, (x k 2 = 0 ∨ x k 2 = 1) ∧
          (∀ j : Fin 3, j ≠ 2 → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1)) :
    Even (((topBdryMeet CappingSpace (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 0).ncard
        + (bottomBdryMeet CappingSpace (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 0).ncard)
      + ((topBdryMeet CappingSpace (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 1).ncard
        + (bottomBdryMeet CappingSpace (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 1).ncard)
      + ((topBdryMeet CappingSpace (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 2).ncard
        + (bottomBdryMeet CappingSpace (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 2).ncard)) :=
  Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped P c ψ hψ hP hPseam
    (meet3Generic_clampedSweeps c ψ P hψ hP ha hc hV hface)

/-- **`hface` puts every class coordinate of a triple point strictly inside the cube.**  A triple point
whose `x k 0` or `x k 1` were `0` or `1` would be a boundary triple point whose face coordinate is not
`x k 2`, contradicting `hface`.  Consequently the `x k 2 = 0`/`x k 2 = 1` faces are the *only* faces a
triple point can meet.

This matters for the concrete presentations: `Work.Drive.diskPlane` (`Submission/Work/Drive/planeChain.lean`)
is `Q ∘ sqDisk ∘ (foldFun, foldFun)` with `foldFun x = (1 − cos (π x))/2`, whose derivative *vanishes*
at the integers, so the class derivative of the plane presentation degenerates exactly on the seam
`x k 0 ∈ {0,1} ∨ x k 1 ∈ {0,1}`.  The lemma below shows that under `hface` no triple point lies there,
so the immersion hypothesis `hc` of `Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes`
is only ever applied where that presentation is non-degenerate. -/
theorem class_coord_interior_of_hface
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
        ∃ k : Fin 3, (x k 2 = 0 ∨ x k 2 = 1) ∧
          (∀ j : Fin 3, j ≠ 2 → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hbox : ∀ k, x k ∈ Submission.Drive.unitBox 2)
    (h01 : Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
      = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1))
    (h02 : Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
      = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2))
    (k : Fin 3) (i : Fin 3) (hi : i ≠ 2) :
    ¬ (x k i = 0 ∨ x k i = 1) := by
  rintro (h0 | h0)
  · have hbdry : ∃ k, x k ∈ Submission.Drive.unitBoxBdry 2 :=
      ⟨k, hbox k, i, Or.inl h0⟩
    obtain ⟨k', -, hk'other, hother⟩ := hface x hbox h01 h02 hbdry
    have hkk : k' = k := by
      by_contra hne
      have hlt := (hother k (Ne.symm hne) i).1
      rw [h0] at hlt
      exact lt_irrefl 0 hlt
    subst hkk
    have hlt := (hk'other i hi).1
    rw [h0] at hlt
    exact lt_irrefl 0 hlt
  · have hbdry : ∃ k, x k ∈ Submission.Drive.unitBoxBdry 2 :=
      ⟨k, hbox k, i, Or.inr h0⟩
    obtain ⟨k', -, hk'other, hother⟩ := hface x hbox h01 h02 hbdry
    have hkk : k' = k := by
      by_contra hne
      have hlt := (hother k (Ne.symm hne) i).2
      rw [h0] at hlt
      exact lt_irrefl 1 hlt
    subst hkk
    have hlt := (hk'other i hi).2
    rw [h0] at hlt
    exact lt_irrefl 1 hlt

/-- Membership in `Ioo 0 1` from membership in `Icc 0 1` and exclusion of the endpoints. -/
lemma mem_Ioo_of_mem_Icc_of_ne {t : ℝ} (h : t ∈ Set.Icc (0 : ℝ) 1) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    t ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le h.1 with h' | h'
    · exact absurd h'.symm h0
    · exact h'
  · rcases eq_or_lt_of_le h.2 with h' | h'
    · exact absurd h' h1
    · exact h'

/-- **`hface` puts every class coordinate of a triple point strictly inside the cube.**  This is the
`Ioo` form of `Work.Drive.class_coord_interior_of_hface` (with the box bounds supplied by
`Work.Drive.unitBox`).  It says that the `x k 2 = 0`/`x k 2 = 1` faces are the *only* faces a triple
point can meet, so a *folded* presentation of the plane whose class derivative degenerates on the seam
(`Work.Drive.diskPlane`, see `Work.Drive.class_coord_interior_of_hface`) is non-degenerate at every
triple point. -/
theorem class_coords_mem_Ioo_of_hface
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
        ∃ k : Fin 3, (x k 2 = 0 ∨ x k 2 = 1) ∧
          (∀ j : Fin 3, j ≠ 2 → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hbox : ∀ k, x k ∈ Submission.Drive.unitBox 2)
    (h01 : Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
      = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1))
    (h02 : Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
      = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2))
    (k : Fin 3) (i : Fin 3) (hi : i ≠ 2) :
    x k i ∈ Set.Ioo (0 : ℝ) 1 :=
  mem_Ioo_of_mem_Icc_of_ne (hbox k i)
    (fun h => class_coord_interior_of_hface c ψ P hface x hbox h01 h02 k i hi (Or.inl h))
    (fun h => class_coord_interior_of_hface c ψ P hface x hbox h01 h02 k i hi (Or.inr h))

/-- **The radial coefficient is non-zero as soon as the cutoff's derivative is and the plane's level
differs from the sweep's target level.**  This is the elementary half of the hypothesis `ha` of
`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes`: the levels `c k` are free
parameters of the construction, so `r k ≠ c k` is a choice, and `deriv ψ ≠ 0` is a property of the
cutoff. -/
theorem radialCoeff_ne_zero {c r t : ℝ} (hc : 0 < c) (hr : 0 < r) (hrc : r ≠ c) {ψ : ℝ → ℝ}
    (hψ : deriv ψ t ≠ 0) : deriv ψ t * (Real.log c - Real.log r) ≠ 0 :=
  mul_ne_zero hψ (sub_ne_zero.mpr (fun h => hrc (Real.log_injOn_pos hc hr h).symm))

end

end Work.Drive
