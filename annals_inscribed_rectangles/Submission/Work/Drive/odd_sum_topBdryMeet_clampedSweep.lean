import Mathlib
import Submission.Work.Drive.meet3Generic_face_clampedSweeps
import Submission.Work.Drive.bottomBdryMeet_clampedSweep_count
import Submission.Work.Drive.hface_clampedSweeps_local
import Submission.Work.Drive.ha_clampedSweeps

/-!
# Hugelmeyer's Lemma 4 identity `n_P + n_Q + n_R ≡ 1`: the parity form

The parity engine (`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes`) gives, for the
three radial sweeps of three plane presentations,

> `Σ_k (top_k + bottom_k)` even,   i.e.   `Σ_k top_k ≡ Σ_k bottom_k` (mod 2).

The end contribution `Σ_k bottom_k` is computed by
`Work.Drive.sum_bottomBdryMeet_clampedSweep_eq_one`: with the truncation levels `c 0 > c 1 > c 2` of the
corrected design (`END_LEVEL_OBSTRUCTION.md` §3) it is **`1`**, provided the three plane charts have a
single common class (`hy`, `huniq`).  Combining the two gives the parity identity of Hugelmeyer's
Lemma 4 in its counting form

> `n_P + n_Q + n_R = Σ_k top_k` is **odd**,

which is the input of the transitivity clause of `Work.Drive.ParityCore γ`
(`Work.Drive.e_add_of_triple` sharpens it, together with the multiplicativity `n_P ≡ ε_Q ε_R`, to
`e a = e c = 1 → e (a+c) = 1`).

The remaining hypotheses of the statement below are the ones the engine asks for: the plane-local
conditions `hc` (the plane presentation is an immersion) and `hV` (the three class `2`-planes are in
general position), the radial non-degeneracy `ha`, the boundary genericity `hface`, and the collision
data of the end contribution.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

/-- **Hugelmeyer's Lemma 4 parity identity: `n_P + n_Q + n_R` is odd.** -/
theorem odd_sum_topBdryMeet_clampedSweeps
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ Ctop ψ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (hanti : StrictAntiOn ψ (Set.Icc (0 : ℝ) 1))
    (hcpos : ∀ k : Fin 3, 0 < c k) (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y))
    (ha : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, deriv ψ (x k 2) * (Real.log (c k) - Real.log
          (levelOf (P k (mk2 (x k 0) (x k 1))))) ≠ 0)
    (hci : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, Function.Injective (planeClassDeriv c ψ P k x))
    (hV : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2) →
        (planeClassDeriv c ψ P 0 x).range ⊓ (planeClassDeriv c ψ P 1 x).range
          ⊓ (planeClassDeriv c ψ P 2 x).range = ⊥)
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2) →
        (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
        ∃ k : Fin 3, (x k 2 = 0 ∨ x k 2 = 1) ∧
          (∀ j : Fin 3, j ≠ 2 → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1))
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (q : Projectivization ℝ (Eucl 3))
    (hy : ∀ k, ∃! y : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 ∧
      (cappingSpaceHomeoProj (P k y)).2 = q)
    (huniq : ∀ q' : Projectivization ℝ (Eucl 3),
      (∀ k, ∃ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P k y)).2 = q') → q' = q) :
    Odd ((topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      + (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1).ncard
      + (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2).ncard) := by
  have heng := even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planes P c ψ hψ hP hPseam
    ha hci hV hface
  have hbot := sum_bottomBdryMeet_clampedSweep_eq_one_local c hcpos hc1 hc2 ψ hψ0 hψ1 hψ01 hcont hanti
    P hlev q hy huniq
  set T0 := (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard with hT0
  set T1 := (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1).ncard with hT1
  set T2 := (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2).ncard with hT2
  set B0 := (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard with hB0
  set B1 := (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1).ncard with hB1
  set B2 := (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2).ncard with hB2
  have hbot' : B0 + B1 + B2 = 1 := hbot
  have hrearr : (T0 + B0) + (T1 + B1) + (T2 + B2) = (T0 + T1 + T2) + (B0 + B1 + B2) := by ring
  rw [hrearr, hbot'] at heng
  exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heng)

/-- **The parity identity `n_P + n_Q + n_R` odd, with `ha` and `hface` discharged.**  The only inputs
left are the plane-local conditions `hc`/`hV` of the plane presentations (immersion and general
position) and the collision data of the end contribution. -/
theorem odd_sum_topBdryMeet_clampedSweeps_of_planes
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ Ctop ψ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0) (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hψ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv ψ t ≠ 0)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1))
    (hanti : StrictAntiOn ψ (Set.Icc (0 : ℝ) 1))
    (hcpos : ∀ k : Fin 3, 0 < c k) (hck : ∀ k : Fin 3, c k ≤ c 0)
    (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Ctop (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y))
    (hci : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, Function.Injective (planeClassDeriv c ψ P k x))
    (hV : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 1) ψ (P 1) (x 1) →
        clampedSweep (c 0) ψ (P 0) (x 0) = clampedSweep (c 2) ψ (P 2) (x 2) →
        (planeClassDeriv c ψ P 0 x).range ⊓ (planeClassDeriv c ψ P 1 x).range
          ⊓ (planeClassDeriv c ψ P 2 x).range = ⊥)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (q : Projectivization ℝ (Eucl 3))
    (hy : ∀ k, ∃! y : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 ∧
      (cappingSpaceHomeoProj (P k y)).2 = q)
    (huniq : ∀ q' : Projectivization ℝ (Eucl 3),
      (∀ k, ∃ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P k y)).2 = q') → q' = q)
    (hyint : ∀ (k : Fin 3) (i : Fin 2), (hy k).choose i ∈ Set.Ioo (0 : ℝ) 1)
    (hrne : ∀ j k : Fin 3, j ≠ k →
      levelOf (P j ((hy j).choose)) ≠ levelOf (P k ((hy k).choose))) :
    Odd ((topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      + (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1).ncard
      + (topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2).ncard) :=
  odd_sum_topBdryMeet_clampedSweeps P c ψ hψ hψ0 hψ1 hψ01 hcont hanti hcpos hc1 hc2 hP hPseam
    (ha_clampedSweeps P c ψ hcpos hck hψ' hlev) hci hV
    (hface_clampedSweeps_local c hcpos hc1 hc2 ψ hψ0 hψ1 hψ01 P hlev q hy huniq hyint hrne)
    hlev q hy huniq

end

end Work.Drive
