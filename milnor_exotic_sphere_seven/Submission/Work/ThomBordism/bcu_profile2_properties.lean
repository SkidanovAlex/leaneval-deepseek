import Mathlib
import Submission.Work.ThomBordism.BCUProfile
import Submission.Work.ThomBordism.bcu_profile_properties

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The elementary properties of the seam-free boundary-collapse profile

`Work.ThomBordism.BCU.profile2` (`Submission/Work/ThomBordism/BCUProfile.lean`) is the
*seam-free* variant of the three-phase boundary-collapse profile: it differs from
`BCU.profile` only in the third phase, where `BCU.shiftPhase` is replaced by the
interpolation

  `shiftPhase2 p e v = clampBall ((p / ‖v‖ + (1 - p)) • v + (p * (1 - p)) • e)`,

which at `p = 1` is the normalisation `v ↦ clampBall (v/‖v‖)` (matching the spherical phase at
`φ = 0`) and at `p = 0` is the identity `clampBall v`.

This file collects the *elementary* (point-set) properties of `profile2` that the boundary-sign
construction uses, mirroring `bcu_profile_properties.lean`:

* every value of the profile is in the standard half-ball (for `e 0 = 0` and `0 ≤ v 0`, `0 ≤ t ≤ 1`);
* for `v` in the hyperplane `{v 0 = 0}` the value is on the boundary of the half-ball;
* at time `1` the profile is the radial clamp;
* for `t ≤ 1/2` the profile is the constant north pole;
* the zero fibre of the third phase is exactly the zero locus of its (linear) argument;
* at every point `V` of the small ball `{‖V‖ ≤ 1/2}` with `V 0 > 0` the preimage of `V` under the
  third phase is exactly `V` (or the degenerate `t = 1`, `v = V`).
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.ThomBordism.BCU

/-! ## The second shift phase -/

/-- The (linear) argument of `shiftPhase2`, `(p/‖v‖ + (1-p)) • v + (p(1-p)) • e`. -/
noncomputable def shift2Arg {m : ℕ} (p : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  (p / ‖v‖ + (1 - p)) • v + (p * (1 - p)) • e

theorem shiftPhase2_eq_clampBall {m : ℕ} (p : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    shiftPhase2 p e v = clampBall (shift2Arg p e v) := rfl

/-- The `0`-th coordinate of the argument of `shiftPhase2`. -/
theorem bcu_shift2Arg_coord {m : ℕ} (p : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    shift2Arg p e v 0 = (p / ‖v‖ + (1 - p)) * (v 0) + (p * (1 - p)) * (e 0) := by
  simp [shift2Arg]

/-- The `0`-th coordinate of the second shift phase. -/
theorem bcu_shift2_coord {m : ℕ} (p : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    (shiftPhase2 p e v) 0 = min 1 ‖shift2Arg p e v‖⁻¹ * (shift2Arg p e v 0) := by
  rw [shiftPhase2, bcu_clampBall_coord]
  rfl

/-- The second shift phase lands in the closed unit ball. -/
theorem bcu_shift2_norm_le {m : ℕ} (p : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖shiftPhase2 p e v‖ ≤ 1 := by
  rw [shiftPhase2]; exact bcu_clampBall_norm_le _

/-- Nonnegativity of the `0`-th coordinate of the argument of `shiftPhase2`, for `0 ≤ p ≤ 1`. -/
theorem bcu_shift2Arg_coord_nonneg {m : ℕ} (p : ℝ)
    (e v : EuclideanSpace ℝ (Fin (m + 1))) (he : e 0 = 0) (hv : 0 ≤ v 0)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ shift2Arg p e v 0 := by
  rw [bcu_shift2Arg_coord, he, mul_zero, add_zero]
  exact mul_nonneg (add_nonneg (div_nonneg hp0 (norm_nonneg v)) (sub_nonneg.mpr hp1)) hv

/-- The second shift phase preserves nonnegativity of the `0`-th coordinate when `e 0 = 0` and
`0 ≤ p ≤ 1`. -/
theorem bcu_shift2_coord_nonneg {m : ℕ} (p : ℝ)
    (e v : EuclideanSpace ℝ (Fin (m + 1))) (he : e 0 = 0) (hv : 0 ≤ v 0)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ (shiftPhase2 p e v) 0 := by
  rw [bcu_shift2_coord]
  exact mul_nonneg (le_min zero_le_one (inv_nonneg.mpr (norm_nonneg _)))
    (bcu_shift2Arg_coord_nonneg p e v he hv hp0 hp1)

/-- On the hyperplane the argument of the second shift phase has `0`-th coordinate `0`. -/
theorem bcu_shift2Arg_coord_eq_zero {m : ℕ} (p : ℝ)
    (e v : EuclideanSpace ℝ (Fin (m + 1))) (he : e 0 = 0) (hv : v 0 = 0) :
    shift2Arg p e v 0 = 0 := by
  rw [bcu_shift2Arg_coord, he, hv, mul_zero, mul_zero, add_zero]

/-- On the hyperplane the second shift phase keeps the `0`-th coordinate equal to `0`. -/
theorem bcu_shift2_coord_eq_zero {m : ℕ} (p : ℝ)
    (e v : EuclideanSpace ℝ (Fin (m + 1))) (he : e 0 = 0) (hv : v 0 = 0) :
    (shiftPhase2 p e v) 0 = 0 := by
  rw [bcu_shift2_coord, bcu_shift2Arg_coord_eq_zero p e v he hv, mul_zero]

/-- The zero fibre of the second shift phase. -/
theorem bcu_shift2_eq_zero_iff {m : ℕ} (p : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    shiftPhase2 p e v = 0 ↔ shift2Arg p e v = 0 := by
  simp only [shiftPhase2, shift2Arg]
  exact bcu_clampBall_eq_zero _

/-- If a value of the second shift phase is small (`‖V‖ < 1`), the clamp was inactive. -/
theorem bcu_shift2Arg_eq_of_norm_lt {m : ℕ} (p : ℝ)
    (e v V : EuclideanSpace ℝ (Fin (m + 1))) (hV : ‖V‖ < 1)
    (h : shiftPhase2 p e v = V) : shift2Arg p e v = V := by
  by_contra hne
  have hh : clampBall (shift2Arg p e v) = V := h
  have h1 : 1 ≤ ‖shift2Arg p e v‖ := by
    by_contra hlt
    have hlt' : ‖shift2Arg p e v‖ < 1 := lt_of_not_ge hlt
    have hcl := bcu_clampBall_eq_self (shift2Arg p e v) (le_of_lt hlt')
    rw [hcl] at hh
    exact hne hh
  have h2 : ‖V‖ = 1 := by rw [← hh, bcu_clampBall_norm_eq_one _ h1]
  rw [h2] at hV
  exact absurd hV (lt_irrefl 1)

end Work.ThomBordism.BCU

namespace Work.ThomBordism

open Work.ThomBordism.BCU

/-- The elementary point-set properties of the seam-free profile family `profile2`. -/
theorem bcu_profile2_properties (m : ℕ) :
    (∀ (e v : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ), e 0 = 0 → 0 ≤ v 0 → 0 ≤ t → t ≤ 1 →
        Work.ThomBordism.BCU.profile2 e t v ∈ Work.ThomBordism.stdHalfBall (m + 1)) ∧
    (∀ (e v : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ), e 0 = 0 → v 0 = 0 → v ≠ 0 →
        ∃ h : Work.ThomBordism.BCU.profile2 e t v ∈ Work.ThomBordism.stdHalfBall (m + 1),
          (⟨Work.ThomBordism.BCU.profile2 e t v, h⟩ : ↥(Work.ThomBordism.stdHalfBall (m + 1)))
            ∈ Work.ThomBordism.stdHalfBallBdry (m + 1)) ∧
    (∀ (e v : EuclideanSpace ℝ (Fin (m + 1))), Work.ThomBordism.BCU.profile2 e 1 v
        = Work.ThomBordism.BCU.clampBall v) ∧
    (∀ (e v : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ), t ≤ 1 / 2 →
        Work.ThomBordism.BCU.profile2 e t v = Work.ThomBordism.BCU.northPole m) ∧
    (∀ (e v : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ), e 0 = 0 → 0 ≤ v 0 → v ≠ 0 →
        Work.ThomBordism.BCU.shiftPhase2 ((1 - t) * 4) e v = 0 →
        ((1 - t) * 4 / ‖v‖ + (1 - (1 - t) * 4)) • v + (((1 - t) * 4) * (1 - (1 - t) * 4)) • e = 0) ∧
    (∀ (e v V : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ), e 0 = 0 → 0 ≤ v 0 → v ≠ 0 →
        0 < V 0 → ‖V‖ ≤ 1 / 2 → Work.ThomBordism.BCU.profile2 e t v = V →
        (t = 1 ∧ v = V) ∨
          ((1 - t) * 4 / ‖v‖ + (1 - (1 - t) * 4)) • v
            + (((1 - t) * 4) * (1 - (1 - t) * 4)) • e = V) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e v t he hv0 ht0 ht1
    rw [profile2]
    split_ifs with h1 h2
    · exact bcu_northPole_mem m
    · obtain ⟨hcos, hsin⟩ := bcu_phase2_nonneg h1 h2
      exact ⟨bcu_sphPhase_coord_nonneg _ _ hcos hsin hv0, bcu_sphPhase_norm_le _ _⟩
    · have ht34 : 3 / 4 < t := not_le.mp h2
      have hp0 : 0 ≤ (1 - t) * 4 := by linarith
      have hp1 : (1 - t) * 4 ≤ 1 := by linarith
      exact ⟨bcu_shift2_coord_nonneg _ e v he hv0 hp0 hp1, bcu_shift2_norm_le _ e v⟩
  · intro e v t he hv hvne
    rw [profile2]
    split_ifs with h1 h2
    · exact ⟨bcu_northPole_mem m, Or.inr (bcu_northPole_norm m)⟩
    · obtain ⟨hcos, hsin⟩ := bcu_phase2_nonneg h1 h2
      have hv0 : 0 ≤ v 0 := le_of_eq hv.symm
      exact ⟨⟨bcu_sphPhase_coord_nonneg _ _ hcos hsin hv0, bcu_sphPhase_norm_le _ _⟩,
        Or.inr (bcu_sphPhase_norm_eq_one _ _ hvne hcos hsin hv0)⟩
    · have hz : (shiftPhase2 ((1 - t) * 4) e v) 0 = 0 :=
        bcu_shift2_coord_eq_zero _ e v he hv
      exact ⟨⟨le_of_eq hz.symm, bcu_shift2_norm_le _ e v⟩, Or.inl hz⟩
  · intro e v
    rw [profile2]
    norm_num
    rw [shiftPhase2]
    norm_num
  · intro e v t ht
    rw [profile2, if_pos ht]
  · intro e v t he hv0 hvne h
    have h' : shiftPhase2 ((1 - t) * 4) e v = 0 := h
    exact (bcu_shift2_eq_zero_iff ((1 - t) * 4) e v).mp h'
  · intro e v V t he hv0 hvne hV0 hVn h
    rw [profile2] at h
    split_ifs at h with h1 h2
    · exfalso
      have hV1 : V 0 = 1 := by rw [← h, bcu_northPole_coord]
      have hle := PiLp.norm_apply_le V 0
      rw [hV1] at hle
      simp at hle
      linarith
    · exfalso
      obtain ⟨hcos, hsin⟩ := bcu_phase2_nonneg h1 h2
      have hnorm := bcu_sphPhase_norm_eq_one _ v hvne hcos hsin hv0
      rw [h] at hnorm
      linarith
    · right
      exact bcu_shift2Arg_eq_of_norm_lt _ e v V (by linarith) h

end Work.ThomBordism
