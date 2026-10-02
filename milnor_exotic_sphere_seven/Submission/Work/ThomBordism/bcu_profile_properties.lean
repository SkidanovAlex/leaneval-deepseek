import Mathlib
import Submission.Work.ThomBordism.BCUProfile

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The elementary properties of the boundary-collapse profile

The profile family `Work.ThomBordism.BCU.profile` (`Submission/Work/ThomBordism/BCUProfile.lean`)
is the three-phase family used by the collapse map `Φ : W → ↥(stdHalfBall (n+1))` of the
boundary-sign construction.  This file collects the *elementary* (point-set, not homological)
properties that the construction uses:

* every value of the profile is in the standard half-ball (for a nonnegative `0`-th coordinate);
* on the hyperplane `{v 0 = 0}` the value is on the *boundary* of the half-ball;
* at time `1` the profile is the radial clamp;
* for `t ≤ 1/2` the profile is the constant north pole;
* the zero fibre of the profile is exactly the segment `{-((1-t)*4) • e}`;
* more generally, at every point `V` of the *small* ball `{‖V‖ ≤ 1/2}` with `V 0 > 0` the
  preimage of `V` under the third phase is the single point `V - ((1-t)*4) • e` (or `t = 1`,
  `v = V`).

These are the point-set hypotheses of `Work.ThomBordism.boundarySign_boundaryChartAt_univ`
(NOTE_BCU_PLAN3.md §1): membership, boundary preservation, the identity at time `1`, the
constant phase, and the two fibre conditions at the two distinguished points (`0` and the
prescribed interior value `V`).
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.ThomBordism.BCU

/-! ## The radial clamp -/

/-- The norm of the radial clamp is the clamped norm. -/
theorem bcu_clampBall_norm {m : ℕ} (w : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖clampBall w‖ = min 1 ‖w‖ := by
  rw [clampBall, norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (inv_nonneg.mpr (norm_nonneg w)))]
  rcases eq_or_lt_of_le (norm_nonneg w) with h | h
  · rw [← h]; simp
  · rcases lt_or_ge ‖w‖ 1 with h1 | h1
    · rw [min_eq_left (le_of_lt ((one_lt_inv₀ h).mpr h1)), one_mul, min_eq_right (le_of_lt h1)]
    · rw [min_eq_right ((inv_le_one₀ h).mpr h1), inv_mul_cancel₀ (ne_of_gt h), min_eq_left h1]

/-- Every value of the radial clamp lies in the closed unit ball. -/
theorem bcu_clampBall_norm_le {m : ℕ} (w : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖clampBall w‖ ≤ 1 := by
  rw [bcu_clampBall_norm]; exact min_le_left _ _

/-- Outside the unit ball the radial clamp has norm exactly `1`. -/
theorem bcu_clampBall_norm_eq_one {m : ℕ} (w : EuclideanSpace ℝ (Fin (m + 1)))
    (h : 1 ≤ ‖w‖) : ‖clampBall w‖ = 1 := by
  rw [bcu_clampBall_norm, min_eq_left h]

/-- Inside the closed unit ball the radial clamp is the identity. -/
theorem bcu_clampBall_eq_self {m : ℕ} (w : EuclideanSpace ℝ (Fin (m + 1))) (h : ‖w‖ ≤ 1) :
    clampBall w = w := by
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | h0
  · have hw : w = 0 := norm_eq_zero.mp h0.symm
    rw [hw, clampBall]; simp
  · rw [clampBall, min_eq_left ((one_le_inv₀ h0).mpr h), one_smul]

/-- The `0`-th coordinate of the radial clamp. -/
theorem bcu_clampBall_coord {m : ℕ} (w : EuclideanSpace ℝ (Fin (m + 1))) :
    (clampBall w) 0 = min 1 ‖w‖⁻¹ * (w 0) := by simp [clampBall]

/-- A radial clamp vanishes only at the origin. -/
theorem bcu_clampBall_eq_zero {m : ℕ} (w : EuclideanSpace ℝ (Fin (m + 1))) :
    clampBall w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have h2 : (min 1 ‖w‖⁻¹) • w = 0 := by rw [← h]; rfl
    rcases smul_eq_zero.mp h2 with h3 | h3
    · have h6 : ‖w‖⁻¹ = 0 := by
        rcases lt_or_ge ‖w‖⁻¹ 1 with hlt | hge
        · rwa [min_eq_right (le_of_lt hlt)] at h3
        · rw [min_eq_left hge] at h3; exact absurd h3 one_ne_zero
      rw [inv_eq_zero, norm_eq_zero] at h6; exact h6
    · exact h3
  · intro h; rw [h, clampBall]; simp

/-- The radial clamp preserves nonnegativity of the `0`-th coordinate. -/
theorem bcu_clampBall_coord_nonneg {m : ℕ} (w : EuclideanSpace ℝ (Fin (m + 1)))
    (h : 0 ≤ w 0) : 0 ≤ (clampBall w) 0 := by
  rw [bcu_clampBall_coord]
  exact mul_nonneg (le_min zero_le_one (inv_nonneg.mpr (norm_nonneg w))) h

/-! ## The north pole -/

/-- The `0`-th coordinate of the north pole. -/
theorem bcu_northPole_coord (m : ℕ) : (northPole m) 0 = 1 := by
  simp [northPole, Work.PTGeometric.consCLM_apply_zero]

/-- The north pole is a unit vector. -/
theorem bcu_northPole_norm (m : ℕ) : ‖northPole m‖ = 1 := by
  rw [northPole, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
  rw [Work.PTGeometric.consCLM_apply_zero]
  simp [Work.PTGeometric.consCLM_apply_succ]

/-- The north pole is nonzero. -/
theorem bcu_northPole_ne_zero (m : ℕ) : northPole m ≠ 0 := by
  intro h
  have := congrArg (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) h
  rw [bcu_northPole_coord] at this; simp at this

/-- The north pole lies in the standard half-ball. -/
theorem bcu_northPole_mem (m : ℕ) : northPole m ∈ stdHalfBall (m + 1) := by
  refine ⟨?_, ?_⟩
  · rw [bcu_northPole_coord]; norm_num
  · rw [bcu_northPole_norm]

/-- The pairing with the north pole is the `0`-th coordinate. -/
theorem bcu_inner_v_northPole {m : ℕ} (v : EuclideanSpace ℝ (Fin (m + 1))) :
    inner ℝ v (northPole m) = v 0 := by
  rw [northPole, PiLp.inner_apply, Fin.sum_univ_succ]
  rw [Work.PTGeometric.consCLM_apply_zero]
  simp [Work.PTGeometric.consCLM_apply_succ]

/-! ## The spherical phase -/

/-- `‖v‖⁻¹ • v` is a unit vector for `v ≠ 0`. -/
theorem bcu_norm_inv_smul_self {m : ℕ} (v : EuclideanSpace ℝ (Fin (m + 1))) (hv : v ≠ 0) :
    ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

/-- The squared norm of the argument of the spherical phase. -/
theorem bcu_sphArg_norm_sq {m : ℕ} (φ : ℝ) (v : EuclideanSpace ℝ (Fin (m + 1)))
    (hv : v ≠ 0) :
    ‖Real.cos φ • (‖v‖⁻¹ • v) + Real.sin φ • northPole m‖ ^ 2
      = Real.cos φ ^ 2 + Real.sin φ ^ 2
        + 2 * Real.cos φ * Real.sin φ * (‖v‖⁻¹ * v 0) := by
  rw [norm_add_sq_real]
  have hu : ‖‖v‖⁻¹ • v‖ = 1 := bcu_norm_inv_smul_self v hv
  have hx : ‖Real.cos φ • (‖v‖⁻¹ • v)‖ ^ 2 = Real.cos φ ^ 2 := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs]
  have hy : ‖Real.sin φ • northPole m‖ ^ 2 = Real.sin φ ^ 2 := by
    rw [norm_smul, bcu_northPole_norm, mul_one, Real.norm_eq_abs, sq_abs]
  have hxy : inner ℝ (Real.cos φ • (‖v‖⁻¹ • v)) (Real.sin φ • northPole m)
      = Real.cos φ * Real.sin φ * (‖v‖⁻¹ * v 0) := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, bcu_inner_v_northPole]
    ring
  rw [hx, hy, hxy]; ring

/-- Under the sign conditions of the spherical phase the argument of the clamp has norm `≥ 1`. -/
theorem bcu_one_le_norm_sphArg {m : ℕ} (φ : ℝ) (v : EuclideanSpace ℝ (Fin (m + 1)))
    (hv : v ≠ 0) (hcos : 0 ≤ Real.cos φ) (hsin : 0 ≤ Real.sin φ) (hv0 : 0 ≤ v 0) :
    1 ≤ ‖Real.cos φ • (‖v‖⁻¹ • v) + Real.sin φ • northPole m‖ := by
  have hsq := bcu_sphArg_norm_sq φ v hv
  have hcs : 0 ≤ Real.cos φ * Real.sin φ := mul_nonneg hcos hsin
  have hk : 0 ≤ ‖v‖⁻¹ * v 0 := mul_nonneg (inv_nonneg.mpr (norm_nonneg v)) hv0
  have h1 : 0 ≤ ‖Real.cos φ • (‖v‖⁻¹ • v) + Real.sin φ • northPole m‖ := norm_nonneg _
  by_contra h
  push_neg at h
  nlinarith [hsq, Real.cos_sq_add_sin_sq φ, mul_nonneg hcs hk, h1, h]

/-- The spherical phase is `clampBall` applied to its argument. -/
theorem bcu_sphPhase_norm_le {m : ℕ} (φ : ℝ) (v : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖sphPhase φ v‖ ≤ 1 := by
  rw [sphPhase]; exact bcu_clampBall_norm_le _

/-- Under the sign conditions of the spherical phase the value has norm exactly `1`. -/
theorem bcu_sphPhase_norm_eq_one {m : ℕ} (φ : ℝ) (v : EuclideanSpace ℝ (Fin (m + 1)))
    (hv : v ≠ 0) (hcos : 0 ≤ Real.cos φ) (hsin : 0 ≤ Real.sin φ) (hv0 : 0 ≤ v 0) :
    ‖sphPhase φ v‖ = 1 := by
  rw [sphPhase]
  exact bcu_clampBall_norm_eq_one _ (bcu_one_le_norm_sphArg φ v hv hcos hsin hv0)

/-- The `0`-th coordinate of the spherical phase. -/
theorem bcu_sphPhase_coord_eq {m : ℕ} (φ : ℝ) (v : EuclideanSpace ℝ (Fin (m + 1))) :
    (sphPhase φ v) 0
      = min 1 ‖Real.cos φ • (‖v‖⁻¹ • v) + Real.sin φ • northPole m‖⁻¹
        * (Real.cos φ * (‖v‖⁻¹ * v 0) + Real.sin φ) := by
  rw [sphPhase, bcu_clampBall_coord]
  congr 1
  simp [PiLp.add_apply, PiLp.smul_apply, bcu_northPole_coord]

/-- The spherical phase preserves nonnegativity of the `0`-th coordinate. -/
theorem bcu_sphPhase_coord_nonneg {m : ℕ} (φ : ℝ) (v : EuclideanSpace ℝ (Fin (m + 1)))
    (hcos : 0 ≤ Real.cos φ) (hsin : 0 ≤ Real.sin φ) (hv0 : 0 ≤ v 0) :
    0 ≤ (sphPhase φ v) 0 := by
  rw [bcu_sphPhase_coord_eq]
  exact mul_nonneg (le_min zero_le_one (inv_nonneg.mpr (norm_nonneg _)))
    (add_nonneg (mul_nonneg hcos (mul_nonneg (inv_nonneg.mpr (norm_nonneg v)) hv0)) hsin)

/-! ## The shift phase -/

/-- The `0`-th coordinate of the shift phase. -/
theorem bcu_shiftPhase_coord {m : ℕ} (σ : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    (shiftPhase σ e v) 0 = min 1 ‖v + σ • e‖⁻¹ * ((v + σ • e) 0) := by
  rw [shiftPhase, bcu_clampBall_coord]

/-- The `0`-th coordinate of a shifted vector. -/
theorem bcu_add_smul_coord {m : ℕ} (σ : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    (v + σ • e) 0 = v 0 + σ * e 0 := by simp

/-- The shift phase preserves nonnegativity of the `0`-th coordinate when `e 0 = 0`. -/
theorem bcu_shiftPhase_coord_nonneg {m : ℕ} (σ : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1)))
    (he : e 0 = 0) (hv : 0 ≤ v 0) : 0 ≤ (shiftPhase σ e v) 0 := by
  rw [bcu_shiftPhase_coord, bcu_add_smul_coord, he, mul_zero, add_zero]
  exact mul_nonneg (le_min zero_le_one (inv_nonneg.mpr (norm_nonneg _))) hv

/-- On the hyperplane the shift phase keeps the `0`-th coordinate equal to `0`. -/
theorem bcu_shiftPhase_coord_eq_zero {m : ℕ} (σ : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1)))
    (he : e 0 = 0) (hv : v 0 = 0) : (shiftPhase σ e v) 0 = 0 := by
  rw [bcu_shiftPhase_coord, bcu_add_smul_coord, he, hv, mul_zero, add_zero, mul_zero]

/-- The shift phase lands in the closed unit ball. -/
theorem bcu_shiftPhase_norm_le {m : ℕ} (σ : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖shiftPhase σ e v‖ ≤ 1 := by
  rw [shiftPhase]; exact bcu_clampBall_norm_le _

/-- If a shift-phase value is small (`‖V‖ < 1`), the clamp was inactive. -/
theorem bcu_shiftPhase_eq_of_norm_lt {m : ℕ} (σ : ℝ) (e v V : EuclideanSpace ℝ (Fin (m + 1)))
    (hV : ‖V‖ < 1) (h : shiftPhase σ e v = V) : v + σ • e = V := by
  by_contra hne
  have h1 : 1 ≤ ‖v + σ • e‖ := by
    by_contra hlt
    have hlt' : ‖v + σ • e‖ < 1 := lt_of_not_ge hlt
    have := bcu_clampBall_eq_self (v + σ • e) (le_of_lt hlt')
    rw [shiftPhase] at h
    rw [this] at h
    exact hne h
  have h2 : ‖V‖ = 1 := by rw [← h, shiftPhase, bcu_clampBall_norm_eq_one _ h1]
  rw [h2] at hV; exact lt_irrefl 1 hV

/-- The zero fibre of the shift phase. -/
theorem bcu_shiftPhase_eq_zero {m : ℕ} (σ : ℝ) (e v : EuclideanSpace ℝ (Fin (m + 1))) :
    shiftPhase σ e v = 0 ↔ v = -σ • e := by
  rw [shiftPhase, bcu_clampBall_eq_zero]
  constructor
  · intro h
    have h' : v = -(σ • e) := eq_neg_of_add_eq_zero_left h
    rw [neg_smul]; exact h'
  · intro h; rw [h]; simp

/-- In the middle phase the angle has nonnegative cosine and sine. -/
theorem bcu_phase2_nonneg {t : ℝ} (h1 : ¬ t ≤ 1 / 2) (h2 : t ≤ 3 / 4) :
    0 ≤ Real.cos ((3 / 4 - t) * 2 * Real.pi) ∧
      0 ≤ Real.sin ((3 / 4 - t) * 2 * Real.pi) := by
  have hlt : 1 / 2 < t := lt_of_not_ge h1
  have hδ0 : 0 ≤ (3 / 4 - t) * 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hδle : (3 / 4 - t) * 2 * Real.pi ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  refine ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hδle⟩,
    Real.sin_nonneg_of_mem_Icc ⟨hδ0, by linarith [Real.pi_pos]⟩⟩

end Work.ThomBordism.BCU

namespace Work.ThomBordism

open Work.ThomBordism.BCU

/-- The elementary point-set properties of the profile family. -/
theorem bcu_profile_properties (m : ℕ) :
    (∀ (e v : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ), e 0 = 0 → 0 ≤ v 0 →
        Work.ThomBordism.BCU.profile e t v ∈ Work.ThomBordism.stdHalfBall (m + 1)) ∧
    (∀ (e v : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ), e 0 = 0 → v 0 = 0 → v ≠ 0 →
        ∃ h : Work.ThomBordism.BCU.profile e t v ∈ Work.ThomBordism.stdHalfBall (m + 1),
          (⟨Work.ThomBordism.BCU.profile e t v, h⟩ : ↥(Work.ThomBordism.stdHalfBall (m + 1)))
            ∈ Work.ThomBordism.stdHalfBallBdry (m + 1)) ∧
    (∀ (e v : EuclideanSpace ℝ (Fin (m + 1))), Work.ThomBordism.BCU.profile e 1 v
        = Work.ThomBordism.BCU.clampBall v) ∧
    (∀ (e v : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ), t ≤ 1 / 2 →
        Work.ThomBordism.BCU.profile e t v = Work.ThomBordism.BCU.northPole m) ∧
    (∀ (e v : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ), e 0 = 0 → 0 ≤ v 0 → v ≠ 0 →
        Work.ThomBordism.BCU.profile e t v = 0 → v = -((1 - t) * 4) • e) ∧
    (∀ (e v V : EuclideanSpace ℝ (Fin (m + 1))) (t : ℝ), e 0 = 0 → 0 ≤ v 0 → v ≠ 0 →
        0 < V 0 → ‖V‖ ≤ 1 / 2 → Work.ThomBordism.BCU.profile e t v = V →
        (t = 1 ∧ v = V) ∨ v = V - ((1 - t) * 4) • e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e v t he hv0
    rw [profile]
    split_ifs with h1 h2
    · exact bcu_northPole_mem m
    · obtain ⟨hcos, hsin⟩ := bcu_phase2_nonneg h1 h2
      exact ⟨bcu_sphPhase_coord_nonneg _ _ hcos hsin hv0, bcu_sphPhase_norm_le _ _⟩
    · exact ⟨bcu_shiftPhase_coord_nonneg _ _ _ he hv0, bcu_shiftPhase_norm_le _ _ _⟩
  · intro e v t he hv hvne
    rw [profile]
    split_ifs with h1 h2
    · exact ⟨bcu_northPole_mem m, Or.inr (bcu_northPole_norm m)⟩
    · obtain ⟨hcos, hsin⟩ := bcu_phase2_nonneg h1 h2
      have hv0 : 0 ≤ v 0 := le_of_eq hv.symm
      exact ⟨⟨bcu_sphPhase_coord_nonneg _ _ hcos hsin hv0, bcu_sphPhase_norm_le _ _⟩,
        Or.inr (bcu_sphPhase_norm_eq_one _ _ hvne hcos hsin hv0)⟩
    · have hz : (shiftPhase ((1 - t) * 4) e v) 0 = 0 :=
        bcu_shiftPhase_coord_eq_zero _ _ _ he hv
      have hmem : shiftPhase ((1 - t) * 4) e v ∈ stdHalfBall (m + 1) :=
        ⟨le_of_eq hz.symm, bcu_shiftPhase_norm_le _ _ _⟩
      exact ⟨hmem, Or.inl hz⟩
  · intro e v
    rw [profile]
    norm_num
    rw [shiftPhase]
    simp
  · intro e v t ht
    rw [profile, if_pos ht]
  · intro e v t he hv0 hvne h
    rw [profile] at h
    split_ifs at h with h1 h2
    · exact absurd h (bcu_northPole_ne_zero m)
    · obtain ⟨hcos, hsin⟩ := bcu_phase2_nonneg h1 h2
      have hnorm := bcu_sphPhase_norm_eq_one _ v hvne hcos hsin hv0
      rw [h] at hnorm
      simp at hnorm
    · rw [shiftPhase, bcu_clampBall_eq_zero] at h
      have h' : v = -(((1 - t) * 4) • e) := eq_neg_of_add_eq_zero_left h
      rw [neg_smul]
      exact h'
  · intro e v V t he hv0 hvne hV0 hVn h
    rw [profile] at h
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
      exact eq_sub_of_add_eq (bcu_shiftPhase_eq_of_norm_lt _ _ _ _ (by linarith) h)

end Work.ThomBordism
