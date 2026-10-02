import Mathlib
import Submission.Work.GATE2.Defs
import Submission.Work.GATE2.phase_gap_integrality

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PathTransport.general

set_option autoImplicit false

noncomputable section

/-! ## Localised one-step helpers, general root angle

The two private helpers of `Submission/Work/GATE2/PathTransport/phase_of_chainWindow_local.lean`
(`bAngle_step_F_local`, `deviation_step_local`) are re-proved here, the second one with the
root-angle hypothesis weakened from `1023 * α = 371` to `∃ s : ℤ, 1023 * α = (s : ℝ)`. -/

/-- **One-step congruence of the Böttcher arguments**, functional equation at a single point:
if `φ (F c z) = (φ z)^1024` then `bAngle φ (F c z) = 1024 · bAngle φ z + k` for some integer `k`. -/
private theorem bAngle_step_F_local {c z : ℂ} {φ : ℂ → ℂ}
    (hz : φ (Work.EL.F c z) = (φ z) ^ (1024 : ℕ)) :
    ∃ k : ℤ, Work.GATE.bAngle φ (Work.EL.F c z) = 1024 * Work.GATE.bAngle φ z
      + (k : ℝ) := by
  have hArg : (Complex.arg (φ (Work.EL.F c z)) : Real.Angle)
      = (1024 : ℕ) • (Complex.arg (φ z) : Real.Angle) := by
    rw [hz]; exact Complex.arg_pow_coe_angle _ _
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hArg
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hk
  refine ⟨k, ?_⟩
  rw [Work.GATE.bAngle, Work.GATE.bAngle]
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt Real.two_pi_pos
  field_simp
  linarith [hk]

/-- **One-step phase gap** at a single point: the functional equation at `z` and the integrality
`(1024 - 1) α ∈ ℤ` (here `∃ s : ℤ, 1023 α = s`) give
`deviation φ α (F c z) = 1024 · deviation φ α z + j`, `j ∈ ℤ`. -/
private theorem deviation_step_local {c z : ℂ} {α : ℝ} {φ : ℂ → ℂ}
    (hα : ∃ s : ℤ, 1023 * α = (s : ℝ)) (hz : φ (Work.EL.F c z) = (φ z) ^ (1024 : ℕ)) :
    ∃ j : ℤ, Work.GATE.deviation φ α (Work.EL.F c z)
      = 1024 * Work.GATE.deviation φ α z + (j : ℝ) := by
  obtain ⟨mm, hb⟩ := bAngle_step_F_local (c := c) (z := z) (φ := φ) hz
  obtain ⟨s, hs⟩ := hα
  have hαint : ∃ t : ℤ, ((1024 : ℝ) - 1) * α = (t : ℝ) := by
    refine ⟨s, ?_⟩
    have h1 : ((1024 : ℝ) - 1) * α = 1023 * α := by norm_num
    rw [h1, hs]
  obtain ⟨j, hj⟩ := PhaseGap.exists_int_repPhase_comb (α := α)
    (bw := Work.GATE.bAngle φ (Work.EL.F c z))
    (bz := Work.GATE.bAngle φ z) (n := 1024) ⟨mm, hb⟩ hαint
  refine ⟨j, ?_⟩
  rw [PhaseGap.deviation_eq_repPhase φ α (Work.EL.F c z),
    PhaseGap.deviation_eq_repPhase φ α z]
  simpa using hj

/-- **The phase identity along a chain window, with the functional equation only at the chain
points.**  This is `Work.GATE2.PathTransport.phase_of_chainWindow_local` with its root-angle
hypothesis `1023 * α = 371` replaced by `∃ s : ℤ, 1023 * α = (s : ℝ)`; everything else is
verbatim. -/
theorem phase_of_chainWindow_local {c e : ℂ} {α : ℝ} {φ : ℂ → ℂ} (m : ℕ)
    (hα : ∃ s : ℤ, 1023 * α = (s : ℝ))
    (hfun : ∀ k < m, φ (Work.EL.F c ((Work.EL.F c)^[k] e)) =
      (φ ((Work.EL.F c)^[k] e)) ^ (1024 : ℕ))
    (h : ∀ k < m, -(1 / 2048 : ℝ) < Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ∧
      Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ≤ (1 / 2048 : ℝ)) :
    Work.GATE.deviation φ α ((Work.EL.F c)^[m] e) =
      (1024 : ℝ) ^ m * Work.GATE.deviation φ α e := by
  suffices key : ∀ m : ℕ,
      (∀ k < m, φ (Work.EL.F c ((Work.EL.F c)^[k] e)) =
        (φ ((Work.EL.F c)^[k] e)) ^ (1024 : ℕ)) →
      (∀ k < m, -(1 / 2048 : ℝ) < Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ∧
        Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ≤ (1 / 2048 : ℝ)) →
      Work.GATE.deviation φ α ((Work.EL.F c)^[m] e) =
        (1024 : ℝ) ^ m * Work.GATE.deviation φ α e by
    exact key m hfun h
  intro m
  induction m with
  | zero => intro _ _; simp
  | succ n ih =>
    intro hfunnn hwnn
    have hfunn : ∀ k < n, φ (Work.EL.F c ((Work.EL.F c)^[k] e)) =
        (φ ((Work.EL.F c)^[k] e)) ^ (1024 : ℕ) :=
      fun k hk => hfunnn k (Nat.lt_succ_of_lt hk)
    have hwn : ∀ k < n, -(1 / 2048 : ℝ) < Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ∧
        Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ≤ (1 / 2048 : ℝ) :=
      fun k hk => hwnn k (Nat.lt_succ_of_lt hk)
    have hrec0 := ih hfunn hwn
    -- the one-step gap at the last chain point, in terms of `(F c)^[Nat.succ n] e`
    obtain ⟨j, hj⟩ := deviation_step_local (c := c) (z := (Work.EL.F c)^[n] e) (φ := φ) hα
      (hfunnn n (Nat.lt_succ_self n))
    have hj' : Work.GATE.deviation φ α ((Work.EL.F c)^[Nat.succ n] e)
        = 1024 * Work.GATE.deviation φ α ((Work.EL.F c)^[n] e) + (j : ℝ) := by
      simpa only [Function.iterate_succ_apply'] using hj
    -- the two window bounds that kill the integer
    have hwin := hwnn n (Nat.lt_succ_self n)
    have hmem := Work.GATE.deviation_mem φ α ((Work.EL.F c)^[Nat.succ n] e)
    have hjt : j = 0 := by
      have hlo : (-1 : ℝ) < (j : ℝ) := by
        have h1 := hmem.1; have h2 := hwin.2; rw [hj'] at h1; linarith
      have hhi : (j : ℝ) < 1 := by
        have h1 := hmem.2; have h2 := hwin.1; rw [hj'] at h1; linarith
      have hjlo : (-1 : ℤ) < j := by exact_mod_cast hlo
      have hjhi : j < 1 := by exact_mod_cast hhi
      omega
    -- the exact one-step recursion
    have hrec : Work.GATE.deviation φ α ((Work.EL.F c)^[Nat.succ n] e)
        = 1024 * Work.GATE.deviation φ α ((Work.EL.F c)^[n] e) := by
      rw [hjt] at hj'
      simpa using hj'
    rw [hrec, hrec0, pow_succ]
    ring

end

end Work.GATE2.PathTransport.general
