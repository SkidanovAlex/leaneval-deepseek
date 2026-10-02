import Mathlib
import Submission.Work.GATE2.Defs
import Submission.Work.GATE2.varphiCrit_F_iterate
import Submission.Work.GATE2.phase_gap_integrality

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# GATE2 — the phase identity along a chain window

`Work.GATE2.phase_of_chainWindow` is the *sufficient geometric form* of the phase identity
`deviation φ α ((F_c)^[m] e) = 1024^m · deviation φ α e` of residual 2 (`TRANSPORT` of §2.3), the
form recorded in `Submission/Work/GATE2/NOTES_OPEN.md` §1: if the whole gate transit keeps the
Böttcher deviation of the critical orbit in the window `(−1/2048, 1/2048]`, then the phase identity
holds.

The mathematics is purely arithmetic.  Write `d_k := deviation φ α ((F_c)^[k] e)` and let
`x_k := bAngle φ ((F_c)^[k] e) − α`.  The functional equation `φ (F_c z) = (φ z)^1024` gives
`x_{k+1} ≡ 1024 · x_k  (mod 1)` (the shift `1023 α = 371` being an integer), hence
`d_{k+1} = d_k · 1024 + j_k` with `j_k ∈ ℤ` (`Work.GATE2.PhaseGap.exists_int_repPhase_comb`).
If `d_k ∈ (−1/2048, 1/2048]` then `1024 · d_k ∈ (−1/2, 1/2]`, so with `d_{k+1} ∈ (−1/2, 1/2]`
(`Work.GATE.deviation_mem`) the integer `j_k` lies in `(−1, 1)`: it vanishes.  Thus
`d_{k+1} = 1024 · d_k` at every step of the window, and the identity follows by induction.

The helper lemmas below are the two ingredients: the one-step congruence of the Böttcher arguments
(`bAngle_step_F`, from the functional equation alone) and the resulting one-step phase gap.
-/

namespace Work.GATE2

/-- **One-step congruence of the Böttcher arguments** along the high return map `F c`, from the
functional equation `φ (F c z) = (φ z)^1024`: the Böttcher argument (in revolutions,
`Work.GATE.bAngle`) is multiplied by `1024` up to an integer. -/
private theorem bAngle_step_F {c z : ℂ} {φ : ℂ → ℂ}
    (hfun : ∀ w : ℂ, φ (Work.EL.F c w) = (φ w) ^ (1024 : ℕ)) :
    ∃ k : ℤ, Work.GATE.bAngle φ (Work.EL.F c z) = 1024 * Work.GATE.bAngle φ z
      + (k : ℝ) := by
  have hArg : (Complex.arg (φ (Work.EL.F c z)) : Real.Angle)
      = (1024 : ℕ) • (Complex.arg (φ z) : Real.Angle) := by
    rw [hfun z]; exact Complex.arg_pow_coe_angle _ _
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hArg
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hk
  refine ⟨k, ?_⟩
  rw [Work.GATE.bAngle, Work.GATE.bAngle]
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt Real.two_pi_pos
  field_simp
  linarith [hk]

/-- **One-step phase gap** of the `α`-relative Böttcher deviation along the chain
`(F_c)^[k] e`: the two consecutive deviations differ by `1024` up to an integer, using the
integrality `1023 α = 371` (i.e. `(1024 − 1) α ∈ ℤ`). -/
private theorem deviation_step_F {c e : ℂ} {α : ℝ} {φ : ℂ → ℂ} (hα : 1023 * α = 371)
    (hfun : ∀ w : ℂ, φ (Work.EL.F c w) = (φ w) ^ (1024 : ℕ)) (k : ℕ) :
    ∃ j : ℤ, Work.GATE.deviation φ α ((Work.EL.F c)^[Nat.succ k] e)
      = 1024 * Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) + (j : ℝ) := by
  have hb : ∃ mm : ℤ, Work.GATE.bAngle φ ((Work.EL.F c)^[Nat.succ k] e)
      = (1024 : ℝ) * Work.GATE.bAngle φ ((Work.EL.F c)^[k] e) + (mm : ℝ) := by
    simpa only [Function.iterate_succ_apply']
      using bAngle_step_F (z := (Work.EL.F c)^[k] e) hfun
  have hαint : ∃ t : ℤ, ((1024 : ℝ) - 1) * α = (t : ℝ) := by
    refine ⟨371, ?_⟩
    have h1 : ((1024 : ℝ) - 1) * α = 1023 * α := by norm_num
    rw [h1, hα]; norm_num
  obtain ⟨j, hj⟩ := PhaseGap.exists_int_repPhase_comb (α := α)
    (bw := Work.GATE.bAngle φ ((Work.EL.F c)^[Nat.succ k] e))
    (bz := Work.GATE.bAngle φ ((Work.EL.F c)^[k] e)) (n := 1024) hb hαint
  refine ⟨j, ?_⟩
  rw [PhaseGap.deviation_eq_repPhase φ α ((Work.EL.F c)^[Nat.succ k] e),
    PhaseGap.deviation_eq_repPhase φ α ((Work.EL.F c)^[k] e)]
  simpa using hj

/-- **The phase identity along a chain window.**  If every point of the chain
`e, F_c e, …, (F_c)^[m-1] e` has its `α`-relative Böttcher deviation in the window
`(−1/2048, 1/2048]`, then the deviation is exactly multiplied by `1024` at each step, so the
`m`-th point has deviation `1024^m` times that of `e`. -/
theorem phase_of_chainWindow {c : ℂ} {e : ℂ} {α : ℝ} {φ : ℂ → ℂ} (m : ℕ)
    (hα : 1023 * α = 371)
    (hfun : ∀ z : ℂ, φ (Work.EL.F c z) = (φ z) ^ (1024 : ℕ))
    (h : ∀ k < m, -(1 / 2048 : ℝ) < Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ∧
      Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ≤ (1 / 2048 : ℝ)) :
    Work.GATE.deviation φ α ((Work.EL.F c)^[m] e) =
      (1024 : ℝ) ^ m * Work.GATE.deviation φ α e := by
  have step := fun k => deviation_step_F (c := c) (e := e) hα hfun k
  suffices key : ∀ m : ℕ,
      (∀ k < m, -(1 / 2048 : ℝ) < Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ∧
        Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ≤ (1 / 2048 : ℝ)) →
      Work.GATE.deviation φ α ((Work.EL.F c)^[m] e) =
        (1024 : ℝ) ^ m * Work.GATE.deviation φ α e by
    exact key m h
  intro m
  induction m with
  | zero => intro _; simp
  | succ n ih =>
    intro hw
    -- the window on the shorter chain
    have hwn : ∀ k < n, -(1 / 2048 : ℝ) < Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ∧
        Work.GATE.deviation φ α ((Work.EL.F c)^[k] e) ≤ (1 / 2048 : ℝ) :=
      fun k hk => hw k (Nat.lt_succ_of_lt hk)
    have hrec0 := ih hwn
    -- the one-step gap, and the two window bounds that kill its integer
    obtain ⟨j, hj⟩ := step n
    have hwin := hw n (Nat.lt_succ_self n)
    have hmem := Work.GATE.deviation_mem φ α ((Work.EL.F c)^[Nat.succ n] e)
    have hjt : j = 0 := by
      have hlo : (-1 : ℝ) < (j : ℝ) := by
        have h1 := hmem.1; have h2 := hwin.2; linarith
      have hhi : (j : ℝ) < 1 := by
        have h1 := hmem.2; have h2 := hwin.1; linarith
      have hjlo : (-1 : ℤ) < j := by exact_mod_cast hlo
      have hjhi : j < 1 := by exact_mod_cast hhi
      omega
    -- the exact one-step recursion
    have hrec : Work.GATE.deviation φ α ((Work.EL.F c)^[Nat.succ n] e)
        = 1024 * Work.GATE.deviation φ α ((Work.EL.F c)^[n] e) := by
      rw [hjt] at hj
      simpa using hj
    rw [hrec, hrec0, pow_succ]
    ring

end Work.GATE2
