/-
# TripodCert — the angle arithmetic of the `b₂`-tripod (basic layer)

Area `Submission/Work/TripodCert/` of `mandelbar_not_path_connected`: the certified `b₂`-tripod
data `Work.EL.Tripod d.hN` consumed by `ELAssembly.AssemblyInputs` (the rays `22/63`, `25/63`,
`37/63` landing at one point, `22/63 + 1` being the same ray).

This file fixes the angle vocabulary and the reduction `tripod_of_fixed`: if the ray of angle
`22/63` lands at a point `y` fixed by `Tsq c = (T_c)^2`, then the three tripod rays land at `y`
(the other two by the equivariance `Work.ELNest.landsN_iterate` of the dynamics on rays, using
`T^[2] (22/63) = 25/63` and `T^[4] (22/63) = 37/63`).

Everything here is unconditional glue; the numerical content (TRI: the landing point of `22/63`
is fixed by `Tsq c`) is in the later files of the area.
-/
import Mathlib
import Submission.Work.ELNest.b2_fix_of_lands
import Submission.Work.ELTop.rayPt_add_int

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.TripodCert

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The angles of the tripod -/

/-- The first tripod angle `22/63`. -/
def angA : ℝ := 22 / 63

/-- The second tripod angle `25/63`. -/
def angB : ℝ := 25 / 63

/-- The third tripod angle `37/63`. -/
def angC : ℝ := 37 / 63

@[simp] theorem angA_def : angA = 22 / 63 := rfl
@[simp] theorem angB_def : angB = 25 / 63 := rfl
@[simp] theorem angC_def : angC = 37 / 63 := rfl

/-- The six angles of the `T`-orbit of `22/63`: `θ j = T^[j] (22/63)`, a cycle of period `6`
(`22 → 19 → 25 → 13 → 37 → 52 → 22`). -/
def theta (j : ℕ) : ℝ := (Work.EL.T^[j]) (22 / 63)

@[simp] theorem theta_zero : theta 0 = 22 / 63 := rfl

theorem theta_succ (j : ℕ) : theta (j + 1) = Work.EL.T (theta j) := by
  simp [theta, Function.iterate_succ_apply']

/-! ## The angle cycle `22 → 19 → 25 → 13 → 37 → 52 → 22` -/

/-- `T (22/63) = 19/63`. -/
theorem T_22 : Work.EL.T (22 / 63) = 19 / 63 := by
  rw [Work.EL.T, show -2 * (22 / 63 : ℝ) = 19 / 63 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

/-- `T (19/63) = 25/63`. -/
theorem T_19 : Work.EL.T (19 / 63) = 25 / 63 := by
  rw [Work.EL.T, show -2 * (19 / 63 : ℝ) = 25 / 63 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

/-- `T (25/63) = 13/63`. -/
theorem T_25 : Work.EL.T (25 / 63) = 13 / 63 := by
  rw [Work.EL.T, show -2 * (25 / 63 : ℝ) = 13 / 63 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

/-- `T (13/63) = 37/63`. -/
theorem T_13 : Work.EL.T (13 / 63) = 37 / 63 := by
  rw [Work.EL.T, show -2 * (13 / 63 : ℝ) = 37 / 63 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

/-- `T (37/63) = 52/63`. -/
theorem T_37 : Work.EL.T (37 / 63) = 52 / 63 := by
  rw [Work.EL.T, show -2 * (37 / 63 : ℝ) = 52 / 63 + ((-2 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

/-- `T (52/63) = 22/63`. -/
theorem T_52 : Work.EL.T (52 / 63) = 22 / 63 := by
  rw [Work.EL.T, show -2 * (52 / 63 : ℝ) = 22 / 63 + ((-2 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

theorem theta_one : theta 1 = 19 / 63 := by
  rw [show theta 1 = Work.EL.T (theta 0) from theta_succ 0, theta_zero, T_22]

theorem theta_two : theta 2 = 25 / 63 := by
  rw [show theta 2 = Work.EL.T (theta 1) from theta_succ 1, theta_one, T_19]

theorem theta_three : theta 3 = 13 / 63 := by
  rw [show theta 3 = Work.EL.T (theta 2) from theta_succ 2, theta_two, T_25]

theorem theta_four : theta 4 = 37 / 63 := by
  rw [show theta 4 = Work.EL.T (theta 3) from theta_succ 3, theta_three, T_13]

theorem theta_five : theta 5 = 52 / 63 := by
  rw [show theta 5 = Work.EL.T (theta 4) from theta_succ 4, theta_four, T_37]

theorem theta_six : theta 6 = 22 / 63 := by
  rw [show theta 6 = Work.EL.T (theta 5) from theta_succ 5, theta_five, T_52]

/-- `T^[4] (22/63) = 37/63` (the third tripod ray). -/
theorem T_four : Work.EL.T^[4] (22 / 63) = 37 / 63 := theta_four

/-- `T^[6] (22/63) = 22/63`: the `22/63`-ray is periodic of period `6`. -/
theorem T_six : Work.EL.T^[6] (22 / 63) = 22 / 63 := theta_six

theorem theta_add_six (j : ℕ) : theta (j + 6) = theta j := by
  have h : theta (j + 6) = (Work.EL.T^[j]) ((Work.EL.T^[6]) (22 / 63)) := by
    rw [theta, Function.iterate_add_apply]
  rw [h, T_six]; rfl

theorem theta_mod (j : ℕ) : theta j = theta (j % 6) := by
  have hmain : ∀ q : ℕ, theta (j % 6 + 6 * q) = theta (j % 6) := by
    intro q
    induction q with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, ← add_assoc, theta_add_six]; exact ih
  conv_lhs => rw [← Nat.mod_add_div j 6]
  exact hmain (j / 6)

/-- The angle `22/63` is periodic of period `6` for the angle-doubling map. -/
theorem periodicAngle_angA : Work.Landing.PeriodicAngle (22 / 63) 6 := by
  show Work.Landing.angDouble^[6] (22 / 63) = 22 / 63
  rw [show Work.Landing.angDouble = Work.EL.T from rfl]
  exact T_six

/-- The angle `22/63` is a periodic angle. -/
theorem isPeriodicAngle_angA : Work.Landing.IsPeriodicAngle (22 / 63) :=
  ⟨6, by norm_num, periodicAngle_angA⟩

/-! ## Landing depends on the angle only modulo `1` -/

theorem rayDirection_add_one (θ : ℝ) :
    Work.Landing.rayDirection (θ + 1) = Work.Landing.rayDirection θ := by
  have harg : ((↑(2 * Real.pi * (θ + 1)) : ℂ) * Complex.I)
      = (↑(2 * Real.pi * θ) : ℂ) * Complex.I + (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [Work.Landing.rayDirection, Work.Landing.rayDirection, harg, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

theorem radialRay_add_one (θ : ℝ) : Work.Landing.radialRay (θ + 1) = Work.Landing.radialRay θ := by
  ext w
  simp only [Work.Landing.radialRay, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨r, hr, hw⟩; exact ⟨r, hr, by rw [← rayDirection_add_one θ, hw]⟩
  · rintro ⟨r, hr, hw⟩; exact ⟨r, hr, by rw [rayDirection_add_one θ, hw]⟩

theorem dynRay_add_one (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) :
    Work.Landing.dynRay c φ (θ + 1) = Work.Landing.dynRay c φ θ := by
  ext z
  simp only [Work.Landing.dynRay, Set.mem_ofPred_eq]
  rw [radialRay_add_one θ]

theorem rayAccum_add_one (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) :
    Work.Landing.rayAccum c φ (θ + 1) = Work.Landing.rayAccum c φ θ := by
  have htrunc : ∀ ρ : ℝ,
      {z : ℂ | z ∈ Work.Landing.dynRay c φ (θ + 1) ∧ ‖φ z‖ ≤ ρ}
        = {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ} := by
    intro ρ
    rw [dynRay_add_one c φ θ]
  ext z
  simp only [Work.Landing.rayAccum, Set.mem_ofPred_eq]
  exact forall_congr' (fun ρ => imp_congr_right (fun _ => by rw [htrunc ρ]))

/-- **`landsAt` depends on the angle only modulo `1`.** -/
theorem landsAt_add_one_iff {c : ℂ} {θ : ℝ} {z : ℂ} :
    Work.Landing.landsAt c (θ + 1) z ↔ Work.Landing.landsAt c θ z := by
  unfold Work.Landing.landsAt Work.Landing.RayLands
  constructor
  · rintro ⟨φ, hφ, h⟩; exact ⟨φ, hφ, (rayAccum_add_one c φ θ).symm.trans h⟩
  · rintro ⟨φ, hφ, h⟩; exact ⟨φ, hφ, (rayAccum_add_one c φ θ).trans h⟩

/-! ## `LandsN` depends on the angle only modulo `1` -/

theorem landsN_add_one {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) : Work.EL.LandsN hN (θ + 1) y := by
  show Tendsto (fun t : ℝ => Work.EL.rayPt hN (θ + 1) t) (nhdsWithin 1 (Set.Ioi 1)) (nhds y)
  have hfun : (fun t : ℝ => Work.EL.rayPt hN (θ + 1) t)
      = fun t : ℝ => Work.EL.rayPt hN θ t := by
    funext t
    simpa using Work.ELTop.rayPt_add_int hN θ t (1 : ℤ)
  rw [hfun]
  exact h

/-! ## `Tsq` and its iterate -/

theorem Tsq_eq_iterate_two (c : ℂ) : Work.Landing.Tsq c = (Tantibar c)^[2] :=
  Work.ELNest.Tsq_eq_comp c

/-- `(Tsq c)^[3] = (T_c)^[6] = (T_c)^[2·3]`. -/
theorem Tsq_iterate_three (c : ℂ) : (Work.Landing.Tsq c)^[3] = (Tantibar c)^[6] := by
  rw [Tsq_eq_iterate_two, ← Function.iterate_mul]

/-! ## The reduction `tripod_of_fixed` -/

/-- **(T1) The reduction of the tripod to TRI.**  If the ray of angle `22/63` lands at a point
`y` fixed by `Tsq c = (T_c)^2`, then the three tripod rays land at `y` (and so does the ray of
angle `22/63 + 1`, which is the same ray). -/
noncomputable def tripod_of_fixed {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hB : Work.ParamRays.IsDynBottcher c φ) {y : ℂ} (h22 : Work.EL.LandsN hN (22 / 63) y)
    (hfix : Work.Landing.Tsq c y = y) : Work.EL.Tripod hN where
  y := y
  lands₁ := h22
  lands₂ := by
    have h := Work.ELNest.landsN_iterate hN hB 2 h22
    rw [Work.ELNest.T_sq_tripod] at h
    have hy : (Tantibar c)^[2] y = y := by
      rw [← Work.ELNest.Tsq_eq_comp c]; exact hfix
    rwa [hy] at h
  lands₃ := by
    have h := Work.ELNest.landsN_iterate hN hB 4 h22
    rw [T_four] at h
    have hy : (Tantibar c)^[4] y = y := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, Function.iterate_mul, ← Work.ELNest.Tsq_eq_comp c,
        Function.iterate_fixed hfix 2]
    rwa [hy] at h
  lands₁' := by
    exact landsN_add_one hN h22

end Work.TripodCert
