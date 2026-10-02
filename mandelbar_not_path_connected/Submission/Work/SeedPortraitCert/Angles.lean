/-
# SeedPortraitCert — the angle vocabulary of the two frontier orbits

Area `Submission/Work/SeedPortraitCert/` of `mandelbar_not_path_connected`.  This file fixes the
angles of the certificate: the two `T`-cycles of the period-`5` angles

  `12/33 → 9/33 → 15/33 → 3/33 → 27/33 → 12/33`   and
  `13/33 → 7/33 → 19/33 → 28/33 → 10/33 → 13/33`

(`T θ = Int.fract (-2θ)` is the action of `T_c` on external angles).  They are recorded as the
`5`-periodic sequences `angA`, `angB`; the emitted certificate data (`Data.lean`) has the ten
classes `0 … 4` (the `angA` cycle) and `5 … 9` (the `angB` cycle) side by side, and the two
chains (`Chain.lean`) run independently, each with its own `5`-periodic family of sets.

In the `1023`-model the two cycles are `372 → 279 → 465 → 93 → 837 → 372` and
`403 → 217 → 589 → 868 → 310 → 403`, i.e. `12/33 = 372/1023` and `13/33 = 403/1023`; these are
exactly the two `g`-fixed angles (`(T^[5]) θ = θ`) of the wake arc `(α₁, α₂)` of the seed
(`Work.SeedSimple2`'s `survivors`), and the two angles whose non-landing at `z₁` is what `GF`
consumes.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.SeedPortraitCert.Num

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedPortraitCert

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The two `T`-cycles -/

/-- The `j`-th angle of the orbit of `12/33`: `T^[j] (12/33)`. -/
def angA (j : ℕ) : ℝ := (Work.EL.T^[j]) (12 / 33)

/-- The `j`-th angle of the orbit of `13/33`: `T^[j] (13/33)`. -/
def angB (j : ℕ) : ℝ := (Work.EL.T^[j]) (13 / 33)

@[simp] theorem angA_zero : angA 0 = 12 / 33 := rfl

@[simp] theorem angB_zero : angB 0 = 13 / 33 := rfl

/-- `angA` is a `T`-trajectory: the successor identity needed by the chain induction. -/
theorem angA_succ (j : ℕ) : angA (j + 1) = Work.EL.T (angA j) := by
  simp [angA, Function.iterate_succ_apply']

/-- `angB` is a `T`-trajectory. -/
theorem angB_succ (j : ℕ) : angB (j + 1) = Work.EL.T (angB j) := by
  simp [angB, Function.iterate_succ_apply']

/-! ## The angle arithmetic of `T θ = Int.fract (-2 θ)` on the `/33` grid -/

theorem T_12 : Work.EL.T (12 / 33) = 9 / 33 := by
  rw [Work.EL.T, show -2 * (12 / 33 : ℝ) = 9 / 33 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

theorem T_9 : Work.EL.T (9 / 33) = 15 / 33 := by
  rw [Work.EL.T, show -2 * (9 / 33 : ℝ) = 15 / 33 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

theorem T_15 : Work.EL.T (15 / 33) = 3 / 33 := by
  rw [Work.EL.T, show -2 * (15 / 33 : ℝ) = 3 / 33 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

theorem T_3 : Work.EL.T (3 / 33) = 27 / 33 := by
  rw [Work.EL.T, show -2 * (3 / 33 : ℝ) = 27 / 33 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

theorem T_27 : Work.EL.T (27 / 33) = 12 / 33 := by
  rw [Work.EL.T, show -2 * (27 / 33 : ℝ) = 12 / 33 + ((-2 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

theorem T_13 : Work.EL.T (13 / 33) = 7 / 33 := by
  rw [Work.EL.T, show -2 * (13 / 33 : ℝ) = 7 / 33 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

theorem T_7 : Work.EL.T (7 / 33) = 19 / 33 := by
  rw [Work.EL.T, show -2 * (7 / 33 : ℝ) = 19 / 33 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

theorem T_19 : Work.EL.T (19 / 33) = 28 / 33 := by
  rw [Work.EL.T, show -2 * (19 / 33 : ℝ) = 28 / 33 + ((-2 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

theorem T_28 : Work.EL.T (28 / 33) = 10 / 33 := by
  rw [Work.EL.T, show -2 * (28 / 33 : ℝ) = 10 / 33 + ((-2 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

theorem T_10 : Work.EL.T (10 / 33) = 13 / 33 := by
  rw [Work.EL.T, show -2 * (10 / 33 : ℝ) = 13 / 33 + ((-1 : ℤ) : ℝ) by norm_num,
    Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩

/-! ## The values of the two cycles -/

theorem angA_one : angA 1 = 9 / 33 := by
  rw [show angA 1 = Work.EL.T (angA 0) from angA_succ 0, angA_zero, T_12]

theorem angA_two : angA 2 = 15 / 33 := by
  rw [show angA 2 = Work.EL.T (angA 1) from angA_succ 1, angA_one, T_9]

theorem angA_three : angA 3 = 3 / 33 := by
  rw [show angA 3 = Work.EL.T (angA 2) from angA_succ 2, angA_two, T_15]

theorem angA_four : angA 4 = 27 / 33 := by
  rw [show angA 4 = Work.EL.T (angA 3) from angA_succ 3, angA_three, T_3]

theorem angA_five : angA 5 = 12 / 33 := by
  rw [show angA 5 = Work.EL.T (angA 4) from angA_succ 4, angA_four, T_27]

theorem angB_one : angB 1 = 7 / 33 := by
  rw [show angB 1 = Work.EL.T (angB 0) from angB_succ 0, angB_zero, T_13]

theorem angB_two : angB 2 = 19 / 33 := by
  rw [show angB 2 = Work.EL.T (angB 1) from angB_succ 1, angB_one, T_7]

theorem angB_three : angB 3 = 28 / 33 := by
  rw [show angB 3 = Work.EL.T (angB 2) from angB_succ 2, angB_two, T_19]

theorem angB_four : angB 4 = 10 / 33 := by
  rw [show angB 4 = Work.EL.T (angB 3) from angB_succ 3, angB_three, T_28]

theorem angB_five : angB 5 = 13 / 33 := by
  rw [show angB 5 = Work.EL.T (angB 4) from angB_succ 4, angB_four, T_10]

/-! ## Periodicity of the two cycles -/

theorem angA_add_five (j : ℕ) : angA (j + 5) = angA j := by
  have h : angA (j + 5) = (Work.EL.T^[j]) ((Work.EL.T^[5]) (12 / 33)) := by
    rw [angA, Function.iterate_add_apply]
  rw [h, show (Work.EL.T^[5]) (12 / 33) = 12 / 33 from angA_five]; rfl

theorem angB_add_five (j : ℕ) : angB (j + 5) = angB j := by
  have h : angB (j + 5) = (Work.EL.T^[j]) ((Work.EL.T^[5]) (13 / 33)) := by
    rw [angB, Function.iterate_add_apply]
  rw [h, show (Work.EL.T^[5]) (13 / 33) = 13 / 33 from angB_five]; rfl

theorem angA_mod (j : ℕ) : angA j = angA (j % 5) := by
  have hmain : ∀ q : ℕ, angA (j % 5 + 5 * q) = angA (j % 5) := by
    intro q
    induction q with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, ← add_assoc, angA_add_five]; exact ih
  conv_lhs => rw [← Nat.mod_add_div j 5]
  exact hmain (j / 5)

theorem angB_mod (j : ℕ) : angB j = angB (j % 5) := by
  have hmain : ∀ q : ℕ, angB (j % 5 + 5 * q) = angB (j % 5) := by
    intro q
    induction q with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, ← add_assoc, angB_add_five]; exact ih
  conv_lhs => rw [← Nat.mod_add_div j 5]
  exact hmain (j / 5)

/-- The `angA`-cycle, in the order of the certificate's angle classes `0 … 4`. -/
theorem angA_cycle : angA 0 = 12 / 33 ∧ angA 1 = 9 / 33 ∧ angA 2 = 15 / 33 ∧
    angA 3 = 3 / 33 ∧ angA 4 = 27 / 33 :=
  ⟨angA_zero, angA_one, angA_two, angA_three, angA_four⟩

/-- The `angB`-cycle, in the order of the certificate's angle classes `5 … 9`. -/
theorem angB_cycle : angB 0 = 13 / 33 ∧ angB 1 = 7 / 33 ∧ angB 2 = 19 / 33 ∧
    angB 3 = 28 / 33 ∧ angB 4 = 10 / 33 :=
  ⟨angB_zero, angB_one, angB_two, angB_three, angB_four⟩

/-! ## The two distinguished angles in the `1023`-model -/

/-- The first certificate angle `12/33` is `372/1023`. -/
theorem angA_zero_1023 : angA 0 = 372 / 1023 := by rw [angA_zero]; norm_num

/-- The second certificate angle `13/33` is `403/1023`. -/
theorem angB_zero_1023 : angB 0 = 403 / 1023 := by rw [angB_zero]; norm_num

/-! ## The ten angle classes of the certificate -/

/-- The angle of the certificate class `j`: classes `0 … 4` are the `12/33`-cycle, classes
`5 … 9` the `13/33`-cycle (the order of the emitted direction data `dirBaseP`). -/
def angP (j : ℕ) : ℝ := if j < 5 then angA j else angB (j - 5)

theorem angP_eq_angA {j : ℕ} (hj : j < 5) : angP j = angA j := by simp [angP, hj]

theorem angP_eq_angB {j : ℕ} (hj : 5 ≤ j) : angP j = angB (j - 5) := by
  have h : ¬ j < 5 := by omega
  simp [angP, h]

theorem angP_zero : angP 0 = 12 / 33 := by rw [angP_eq_angA (by norm_num), angA_zero]

theorem angP_one : angP 1 = 9 / 33 := by rw [angP_eq_angA (by norm_num), angA_one]

theorem angP_two : angP 2 = 15 / 33 := by rw [angP_eq_angA (by norm_num), angA_two]

theorem angP_three : angP 3 = 3 / 33 := by rw [angP_eq_angA (by norm_num), angA_three]

theorem angP_four : angP 4 = 27 / 33 := by rw [angP_eq_angA (by norm_num), angA_four]

theorem angP_five : angP 5 = 13 / 33 := by
  rw [angP_eq_angB (by norm_num), show 5 - 5 = 0 from rfl, angB_zero]

theorem angP_six : angP 6 = 7 / 33 := by
  rw [angP_eq_angB (by norm_num), show 6 - 5 = 1 from rfl, angB_one]

theorem angP_seven : angP 7 = 19 / 33 := by
  rw [angP_eq_angB (by norm_num), show 7 - 5 = 2 from rfl, angB_two]

theorem angP_eight : angP 8 = 28 / 33 := by
  rw [angP_eq_angB (by norm_num), show 8 - 5 = 3 from rfl, angB_three]

theorem angP_nine : angP 9 = 10 / 33 := by
  rw [angP_eq_angB (by norm_num), show 9 - 5 = 4 from rfl, angB_four]

end Work.SeedPortraitCert
