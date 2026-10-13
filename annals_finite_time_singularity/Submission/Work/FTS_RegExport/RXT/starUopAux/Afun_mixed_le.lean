import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.starUopAux

noncomputable section

open Set Filter
open scoped Real Topology

/-! ## The `z`-only factor `A(z) = z/(1+z)` and its first two `D_z`-derivatives

`D_z = z·∂_z`, so `D_z A = z·A' = B` and `D_z B = z·B' = C` with

  `A(z) = z/(1+z)`,  `B(z) = z/(1+z)²`,  `C(z) = z·(1-z)/(1+z)³`,

and all three have absolute value `≤ min z 1` for `z > 0`. -/

/-- `A(z) = z/(1+z)`. -/
private def zA (z : ℝ) : ℝ := z / (1 + z)

/-- `B(z) = z/(1+z)² = D_z A`. -/
private def zB (z : ℝ) : ℝ := z / (1 + z) ^ 2

/-- `C(z) = z·(1-z)/(1+z)³ = D_z B`. -/
private def zC (z : ℝ) : ℝ := z * ((1 - z) / (1 + z) ^ 3)

/-- The two-variable function used throughout is the `θ`-independent `A`. -/
private lemma zA_fun_eq : (fun z θ : ℝ => zA z) = (fun z θ : ℝ => z / (1 + z)) := rfl

private lemma hasDerivAt_zA {z : ℝ} (hz : 0 < z) : HasDerivAt zA (1 / (1 + z) ^ 2) z := by
  have hne : (1 + z) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun y : ℝ => (1 : ℝ) + y) (1 : ℝ) z :=
    (hasDerivAt_const_add_iff (1 : ℝ)).mpr (hasDerivAt_id z)
  have h := h1.div h2 hne
  rw [show ((fun y : ℝ => y) / (fun y : ℝ => (1 : ℝ) + y)) = zA from rfl] at h
  rw [show (1 : ℝ) * (1 + z) - z * 1 = 1 by ring] at h
  exact h

private lemma hasDerivAt_zB {z : ℝ} (hz : 0 < z) :
    HasDerivAt zB ((1 - z) / (1 + z) ^ 3) z := by
  have hne : ((1 : ℝ) + z) ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun y : ℝ => ((1 : ℝ) + y) ^ 2) (2 * (1 + z) ^ (2 - 1) * 1) z :=
    ((hasDerivAt_const_add_iff (1 : ℝ)).mpr (hasDerivAt_id z)).pow 2
  have h := h1.div h2 hne
  rw [show ((fun y : ℝ => y) / (fun y : ℝ => ((1 : ℝ) + y) ^ 2)) = zB from rfl] at h
  rw [show (2 : ℕ) - 1 = 1 by norm_num, pow_one, mul_one] at h
  rw [show (1 * (1 + z) ^ 2 - z * (2 * (1 + z))) / ((1 + z) ^ 2) ^ 2
      = (1 - z) / (1 + z) ^ 3 by
    field_simp
    ring] at h
  exact h

private lemma zA_abs_le {z : ℝ} (hz : 0 < z) : |zA z| ≤ min z 1 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  rw [zA, abs_of_nonneg (div_nonneg hz.le (by linarith))]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h1]; nlinarith
  · rw [div_le_one h1]; linarith

private lemma zB_abs_le {z : ℝ} (hz : 0 < z) : |zB z| ≤ min z 1 := by
  have h2 : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  rw [zB, abs_div, abs_of_pos hz, abs_of_pos h2]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h2]; nlinarith [sq_nonneg z, hz]
  · rw [div_le_one h2]; nlinarith [sq_nonneg z]

private lemma zC_abs_le {z : ℝ} (hz : 0 < z) : |zC z| ≤ min z 1 := by
  have h2 : (0 : ℝ) < (1 + z) ^ 3 := by positivity
  have hzabs : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
  have hcube : (1 + z) ≤ (1 + z) ^ 3 := by nlinarith [sq_nonneg (1 + z)]
  have hsq : z ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
  have hval : |zC z| = z * |1 - z| / (1 + z) ^ 3 := by
    rw [zC, abs_mul, abs_of_nonneg hz.le, abs_div, abs_of_pos h2]
    ring
  rw [hval]
  refine le_min ?_ ?_
  · rw [div_le_iff₀ h2]; nlinarith [mul_le_mul_of_nonneg_left hzabs hz.le]
  · rw [div_le_one h2]; nlinarith [mul_le_mul_of_nonneg_left hzabs hz.le]

/-- `z·A'(z) = B(z)` (the `z`-multiple of the derivative). -/
private lemma zB_eq (z : ℝ) : z * (1 / (1 + z) ^ 2) = zB z := by
  rw [zB, one_div, div_eq_mul_inv]

/-! ## The mixed `D`-derivatives

`A` does not depend on `θ`, so `D_θ^a A = 0` for `a ≥ 1` and hence `D_z^b D_θ^a A = 0` for all
`b`.  For `a = 0` and `b ≤ 2` the values are `A`, `B`, `C`. -/

private lemma pth_zA_fun : Work.Spaces.pth (fun z θ : ℝ => zA z) = 0 := by
  funext z θ
  simp [Work.Spaces.pth]

private lemma Dth_zero_fun : Work.Spaces.Dth (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ
  simp [Work.Spaces.Dth, Work.Spaces.pth]

private lemma Dth_zA_fun : Work.Spaces.Dth (fun z θ : ℝ => zA z) = 0 := by
  funext z θ
  simp [Work.Spaces.Dth, pth_zA_fun]

private lemma DthIter_zA_succ (a : ℕ) :
    Work.Spaces.DthIter (a + 1) (fun z θ : ℝ => zA z) = 0 := by
  induction a with
  | zero =>
      show Work.Spaces.DthIter 1 (fun z θ : ℝ => zA z) = 0
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
      exact Dth_zA_fun
  | succ a ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      exact Dth_zero_fun

private lemma Dz_zero_fun : Work.Spaces.Dz (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ
  simp [Work.Spaces.Dz, Work.Spaces.pz]

private lemma DzIter_zero_fun : ∀ b : ℕ, Work.Spaces.DzIter b (0 : ℝ → ℝ → ℝ) = 0
  | 0 => rfl
  | b + 1 => by
      rw [Work.Spaces.DzIter_succ, DzIter_zero_fun b]
      exact Dz_zero_fun

private lemma mixed_zA_succ (b a : ℕ) :
    Work.Spaces.mixed b (a + 1) (fun z θ : ℝ => zA z) = 0 := by
  rw [Work.Spaces.mixed, DthIter_zA_succ a, DzIter_zero_fun b]

/-- For `a = 0` and `b ≤ 2`, the mixed derivative of `A` is `A`, `B` or `C`. -/
private lemma mixed_zA_b0_le (b : ℕ) (hb : b ≤ 2) (z θ : ℝ) (hz : 0 < z) :
    |Work.Spaces.mixed b 0 (fun z θ : ℝ => zA z) z θ| ≤ min z 1 := by
  rw [Work.Spaces.mixed_zero_right]
  interval_cases b
  · simpa using zA_abs_le hz
  · show |Work.Spaces.Dz (fun z θ : ℝ => zA z) z θ| ≤ min z 1
    rw [Work.Spaces.Dz]
    have hpz : Work.Spaces.pz (fun z θ : ℝ => zA z) z θ = 1 / (1 + z) ^ 2 :=
      (hasDerivAt_zA hz).deriv
    rw [hpz, zB_eq z]
    exact zB_abs_le hz
  · show |Work.Spaces.Dz (Work.Spaces.Dz (fun z θ : ℝ => zA z)) z θ| ≤ min z 1
    rw [Work.Spaces.Dz]
    have hdz : Work.Spaces.pz (Work.Spaces.Dz (fun z θ : ℝ => zA z)) z θ
        = (1 - z) / (1 + z) ^ 3 := by
      rw [Work.Spaces.pz]
      have h1 : (fun z' : ℝ => Work.Spaces.Dz (fun z θ : ℝ => zA z) z' θ)
          = (fun z' : ℝ => z' * deriv zA z') := by
        funext z'
        rw [Work.Spaces.Dz, Work.Spaces.pz]
      rw [h1]
      have hev : (fun z' : ℝ => z' * deriv zA z') =ᶠ[𝓝 z] zB := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        rw [(hasDerivAt_zA hz').deriv, zB_eq z']
      rw [Filter.EventuallyEq.deriv_eq hev, (hasDerivAt_zB hz).deriv]
    rw [hdz]
    exact zC_abs_le hz

/-- The mixed `D`-derivatives of the `z`-only factor `A(z) = z/(1+z)` of order `≤ 2` are bounded
by `min z 1` on `z > 0`: `A`, `D_z A = z/(1+z)^2`, `D_z^2 A = z(1-z)/(1+z)^3` all have absolute
value `≤ min z 1`, and `D_z^b D_θ^a A = 0` for `a ≥ 1` (no `θ`-dependence).  Prove it locally
from `Work.Spaces.Dz`, `Work.Spaces.Dth`, `Work.Spaces.mixed`; do not import
`Submission.Work.FTS_RegExport.RXT.StarVopDefs` (a sibling agent owns that file). -/
theorem Afun_mixed_le (b a : ℕ) (hab : a + b ≤ 2) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (fun z θ : ℝ => z / (1 + z)) z θ| ≤ min z 1 := by
  intro z θ hz _hθ _hπ
  rcases a with _ | a
  · have hb : b ≤ 2 := by omega
    have h := mixed_zA_b0_le b hb z θ hz
    rwa [zA_fun_eq] at h
  · have h : |Work.Spaces.mixed b (a + 1) (fun z θ : ℝ => zA z) z θ| ≤ min z 1 := by
      rw [mixed_zA_succ b a]
      simpa using le_min hz.le zero_le_one
    rwa [zA_fun_eq] at h

end

end Work.FTS_RegExport.RXT.starUopAux
