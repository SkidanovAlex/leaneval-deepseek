import Mathlib
import Submission.Work.Diff.C.cutoff_psi_defs
import Submission.Work.Diff.C.cutW_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The values of the candidate cutoff `cutPsi`

We prove that the candidate cutoff
`cutPsi c s = (-1 + c) + ∫ x in (-1+c)..s, cutRho c x`,
with `cutRho c x = cutW ((x + 1 - c)/c)`, is constant `-1 + c` below `-1 + c` and is the
identity above `-1 + 2c` (assuming the normalisation `∫ u in 0..1, cutW u = 1`).

The point is the affine substitution `x = -1 + c + c·u`, i.e.
`(x + 1 - c)/c = (1/c) * x + (1 - c)/c`, which turns the integral of `cutRho` into `c` times the
integral of `cutW` over `0..(s + 1 - c)/c`.  On `[1, ∞)` the profile `cutW` is constantly `1`, and
on `(-∞, 0]` it vanishes, which gives the two statements.
-/

namespace Work.Diff.C

open MeasureTheory

/-- The substitution `x = -1 + c + c·u` in the integral of `cutRho`: it equals `c` times the
integral of `cutW` over `0..(s + 1 - c)/c`. -/
lemma cutRho_intervalIntegral {c : ℝ} (hc : 0 < c) (s : ℝ) :
    (∫ x in (-1 + c)..s, cutRho c x) = c * ∫ u in (0 : ℝ)..((s + 1 - c) / c), cutW u := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hcongr : (∫ x in (-1 + c)..s, cutRho c x)
      = ∫ x in (-1 + c)..s, cutW (c⁻¹ * x + (1 - c) / c) := by
    apply intervalIntegral.integral_congr
    intro x _
    unfold cutRho
    congr 1
    field_simp
    ring
  rw [hcongr,
    intervalIntegral.integral_comp_mul_add cutW (inv_ne_zero hcne) ((1 - c) / c)]
  have h0 : c⁻¹ * (-1 + c) + (1 - c) / c = 0 := by field_simp; ring
  have h1 : c⁻¹ * s + (1 - c) / c = (s + 1 - c) / c := by field_simp; ring
  rw [inv_inv, smul_eq_mul, h0, h1]

theorem cutPsi_values {c : ℝ} (hc : 0 < c) (hI : (∫ u in (0 : ℝ)..1, cutW u) = 1) :
    (∀ s : ℝ, -1 + 2 * c ≤ s → cutPsi c s = s) ∧
      (∀ s : ℝ, s ≤ -1 + c → cutPsi c s = -1 + c) := by
  have hcont : Continuous cutW := by unfold cutW; fun_prop
  constructor
  · -- Above `-1 + 2c` the profile `cutW` is constantly `1`, so `cutPsi` grows with slope `1`
    -- starting from the value `c` at `s = -1 + 2c`.
    intro s hs
    have ht : 1 ≤ (s + 1 - c) / c := by rw [le_div_iff₀ hc]; linarith
    have hadj : (∫ u in (0 : ℝ)..1, cutW u) + (∫ u in (1 : ℝ)..(s + 1 - c) / c, cutW u)
        = ∫ u in (0 : ℝ)..(s + 1 - c) / c, cutW u :=
      intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 1)
        (hcont.intervalIntegrable 1 ((s + 1 - c) / c))
    have hone : (∫ u in (1 : ℝ)..(s + 1 - c) / c, cutW u) = (s + 1 - c) / c - 1 := by
      have hc1 : (∫ u in (1 : ℝ)..(s + 1 - c) / c, cutW u)
          = ∫ u in (1 : ℝ)..(s + 1 - c) / c, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact cutW_eq_one_of_one_le (by linarith)
        · exact cutW_eq_one_of_one_le (by linarith)
      rw [hc1, intervalIntegral.integral_const]
      simp
    unfold cutPsi
    rw [cutRho_intervalIntegral hc s, ← hadj, hI, hone]
    field_simp
    ring
  · -- Below `-1 + c` the profile `cutRho` vanishes, so `cutPsi` is constant.
    intro s hs
    have ht : (s + 1 - c) / c ≤ 0 := by rw [div_le_iff₀ hc]; linarith
    have hzero : (∫ u in (0 : ℝ)..(s + 1 - c) / c, cutW u) = 0 := by
      have hc0 : (∫ u in (0 : ℝ)..(s + 1 - c) / c, cutW u)
          = ∫ u in (0 : ℝ)..(s + 1 - c) / c, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact cutW_eq_zero_of_nonpos (by linarith)
        · exact cutW_eq_zero_of_nonpos (by linarith)
      rw [hc0, intervalIntegral.integral_zero]
    unfold cutPsi
    rw [cutRho_intervalIntegral hc s, hzero]
    ring

end Work.Diff.C
