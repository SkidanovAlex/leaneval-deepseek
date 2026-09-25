import Mathlib
import Submission.Work.BourgainPlan.Oscillation.defs
import Submission.Commons.Analysis.Fourier.circle_multiplier_identity
import Submission.Commons.Analysis.Fourier.multiplier_plancherel_circle
import Submission.Commons.Analysis.HardyLittlewood.discrete_maximal_lp

/-!
# Definitions for the lacunary truncated maximal `ℓ²` estimate

We build the objects used to prove
`Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2`:

* `cc ρ i = ρ ^ (-(i:ℤ))` : the lacunary scales;
* `lam ρ i = exp (-2π ρ^{-i})` : the Poisson parameter at scale `i`;
* `kap ρ i z = (1-λ_i)/(1+λ_i) · λ_i^{|z|}` : the Poisson kernel on `ℤ`;
* `mmClosed ρ i θ` : the corresponding circle multiplier (Poisson kernel in closed form);
* `piCut` : the frequency cut `1_{[0,1/2]}`;
* `phi`, `bb` : the smooth part and the boundary layer of the truncated multiplier
  `1_{[0,ρ^{-i}]} = phi + bb`;
* `trigP` : the trigonometric polynomial of a finitely supported sequence;
* `hlMaxZ` : the two-sided Hardy--Littlewood maximal function on `ℤ`.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Oscillation
namespace Lacunary

noncomputable section

/-- The lacunary scale `ρ^{-i}` (as in the statement, via `zpow`). -/
def cc (ρ : ℝ) (i : ℕ) : ℝ := ρ ^ (-(i : ℤ))

/-- The Poisson parameter `λ_i = exp(-2π ρ^{-i})`. -/
def lam (ρ : ℝ) (i : ℕ) : ℝ := Real.exp (-(2 * Real.pi * cc ρ i))

/-- The Poisson kernel on `ℤ`, normalized to have total mass `1`:
`κ_i(z) = (1-λ_i)/(1+λ_i) · λ_i^{|z|}`. -/
def kap (ρ : ℝ) (i : ℕ) (z : ℤ) : ℝ :=
  (1 - lam ρ i) / (1 + lam ρ i) * (lam ρ i) ^ z.natAbs

/-- The Poisson-type circle multiplier, in closed form. -/
def mmClosed (ρ : ℝ) (i : ℕ) (θ : ℝ) : ℝ :=
  (1 - lam ρ i) ^ 2 / (1 - 2 * lam ρ i * Real.cos (2 * Real.pi * θ) + (lam ρ i) ^ 2)

/-- The frequency cut `1_{[0,1/2]}` on the circle. -/
def piCut (θ : ℝ) : ℂ := if θ ≤ 1 / 2 then 1 else 0

/-- The smooth part of the truncated multiplier. -/
def phi (ρ : ℝ) (i : ℕ) (θ : ℝ) : ℂ := piCut θ * (mmClosed ρ i θ : ℂ)

/-- The boundary-layer part of the truncated multiplier; on `(0,1)` we have
`1_{[0,ρ^{-i}]} = phi + bb`. -/
def bb (ρ : ℝ) (i : ℕ) (θ : ℝ) : ℂ :=
  (if |θ| ≤ cc ρ i then (1 : ℂ) else 0) - phi ρ i θ

/-- The trigonometric polynomial of a finitely supported sequence `f : ℤ → ℂ`. -/
def trigP (s : Finset ℤ) (f : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑ j ∈ s, f j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℤ) : ℂ) * (θ : ℂ))

/-- The two-sided Hardy--Littlewood maximal function on `ℤ`. -/
def hlMaxZ (g : ℤ → ℝ≥0∞) (x : ℤ) : ℝ≥0∞ :=
  ⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
    ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, g k

/-! ## Elementary facts about the scales -/

lemma cc_pos {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) : 0 < cc ρ i := by
  unfold cc; exact zpow_pos hρ _

lemma cc_le_one {ρ : ℝ} (hρ : 1 ≤ ρ) (i : ℕ) : cc ρ i ≤ 1 := by
  unfold cc
  have h : (-(i : ℤ)) ≤ 0 := by simp
  calc ρ ^ (-(i : ℤ)) ≤ ρ ^ (0 : ℤ) := zpow_le_zpow_right₀ (by linarith) h
    _ = 1 := zpow_zero ρ

lemma lam_pos {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) : 0 < lam ρ i := Real.exp_pos _

lemma lam_lt_one {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) : lam ρ i < 1 := by
  unfold lam
  rw [Real.exp_lt_one_iff]
  have := cc_pos hρ i
  nlinarith [Real.pi_pos]

lemma lam_nonneg {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) : 0 ≤ lam ρ i := (lam_pos hρ i).le

lemma one_sub_lam_pos {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) : 0 < 1 - lam ρ i := by
  linarith [lam_lt_one hρ i]

lemma one_add_lam_pos {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) : 0 < 1 + lam ρ i := by
  linarith [lam_nonneg hρ i]


lemma mmClosed_denom_pos {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) (θ : ℝ) :
    0 < 1 - 2 * lam ρ i * Real.cos (2 * Real.pi * θ) + (lam ρ i) ^ 2 := by
  have h1 := lam_lt_one hρ i
  have h2 := lam_nonneg hρ i
  have h3 := Real.cos_le_one (2 * Real.pi * θ)
  nlinarith [sq_nonneg (1 - lam ρ i), sq_nonneg (lam ρ i)]

lemma mmClosed_pos {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) (θ : ℝ) : 0 < mmClosed ρ i θ := by
  unfold mmClosed
  exact div_pos (pow_pos (one_sub_lam_pos hρ i) 2) (mmClosed_denom_pos hρ i θ)

lemma mmClosed_le_one {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) (θ : ℝ) : mmClosed ρ i θ ≤ 1 := by
  unfold mmClosed
  rw [div_le_one (mmClosed_denom_pos hρ i θ)]
  have h2 := lam_nonneg hρ i
  have h3 := Real.cos_le_one (2 * Real.pi * θ)
  nlinarith

lemma mmClosed_nonneg {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) (θ : ℝ) : 0 ≤ mmClosed ρ i θ :=
  (mmClosed_pos hρ i θ).le

lemma mmClosed_zero {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) : mmClosed ρ i 0 = 1 := by
  unfold mmClosed
  rw [mul_zero, Real.cos_zero, mul_one]
  have h : (1 - lam ρ i) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (one_sub_lam_pos hρ i))
  rw [show (1 - 2 * lam ρ i + (lam ρ i) ^ 2) = (1 - lam ρ i) ^ 2 by ring]
  exact div_self h

lemma piCut_norm_le (θ : ℝ) : ‖piCut θ‖ ≤ 1 := by
  unfold piCut; split <;> simp

lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

lemma phi_norm_le {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) (θ : ℝ) : ‖phi ρ i θ‖ ≤ 1 := by
  unfold phi
  rw [norm_mul]
  have h2 : ‖((mmClosed ρ i θ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_ofReal_complex, abs_of_nonneg (mmClosed_nonneg hρ i θ)]
    exact mmClosed_le_one hρ i θ
  calc ‖piCut θ‖ * ‖((mmClosed ρ i θ : ℝ) : ℂ)‖ ≤ 1 * 1 :=
        mul_le_mul (piCut_norm_le θ) h2 (norm_nonneg _) (by norm_num)
    _ = 1 := by ring

lemma bb_norm_le {ρ : ℝ} (hρ : 0 < ρ) (i : ℕ) (θ : ℝ) : ‖bb ρ i θ‖ ≤ 2 := by
  unfold bb
  have h1 : ‖(if |θ| ≤ cc ρ i then (1 : ℂ) else 0)‖ ≤ 1 := by split <;> simp
  calc ‖(if |θ| ≤ cc ρ i then (1 : ℂ) else 0) - phi ρ i θ‖
      ≤ ‖(if |θ| ≤ cc ρ i then (1 : ℂ) else 0)‖ + ‖phi ρ i θ‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add h1 (phi_norm_le hρ i θ)
    _ = 2 := by norm_num

end

end Lacunary
end Work.BourgainPlan.Oscillation
