/-
# Auxiliary definitions for `Work.ConstructionInstance.holder_omegaStar`

`holder_omegaStar` proves `Holder ⟨β, _⟩ (omegaStar β)` for `0 < β ≤ 1`.  The pointwise
Hölder estimate runs through the *explicit* scalar amplitude of the model field

  `omegaStar β x = (Γ(θ x) · F_*(ρ x ^ (3β))) • e_θ(x)`,

which on `x₂ ≥ 0` equals `A0 β x = 2 |x₂|^β r(x)^{2β} / (1 + ρ(x)^{3β})²` and on `x₂ < 0`
equals `cos (βπ)` times it — the factor produced by `Real.rpow` at the negative base
`sin θ cos²θ` (`Real.rpow_def_of_neg`, `Real.log_neg_eq_log`).  This file collects the
definitions and the elementary bounds; the analytic estimates live in sibling files.

## Main definitions

* `Pall x = |x₂| r(x)²` — the non-negative homogeneous degree `3` factor whose `β`-th power is
  the numerator of the amplitude, and `Pall x ≤ ρ x ^ 3`;
* `A0 β x = 2 (Pall x)^β / (1 + ρ(x)^{3β})²` — the non-negative amplitude (`A0_eq_alt` records
  the equivalent split form `2 |x₂|^β r^{2β} / (1+ρ^{3β})²`);
* `cSign β t` — `1` for `t ≥ 0`, `cos (βπ)` for `t < 0`: the factor by which `Real.rpow`
  differs from `|·|^β` at a negative base; `Aom β x = cSign β (x₂) · A0 β x` is the true
  amplitude, so that `omegaStar β x = Aom β x • eTheta x` (`omegaStar_eq_Aom`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology NNReal ENNReal

namespace Work.ConstructionInstance

/-- The factor of `Γ(θ) = (sin θ cos²θ)^β` produced by `Real.rpow` at a negative base: `1` if
the base (which has the sign of `x₂`) is `≥ 0`, and `cos (βπ)` if it is `< 0`. -/
def cSign (β t : ℝ) : ℝ := if 0 ≤ t then 1 else Real.cos (β * Real.pi)

/-- The non-negative homogeneous degree `3` profile `P(x) = |x₂| r(x)²`. -/
def Pall (x : R3) : ℝ := |x 2| * (Work.Cyl.radial x) ^ 2

/-- The non-negative amplitude `A0 β x = 2 |x₂|^β r(x)^{2β} / (1 + ρ(x)^{3β})²` of the model
field (equal to `2 (Pall x)^β / (1+ρ^{3β})²`, see `A0_eq_Pall`). -/
def A0 (β : ℝ) (x : R3) : ℝ :=
  2 * |x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β) / (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2

/-- The amplitude of `omegaStar β` including the sign factor of `Real.rpow` at the negative
base: `Aom β x = cSign β (x₂) · A0 β x`. -/
def Aom (β : ℝ) (x : R3) : ℝ := cSign β (x 2) * A0 β x

/-! ## Elementary `Real.rpow` facts -/

lemma rpow_sq_mul (β r : ℝ) (hr : 0 ≤ r) : ((r ^ 2 : ℝ)) ^ β = r ^ (2 * β) := by
  rw [Real.rpow_mul hr]; norm_num

lemma rpow_two_mul (β r : ℝ) (hr : 0 ≤ r) : r ^ (2 * β) = r ^ β * r ^ β := by
  rw [← rpow_sq_mul β r hr, show r ^ 2 = r * r by ring, Real.mul_rpow hr hr]

/-- For `0 ≤ a ≤ b` and `t ≥ 0`: `t ^ a ≤ (1 + t ^ b) ^ 2`. -/
lemma rpow_le_one_add_sq (a b t : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 ≤ t) :
    t ^ a ≤ (1 + t ^ b) ^ 2 := by
  have h1 : 0 ≤ t ^ b := Real.rpow_nonneg ht b
  rcases le_total t 1 with h | h
  · refine le_trans (Real.rpow_le_one ht h ha) ?_; nlinarith
  · rcases lt_or_eq_of_le h with ht1 | heq
    · have h2 : t ^ a ≤ t ^ b := by rw [Real.rpow_le_rpow_left_iff ht1]; exact hab
      nlinarith
    · subst heq; norm_num [Real.one_rpow]

lemma denom_pos (β : ℝ) (x : R3) : 0 < (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2 := by
  have := Real.rpow_nonneg (Work.Cyl.rho_nonneg x) (3 * β); positivity

/-! ## The amplitude `A0` -/

lemma Pall_nonneg (x : R3) : 0 ≤ Pall x := by rw [Pall]; positivity

lemma Pall_le_rho_cube (x : R3) : Pall x ≤ Work.Cyl.rho x ^ 3 := by
  have h1 : |x 2| ≤ Work.Cyl.rho x := Work.Cyl.abs_axial_le_rho x
  have h2 : (Work.Cyl.radial x) ^ 2 ≤ Work.Cyl.rho x ^ 2 := by
    rw [Work.Cyl.radial_sq]; exact Work.Cyl.radSq_le_rho_sq x
  rw [Pall]
  nlinarith [abs_nonneg (x 2), sq_nonneg (Work.Cyl.rho x)]

lemma A0_nonneg (β : ℝ) (x : R3) : 0 ≤ A0 β x := by
  rw [A0]
  have h : 0 ≤ |x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β) :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) β)
      (Real.rpow_nonneg (Work.Cyl.radial_nonneg x) (2 * β))
  exact div_nonneg (by linarith) (denom_pos β x).le

lemma A0_eq_Pall (β : ℝ) (x : R3) :
    A0 β x = 2 * (Pall x) ^ β / (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2 := by
  have hr : 0 ≤ Work.Cyl.radial x := Work.Cyl.radial_nonneg x
  have hP : (Pall x) ^ β = |x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β) := by
    rw [Pall, Real.mul_rpow (abs_nonneg (x 2)) (by positivity),
      ← rpow_sq_mul β (Work.Cyl.radial x) hr]
  rw [A0, hP]; ring

/-- `|x₂| r ≤ ρ²`. -/
lemma abs_ax_mul_radial_le (x : R3) :
    |x 2| * Work.Cyl.radial x ≤ Work.Cyl.rho x ^ 2 := by
  have h1 : |x 2| ≤ Work.Cyl.rho x := Work.Cyl.abs_axial_le_rho x
  have h2 : (Work.Cyl.radial x) ^ 2 ≤ Work.Cyl.rho x ^ 2 := by
    rw [Work.Cyl.radial_sq]; exact Work.Cyl.radSq_le_rho_sq x
  have h3 : 0 ≤ Work.Cyl.radial x := Work.Cyl.radial_nonneg x
  nlinarith [abs_nonneg (x 2), sq_nonneg (Work.Cyl.rho x - Work.Cyl.radial x)]

lemma A0_le_half (β : ℝ) (hβ : 0 < β) (x : R3) : A0 β x ≤ 1 / 2 := by
  have hρ : 0 ≤ Work.Cyl.rho x := Work.Cyl.rho_nonneg x
  have hP : Pall x ≤ Work.Cyl.rho x ^ 3 := Pall_le_rho_cube x
  have hP0 : 0 ≤ Pall x := Pall_nonneg x
  have h4 : (Pall x) ^ β ≤ (Work.Cyl.rho x ^ (3 : ℝ)) ^ β :=
    Real.rpow_le_rpow hP0 (by norm_num; exact hP) hβ.le
  have h5 : (Work.Cyl.rho x ^ (3 : ℝ)) ^ β = Work.Cyl.rho x ^ (3 * β) :=
    (Real.rpow_mul hρ 3 β).symm
  rw [A0_eq_Pall, div_le_iff₀ (denom_pos β x)]
  set t := Work.Cyl.rho x ^ (3 * β) with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact Real.rpow_nonneg hρ _
  have h6 : (Pall x) ^ β ≤ t := h5 ▸ h4
  rw [ht] at h6
  nlinarith [sq_nonneg (1 - t)]

lemma A0_le_ax (β : ℝ) (hβ : 0 < β) (x : R3) : A0 β x ≤ 2 * |x 2| ^ β := by
  have hr : 0 ≤ Work.Cyl.radial x := Work.Cyl.radial_nonneg x
  have hρ : 0 ≤ Work.Cyl.rho x := Work.Cyl.rho_nonneg x
  rw [A0, div_le_iff₀ (denom_pos β x)]
  have h1 : (Work.Cyl.radial x) ^ (2 * β) ≤ (Work.Cyl.rho x) ^ (2 * β) :=
    Real.rpow_le_rpow hr (Work.Cyl.radial_le_rho x) (by linarith)
  have h2 : (Work.Cyl.rho x) ^ (2 * β) ≤ (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2 :=
    rpow_le_one_add_sq (2 * β) (3 * β) _ (by linarith) (by linarith) hρ
  have hz : 0 ≤ |x 2| ^ β := Real.rpow_nonneg (abs_nonneg _) β
  nlinarith [h1, h2, hz, Real.rpow_nonneg hr (2 * β)]

lemma A0_le_rpow2 (β : ℝ) (hβ : 0 < β) (x : R3) :
    A0 β x ≤ 2 * (Work.Cyl.radial x) ^ (2 * β) := by
  have hr : 0 ≤ Work.Cyl.radial x := Work.Cyl.radial_nonneg x
  have hρ : 0 ≤ Work.Cyl.rho x := Work.Cyl.rho_nonneg x
  rw [A0, div_le_iff₀ (denom_pos β x)]
  have h1 : (|x 2|) ^ β ≤ (Work.Cyl.rho x) ^ β :=
    Real.rpow_le_rpow (abs_nonneg _) (Work.Cyl.abs_axial_le_rho x) hβ.le
  have h2 : (Work.Cyl.rho x) ^ β ≤ (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2 :=
    rpow_le_one_add_sq β (3 * β) _ hβ.le (by linarith) hρ
  nlinarith [h1, h2, Real.rpow_nonneg hr (2 * β)]

lemma A0_le_rpow (β : ℝ) (hβ : 0 < β) (x : R3) :
    A0 β x ≤ 2 * (Work.Cyl.radial x) ^ β := by
  have hr : 0 ≤ Work.Cyl.radial x := Work.Cyl.radial_nonneg x
  have hρ : 0 ≤ Work.Cyl.rho x := Work.Cyl.rho_nonneg x
  rw [A0, div_le_iff₀ (denom_pos β x)]
  have hfac : |x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β)
      = (|x 2| * Work.Cyl.radial x) ^ β * (Work.Cyl.radial x) ^ β := by
    rw [Real.mul_rpow (abs_nonneg _) hr, rpow_two_mul β _ hr]; ring
  have hkey : (|x 2| * Work.Cyl.radial x) ^ β ≤ (1 + (Work.Cyl.rho x) ^ (3 * β)) ^ 2 := by
    have h1 : (|x 2| * Work.Cyl.radial x) ^ β ≤ ((Work.Cyl.rho x) ^ 2) ^ β :=
      Real.rpow_le_rpow (by positivity) (abs_ax_mul_radial_le x) hβ.le
    rw [rpow_sq_mul β _ hρ] at h1
    exact le_trans h1
      (rpow_le_one_add_sq (2 * β) (3 * β) _ (by linarith) (by linarith) hρ)
  rw [show 2 * |x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β)
      = 2 * (|x 2| ^ β * (Work.Cyl.radial x) ^ (2 * β)) by ring, hfac]
  have hrβ : 0 ≤ (Work.Cyl.radial x) ^ β := Real.rpow_nonneg hr β
  nlinarith [mul_le_mul_of_nonneg_right hkey hrβ]

lemma A0_eq_zero_of_radial_eq_zero (β : ℝ) (hβ : 0 < β) {x : R3}
    (h : Work.Cyl.radial x = 0) : A0 β x = 0 := by
  rw [A0, h, Real.zero_rpow (by positivity : (2 : ℝ) * β ≠ 0)]
  simp

/-! ## The signed amplitude `Aom` -/

lemma abs_cSign_le_one (β t : ℝ) : |cSign β t| ≤ 1 := by
  by_cases h : 0 ≤ t
  · rw [cSign, if_pos h]; norm_num
  · rw [cSign, if_neg h]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

lemma abs_Aom_le_A0 (β : ℝ) (x : R3) : |Aom β x| ≤ A0 β x := by
  rw [Aom, abs_mul, abs_of_nonneg (A0_nonneg β x)]
  calc |cSign β (x 2)| * A0 β x ≤ 1 * A0 β x :=
        mul_le_mul_of_nonneg_right (abs_cSign_le_one β (x 2)) (A0_nonneg β x)
    _ = A0 β x := one_mul _

/-! ## `r` is `1`-Lipschitz and `‖e_θ‖ ≤ 1` -/

lemma norm_radialVec (x : R3) : ‖Work.Cyl.radialVec x‖ = Work.Cyl.radial x := by
  have h : ‖Work.Cyl.radialVec x‖ ^ 2 = Work.Cyl.radial x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, Work.Cyl.inner_radialVec_self, Work.Cyl.radial_sq]
  nlinarith [norm_nonneg (Work.Cyl.radialVec x), Work.Cyl.radial_nonneg x]

lemma radialVec_sub (x y : R3) :
    Work.Cyl.radialVec x - Work.Cyl.radialVec y = Work.Cyl.radialVec (x - y) := by
  ext i
  fin_cases i <;> simp [Work.Cyl.radialVec]

lemma radial_dist_le (x y : R3) :
    |Work.Cyl.radial x - Work.Cyl.radial y| ≤ ‖x - y‖ := by
  have h1 : ‖Work.Cyl.radialVec x‖ = Work.Cyl.radial x := norm_radialVec x
  have h2 : ‖Work.Cyl.radialVec y‖ = Work.Cyl.radial y := norm_radialVec y
  calc |Work.Cyl.radial x - Work.Cyl.radial y|
      = |‖Work.Cyl.radialVec x‖ - ‖Work.Cyl.radialVec y‖| := by rw [h1, h2]
    _ ≤ ‖Work.Cyl.radialVec x - Work.Cyl.radialVec y‖ := abs_norm_sub_norm_le _ _
    _ = ‖Work.Cyl.radialVec (x - y)‖ := by rw [radialVec_sub]
    _ = Work.Cyl.radial (x - y) := norm_radialVec _
    _ ≤ Work.Cyl.rho (x - y) := Work.Cyl.radial_le_rho _
    _ = ‖x - y‖ := Work.Cyl.rho_eq_norm _

lemma norm_eTheta_le_one (x : R3) : ‖Work.Cyl.eTheta x‖ ≤ 1 := by
  rcases eq_or_ne (Work.Cyl.radial x) 0 with h | h
  · have hz : (1 : ℝ) / Work.Cyl.radial x = 0 := by rw [h]; norm_num
    rw [Work.Cyl.eTheta, hz, zero_smul, norm_zero]; norm_num
  · rw [Work.Cyl.norm_eTheta x h]

lemma eTheta_norm_sub_le_two (x y : R3) : ‖Work.Cyl.eTheta x - Work.Cyl.eTheta y‖ ≤ 2 := by
  refine le_trans (norm_sub_le _ _) ?_
  have h1 := norm_eTheta_le_one x
  have h2 := norm_eTheta_le_one y
  linarith

/-! ## From a pointwise norm bound to `HolderWith` -/

/-- `HolderWith` (with exponent the non-negative real `α`, written with the real calibration
`βr = α`) follows from the pointwise norm bound `‖f x - f y‖ ≤ C ‖x-y‖^βr`. -/
theorem holder_of_norm_le {α : ℝ≥0} {βr : ℝ} (hα : (α : ℝ) = βr) (hβ : 0 ≤ βr) {f : R3 → R3}
    {C : ℝ≥0} (h : ∀ x y : R3, ‖f x - f y‖ ≤ (C : ℝ) * ‖x - y‖ ^ βr) :
    HolderWith C α f := by
  intro x y
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, hα]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (x - y)) hβ]
  rw [ENNReal.coe_nnreal_eq C, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x y)

lemma one_add_rpow_pos (β : ℝ) (x : R3) : 0 < 1 + (Work.Cyl.rho x) ^ (3 * β) := by
  have := Real.rpow_nonneg (Work.Cyl.rho_nonneg x) (3 * β); linarith

/-- The axial factor `|x₂|^β / (1 + ρ^{3β})` of the amplitude: `A0 = 2 · Acol · Arow`. -/
def Acol (β : ℝ) (x : R3) : ℝ := |x 2| ^ β / (1 + (Work.Cyl.rho x) ^ (3 * β))

/-- The radial factor `r^{2β} / (1 + ρ^{3β})` of the amplitude: `A0 = 2 · Acol · Arow`. -/
def Arow (β : ℝ) (x : R3) : ℝ := (Work.Cyl.radial x) ^ (2 * β) / (1 + (Work.Cyl.rho x) ^ (3 * β))

lemma Acol_nonneg (β : ℝ) (x : R3) : 0 ≤ Acol β x :=
  div_nonneg (Real.rpow_nonneg (abs_nonneg _) β) (one_add_rpow_pos β x).le

lemma Arow_nonneg (β : ℝ) (x : R3) : 0 ≤ Arow β x :=
  div_nonneg (Real.rpow_nonneg (Work.Cyl.radial_nonneg x) (2 * β)) (one_add_rpow_pos β x).le

lemma rho_rpow_le_den {β : ℝ} (hβ : 0 ≤ β) (x : R3) :
    (Work.Cyl.rho x) ^ β ≤ 1 + (Work.Cyl.rho x) ^ (3 * β) := by
  have hρ := Work.Cyl.rho_nonneg x
  rcases le_total (Work.Cyl.rho x) 1 with h | h
  · have h1 : (Work.Cyl.rho x) ^ β ≤ 1 := Real.rpow_le_one hρ h hβ
    have h2 : 0 ≤ (Work.Cyl.rho x) ^ (3 * β) := Real.rpow_nonneg hρ _
    linarith
  · have h1 : (Work.Cyl.rho x) ^ β ≤ (Work.Cyl.rho x) ^ (3 * β) :=
      Real.rpow_le_rpow_of_exponent_le h (by linarith)
    linarith [Real.rpow_nonneg hρ (3 * β)]

lemma Acol_le_one (β : ℝ) (hβ : 0 ≤ β) (x : R3) : Acol β x ≤ 1 := by
  rw [Acol, div_le_iff₀ (one_add_rpow_pos β x)]
  have h1 : |x 2| ^ β ≤ (Work.Cyl.rho x) ^ β :=
    Real.rpow_le_rpow (abs_nonneg _) (Work.Cyl.abs_axial_le_rho x) hβ
  linarith [rho_rpow_le_den (β := β) hβ x]

lemma Arow_le_one (β : ℝ) (hβ : 0 ≤ β) (x : R3) : Arow β x ≤ 1 := by
  rw [Arow, div_le_iff₀ (one_add_rpow_pos β x)]
  have hρ := Work.Cyl.rho_nonneg x
  have h1 : (Work.Cyl.radial x) ^ (2 * β) ≤ (Work.Cyl.rho x) ^ (2 * β) :=
    Real.rpow_le_rpow (Work.Cyl.radial_nonneg x) (Work.Cyl.radial_le_rho x) (by linarith)
  have h2 : (Work.Cyl.rho x) ^ (2 * β) ≤ 1 + (Work.Cyl.rho x) ^ (3 * β) := by
    rcases le_total (Work.Cyl.rho x) 1 with h | h
    · have h3 : (Work.Cyl.rho x) ^ (2 * β) ≤ 1 := Real.rpow_le_one hρ h (by linarith)
      linarith [Real.rpow_nonneg hρ (3 * β)]
    · have h3 : (Work.Cyl.rho x) ^ (2 * β) ≤ (Work.Cyl.rho x) ^ (3 * β) :=
        Real.rpow_le_rpow_of_exponent_le h (by linarith)
      linarith [Real.rpow_nonneg hρ (3 * β)]
  linarith

lemma A0_eq_col_row (β : ℝ) (x : R3) : A0 β x = 2 * Acol β x * Arow β x := by
  have h : (1 + (Work.Cyl.rho x) ^ (3 * β)) ≠ 0 := ne_of_gt (one_add_rpow_pos β x)
  rw [A0, Acol, Arow]
  field_simp

end Work.ConstructionInstance
