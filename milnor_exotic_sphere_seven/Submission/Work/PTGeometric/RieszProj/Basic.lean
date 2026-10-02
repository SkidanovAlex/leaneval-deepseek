import Submission.Work.PTGeometric.RieszProj.Defs
import Submission.Work.PTGeometric.RieszProj.inv_integral_cos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Riesz projection: scalar reduction and the value on an eigenvector
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped ContDiff
open Set Function MeasureTheory

namespace Work.PTGeometric

noncomputable section

variable {n : ℕ}

/-! ## Basic scalar identities -/

lemma cc_eq (θ : ℝ) : cc θ = 1 + Real.cos θ / 2 := by
  rw [cc]; ring

lemma ss_eq (θ : ℝ) : ss θ = Real.sin θ / 2 := by
  rw [ss]; ring

lemma cc_sub_one (θ : ℝ) : cc θ - 1 = Real.cos θ / 2 := by
  rw [cc_eq]; ring

/-- `(cc θ - lam)² + (ss θ)²` in terms of `a = lam - 1`. -/
lemma den_eq (a θ : ℝ) :
    (cc θ - (1 + a)) ^ 2 + (ss θ) ^ 2 = a ^ 2 + 1/4 - a * Real.cos θ := by
  rw [cc_eq, ss_eq]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The pointwise identity behind the value of the Riesz projection on an eigenvector. -/
lemma scalar_factor (a θ : ℝ) (h : a ^ 2 + 1/4 - a * Real.cos θ ≠ 0) :
    (1/4 - a/2 * Real.cos θ) * (a ^ 2 + 1/4 - a * Real.cos θ)⁻¹
      = 1/2 + (1/4 - a ^ 2)/2 * (a ^ 2 + 1/4 - a * Real.cos θ)⁻¹ := by
  have key : (1/4 - a/2 * Real.cos θ)
      = 1/2 * (a ^ 2 + 1/4 - a * Real.cos θ) + (1/4 - a ^ 2)/2 := by ring
  rw [key, add_mul, mul_assoc, mul_inv_cancel₀ h, mul_one]

/-- The denominator `a² + 1/4 - a cos θ` is positive when `a² ≠ 1/4`. -/
lemma den_pos (a : ℝ) (ha : a ^ 2 ≠ 1/4) (θ : ℝ) : 0 < a ^ 2 + 1/4 - a * Real.cos θ := by
  have hcos : a * Real.cos θ ≤ |a| := by
    calc a * Real.cos θ ≤ |a * Real.cos θ| := le_abs_self _
      _ = |a| * |Real.cos θ| := abs_mul a _
      _ ≤ |a| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg a)
      _ = |a| := mul_one _
  have h2 : 0 < (|a| - 1/2) ^ 2 := by
    have hne : |a| - 1/2 ≠ 0 := by
      intro hh
      apply ha
      have h' : |a| = 1/2 := by linarith
      rw [← sq_abs a, h']
      norm_num
    exact sq_pos_of_ne_zero hne
  rw [← sq_abs a]
  nlinarith [hcos, h2]

/-- The value of the scalar integral. -/
lemma scalar_value (a : ℝ) (ha : a ^ 2 ≠ 1/4) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        (1/2 + (1/4 - a ^ 2)/2 * (a ^ 2 + 1/4 - a * Real.cos θ)⁻¹)
      = (1/2 : ℝ) + (1/4 - a ^ 2) / (2 * |a ^ 2 - 1/4|) := by
  have hpos : ∀ θ : ℝ, a ^ 2 + 1/4 - a * Real.cos θ ≠ 0 := fun θ =>
    ne_of_gt (den_pos a ha θ)
  have hint : IntervalIntegrable (fun θ : ℝ => (a ^ 2 + 1/4 - a * Real.cos θ)⁻¹)
      volume 0 (2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro θ _
      exact hpos θ
  have h1 : (∫ θ in (0:ℝ)..(2 * Real.pi),
      (1/2 + (1/4 - a ^ 2)/2 * (a ^ 2 + 1/4 - a * Real.cos θ)⁻¹))
      = (∫ θ in (0:ℝ)..(2 * Real.pi), (1/2 : ℝ))
        + (1/4 - a ^ 2)/2 * (∫ θ in (0:ℝ)..(2 * Real.pi),
            (a ^ 2 + 1/4 - a * Real.cos θ)⁻¹) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hint.const_mul _),
      intervalIntegral.integral_const_mul]
  have hconst : (∫ θ in (0:ℝ)..(2 * Real.pi), (1/2 : ℝ)) = Real.pi := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hval : (∫ θ in (0:ℝ)..(2 * Real.pi), (a ^ 2 + 1/4 - a * Real.cos θ)⁻¹)
      = 2 * Real.pi * (1 / |a ^ 2 - 1/4|) := by
    have h2 := RieszProj.inv_integral_cos a ha
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    rw [← h2, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  rw [h1, hconst, hval]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have habs : (|a ^ 2 - 1/4|) ≠ 0 := by
    intro hh
    apply ha
    linarith [abs_eq_zero.mp hh]
  field_simp

/-- The value of the scalar integral in the "inside" case. -/
lemma scalar_value_top (a : ℝ) (ha : a ^ 2 ≠ 1/4) (h : |a| < 1/2) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        (1/2 + (1/4 - a ^ 2)/2 * (a ^ 2 + 1/4 - a * Real.cos θ)⁻¹) = 1 := by
  have ha' : (1/4 : ℝ) - a ^ 2 ≠ 0 := by
    intro hh
    apply ha
    linarith
  have h1 : |a ^ 2 - 1/4| = 1/4 - a ^ 2 := by
    have h2 : a ^ 2 < 1/4 := by
      have h3 : |a| ^ 2 < (1/2 : ℝ) ^ 2 := by nlinarith [h, abs_nonneg a]
      rw [sq_abs] at h3
      norm_num at h3
      exact h3
    rw [abs_of_neg (by linarith : a ^ 2 - 1/4 < 0)]
    ring
  rw [scalar_value a ha, h1]
  have hd : (2:ℝ) * (1/4 - a ^ 2) ≠ 0 := by positivity
  have hinner : (1/4 - a ^ 2) / (2 * (1/4 - a ^ 2)) = 1/2 := by
    rw [div_eq_iff hd]; ring
  rw [hinner]
  norm_num

/-- The value of the scalar integral in the "outside" case. -/
lemma scalar_value_bot (a : ℝ) (ha : a ^ 2 ≠ 1/4) (h : 1/2 < |a|) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        (1/2 + (1/4 - a ^ 2)/2 * (a ^ 2 + 1/4 - a * Real.cos θ)⁻¹) = 0 := by
  have ha' : a ^ 2 - 1/4 ≠ 0 := by
    intro hh
    apply ha
    linarith
  have h1 : |a ^ 2 - 1/4| = a ^ 2 - 1/4 := by
    have h2 : (1/4 : ℝ) < a ^ 2 := by
      have h3 : (1/2 : ℝ) ^ 2 < |a| ^ 2 := by nlinarith [h, abs_nonneg a]
      rw [sq_abs] at h3
      norm_num at h3
      exact h3
    exact abs_of_pos (by linarith)
  rw [scalar_value a ha, h1]
  have hd : (2:ℝ) * (a ^ 2 - 1/4) ≠ 0 := by positivity
  have hinner : (1/4 - a ^ 2) / (2 * (a ^ 2 - 1/4)) = -(1/2) := by
    rw [div_eq_iff hd]; ring
  rw [hinner]
  norm_num



/-! ## The cluster condition on a self-adjoint operator -/

/-- `Cluster S` says that every (real) eigenvalue of `S` lies within `1/4` of `0` or `1`. -/
def Cluster (S : EndOp n) : Prop :=
  ∀ mu : ℝ, Module.End.HasEigenvalue (S : Amb n →ₗ[ℝ] Amb n) mu → min |mu| |mu - 1| < 1/4

lemma Cluster.eigen_mem {S : EndOp n} (hS : Cluster S) {mu : ℝ}
    (h : Module.End.HasEigenvalue (S : Amb n →ₗ[ℝ] Amb n) mu) :
    mu ∈ Ioo (-(1/4)) (1/4) ∨ mu ∈ Ioo (3/4) (5/4) := by
  have h' := hS mu h
  rcases lt_or_ge |mu| (1/4) with h1 | h1
  · left
    exact ⟨by linarith [(abs_lt.mp h1).1], by linarith [(abs_lt.mp h1).2]⟩
  · right
    have h2 : |mu - 1| < 1/4 := by
      rcases le_total |mu| |mu - 1| with h3 | h3
      · rw [min_eq_left h3] at h'
        exact absurd h' (not_lt.mpr h1)
      · rw [min_eq_right h3] at h'
        exact h'
    exact ⟨by linarith [(abs_lt.mp h2).1], by linarith [(abs_lt.mp h2).2]⟩

lemma Cluster.ne_half {S : EndOp n} (hS : Cluster S) {mu : ℝ}
    (h : Module.End.HasEigenvalue (S : Amb n →ₗ[ℝ] Amb n) mu) : mu ≠ 1/2 := by
  intro hh
  rcases hS.eigen_mem h with h' | h'
  · rw [hh] at h'; norm_num at h'
  · rw [hh] at h'; norm_num at h'

lemma Cluster.ne_three_half {S : EndOp n} (hS : Cluster S) {mu : ℝ}
    (h : Module.End.HasEigenvalue (S : Amb n →ₗ[ℝ] Amb n) mu) : mu ≠ 3/2 := by
  intro hh
  rcases hS.eigen_mem h with h' | h'
  · rw [hh] at h'; norm_num at h'
  · rw [hh] at h'; norm_num at h'

/-- Under the cluster condition, "in the top cluster" is the same as `1/2 < mu`. -/
lemma Cluster.half_lt_iff {S : EndOp n} (hS : Cluster S) {mu : ℝ}
    (h : Module.End.HasEigenvalue (S : Amb n →ₗ[ℝ] Amb n) mu) :
    (1/2 < mu) ↔ |mu - 1| < 1/2 := by
  constructor
  · intro h1
    rcases hS.eigen_mem h with h' | h'
    · exact absurd h1 (by linarith [h'.2])
    · rw [abs_lt]
      exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
  · intro h1
    rcases hS.eigen_mem h with h' | h'
    · rw [abs_lt] at h1
      linarith [h'.1, h'.2, h1.1]
    · linarith [h'.1]

/-! ## The value of the Riesz projection on an eigenvector -/

lemma contDen_apply_of_eigen {S : EndOp n} {u : Amb n} {lam : ℝ}
    (h : S u = lam • u) (θ : ℝ) :
    contDen S θ u = ((cc θ - lam) ^ 2 + (ss θ) ^ 2) • u := by
  have h1 : (cc θ • (1 : EndOp n) - S) u = (cc θ - lam) • u := by
    rw [sub_apply, smul_apply, one_apply_eq_self, h, sub_smul]
  have step1 : ((cc θ • (1 : EndOp n) - S) * (cc θ • (1 : EndOp n) - S)) u
      = (cc θ - lam) • ((cc θ - lam) • u) := by
    rw [ContinuousLinearMap.mul_apply, h1, map_smul, h1]
  have step2 : ((ss θ) ^ 2 • (1 : EndOp n)) u = (ss θ) ^ 2 • u := by
    rw [smul_apply, one_apply_eq_self]
  rw [contDen, add_apply, step1, step2, smul_smul, ← add_smul]
  congr 1
  ring

lemma contNum_apply_of_eigen {S : EndOp n} {u : Amb n} {lam : ℝ}
    (h : S u = lam • u) (θ : ℝ) :
    contNum S θ u = ((cc θ - 1) * (cc θ - lam) + (ss θ) ^ 2) • u := by
  have h1 : (cc θ • (1 : EndOp n) - S) u = (cc θ - lam) • u := by
    rw [sub_apply, smul_apply, one_apply_eq_self, h, sub_smul]
  have step1 : ((cc θ - 1) • (cc θ • (1 : EndOp n) - S)) u
      = (cc θ - 1) • ((cc θ - lam) • u) := by
    rw [smul_apply, h1]
  have step2 : ((ss θ) ^ 2 • (1 : EndOp n)) u = (ss θ) ^ 2 • u := by
    rw [smul_apply, one_apply_eq_self]
  rw [contNum, add_apply, step1, step2, smul_smul, ← add_smul]

/-- The numerator identity: `(cc θ - 1)(cc θ - lam) + (ss θ)² = 1/4 - (a/2) cos θ` for
`lam = 1 + a`. -/
lemma num_eq (a θ : ℝ) :
    (cc θ - 1) * (cc θ - (1 + a)) + (ss θ) ^ 2 = 1/4 - a/2 * Real.cos θ := by
  rw [cc_eq, ss_eq]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The ratio identity: the scalar obtained by dividing the numerator by the denominator is exactly
the integrand of the scalar integral. -/
lemma ratio_eq (a θ : ℝ) :
    ((cc θ - 1) * (cc θ - (1 + a)) + (ss θ) ^ 2)
        * (((cc θ - (1 + a)) ^ 2 + (ss θ) ^ 2))⁻¹
      = (1/4 - a/2 * Real.cos θ) * (a ^ 2 + 1/4 - a * Real.cos θ)⁻¹ := by
  rw [num_eq a θ, den_eq a θ]

/-- The inverse of an invertible operator on an eigenvector. -/
lemma ringInverse_apply_of_eigen {T : EndOp n} (hT : IsUnit T) {u : Amb n} {mu : ℝ}
    (hmu : mu ≠ 0) (h : T u = mu • u) : Ring.inverse T u = mu⁻¹ • u := by
  have h1 : Ring.inverse T * T = 1 := Ring.inverse_mul_cancel T hT
  have h2 : (Ring.inverse T * T) u = u := by rw [h1, one_apply_eq_self]
  rw [ContinuousLinearMap.mul_apply, h, map_smul] at h2
  have h3 := congrArg (fun z : Amb n => mu⁻¹ • z) h2
  simpa [smul_smul, inv_mul_cancel₀ hmu, one_smul] using h3

end

end Work.PTGeometric
