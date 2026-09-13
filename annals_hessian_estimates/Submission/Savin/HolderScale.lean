/-
# The Holder estimate at an arbitrary centre/scale, and for the `Fop`-perturbation

Two corollaries of `Submission.Savin.Holder.holder_estimate` that are used in the proof of
Savin's Proposition 4.1 (quadratic approximation):

* `holder_estimate_scaled` : `holder_estimate` at an arbitrary centre `x₀` and scale `R`
  (obtained by the rescaling `Ψ (y) = Φ (x₀ + R y) / R ^ 2`, for which the equation
  `s2 (A + D²Φ) = 1` is invariant);

* `holder_estimate_eps` : `holder_estimate` for the perturbed operator
  `Fop (cofOp N) ε`, i.e. for `s2 (N + ε • D²Φ) = 1` with `0 < ε ≤ 1`.  The scaling
  `Ψ = ε • Φ` maps this equation to the *unperturbed* one `s2 (N + D²Ψ) = 1`, and the bounds
  and the conclusion are unchanged because they are homogeneous.  This is exactly the input
  needed for the compactness step of Proposition 4.1: after rescaling by a small `r` the
  equation becomes `Fop (cofOp N) (r^β)` with `r^β` small, and the smallness parameter of the
  Holder estimate is `ε · osc`, which tends to `0`.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Holder

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- **The Holder estimate at an arbitrary centre and scale.**  Same as `holder_estimate`, but on
`ball x₀ R`: the smallness condition is `M₀ - m₀ ≤ c₁ R² 2^{-2k}` and the conclusion holds on the
balls `closedBall x₀ (R 2^{-(s+1)})`. -/
theorem holder_estimate_scaled_uniform {c c' Y p M : ℝ} (hc : 0 < c) (hc'pos : 0 < c')
    (hYnn : 0 ≤ Y) (hp : 0 < p) (hM1 : 1 < M)
    (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1))) (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ c₁ δ : ℝ, 0 < c₁ ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (A : ℝ⁴ →L[ℝ] ℝ⁴) (hA : A.IsSymmetric) (hA1 : s2 A = 1)
        (htrA : 0 < trOp A) (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
        (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
        (hYb : 2 * trOp (cofOp A) / c ≤ Y)
        (Φ : ℝ⁴ → ℝ) (x₀ : ℝ⁴) (R : ℝ) (k : ℕ) (m₀ M₀ : ℝ), 0 < R →
        ContDiffOn ℝ 2 Φ (ball x₀ R) →
        (∀ x ∈ ball x₀ R, s2 (A + hessOp Φ x) = 1) →
        (∀ x ∈ ball x₀ R, 0 < trOp (A + hessOp Φ x)) →
        (∀ x ∈ ball x₀ R, m₀ ≤ Φ x) → (∀ x ∈ ball x₀ R, Φ x ≤ M₀) →
        M₀ - m₀ ≤ c₁ * R ^ 2 * (1 / 2 : ℝ) ^ (2 * k) →
        ∀ s ≤ k, ∀ x ∈ closedBall x₀ (R * (1 / 2 : ℝ) ^ (s + 1)),
          ∀ y ∈ closedBall x₀ (R * (1 / 2 : ℝ) ^ (s + 1)),
            Φ x - Φ y ≤ (1 - δ) ^ s * (M₀ - m₀) := by
  obtain ⟨c₁, δ, hc₁, hδ, hδ1, H⟩ :=
    holder_estimate_uniform (Y := Y) hc hc'pos hYnn hp hM1 hM hpbig
  refine ⟨c₁, δ, hc₁, hδ, hδ1, ?_⟩
  intro A hA hA1 htrA hcq hcq' hYb Φ x₀ R k m₀ M₀ hR hΦ heq hpos hlow hup hsmall
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hRne : R ≠ 0 := ne_of_gt hR
  set Ψ : ℝ⁴ → ℝ := fun y => Φ (x₀ + R • y) / R ^ 2 with hΨdef
  have hmap : Set.MapsTo (fun y : ℝ⁴ => x₀ + R • y) (ball 0 1) (ball x₀ R) := by
    intro y hy
    have hy1 : ‖y‖ < 1 := by
      have h := hy; rw [mem_ball, dist_zero_right] at h; exact h
    rw [mem_ball]
    have h1 : dist (x₀ + R • y) x₀ = R * ‖y‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (le_of_lt hR)]
    rw [h1]
    nlinarith [hy1, hR]
  have hΨ2 : ContDiffOn ℝ 2 Ψ (ball 0 1) := by
    have hinner : ContDiffOn ℝ 2 (fun y : ℝ⁴ => x₀ + R • y) (ball 0 1) :=
      (contDiff_const.add (contDiff_id.const_smul R)).contDiffOn
    have h1 : ContDiffOn ℝ 2 (fun y : ℝ⁴ => Φ (x₀ + R • y)) (ball 0 1) := hΦ.comp hinner hmap
    have h2 := h1.const_smul ((R ^ 2)⁻¹)
    have h3 : Ψ = fun y => (R ^ 2)⁻¹ • Φ (x₀ + R • y) := by
      funext y
      simp only [hΨdef, Pi.smul_apply, smul_eq_mul]
      rw [div_eq_mul_inv, mul_comm]
    rw [h3]; exact h2
  have hhess : ∀ y ∈ ball 0 1, hessOp Ψ y = hessOp Φ (x₀ + R • y) := by
    intro y hy
    have hyR : x₀ + R • y ∈ ball x₀ R := hmap hy
    have hcd : ContDiffAt ℝ 2 Φ (x₀ + R • y) := hΦ.contDiffAt (isOpen_ball.mem_nhds hyR)
    rw [hΨdef]
    exact hessOp_comp_affine_div hR hcd
  have heqΨ : ∀ y ∈ ball 0 1, s2 (A + hessOp Ψ y) = 1 := by
    intro y hy
    rw [hhess y hy]; exact heq _ (hmap hy)
  have hposΨ : ∀ y ∈ ball 0 1, 0 < trOp (A + hessOp Ψ y) := by
    intro y hy
    rw [hhess y hy]; exact hpos _ (hmap hy)
  have hlowΨ : ∀ y ∈ ball 0 1, m₀ / R ^ 2 ≤ Ψ y := by
    intro y hy
    simp only [hΨdef]
    exact div_le_div_of_nonneg_right (hlow _ (hmap hy)) (le_of_lt hR2)
  have hupΨ : ∀ y ∈ ball 0 1, Ψ y ≤ M₀ / R ^ 2 := by
    intro y hy
    simp only [hΨdef]
    exact div_le_div_of_nonneg_right (hup _ (hmap hy)) (le_of_lt hR2)
  have hsmallΨ : M₀ / R ^ 2 - m₀ / R ^ 2 ≤ c₁ * (1 / 2 : ℝ) ^ (2 * k) := by
    have h1 : M₀ / R ^ 2 - m₀ / R ^ 2 = (M₀ - m₀) / R ^ 2 := by ring
    rw [h1, div_le_iff₀ hR2]
    have h2 : c₁ * R ^ 2 * (1 / 2 : ℝ) ^ (2 * k) = c₁ * (1 / 2 : ℝ) ^ (2 * k) * R ^ 2 := by ring
    linarith [hsmall, h2.le, h2.ge]
  have hres := H A hA hA1 htrA hcq hcq' hYb Ψ k (m₀ / R ^ 2) (M₀ / R ^ 2) hΨ2 heqΨ hposΨ
    hlowΨ hupΨ hsmallΨ
  intro s hs x hx y hy
  have hx' : R⁻¹ • (x - x₀) ∈ closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1)) := by
    rw [mem_closedBall, dist_zero_right]
    have hxR : ‖x - x₀‖ ≤ R * (1 / 2 : ℝ) ^ (s + 1) := by
      have h := hx
      rw [mem_closedBall, dist_eq_norm] at h
      exact h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ R⁻¹)]
    rw [inv_mul_le_iff₀ hR]
    exact hxR
  have hy' : R⁻¹ • (y - x₀) ∈ closedBall (0 : ℝ⁴) ((1 / 2 : ℝ) ^ (s + 1)) := by
    rw [mem_closedBall, dist_zero_right]
    have hyR : ‖y - x₀‖ ≤ R * (1 / 2 : ℝ) ^ (s + 1) := by
      have h := hy
      rw [mem_closedBall, dist_eq_norm] at h
      exact h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ R⁻¹)]
    rw [inv_mul_le_iff₀ hR]
    exact hyR
  have hres' := hres s hs (R⁻¹ • (x - x₀)) hx' (R⁻¹ • (y - x₀)) hy'
  have hxeq : Ψ (R⁻¹ • (x - x₀)) = Φ x / R ^ 2 := by
    simp only [hΨdef]
    have : x₀ + R • (R⁻¹ • (x - x₀)) = x := by
      rw [smul_smul, mul_inv_cancel₀ hRne, one_smul, add_sub_cancel]
    rw [this]
  have hyeq : Ψ (R⁻¹ • (y - x₀)) = Φ y / R ^ 2 := by
    simp only [hΨdef]
    have : x₀ + R • (R⁻¹ • (y - x₀)) = y := by
      rw [smul_smul, mul_inv_cancel₀ hRne, one_smul, add_sub_cancel]
    rw [this]
  rw [hxeq, hyeq] at hres'
  have hdiff : Φ x / R ^ 2 - Φ y / R ^ 2 = (Φ x - Φ y) / R ^ 2 := by ring
  rw [hdiff] at hres'
  have hdiff2 : M₀ / R ^ 2 - m₀ / R ^ 2 = (M₀ - m₀) / R ^ 2 := by ring
  rw [hdiff2] at hres'
  rw [div_le_iff₀ hR2] at hres'
  have h3 : (1 - δ) ^ s * ((M₀ - m₀) / R ^ 2) * R ^ 2 = (1 - δ) ^ s * (M₀ - m₀) := by
    field_simp
  linarith [hres', h3.le, h3.ge]

/-- **The Holder estimate at an arbitrary centre and scale.**  Same as `holder_estimate`, but on
`ball x₀ R`: the smallness condition is `M₀ - m₀ ≤ c₁ R² 2^{-2k}` and the conclusion holds on the
balls `closedBall x₀ (R 2^{-(s+1)})`. -/
theorem holder_estimate_scaled {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hA1 : s2 A = 1)
    (htrA : 0 < trOp A) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {p M : ℝ} (hp : 0 < p) (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ c₁ δ : ℝ, 0 < c₁ ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (Φ : ℝ⁴ → ℝ) (x₀ : ℝ⁴) (R : ℝ) (k : ℕ) (m₀ M₀ : ℝ), 0 < R →
        ContDiffOn ℝ 2 Φ (ball x₀ R) →
        (∀ x ∈ ball x₀ R, s2 (A + hessOp Φ x) = 1) →
        (∀ x ∈ ball x₀ R, 0 < trOp (A + hessOp Φ x)) →
        (∀ x ∈ ball x₀ R, m₀ ≤ Φ x) → (∀ x ∈ ball x₀ R, Φ x ≤ M₀) →
        M₀ - m₀ ≤ c₁ * R ^ 2 * (1 / 2 : ℝ) ^ (2 * k) →
        ∀ s ≤ k, ∀ x ∈ closedBall x₀ (R * (1 / 2 : ℝ) ^ (s + 1)),
          ∀ y ∈ closedBall x₀ (R * (1 / 2 : ℝ) ^ (s + 1)),
            Φ x - Φ y ≤ (1 - δ) ^ s * (M₀ - m₀) := by
  obtain ⟨hc'pos, hYnn⟩ := harnack_base_data hc hcq hcq'
  obtain ⟨c₁, δ, h1, h2, h3, h4⟩ :=
    holder_estimate_scaled_uniform (Y := 2 * trOp (cofOp A) / c) hc hc'pos hYnn hp hM1 hM hpbig
  exact ⟨c₁, δ, h1, h2, h3, h4 A hA hA1 htrA hcq hcq' le_rfl⟩

/-- **The Holder estimate for the perturbed operator `Fop (cofOp N) ε`.**  Same conclusion as
`holder_estimate`, for a function `Φ` with `s2 (N + ε • D²Φ) = 1`, `0 < ε ≤ 1`.  The value
scaling `Ψ = ε • Φ` transforms it into the unperturbed equation `s2 (N + D²Ψ) = 1`, and all the
bounds are homogeneous, so the conclusion is unchanged. -/
theorem holder_estimate_eps {N : ℝ⁴ →L[ℝ] ℝ⁴} (hN : N.IsSymmetric) (hN1 : s2 N = 1)
    (htrN : 0 < trOp N) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp N v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp N v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {p M : ℝ} (hp : 0 < p) (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ c₁ δ : ℝ, 0 < c₁ ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (Φ : ℝ⁴ → ℝ) (ε : ℝ) (k : ℕ) (m₀ M₀ : ℝ), 0 < ε → ε ≤ 1 →
        ContDiffOn ℝ 2 Φ (ball 0 1) →
        (∀ x ∈ ball 0 1, Fop (cofOp N) ε (hessOp Φ x) = 0) →
        (∀ x ∈ ball 0 1, 0 < trOp (N + hessOp Φ x)) →
        (∀ x ∈ ball 0 1, m₀ ≤ Φ x) → (∀ x ∈ ball 0 1, Φ x ≤ M₀) →
        M₀ - m₀ ≤ c₁ * (1 / 2 : ℝ) ^ (2 * k) →
        ∀ s ≤ k, ∀ x ∈ closedBall 0 ((1 / 2 : ℝ) ^ (s + 1)),
          ∀ y ∈ closedBall 0 ((1 / 2 : ℝ) ^ (s + 1)),
            Φ x - Φ y ≤ (1 - δ) ^ s * (M₀ - m₀) := by
  obtain ⟨c₁, δ, hc₁, hδ, hδ1, H⟩ := holder_estimate hN hN1 htrN hc hcq hcq' hp hM1 hM hpbig
  refine ⟨c₁, δ, hc₁, hδ, hδ1, ?_⟩
  intro Φ ε k m₀ M₀ hε hε1 hΦ heq hpos hlow hup hsmall
  set Ψ : ℝ⁴ → ℝ := fun x => ε * Φ x with hΨdef
  have hΨ2 : ContDiffOn ℝ 2 Ψ (ball 0 1) := by
    have h := hΦ.const_smul ε
    simpa only [hΨdef, Pi.smul_apply, smul_eq_mul] using h
  have hhess : ∀ x ∈ ball 0 1, hessOp Ψ x = ε • hessOp Φ x := by
    intro x hx
    have hcd : ContDiffAt ℝ 2 Φ x := hΦ.contDiffAt (isOpen_ball.mem_nhds hx)
    rw [hΨdef]
    exact hessOp_const_mul ε hcd
  have heqΨ : ∀ x ∈ ball 0 1, s2 (N + hessOp Ψ x) = 1 := by
    intro x hx
    have hcd : ContDiffAt ℝ 2 Φ x := hΦ.contDiffAt (isOpen_ball.mem_nhds hx)
    have hsym : (hessOp Φ x).IsSymmetric := hessOp_symm_of_contDiffAt hcd
    have hF : pairOp (cofOp N) (hessOp Φ x) + ε * s2 (hessOp Φ x) = 0 := heq x hx
    have hpair : pairOp (cofOp N) (hessOp Φ x) = -ε * s2 (hessOp Φ x) := by linarith [hF]
    rw [hhess x hx, s2_add_expansion hN (hsym.smul (by simp)), s2_smul,
      pairOp_smul, hN1, hpair]
    ring
  have hposΨ : ∀ x ∈ ball 0 1, 0 < trOp (N + hessOp Ψ x) := by
    intro x hx
    rw [hhess x hx, trOp_add, trOp_smul]
    have h1 : 0 < trOp (N + hessOp Φ x) := hpos x hx
    rw [trOp_add] at h1
    nlinarith [h1, hε, hε1, htrN]
  have hlowΨ : ∀ x ∈ ball 0 1, ε * m₀ ≤ Ψ x := by
    intro x hx
    simp only [hΨdef]
    exact mul_le_mul_of_nonneg_left (hlow x hx) (le_of_lt hε)
  have hupΨ : ∀ x ∈ ball 0 1, Ψ x ≤ ε * M₀ := by
    intro x hx
    simp only [hΨdef]
    exact mul_le_mul_of_nonneg_left (hup x hx) (le_of_lt hε)
  have h0 : (0 : ℝ⁴) ∈ ball 0 1 := by rw [mem_ball, dist_self]; norm_num
  have hM0 : 0 ≤ M₀ - m₀ := by have h1 := hlow 0 h0; have h2 := hup 0 h0; linarith
  have hsmallΨ : ε * M₀ - ε * m₀ ≤ c₁ * (1 / 2 : ℝ) ^ (2 * k) := by
    have h1 : ε * M₀ - ε * m₀ = ε * (M₀ - m₀) := by ring
    rw [h1]
    calc ε * (M₀ - m₀) ≤ 1 * (M₀ - m₀) := mul_le_mul_of_nonneg_right hε1 hM0
      _ = M₀ - m₀ := one_mul _
      _ ≤ c₁ * (1 / 2 : ℝ) ^ (2 * k) := hsmall
  have hres := H Ψ k (ε * m₀) (ε * M₀) hΨ2 heqΨ hposΨ hlowΨ hupΨ hsmallΨ
  intro s hs x hx y hy
  have hres' := hres s hs x hx y hy
  have hxval : Ψ x = ε * Φ x := by simp only [hΨdef]
  have hyval : Ψ y = ε * Φ y := by simp only [hΨdef]
  rw [hxval, hyval] at hres'
  have h1 : ε * Φ x - ε * Φ y = ε * (Φ x - Φ y) := by ring
  rw [h1] at hres'
  have h2 : ε * M₀ - ε * m₀ = ε * (M₀ - m₀) := by ring
  rw [h2] at hres'
  have h3 : (1 - δ) ^ s * (ε * (M₀ - m₀)) = ε * ((1 - δ) ^ s * (M₀ - m₀)) := by ring
  rw [h3] at hres'
  exact le_of_mul_le_mul_left hres' hε

end

end Submission
