import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine_v2

open Complex DirichletCharacter Metric BigOperators
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

theorem IsRectMin.hmax_rect {q : ℕ} [NeZero q] {L : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hR : IsRectMin L χ₁ ρ₁) {ψ : DirichletCharacter ℂ q} {u : ℂ}
    (hψ : ψ ≠ 1) (hzm : zeroMult ψ u ≠ 0) (him : |u.im| ≤ 10 * L) :
    lamOf q ρ₁ ≤ lamOf q u :=
  hR.2 ψ u ⟨hψ, hzm, him⟩

/-- A zero `u` of a non-principal `ψ` in the Lemma-5.2 window of a point `s` with
`Re s = Re ρ₁` has `Re u ≤ Re s`. -/
theorem IsRectMin.window_left {q : ℕ} [NeZero q] {L : ℝ} {χ₁ : DirichletCharacter ℂ q}
    {ρ₁ : ℂ} (hR : IsRectMin L χ₁ ρ₁) (hlog : 0 < Real.log (q : ℝ))
    {ψ : DirichletCharacter ℂ q} [NeZero ψ.conductor] (hψ : ψ ≠ 1) {s : ℂ} {δ R : ℝ}
    (him : |s.im| + δ ≤ 10 * L) (hsre : s.re = ρ₁.re) :
    ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
        (Metric.closedBall 0 R)) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re := by
  intro u hdiv hwin
  have hzm : zeroMult ψ u ≠ 0 := Work.ZeroFreeTables.zeroMult_ne_zero_of_divisor_v2 ψ hψ hdiv
  have h1 : |s.im - u.im| ≤ δ := by
    have h := Complex.abs_im_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
    have h' : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).im) = s.im - u.im := by simp
    rw [h'] at h; exact le_trans h hwin
  have h2 : |u.im| ≤ 10 * L := by
    have h3 : |u.im| ≤ |s.im| + δ := by
      calc |u.im| = |s.im - (s.im - u.im)| := by ring_nf
        _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
        _ ≤ |s.im| + δ := by linarith
    linarith
  have hle := IsRectMin.hmax_rect hR hψ hzm h2
  simp only [lamOf] at hle
  have h4 : u.re ≤ ρ₁.re := by nlinarith [hlog, hle]
  rw [hsre]; exact h4

/-- The six two-factor products of the three characters of the three-character method
(one from each of the three conjugate pairs) are all non-principal. -/
theorem pairProducts_ne_one {q : ℕ} [NeZero q] {χ₁ χ₂ χ₃ : DirichletCharacter ℂ q}
    (h21 : χ₂ ≠ χ₁) (h21' : χ₂ ≠ χ₁⁻¹) (h31 : χ₃ ≠ χ₁) (h31' : χ₃ ≠ χ₁⁻¹)
    (h32 : χ₃ ≠ χ₂) (h32' : χ₃ ≠ χ₂⁻¹) :
    χ₁ * χ₂ ≠ 1 ∧ χ₁ * χ₂⁻¹ ≠ 1 ∧ χ₁ * χ₃ ≠ 1 ∧ χ₁ * χ₃⁻¹ ≠ 1 ∧
      χ₂ * χ₃ ≠ 1 ∧ χ₂ * χ₃⁻¹ ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact h21' (eq_inv_of_mul_eq_one_right h)
  · intro h; exact h21 ((mul_inv_eq_one.mp h).symm)
  · intro h; exact h31' (eq_inv_of_mul_eq_one_right h)
  · intro h; exact h31 ((mul_inv_eq_one.mp h).symm)
  · intro h; exact h32' (eq_inv_of_mul_eq_one_right h)
  · intro h; exact h32 ((mul_inv_eq_one.mp h).symm)

/-- The arithmetic kernel of HB (1992) §10: the `(10.6)` inequality follows from the four
"leading" bounds, the six pair bounds (aggregated) and the four triple bounds, with the
`(A)`-credits `creds j = L * Re F (i mu_j)` attached to the principal triples. -/
theorem HB10_3_arith (T : Work.ZeroFreeTables.TestFn) (ε : ℝ) (hε : 0 < ε)
    {L lam1 lam2 lam3 : ℝ} (hL : 0 < L) (creds : Fin 4 → ℝ) {bT : Fin 4 → ℝ}
    {bPsum K0 K1 K2 K3 : ℝ}
    (hbK0 : K0 ≤ L * T.F (-lam1) + T.f 0 * ε * L)
    (hbK1 : K1 ≤ -L * T.F 0 + T.f 0 * (1/6 + ε) * L)
    (hbK2 : K2 ≤ -L * T.F (lam2 - lam1) + T.f 0 * (1/6 + ε) * L)
    (hbK3 : K3 ≤ -L * T.F (lam3 - lam1) + T.f 0 * (1/6 + ε) * L)
    (hbT : ∀ j : Fin 4, bT j ≤ T.f 0 * (1/6 + ε) * L + 2 * creds j)
    (hbP : bPsum ≤ 6 * (T.f 0 * (1/6 + ε) * L) - ∑ j : Fin 4, creds j)
    (hpos : 0 ≤ K0 + K1 + K2 + K3 + (1/2) * bPsum + (1/4) * ∑ j : Fin 4, bT j) :
    0 ≤ T.F (-lam1) - T.F 0 - T.F (lam2 - lam1) - T.F (lam3 - lam1) + T.f 0 * (7/6 + 8 * ε) := by
  have hTsum : ∑ j : Fin 4, bT j ≤ 4 * (T.f 0 * (1/6 + ε) * L) + 2 * ∑ j : Fin 4, creds j := by
    calc ∑ j : Fin 4, bT j
        ≤ ∑ j : Fin 4, (T.f 0 * (1/6 + ε) * L + 2 * creds j) :=
          Finset.sum_le_sum (fun j _ => hbT j)
      _ = 4 * (T.f 0 * (1/6 + ε) * L) + 2 * ∑ j : Fin 4, creds j := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            ← Finset.mul_sum]
          norm_num
  have key : 0 ≤ L * (T.F (-lam1) - T.F 0 - T.F (lam2 - lam1) - T.F (lam3 - lam1)
      + T.f 0 * (7/6 + 8 * ε)) := by
    have h1 : (1/4) * (∑ j : Fin 4, bT j)
        ≤ (4 * (T.f 0 * (1/6 + ε) * L)) * (1/4) + (2 * ∑ j : Fin 4, creds j) * (1/4) := by
      have h := mul_le_mul_of_nonneg_left hTsum (by norm_num : (0:ℝ) ≤ 1/4)
      linarith only [h]
    have h2 : (1/2) * bPsum
        ≤ (6 * (T.f 0 * (1/6 + ε) * L) - ∑ j : Fin 4, creds j) * (1/2) := by
      have h := mul_le_mul_of_nonneg_left hbP (by norm_num : (0:ℝ) ≤ 1/2)
      linarith only [h]
    linarith only [hpos, hbK0, hbK1, hbK2, hbK3, h1, h2]
  by_contra hcon
  push_neg at hcon
  nlinarith only [key, hL, hcon]

end Work.ZeroFreeTables.OffAxis
