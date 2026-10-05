import Mathlib
import Submission.Work.RPCore.Defs

/-!
# `Wrot` is a type-2 generating function of `tau δ` (`|δ| < π/2`)

We show `Work.RPV.Wrot δ` is a type-2 generating function for the time-`δ` flow
`Work.RPV.tau δ` of `K₀`, as long as `|δ| < π/2` (so that `cos δ ≠ 0`).

The proof is a direct computation: the Fréchet derivative of the explicit quadratic
polynomial `Wrot δ` is computed in `Wrot_fderiv`, which turns the type-2 conditions
`p = P + ∂_q W` and `Q = q + ∂_P W` into explicit algebraic relations
`p.1 = P.1/cos δ - tan δ · q.1`, `p.2 = P.2`, `Q.1 = q.1/cos δ - tan δ · P.1`,
`Q.2 = q.2 + δ`; these are exactly the components of `tau δ (q,p) = (Q,P)`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

open Work.RPV

namespace Work.RPCore.GenFun

/-- The coordinate `x ↦ q₁` of `PS = (ℝ×ℝ)×(ℝ×ℝ)` as a continuous linear map. -/
noncomputable def Lq1 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- The coordinate `x ↦ p₁` of `PS` as a continuous linear map. -/
noncomputable def Lp1 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- The coordinate `x ↦ p₂` of `PS` as a continuous linear map. -/
noncomputable def Lp2 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- Fréchet derivative of `Wrot δ` at `x`. -/
lemma hasFDerivAt_Wrot (δ : ℝ) (x : PS) :
    HasFDerivAt (Wrot δ)
      (((1 / Real.cos δ - 1) * (x.2.1 : ℝ) - Real.tan δ * (x.1.1 : ℝ)) • Lq1
        + ((1 / Real.cos δ - 1) * (x.1.1 : ℝ) - Real.tan δ * (x.2.1 : ℝ)) • Lp1
        + (δ : ℝ) • Lp2) x := by
  have h1 : HasFDerivAt (fun y : PS => (1 / Real.cos δ - 1) * (Lq1 y * Lp1 y))
      ((1 / Real.cos δ - 1) • (Lq1 x • Lp1 + Lp1 x • Lq1)) x :=
    ((ContinuousLinearMap.hasFDerivAt Lq1).mul
      (ContinuousLinearMap.hasFDerivAt Lp1)).const_mul _
  have h2a : HasFDerivAt (fun y : PS => Lq1 y * Lq1 y) (Lq1 x • Lq1 + Lq1 x • Lq1) x :=
    (ContinuousLinearMap.hasFDerivAt Lq1).mul (ContinuousLinearMap.hasFDerivAt Lq1)
  have h2b : HasFDerivAt (fun y : PS => Lp1 y * Lp1 y) (Lp1 x • Lp1 + Lp1 x • Lp1) x :=
    (ContinuousLinearMap.hasFDerivAt Lp1).mul (ContinuousLinearMap.hasFDerivAt Lp1)
  have h2 : HasFDerivAt (fun y : PS => (Real.tan δ / 2) * (Lq1 y * Lq1 y + Lp1 y * Lp1 y))
      ((Real.tan δ / 2) • ((Lq1 x • Lq1 + Lq1 x • Lq1) + (Lp1 x • Lp1 + Lp1 x • Lp1))) x :=
    (h2a.add h2b).const_mul _
  have h3 : HasFDerivAt (fun y : PS => δ * Lp2 y) (δ • Lp2) x :=
    (ContinuousLinearMap.hasFDerivAt Lp2).const_mul _
  have h := (h1.sub h2).add h3
  convert h using 1
  · ext y; simp [Wrot, Lq1, Lp1, Lp2]; ring
  · apply ContinuousLinearMap.ext; intro v
    simp only [add_apply, sub_apply, smul_apply]
    simp [Lq1, Lp1, Lp2]; ring

/-- Explicit value of the Fréchet derivative of `Wrot δ`. -/
lemma Wrot_fderiv (δ : ℝ) (x v : PS) :
    fderiv ℝ (Wrot δ) x v =
      (1 / Real.cos δ - 1) * (v.1.1 * x.2.1 + x.1.1 * v.2.1)
        - Real.tan δ * (x.1.1 * v.1.1 + x.2.1 * v.2.1) + δ * v.2.2 := by
  rw [(hasFDerivAt_Wrot δ x).fderiv]
  simp [Lq1, Lp1, Lp2]; ring

theorem wrot_isType2GF (δ : ℝ) (hδ : |δ| < Real.pi / 2) : Work.RPV.IsType2GF (Work.RPV.tau δ) (Work.RPV.Wrot δ) := by
  have hcos : Real.cos δ ≠ 0 := by
    have hδ' := abs_lt.mp hδ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨hδ'.1, hδ'.2⟩)
  have hsin : Real.sin δ ^ 2 = 1 - Real.cos δ ^ 2 := by
    linear_combination (Real.sin_sq_add_cos_sq δ)
  intro q p Q P
  have hA : tau δ (q, p) = (Q, P) ↔
      (Q.1 = q.1 * Real.cos δ - p.1 * Real.sin δ ∧ Q.2 = q.2 + δ ∧
        P.1 = q.1 * Real.sin δ + p.1 * Real.cos δ ∧ P.2 = p.2) := by
    simp only [tau, Prod.ext_iff]
    tauto
  have hB : (p = P + dq (Wrot δ) q P ∧ Q = q + dP (Wrot δ) q P) ↔
      (p.1 = P.1 + ((1 / Real.cos δ - 1) * P.1 - Real.tan δ * q.1) ∧ p.2 = P.2 ∧
        Q.1 = q.1 + ((1 / Real.cos δ - 1) * q.1 - Real.tan δ * P.1) ∧ Q.2 = q.2 + δ) := by
    simp only [dq, dP, Prod.ext_iff]
    rw [Wrot_fderiv, Wrot_fderiv, Wrot_fderiv, Wrot_fderiv]
    simp only [Prod.fst_add, Prod.snd_add, one_mul, mul_one, mul_zero, zero_mul, add_zero,
      zero_add, sub_self]
    tauto
  rw [hA, hB]
  rw [Real.tan_eq_sin_div_cos]
  constructor
  · rintro ⟨hQ1, hQ2, hP1, hP2⟩
    refine ⟨?_, hP2.symm, ?_, hQ2⟩
    · rw [hP1]; field_simp; ring
    · rw [hP1, hQ1]; field_simp; ring_nf; rw [hsin]; ring
  · rintro ⟨hp1, hp2, hQ1, hQ2⟩
    have hP1 : P.1 = q.1 * Real.sin δ + p.1 * Real.cos δ := by
      rw [hp1]; field_simp; ring
    refine ⟨?_, hQ2, hP1, hp2.symm⟩
    · rw [hQ1, hP1]; field_simp; ring_nf; rw [hsin]; ring

end Work.RPCore.GenFun
