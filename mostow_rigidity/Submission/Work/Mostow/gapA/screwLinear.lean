import Mathlib
import Submission.Work.Mostow.gapA.screwDefs
import Submission.Work.Mostow.gapA.screwLine
import Submission.Work.Mostow.pairStabDefs

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

/-- If the Lorentz map `Λ = emat g` sends the axis `s ↦ axisV a b s` to the translate
`s ↦ axisV a b (s + c)`, then it scales the two future null vectors `nvec a`, `nvec b` by
`e^c` and `e^{-c}` respectively.

Indeed `axisV a b s = κ (e^s · nvec a + e^{-s} · nvec b)` with `κ = kkB a b ≠ 0`, so the
hypothesis reads
`κ (e^s · Λ A + e^{-s} · Λ B) = κ (e^{s+c} · A + e^{-(s+c)} · B)`
for all `s`; cancelling `κ` and evaluating at `s = 0` and `s = 1` gives a linear system whose
solution is `Λ A = e^c · A`, `Λ B = e^{-c} · B`. -/
theorem screwLinear {a b : Submission.Mostow.E 3} (ha : a ∈ Submission.Mostow.Sph 3)
    (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (g : LeanEval.Geometry.MostowRigidity.PO 3 1) (c : ℝ)
    (h : ∀ s : ℝ, _root_.Matrix.mulVec (Work.Mostow.emat g) (Work.Mostow.gapA.axisV a b s)
      = Work.Mostow.gapA.axisV a b (s + c)) :
    _root_.Matrix.mulVec (Work.Mostow.emat g) (Work.Mostow.nvec a)
        = Real.exp c • Work.Mostow.nvec a ∧
      _root_.Matrix.mulVec (Work.Mostow.emat g) (Work.Mostow.nvec b)
        = (Real.exp c)⁻¹ • Work.Mostow.nvec b := by
  have hkk : 0 < Work.Mostow.gapA.kkB a b := (Work.Mostow.gapA.screwLine ha hb hab).2.1
  have hkkne : Work.Mostow.gapA.kkB a b ≠ 0 := ne_of_gt hkk
  -- The hypothesis, in the null-vector coordinates of the axis.
  have key : ∀ s : ℝ,
      Real.exp s • _root_.Matrix.mulVec (Work.Mostow.emat g) (Work.Mostow.nvec a) +
        Real.exp (-s) • _root_.Matrix.mulVec (Work.Mostow.emat g) (Work.Mostow.nvec b)
      = Real.exp s • (Real.exp c • Work.Mostow.nvec a) +
        Real.exp (-s) • ((Real.exp c)⁻¹ • Work.Mostow.nvec b) := by
    intro s
    have hs := h s
    simp only [Work.Mostow.gapA.axisV, Work.Mostow.gapA.nullA, Work.Mostow.gapA.nullB] at hs
    rw [_root_.Matrix.mulVec_smul, _root_.Matrix.mulVec_add,
      _root_.Matrix.mulVec_smul, _root_.Matrix.mulVec_smul] at hs
    rw [show Real.exp (-(s + c)) = Real.exp (-s) * (Real.exp c)⁻¹ by
        rw [show -(s + c) = -s + -c by ring, Real.exp_add, Real.exp_neg, Real.exp_neg],
      Real.exp_add] at hs
    simp only [← smul_smul] at hs
    exact (smul_right_injective (R := ℝ) _ hkkne) hs
  set X := _root_.Matrix.mulVec (Work.Mostow.emat g) (Work.Mostow.nvec a) with hX
  set Y := _root_.Matrix.mulVec (Work.Mostow.emat g) (Work.Mostow.nvec b) with hY
  set A := Work.Mostow.nvec a with hAd
  set B := Work.Mostow.nvec b with hBd
  have h0 := key 0
  have h1 := key 1
  simp only [Real.exp_zero, neg_zero, one_smul] at h0
  have c0 : ∀ i, X i + Y i = Real.exp c * A i + (Real.exp c)⁻¹ * B i := by
    intro i
    have := congrFun h0 i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have c1 : ∀ i, Real.exp 1 * X i + Real.exp (-1) * Y i
      = Real.exp 1 * (Real.exp c * A i) + Real.exp (-1) * ((Real.exp c)⁻¹ * B i) := by
    intro i
    have := congrFun h1 i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hne1 : Real.exp (-1) - Real.exp 1 ≠ 0 := by
    have hlt : Real.exp (-1) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
    linarith
  have hne2 : Real.exp 1 - Real.exp (-1) ≠ 0 := by
    have hlt : Real.exp (-1) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
    linarith
  have hXe : ∀ i, X i = Real.exp c * A i := by
    intro i
    have h2 : (Real.exp (-1) - Real.exp 1) * X i
        = (Real.exp (-1) - Real.exp 1) * (Real.exp c * A i) := by
      linear_combination Real.exp (-1) * c0 i - c1 i
    exact mul_left_cancel₀ hne1 h2
  have hYe : ∀ i, Y i = (Real.exp c)⁻¹ * B i := by
    intro i
    have h2 : (Real.exp 1 - Real.exp (-1)) * Y i
        = (Real.exp 1 - Real.exp (-1)) * ((Real.exp c)⁻¹ * B i) := by
      linear_combination Real.exp 1 * c0 i - c1 i
    exact mul_left_cancel₀ hne2 h2
  constructor
  · funext i
    rw [hXe i]
    simp only [Pi.smul_apply, smul_eq_mul]
  · funext i
    rw [hYe i]
    simp only [Pi.smul_apply, smul_eq_mul]

end

end Work.Mostow.gapA
