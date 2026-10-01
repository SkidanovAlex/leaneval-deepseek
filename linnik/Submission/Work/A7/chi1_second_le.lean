import Mathlib
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.LinnikAreas.A7.Basic7

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract
open Work.LinnikAreas.A7

/-- If *every* box zero of `χ` has zero-parameter at least `c₀`, while `lam ≤ c₀` and
`Cf Λ lam - Aref c₀ lam ≤ CST1`, then the λ-weighted box sum of `χ` is at most the
area-7 credit `(9/100)·(CST1 + (Φ Λ/w Λ)·w(lam) + η)`.

The proof weights the whole box sum with `e^{-a c₀}` (legitimate, since all box zeros are
weighted by at most that), compares `boxAbs` with `B(lam) + η`, and then uses that
`e^{-a c₀}·B(K,lam) ≤ Φ(lam) - Aref c₀ lam`, together with the splitting
`Φ(lam) = C(Λ,lam) + (Φ Λ/w Λ)·w(lam)`. -/
theorem chi1_second_le {q : ℕ} [NeZero q] {R Λ c₀ η lam CST1 : ℝ}
    {χ : DirichletCharacter ℂ q}
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hlam0 : 0 < lam) (hlamΛ : lam ≤ Λ) (hlamc : lam ≤ c₀)
    (hsecond : ∀ ρ' : ℂ, Work.LinnikContract.InBox q R ρ' → Work.LinnikContract.zeroMult χ ρ' ≠ 0 →
      c₀ ≤ Work.LinnikContract.lamOf q ρ')
    (hcert : Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤
      ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η))
    (hrowA : Work.LinnikAreas.A7.Cf Λ lam - Work.LinnikAreas.A7.Aref c₀ lam ≤ CST1) :
    Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤
      ((9:ℝ)/100) * (CST1 + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) *
        Work.LinnikContract.wHB lam + η) := by
  classical
  have hac : (0:ℝ) < ac := ac_pos
  have hc0 : (0:ℝ) < c₀ := lt_of_lt_of_le hlam0 hlamc
  have hE1 : Real.exp (-(ac * c₀)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [hac, hc0])
  have heta : Real.exp (-(ac * c₀)) * η ≤ η := by
    simpa using mul_le_mul_of_nonneg_right hE1 hη
  have hEpos : (0:ℝ) ≤
      (Real.exp (-(ac * lam)) - Real.exp (-(ac * c₀))) *
        (((1 - Real.exp (-(Kc * lam))) / lam) ^ 2 / K2) := by
    apply mul_nonneg
    · rw [sub_nonneg]
      exact Real.exp_le_exp.mpr (by nlinarith [hac, hlamc])
    · apply div_nonneg (sq_nonneg _)
      norm_num [K2]
  have hBfun_le : Real.exp (-(ac * c₀)) * Bfun Kc lam ≤ Phi lam - Aref c₀ lam := by
    rw [Work.LinnikAreas.A7.Aref_expand (ne_of_gt hlam0)]
    linarith [hEpos]
  have hW : WBox q ((3:ℝ)/10) R χ ≤ Real.exp (-(ac * c₀)) * boxAbs q ((3:ℝ)/10) R χ :=
    WBox_le_exp_mul_boxAbs ((3:ℝ)/10) R χ hsecond
  have hWbox_le : WBox q ((3:ℝ)/10) R χ ≤
      ((9:ℝ)/100) * (Real.exp (-(ac*c₀)) * Bfun ((3:ℝ)/10) lam + η) := by
    calc WBox q ((3:ℝ)/10) R χ
        ≤ Real.exp (-(ac*c₀)) * boxAbs q ((3:ℝ)/10) R χ := hW
      _ ≤ Real.exp (-(ac*c₀)) * (((9:ℝ)/100) * (Bfun ((3:ℝ)/10) lam + η)) :=
          mul_le_mul_of_nonneg_left hcert (Real.exp_nonneg _)
      _ = ((9:ℝ)/100) * (Real.exp (-(ac*c₀)) * Bfun ((3:ℝ)/10) lam
            + Real.exp (-(ac*c₀)) * η) := by ring
      _ ≤ ((9:ℝ)/100) * (Real.exp (-(ac*c₀)) * Bfun ((3:ℝ)/10) lam + η) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith [heta]
  have hB_le : Real.exp (-(ac*c₀)) * Bfun ((3:ℝ)/10) lam ≤
      CST1 + (Phi Λ / Wf Λ) * wHB lam := by
    have hBK : Bfun ((3:ℝ)/10) lam = Bfun Kc lam := rfl
    rw [hBK]
    have hsplit := Phi_eq_Cf_add hΛ hlam0 hlamΛ
    have hwf : Wf lam = wHB lam := rfl
    calc Real.exp (-(ac*c₀)) * Bfun Kc lam
        ≤ Phi lam - Aref c₀ lam := hBfun_le
      _ = Cf Λ lam - Aref c₀ lam + (Phi Λ / Wf Λ) * wHB lam := by
          rw [hsplit, hwf]; ring
      _ ≤ CST1 + (Phi Λ / Wf Λ) * wHB lam := by linarith [hrowA]
  calc WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (Real.exp (-(ac*c₀)) * Bfun ((3:ℝ)/10) lam + η) := hWbox_le
    _ ≤ ((9:ℝ)/100) * (CST1 + (Phi Λ / Wf Λ) * wHB lam + η) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        linarith [hB_le]

end

end Work.A7
