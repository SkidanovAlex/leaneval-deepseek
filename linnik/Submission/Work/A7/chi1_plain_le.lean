import Mathlib
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.LinnikAreas.A7.Basic7

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

theorem chi1_plain_le {q : ℕ} [NeZero q] {R Λ c₀ η lam CST1 CST2 : ℝ}
    {χ : DirichletCharacter ℂ q}
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hlam0 : 0 < lam) (hlamΛ : lam ≤ Λ)
    (hsecond : ∀ ρ' : ℂ, Work.LinnikContract.InBox q R ρ' → Work.LinnikContract.zeroMult χ ρ' ≠ 0 →
      lam ≤ Work.LinnikContract.lamOf q ρ')
    (hcert : Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤
      ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η))
    (hrowB : Work.LinnikAreas.A7.Cf Λ lam ≤ CST2) (hcred12 : CST2 ≤ CST1) :
    Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤
      ((9:ℝ)/100) * (CST1 + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) *
        Work.LinnikContract.wHB lam + η) := by
  have hac : (0:ℝ) < Work.LinnikAreas.A7.ac := Work.LinnikAreas.A7.ac_pos
  have hW := Work.LinnikAreas.A7.WBox_le_exp_mul_boxAbs ((3:ℝ)/10) R χ hsecond
  have hPhi := Work.LinnikAreas.A7.Phi_eq_Cf_add (Λ := Λ) (z := lam) hΛ hlam0 hlamΛ
  have hCf_le : Work.LinnikAreas.A7.Cf Λ lam ≤ CST1 := le_trans hrowB hcred12
  have hE1 : Real.exp (-(Work.LinnikAreas.A7.ac * lam)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [hac, hlam0]
  have hEta : Real.exp (-(Work.LinnikAreas.A7.ac * lam)) * η ≤ η := by
    nlinarith [hE1, hη, Real.exp_nonneg (-(Work.LinnikAreas.A7.ac * lam))]
  have hmain : Work.LinnikAreas.A7.Phi lam + Real.exp (-(Work.LinnikAreas.A7.ac * lam)) * η
      ≤ CST1 + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ)
          * Work.LinnikContract.wHB lam + η := by
    have h1 : Work.LinnikAreas.A7.Phi lam
        ≤ CST1 + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ)
            * Work.LinnikContract.wHB lam := by
      rw [hPhi]
      have hWf : (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ)
            * Work.LinnikAreas.A7.Wf lam
          = (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ)
            * Work.LinnikContract.wHB lam := rfl
      rw [hWf]; linarith [hCf_le]
    linarith [h1, hEta]
  have h9 : (0:ℝ) ≤ (9:ℝ)/100 := by norm_num
  calc Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ Real.exp (-(Work.LinnikAreas.A7.ac * lam)) *
          Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ := hW
    _ ≤ Real.exp (-(Work.LinnikAreas.A7.ac * lam)) *
          (((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η)) :=
        mul_le_mul_of_nonneg_left hcert (Real.exp_nonneg _)
    _ = ((9:ℝ)/100) * (Work.LinnikAreas.A7.Phi lam
          + Real.exp (-(Work.LinnikAreas.A7.ac * lam)) * η) := by
        rw [Work.LinnikAreas.A7.Phi, Work.LinnikAreas.A7.Kc]; ring
    _ ≤ ((9:ℝ)/100) * (CST1 + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ)
          * Work.LinnikContract.wHB lam + η) := mul_le_mul_of_nonneg_left hmain h9

end

end Work.A7
