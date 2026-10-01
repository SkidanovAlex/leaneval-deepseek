import Mathlib
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.LinnikAreas.A7.Basic7
import Submission.Work.A7.WBox_refined

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract
open Work.LinnikAreas.A7

/-- The χ₁-termination lemma (α = 1 case).  Combining the refined per-character bound
`WBox ≤ K²(Φ(λ) - A<c₀>λ) + K²e^{-a c₀}η` of `WBox_refined` with

* the splitting `Φ(λ) = C(Λ,λ) + (Φ(Λ)/w(Λ))·w(λ)` for `λ ≤ Λ` (`Phi_eq_Cf_add`),
* the credit hypothesis `C(Λ,λ) - A<c₀>λ ≤ CST1`,
* `e^{-a c₀} ≤ 1` (as `c₀ ≥ λ > 0`),

one obtains the final χ₁-bound in the form used by the §15 assembly. -/
theorem chi1_refined_le {q : ℕ} [NeZero q] {R Λ c₀ η lam CST1 : ℝ}
    {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hlam0 : 0 < lam) (hlamΛ : lam ≤ Λ) (hlamc : lam ≤ c₀)
    (hbox : Work.LinnikContract.InBox q R ρ) (hmult : Work.LinnikContract.zeroMult χ ρ = 1)
    (hlam : Work.LinnikContract.lamOf q ρ = lam)
    (hsecond : ∀ ρ' : ℂ, Work.LinnikContract.InBox q R ρ' → Work.LinnikContract.zeroMult χ ρ' ≠ 0 →
      ρ' ≠ ρ → c₀ ≤ Work.LinnikContract.lamOf q ρ')
    (hcert : Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤
      ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η))
    (hrowA : Work.LinnikAreas.A7.Cf Λ lam - Work.LinnikAreas.A7.Aref c₀ lam ≤ CST1) :
    Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤
      ((9:ℝ)/100) * (CST1 + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) *
        Work.LinnikContract.wHB lam + η) := by
  have hK2 : (0:ℝ) < (9:ℝ)/100 := by norm_num
  have hac : (0:ℝ) < ac := ac_pos
  have hc0pos : (0:ℝ) < c₀ := lt_of_lt_of_le hlam0 hlamc
  -- the refined per-character bound for the isolated simple zero `ρ`
  have hW := WBox_refined hbox hmult hlam hlam0 hlamc hsecond hcert
  -- the `Φ`-splitting at the reference point `Λ`
  have hPhi := Phi_eq_Cf_add hΛ hlam0 hlamΛ
  -- step A: the credit hypothesis turns `Φ(λ) - A<c₀>λ` into `CST1 + (ΦΛ/wΛ)·w(λ)`
  have hA : Phi lam - Aref c₀ lam ≤ CST1 + (Phi Λ / Wf Λ) * wHB lam := by
    have h : Phi lam - Aref c₀ lam
        = (Cf Λ lam - Aref c₀ lam) + (Phi Λ / Wf Λ) * Wf lam := by
      rw [hPhi]; ring
    rw [h]
    have h3 := add_le_add_right hrowA ((Phi Λ / Wf Λ) * Wf lam)
    simpa [Wf] using h3
  -- step B: `e^{-a c₀} ≤ 1` because `c₀ ≥ λ > 0`
  have hB : Real.exp (-(ac * c₀)) * η ≤ η := by
    have h1 : Real.exp (-(ac * c₀)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    calc Real.exp (-(ac * c₀)) * η ≤ 1 * η := mul_le_mul_of_nonneg_right h1 hη
      _ = η := one_mul η
  calc Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ
      ≤ ((9:ℝ)/100) * (Phi lam - Aref c₀ lam) +
          ((9:ℝ)/100) * Real.exp (-(ac * c₀)) * η := hW
    _ ≤ ((9:ℝ)/100) * (CST1 + (Phi Λ / Wf Λ) * wHB lam) + ((9:ℝ)/100) * η := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hA hK2.le
        · rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hB hK2.le
    _ = ((9:ℝ)/100) * (CST1 + (Phi Λ / Wf Λ) * wHB lam + η) := by ring

end

end Work.A7
