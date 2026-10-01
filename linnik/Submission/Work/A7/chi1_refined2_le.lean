import Mathlib
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.LinnikAreas.A7.Basic7
import Submission.Work.LinnikAreas.A7.Aref2
import Submission.Work.A7.WBox_refined2

namespace Work.A7

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikAreas.A7

/-- `e^{-a c} ≤ 1` for `c ≥ 0`. -/
private lemma exp_neg_ac_le_one {c : ℝ} (hc : 0 ≤ c) : Real.exp (-(ac * c)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  nlinarith [ac_pos, hc]

theorem chi1_refined2_le {q : ℕ} [NeZero q] {R Λ c₀ η lam CST1 : ℝ}
    {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hΛ : 0 < Λ) (hη : 0 ≤ η) (hlam0 : 0 < lam) (hlamΛ : lam ≤ Λ) (hlamc : lam ≤ c₀)
    (hbox : Work.LinnikContract.InBox q R ρ) (hboxc : Work.LinnikContract.InBox q R ((starRingEnd ℂ) ρ))
    (hχ : χ ^ 2 = 1) (hmult : Work.LinnikContract.zeroMult χ ρ = 1) (hne : (starRingEnd ℂ) ρ ≠ ρ)
    (hlam : Work.LinnikContract.lamOf q ρ = lam)
    (hsecond : ∀ ρ' : ℂ, Work.LinnikContract.InBox q R ρ' → Work.LinnikContract.zeroMult χ ρ' ≠ 0 →
      ρ' ≠ ρ → ρ' ≠ (starRingEnd ℂ) ρ → c₀ ≤ Work.LinnikContract.lamOf q ρ')
    (hcert : Work.LinnikContract.boxAbs q ((3:ℝ)/10) R χ ≤
      ((9:ℝ)/100) * (Work.LinnikContract.Bfun ((3:ℝ)/10) lam + η))
    (hrowA : Work.LinnikAreas.A7.Cf Λ lam - Work.LinnikAreas.A7.Aref2 c₀ lam ≤ CST1) :
    Work.LinnikAreas.A7.WBox q ((3:ℝ)/10) R χ ≤
      ((9:ℝ)/100) * (CST1 + (Work.LinnikAreas.A7.Phi Λ / Work.LinnikAreas.A7.Wf Λ) *
        Work.LinnikContract.wHB lam + η) := by
  -- The two-zero refinement bound (this is exactly `WBox_refined2`).
  have hW := WBox_refined2 (q := q) (R := R) (lam := lam) (c := c₀) (η := η)
    (χ := χ) (ρs := ρ) hbox hboxc hχ hmult hne hlam hlam0 hlamc hsecond hcert
  -- Splitting `Φ(lam) = Cf Λ lam + (Φ Λ / Wf Λ) · Wf lam` (valid since `0 < lam ≤ Λ`).
  have hΦ : Phi lam = Cf Λ lam + (Phi Λ / Wf Λ) * Work.LinnikContract.wHB lam := by
    rw [Work.LinnikAreas.A7.Phi_eq_Cf_add hΛ hlam0 hlamΛ]
    simp only [Wf]
  -- Hence `Φ(lam) - Aref2 c₀ lam ≤ CST1 + (Φ Λ / Wf Λ) · wHB lam`.
  have hkey : Phi lam - Aref2 c₀ lam ≤ CST1 + (Phi Λ / Wf Λ) * Work.LinnikContract.wHB lam := by
    linarith [hrowA]
  -- And `e^{-a c₀} η ≤ η` since `c₀ ≥ lam > 0` and `η ≥ 0`.
  have hc0 : 0 ≤ c₀ := le_trans hlam0.le hlamc
  have hexp_le : Real.exp (-(ac * c₀)) ≤ 1 := exp_neg_ac_le_one hc0
  have hexpη : Real.exp (-(ac * c₀)) * η ≤ η := by
    nlinarith [hexp_le, hη]
  -- Combine.
  have hfinal : (9/100) * (Phi lam - Aref2 c₀ lam) + (9/100) * Real.exp (-(ac * c₀)) * η
      ≤ (9/100) * (CST1 + (Phi Λ / Wf Λ) * Work.LinnikContract.wHB lam + η) := by
    nlinarith [hkey, hexpη]
  linarith [hW, hfinal]

end

end Work.A7
