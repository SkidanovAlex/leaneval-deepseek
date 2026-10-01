import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.pairCountHeight_le_famCount

namespace Work.LinnikAreas

/-- **The per-layer `λ₁`-free pair count.**  From the λ₁-free log-free family count with constant
`C₂` at level `q` (the instance `σ ↦ 1 - t/log q`, `T ↦ 2^{j+1}` of
`Work.ZeroDensity.LogFreeFamHeight (5/2) (3/2)`), the multiplicity-weighted pair count of height
`2^{j+1}·log q` is at most `C₂·e^{(5/2)t}·(2^{j+1})^{3/2}`.

Proof: `pairCountHeight_le_famCount` with `T = 2^{j+1}·log q` reduces this to
`famCount q (1 - t/log q) (2^{j+1})`, and `hC` gives `C₂·e^{(5/2)·((1-(1-t/log q))·log q)}·(2^{j+1})^{3/2}`
with `(1 - (1 - t/log q))·log q = t` (field_simp, `log q ≠ 0`). -/
theorem pairCountHeightDyadicFree {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) {C₂ : ℝ} (j : ℕ)
    (hC : ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.famCount q σ T
        ≤ C₂ * Real.exp ((5 / 2) * ((1 - σ) * Real.log q)) * T ^ (3 / 2 : ℝ)) :
    ∀ t : ℝ, 0 < t → t ≤ Real.log q →
      Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t ((2 : ℝ) ^ (j + 1) * Real.log q)
        ≤ C₂ * Real.exp ((5 / 2) * t) * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) := by
  intro t ht htL
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have htwo : 1 ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
  have hdiv_le_one : t / Real.log (q : ℝ) ≤ 1 := (div_le_one hlog).mpr htL
  have hdiv_nonneg : 0 ≤ t / Real.log (q : ℝ) := div_nonneg ht.le hlog.le
  have hσ0 : 0 ≤ 1 - t / Real.log (q : ℝ) := by linarith
  have hσ1 : 1 - t / Real.log (q : ℝ) ≤ 1 := by linarith
  have hexp : (1 - (1 - t / Real.log (q : ℝ))) * Real.log (q : ℝ) = t := by
    rw [sub_sub_cancel]
    exact div_mul_cancel₀ t hlog.ne'
  calc Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t ((2 : ℝ) ^ (j + 1) * Real.log q)
      ≤ Work.ZeroDensity.famCount q (1 - t / Real.log (q : ℝ))
          (((2 : ℝ) ^ (j + 1) * Real.log q) / Real.log (q : ℝ)) :=
        pairCountHeight_le_famCount hq χ₁ β₁
    _ = Work.ZeroDensity.famCount q (1 - t / Real.log (q : ℝ)) ((2 : ℝ) ^ (j + 1)) := by
        rw [mul_div_cancel_right₀ _ hlog.ne']
    _ ≤ C₂ * Real.exp ((5 / 2) * ((1 - (1 - t / Real.log (q : ℝ))) * Real.log (q : ℝ)))
          * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) :=
        hC (1 - t / Real.log (q : ℝ)) ((2 : ℝ) ^ (j + 1)) hσ0 hσ1 htwo
    _ = C₂ * Real.exp ((5 / 2) * t) * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) := by
        rw [hexp]

end Work.LinnikAreas
