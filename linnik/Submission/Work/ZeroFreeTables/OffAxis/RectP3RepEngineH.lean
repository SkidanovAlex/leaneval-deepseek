import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.Rep9.Assembly
import Submission.Work.ZeroFreeTables.OffAxis.hbLemma9_2_engine_H
import Submission.Work.ZeroFreeTables.OffAxis.RectRepGeneric
import Submission.Work.ZeroFreeTables.OffAxis.RectRepOrder3Case
import Submission.Work.ZeroFreeTables.OffAxis.RectRepOrder2Diag

namespace Work.ZeroFreeTables.OffAxis

/-- **HB Lemma 9.1 at a multiple zero, at rectangle height `H`** (the statement requested by
`RectC_Z4.RectRepEngineStmt`): for `a, K, ε > 0`, `1 ≤ H` and `3H + 1 ≤ W` there is `q₀` such
that for `q ≥ q₀`, a pair `(χ₁, ρ₁)` with `H ≤ log q`, the wide minimality `IsMinWideAt H W χ₁ ρ₁`,
not the real-real case (`¬(χ₁² = 1 ∧ Im ρ₁ = 0)`), a multiple zero `2 ≤ zeroMult χ₁ ρ₁` and the
side condition `cond913 λ₁ λ₁ a K` satisfies HB's inequality `ineq913 λ₁ λ₁ a K ε`.

The three cases (generic, order `3`, order `2` of `χ₁`) are `rectRepGeneric`,
`RectRepOrder3Case` and `RectRepOrder2Case`. -/
theorem RectP3RepEngineH : ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₁) a K ε := by
  intro a K ε ha hK hε H W hH1 hHW
  obtain ⟨q₁, hq₁⟩ := rectRepGeneric (a := a) (K := K) (ε := ε) (H := H) (W := W)
    ha hK hε hH1 hHW
  obtain ⟨q₃, hq₃⟩ := RectRepOrder3Case (a := a) (K := K) (ε := ε) (H := H) (W := W)
    ha hK hε hH1 hHW
  obtain ⟨q₂, hq₂⟩ := RectRepOrder2Diag (a := a) (K := K) (ε := ε) (H := H) (W := W)
    ha hK hε hH1 hHW
  refine ⟨max (max q₁ q₃) q₂, ?_⟩
  intro q hq inst χ₁ ρ₁ hHlog hmin hnr hmult hcond
  have hle1 : q₁ ≤ q := by omega
  have hle3 : q₃ ≤ q := by omega
  have hle2 : q₂ ≤ q := by omega
  by_cases hχ2 : χ₁ ^ 2 = 1
  · have him : ρ₁.im ≠ 0 := by
      intro h0
      exact hnr ⟨hχ2, h0⟩
    exact hq₂ q hle2 χ₁ ρ₁ hHlog hmin hmult hχ2 him hcond
  · by_cases hχ3 : χ₁ ^ 3 = 1
    · exact hq₃ q hle3 χ₁ ρ₁ hHlog hmin hmult hχ2 hχ3 hcond
    · exact hq₁ q hle1 χ₁ ρ₁ hHlog hmin hmult hχ2 hχ3 hcond

end Work.ZeroFreeTables.OffAxis
