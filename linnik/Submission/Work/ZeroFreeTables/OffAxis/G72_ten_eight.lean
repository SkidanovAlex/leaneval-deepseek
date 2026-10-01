import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.ZeroFreeTables.OffAxis.tf72Fc_ten_eight

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables

/-- **HB (10.8) at `lam = 6/7`, in scale-free form.**  With `G72 w = ∫₀² e^{-wy} g72 y dy`,
`g72 y = (1/30)(2-y)³(4+6y+y²)` (HB Lemma 7.2's weight; the Laplace transform of HB's test function
of parameter `lam` is `z ↦ G72 (z/lam)`, and then `f(0) = 16 lam/15`), one has for all `s ∈ [0,1]`,
`σ ≥ 0`:

    Re (G72 (-s + iσ)) - 2 Re (G72 (iσ)) ≤ 16/105 .

This is Heath-Brown's inequality (10.8), `Re (F(-lam₁ + iµ)) - 2 Re (F(iµ)) ≤ f(0)/6`, at
`lam = 6/7`: with `s = lam₁/lam ∈ [0,1]`, `σ = µ/lam` the left side is unchanged and the right
side is `(16 lam/15)/6 = 8 lam/45 ≤ 8·(6/7)/45 = 16/105`.  (Both sides are even in `σ`, so `σ ≥ 0`
is no loss; the sharp numerical truth is that the left side is `≤ 0`, cf. `G72 0 = 8/9`,
`G72 (-1) = 8/5`.)  This is the numerical core of the `F`-method cases of HB §10 (Lemma 10.2), the
term `-2 Re (G72 (iσ))` being what remains after the three-character combination is bounded. -/
theorem G72_ten_eight : ∀ s σ : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ σ →
    (G72 (((-s : ℝ) : ℂ) + (σ : ℂ) * Complex.I)).re
      - 2 * (G72 ((σ : ℂ) * Complex.I)).re ≤ 16/105 :=
  fun s σ hs hs1 hσ => Isub_le_ten_eight s σ hs hs1 hσ

end Work.ZeroFreeTables.OffAxis
end

