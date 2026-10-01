/-
# ZeroFreeTables/OffAxis — `RectLam3`

**HB Lemma 10.3 (`λ₃ ≥ 6/7 − 1/1000`) at rectangle height `L`** (with the round constant
`856/1000`), in the form needed by the off-axis assembly `RectCertS`: for the height-`L`
numbering `IsRectStrip L χ₁ ρ₁` there is a character `χ₂` such that every zero at height `≤ L`
of a character outside the two conjugate pairs `{χ₁^{±1}}`, `{χ₂^{±1}}` has `λ ≥ 856/1000`.

The proof is the *selection* argument of HB §6/§9 (`RectC_Lam3`, `Rect10_3H`): if
`λ₁ ≥ 856/1000` the witness is `χ₁`; if there is no zero of `λ < 856/1000` outside `{χ₁^{±1}}`
the witness is `χ₁` again; otherwise one takes for `χ₂` a pair realising the minimum of `λ`
outside `{χ₁^{±1}}` (`exists_min_lam_avoiding_H`), and any further pair outside
`{χ₁^{±1}, χ₂^{±1}}` with `λ < 856/1000` would give three conjugate pairs whose `λ`'s are
successive minima, contradicting HB Lemma 10.3 at rectangle height `L`.

The assembly is `OffAxis/Lead/RectLam3Parts.rectLam3_of_near`, with the near-case engine
`OffAxis/Lead/Rect10_3Near` (`Rect10_3NearStmt`) as its hypothesis.  That module also contains

* `rect10_3H_of_cases` — the off-axis route `1 < |ρ₁.im|`, `λ₁ ≥ 348/1000` (HB §10 Lemmas 10.1
  and 10.2, from `Rect10_3H_F1` and the `F2` case `rect10_3FarF2`);
* the `IsRectStrip L ⟹ IsRectMin L` upgrade (`isRectMin_of_isRectStrip`, via
  `WideDefs.isMinWideAt_of_isRectStrip`, using `λ₁ < 856/1000 < 2`).

The near-case engine `OffAxis/Lead/Rect10_3Near` covers the remaining configurations
(`|ρ₁.im| ≤ 1`, or the small-`λ₁` case `λ₁ ≤ 348/1000`): HB §10 with the `P₃`/all-real cases
included.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.OffAxis.Lead.RectLam3Parts
import Submission.Work.OffAxis.Lead.Rect10_3Near

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

/-- **HB Lemma 10.3 at rectangle height `L` (`λ₃ ≥ 856/1000`).** -/
theorem RectLam3 : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), Work.ZeroFreeTables.IsRectStrip L χ₁ ρ₁ →
    Work.ZeroFreeTables.Lam3BoundH L χ₁ (856/1000) :=
  Work.ZeroFreeTables.OffAxis.Lead.rectLam3_of_near Work.OffAxis.Lead.Rect10_3Near

end Work.ZeroFreeTables.OffAxis
