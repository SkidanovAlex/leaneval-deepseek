/-
# ZeroFreeTables — `HBTheorem1_complex_h5plus`

The `h ≥ 5` half of Heath-Brown's Lemma 9.5 / Theorem 1 realness statement: if `χ₁` has order
`≥ 5` (so `χ₁` is complex and the powers `χ₁, χ₁², χ₁³, χ₁⁴` are four *distinct non-principal*
characters), and `ρ₁` is the `λ`-minimal zero of the strip `|Im| ≤ 10` over all non-principal
characters (`IsMin1WideAt 10`), then `λ₁ = lamOf q ρ₁ ≥ 0.348`.

## Status and route (see `Submission/Work/ZeroFreeTables/HB95plus/Main.lean`)

The module `Work.ZeroFreeTables.HB95plus.Main` contains the *derivation core* of this theorem:

* `c95_hP` — HB (9.15): `(3+10x)²(9+10x)² = Σ_{k≤4} c95 k·T_k(x) ≥ 0` in the Chebyshev basis;
* `main95_assembly` — (★): the pointwise positivity applied to the unit point
  `z = χ₁(n)n^{-iγ₁}` gives `0 ≤ 14379·K(β,χ₀) + 24480·K(β+iγ₁,χ₁) + 14900·K(β+2iγ₁,χ₁²)
  + 6000·K(β+3iγ₁,χ₁³) + 1250·K(β+4iγ₁,χ₁⁴)`, and the five `K`-sum bounds of HB Lemmas 5.2/5.3
  (`Ksum_principal_le`, `Ksum_le_single_of_L52_phi`, `Ksum_le_self_of_L52_phi`, all *proved*
  in this workspace) bound it above by `Σ_k c95 k·Bd k`;
* `caseA_arith`, `caseB_arith`, `lam2_arith`, `tf_numeric_consequences` — the explicit rational
  arithmetic of the two cases, consuming only the five elementary integrals of `TfNumericInputs`.

The two cases are:
* **Case A** (`orderOf (χ₁ᵏ) ≤ log q` for `k ≤ 4`, so the `L52Hyp` bound is available with
  `s = 1/8`, e.g. from `L52Hyp_ord_le`): take `λ* = λ₁`; the retained zero `ρ₁` contributes
  `F(0) = 8/9` exactly and the principal term needs only `∫e^{λ₁t}f ≤ ∫e^{0.348t}f ≤ 1.18`.
* **Case B** (some `χ₁ᵏ` of order `> log q`, `s = 1/6`): take `λ* = 0.82`.  Dropping the
  window zeros of `χ₁ᵏ` requires `λ(u) ≥ λ*`, which follows from the *second-minimum* bound
  `λ₂ ≥ 0.82`; that bound is HB Lemma 6.2 (`Commons.NumberTheory.Linnik.lemma6_2_assembly`,
  *proved*) applied to the pair `(ρ₁, ρ₂)`, `ρ₂` the `λ`-minimal zero other than `ρ₁`, again
  with `IsMin1WideAt 10` supplying the dropped zeros, and with the test function `tf72f (17/20)`.

Still to be supplied (all independent of the above): the two `L52Hyp` supplies
(`L52Hyp χ (1/8) ε δ` for `orderOf χ ≤ log q`, and `L52Hyp χ (1/6) ε δ` in general, both from
the *proved* `Work.LinnikAreas.LBoundSmall_holds`/`LBound13_holds` through `lemma3_1`), the
numeric inputs `TfNumericInputs`, and the assembly of the two cases (including the
`χ₂ ∈ {χ₁^{±1}}` case of the Lemma-6.2 application, where one of the product characters is
principal and the principal `K`-sum must be taken at a shifted point).
## Resolution

The `h ≥ 5` case has been assembled in parallel by the colleague who owns HB Lemma 9.4
(`Submission/Work/ZeroFreeTables/HB94/`, which needs this lemma as its only external input):
`Work.ZeroFreeTables.HB94.h5plus` is *exactly* the statement of this file, proved there from
`HB94.h5CaseA` (Case A: `L52Hyp` at `1/8` for characters of order `≤ log conductor`) and
`HB94.h5CaseB` (Case B: `L52Hyp` at `1/6`, the repulsion inputs `HB94.Lam0Ge`, `HB94.Lam2GeWide`)
— the derivation core used throughout (`c95_hP`, `main95_assembly`, `lam2_arith`,
`le_of_F_lt_of_le_F`, `TfNumericInputs`) is this directory's `HB95plus/Main.lean` and
`HB95plus/tf72_numeric_inputs.lean`.  The proof below is therefore a direct import of it; the
*statement* of this file is unchanged, and `#print axioms` will be clean as soon as the
colleague's remaining pending pieces (`HB94/L52supply*.lean`, `HB94/Lam0Ge.lean`,
`HB94/h5CaseB.lean`, `HB94/tf72F17_*.lean`) lose their `sorry`s.

(At the time of writing the surrounding build is also blocked by an in-progress edit of
`Submission/Work/ZeroFreeTables/HBTheorem1_complex_h4.lean`, which `HB94/h5CaseA.lean` imports.)

-/
import Mathlib
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.HB95plus.Main
import Submission.Work.ZeroFreeTables.HB94.h5plus_v2

namespace Work.ZeroFreeTables

theorem HBTheorem1_complex_h5plus : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → 5 ≤ orderOf χ₁ →
      (348 : ℝ) / 1000 ≤ Work.LinnikContract.lamOf q ρ₁ :=
  Work.ZeroFreeTables.HB94.h5plus_v2

end Work.ZeroFreeTables
