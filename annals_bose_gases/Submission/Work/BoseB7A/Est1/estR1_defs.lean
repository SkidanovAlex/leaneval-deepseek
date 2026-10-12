import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseB7A.Est1.Algebra
import Submission.Work.BoseB7A.NWindow_bp_N_le
import Submission.Work.BoseB7A.NWindow_linear_bound
import Submission.Work.BoseB7A.NWindow_shift
import Submission.Work.BoseB7A.PH_subset_PHq_sub
import Submission.Work.BoseB7A.Prep
import Submission.Work.BoseB7A.kernel_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Est1.estR1_defs` — the objects of the `R1` estimate

Piece **C** of FS `eq:EstimateQ3Tilde1` (FS ll. 3300–3320): the leftover

`R1 = (z/ℓ³) Σ_{s,k} γ_{sk}β_{sk} ( κB(b_k†+b_k) + κA(b_{s-k}†+b_{s-k}) - κC(ã_{-s}†+ã_{-s}) )`

is a *linear word*, and its three families are estimated separately:

* `Wta` — the `σ₂`-word `κC(ã_{-s}†+ã_{-s})` (θ-modes), charged to the **energy
  gap** `(b/800)ℓ⁻²n₊` by the `ε_s`-trick.  The coefficients are collected per
  mode `s` in `cTa`, and the error bracket is `costTa`.
* `Wb1` — the `σ₁`-word `κB(b_k†+b_k)`, charged to the **kinetic reserve**
  `(𝓁²/4)⟨dNumOpR(P_H^q)⟩` by Cauchy–Schwarz in the weights `D_k`; the error
  bracket is `costB2`.
* `Wb2` — the `σ₁`-word `κA(b_{s-k}†+b_{s-k})`, the same with the mode `s-k`;
  the error bracket is `costB3`.

The `s`-sums are restricted to `suppL E = {s ∈ excited Mode : f_L(s) ≠ 0}`
(all coefficients carry a factor `f_L(s)`, so this does not change the word),
which is what makes the mode counts finite: `#suppL ≤ K₀(K_ℓK_L)³`
(`Q3Kernel.count_PL`).

## Contents

* `suppL` and its elementary properties.
* `cTa`, `Wta`, `Wb1`, `Wb2` — the three words.
* `Mc`, `costTa`, `costB2`, `costB3` — the error brackets.
-/

noncomputable section

open scoped BigOperators

set_option linter.unusedVariables false

namespace Work.BoseB7A

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The low-momentum index set -/

/-- The modes `s` of the low-momentum localisation that are actually seen:
`suppL E = {s ∈ excited Mode : f_L(s) ≠ 0}`. -/
def suppL (E : Q3Env Mode) : Finset Mode := (excited Mode).filter (fun s => E.fL s ≠ 0)

theorem mem_suppL {E : Q3Env Mode} {s : Mode} :
    s ∈ suppL E ↔ s ∈ excited Mode ∧ E.fL s ≠ 0 := Finset.mem_filter

theorem suppL_ne_zero {E : Q3Env Mode} {s : Mode} (hs : s ∈ suppL E) : s ≠ 0 :=
  (Finset.mem_erase.mp (mem_suppL.mp hs).1).1

theorem suppL_fL_ne_zero {E : Q3Env Mode} {s : Mode} (hs : s ∈ suppL E) : E.fL s ≠ 0 :=
  (mem_suppL.mp hs).2

theorem suppL_subset {E : Q3Env Mode} : suppL E ⊆ excited Mode := Finset.filter_subset _ _

/-- `#suppL ≤ K₀(K_ℓK_L)³` (`Q3Kernel.count_PL`). -/
theorem suppL_card_le {K₀ : ℝ} {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode}
    (hK : Q3Kernel K₀ F T E) : ((suppL E).card : ℝ) ≤ K₀ * (E.Kl * E.KL) ^ 3 :=
  hK.count_PL

/-- `Σ_{s ∈ suppL} f_L(s) ≤ #suppL` (`0 ≤ f_L ≤ 1`). -/
theorem sum_suppL_fL_le_card {K₀ : ℝ} {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode}
    (hK : Q3Kernel K₀ F T E) :
    ∑ s ∈ suppL E, E.fL s ≤ ((suppL E).card : ℝ) := by
  have h := Finset.sum_le_sum (fun s (_ : s ∈ suppL E) => hK.fL_le_one s)
  simpa using h

/-! ## 2. The three words of `R1` -/

/-- The `s`-coefficient of the θ-word `κC(ã_{-s}†+ã_{-s})`. -/
def cTa (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (s : Mode) : ℝ :=
  (E.z / E.ell ^ 3) * ∑ k ∈ F.PHset E, (gA E s k * bA E s k * (-(kC E s k)))

/-- **Family 1**: the `σ₂`-word `-(z/ℓ³)Σ_{s,k}γβκC·(ã_{-s}†+ã_{-s})`, collected
per mode `s`. -/
def Wta (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  ∑ s ∈ suppL E, (cTa F T E s) • (T.taDag (-s) + T.ta (-s))

/-- **Family 2**: the `σ₁`-word `(z/ℓ³)Σ_{s,k}γβκB·(b_k†+b_k)`. -/
def Wb1 (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  ∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
    ((E.z / E.ell ^ 3) * (gA E s k * bA E s k * kB T E s k)) •
      (F.bOpDag E.alpha k + F.bOp E.alpha k)

/-- **Family 3**: the `σ₁`-word `(z/ℓ³)Σ_{s,k}γβκA·(b_{s-k}†+b_{s-k})`. -/
def Wb2 (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  ∑ s ∈ suppL E, ∑ k ∈ F.PHset E,
    ((E.z / E.ell ^ 3) * (gA E s k * bA E s k * kA T E s k)) •
      (F.bOpDag E.alpha (s - k) + F.bOp E.alpha (s - k))

/-! ## 3. The error brackets -/

/-- The uniform bound on the θ-word coefficients
`Mc = (1+K₀²)·1024|z|K₀³𝓁²K_HK_L√t·ρ_z a`, so that
`|cTa F T E s| ≤ Mc·f_L(s)` for every `s`.

The pointwise bound uses `Σ_k|Ŵ₁(k)α_k| ≤ 2ρ_zK₀aℓ³`
(`Work.BoseB7A.sum_abs_W1_alpha_le`, from `Q3Kernel.sum_W1sq` and `A_ge`/`B_eq`):
**no count of the `P_H` modes is needed** — the multiplicity is compensated by the
`ℓ²`-weight `1/‖kmom k‖²` in `sum_W1sq`, so `Q3Kernel` is enough. -/
def Mc (K₀ : ℝ) (E : Q3Env Mode) (hv : FSParamsView E) : ℝ :=
  (1 + K₀ ^ 2) *
    (1024 * |E.z| * K₀ ^ 3 * E.lille ^ 2 * E.KH * E.KL * Real.sqrt hv.t * E.rho * E.aScat)

/-- The error bracket of the θ-word:
`costTa = (800/b)·ℓ²·K₀·(K_ℓK_L)³·Mc²`.

Here `ℓ = E.ell` is the **box side** (`side E.Kl E.mu E.aScat`), *not* the Landau
ratio `𝓁 = E.lille`: the `ε`-trick against the gap term `(b/800)ℓ⁻²n₊` produces
`ℓ²·Mc·Σ_s|c_s|`, and `Σ_s|c_s| ≤ Mc·#suppL ≤ Mc·K₀(K_ℓK_L)³` (`count_PL`).
(With `𝓁²` in place of `ℓ²` the bracket would be smaller than the coefficients
whenever `a` is small — `ℓ²/𝓁² = (μa³)K_H⁴(μa)/K_ℓ²` is unbounded — and the
statement would be false; see the `2`-state test `(★)`
`|c_s|² ≤ costTa·(costTa + (b/800)ℓ⁻²)`, which holds here because
`costTa·(b/800)ℓ⁻² = K₀(K_ℓK_L)³Mc² ≥ Mc²` as soon as `K₀(K_ℓK_L)³ ≥ 1`.) -/
def costTa (K₀ : ℝ) (E : Q3Env Mode) (hv : FSParamsView E) : ℝ :=
  (800 / E.b) * E.ell ^ 2 * K₀ * (E.Kl * E.KL) ^ 3 * (Mc K₀ E hv) ^ 2

/-- The error bracket of the `κB`-word (`b_k`). -/
def costB2 (K₀ : ℝ) (E : Q3Env Mode) : ℝ :=
  512 * 64 ^ 6 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2 * E.rho * E.aScat

/-- The error bracket of the `κA`-word (`b_{s-k}`). -/
def costB3 (K₀ : ℝ) (E : Q3Env Mode) : ℝ :=
  2048 * 64 ^ 6 * K₀ ^ 11 * (E.Kl * E.KL) ^ 6 * E.lille ^ 4 * (eta E) ^ 2 * E.rho * E.aScat

end Est1

end Work.BoseB7A
