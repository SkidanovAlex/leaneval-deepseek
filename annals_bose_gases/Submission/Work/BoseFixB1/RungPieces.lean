import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxA2
import Submission.Work.BoseFixB1.PairBlockCore
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.RungPieces` — the vocabulary of the corrected rung-4 decomposition

**STATUS / WHY THIS FILE EXISTS** (see `FINDING_boxA0A2Rung_mechanics.md` §7, ADDENDUM):

The target `Work.BoseFixB1.boxA0A2Rung` is (machine-verified to `1e-16` and by the two independent
computations `Submission/Work/BoseFixB1S/boxPairManifestSumB1S` + `ScratchB1S/c3/direct.py`) equal
to the nonnegativity of the *(T′)-slack*

    (T′)  2μP + μQ + boxA2 + (1/2)(M₁/V²)(S²−S)  ≤  Σig + M₁·G + C·a(v)·(μ+S/V)·n₊ ,

where (all at the sliding box `A = dlBox ℓ d u`, `V = boxMass ℓ d u`, `w = wSmallPair M ℓ d u v`,
`w₁ = wSmall1Pair h M ℓ d u`, `fib = w1Fibre ℓ w₁`, `S = boxFlatCount`, `n₊ = boxQCount`)

* `P  = Σᵢ∫(QᵢΦ)(PᵢΦ)·fib(xᵢ)`  (`rungP`),  `Q = Σᵢ∫(QᵢΦ)²·fib(xᵢ)` (`rungQ`),
* `boxA2 = Σ_p ∫(P_iP_jΦ)(Q_jQ_iΦ)w₁` (the corpus's `Work.BoseFixB1.boxA2`, the *pairing* debit),
* `Σig = Σ_{i≠j}∫1_A(xᵢ)1_A(xⱼ)Φ²w(xᵢ,xⱼ)`  (`rungPair`, the *pair energy*, the main payer),
* `G = ¼(S/V−μ)² + (S/V+μ)/(2V) + 1/(4V²)`  (`rungG`),  `M₁ = boxM1 ℓ A w₁`,
* the *slack* `(1/2)(M₁/V²)(S²−S)` (`rungSlack`) and the *credit rate* `μ + S/V` (`rungRate`).

The previous session's split (delegated as `boxQ1n0_sqrt_joint_norm` / `rungXB_le_block_add_credit`)
is **wrong**: it asked the credit `Ca(μ+S/V)n₊` to pay `2μP + μQ` out of `M₁G`, which is *false* —
with the (corpus-proved) `Work.BoseFixB1S.boxPQ_abs_bounds` bound
`|P| ≤ C a √(n₊ (M₁/V) S)`, `Q ≤ C a n₊` the required constant there grows like `√(S/B)`, unbounded;
the payer of the μ-line in this regime is the **pair energy `Σig`**, exactly as in FS's proof
("*using the positivity of w_B*").

Nothing here is a theorem; the definitions exist so that the (corrected) analytic pieces can be
stated in one vocabulary.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false

/-- The μ-cross object `P = Σᵢ∫(QᵢΦ)(PᵢΦ)·w₁-fibre(xᵢ)` (so that `boxQ1`'s μ-line is `−2μP`). -/
noncomputable def rungP {N : ℕ} (V ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N ℓ,
    (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A i Φ x)
      * w1Fibre ℓ w1 (x i)

/-- The excited μ-object `Q = Σᵢ∫(QᵢΦ)²·w₁-fibre(xᵢ)`. -/
noncomputable def rungQ {N : ℕ} (V ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∫ x in abox N ℓ,
    (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * w1Fibre ℓ w1 (x i)

/-- The **pair energy** `Σig = Σ_{i≠j}∫1_A(xᵢ)1_A(xⱼ)Φ²·w(xᵢ,xⱼ)` — the main *payer* of the
corrected (T′)-balance (FS: "*using the positivity of `w_B`*"). -/
noncomputable def rungPair {N : ℕ} (ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ) : ℝ :=
  ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
    (A.indicator (fun _ => (1 : ℝ)) (x p.1) * A.indicator (fun _ => (1 : ℝ)) (x p.2))
      * (Φ x) ^ 2 * w (x p.1) (x p.2)

/-- The `A₀`-defect `G = ¼(S/V−μ)² + (S/V+μ)/(2V) + 1/(4V²)`. -/
noncomputable def rungG (V μ S : ℝ) : ℝ :=
  (1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2)

/-- The pair-condensate **slack** `(1/2)(M₁/V²)(S²−S)`. -/
noncomputable def rungSlack (V M1 S : ℝ) : ℝ :=
  (1 / 2) * (M1 / V ^ 2) * (S ^ 2 - S)

/-- The **credit rate** `μ + S/V`. -/
noncomputable def rungRate (V μ S : ℝ) : ℝ := μ + S / V

/-- The **pair-condensate block** `pcb = ½(M₂/V²)·Pc − rungSlack`.

It is the `≥ 0` payer produced by the corpus's `boxQ0_value` + the `A₀`-slack
(`half_pc_slack_nonneg`, from `hcS2` and `M₁ ≤ M₂`), and it is the payer of the second half
of the rung-4 core (see `RungAssembly.lean` / `FINDING_boxA0A2Rung_mechanics.md`). -/
noncomputable def rungPCBlock (V M2 M1 S Pc : ℝ) : ℝ :=
  (1 / 2) * (M2 / V ^ 2) * Pc - rungSlack V M1 S

/-- The **`ω`-cross** of the potsplit (FS's surviving term of `eq:Q3+Q4CS`):
`Σ_p∫(P_{p.1}Q_{p.2}Φ)(P_{p.1}P_{p.2}Φ)(w·ω)(x_{p.1},x_{p.2})`, i.e. the pairing `boxA2` with the
kernel `w₁` replaced by `w·ω = w − w₁`.  This identifies the pairing with the `ω`-cross — the
structural reason why the debits and the payers of the rung-4 core cannot be decoupled. -/
noncomputable def rungOmCross {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : X N → ℝ) : ℝ :=
  ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
    (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
      * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
      * (w (x p.1) (x p.2) - w1 (x p.1) (x p.2))

end Work.BoseFixB1
