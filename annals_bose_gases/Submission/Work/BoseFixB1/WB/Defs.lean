import ChallengeDeps
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.WB.Defs` — the vocabulary of the particle window

`windowBridge_holds` (FS `thm:aprioriHLambda`, step 4) is the passage

  `AprioriHLambdaIneq v h J ⟹ WindowBridge v h J`,

i.e. from the a-priori inequality (the Appendix output `eq:aprioriRn+`, which
bounds the remainder `R_Ψ` and the excited count `n₊`) to the *particle* window
`|n − μℓ³| ≤ C·nWindow` for low box states.

This file fixes the objects along FS's own route (all at FS's parameters
`M, d = paramsAt μ (a v)`, `ℓ = sideAt μ (a v)`); each step of the proof is a
separate lemma in a sibling module.

## FS's step 4, in the corpus's (repaired) normalisation

With the cutoff mass `chiMass M ℓ d u = ∫_Λ χ_{B(u)}²` (the repair of
`FINDING_windowBridge_RPsiB_normalisation`), the local density of a state `Φ` is

  `dens u = (∫_{abox n ℓ} Φ² · nCountB u) / (‖Φ‖² · chiMass u)`,
  `nCountB u x = Σᵢ χ_{B(u)}(xᵢ)²`,

so that `R_Ψ = ∫_{I₋} wmass u · ∫_{abox n ℓ} Φ² F(nCountB u/chiMass u)` with
`F = psiWeight 1 μ` and `wmass u = ∬ w_{1,B(u)}`.  FS's step 4 is

* **Jensen** (`jensen_dens`): `R_Ψ ≥ ‖Φ‖² ∫_{I₋} wmass·F(dens)`, because `F` is
  convex on `[0,∞)`; hence the a-priori bound gives
  `∫_{I₋} (dens−μ)²/(1+dens/μ) · wmass ≤ C_A μ²aℓ³K_B³(μa³)^{1/2}`;
* **Cauchy–Schwarz** (`cs_window`): with `(t−μ) = [(t−μ)/√(1+t/μ)]·√(1+t/μ)`,
  `|∫(dens−μ)·wmass| ≤ √(∫(dens−μ)²/(1+dens/μ)·wmass)·√(∫(1+dens/μ)·wmass)`,
  and `∫(1+dens/μ)wmass = W + sig/μ` where `W = ∫_{I₋}wmass` and
  `sig = ∫_{I₋} dens·wmass`;
* **the `U`-identity** (`sig_eq`): `sig = ‖Φ‖⁻² ∫_{abox n ℓ} Φ²·Σᵢ Ufun(xᵢ)`,
  where `Ufun z = ∫_{I₋} (wmass u/chiMass u)·χ_{B(u)}(z)² du` — the corpus form of
  FS's `U`, satisfying the *exact* identity `∫_Λ Ufun = W`;
* **the `P/Q`-split** (`pq_upper`/`pq_lower`): with `Σᵢ‖PᵢΦ‖² = n‖Φ‖² − n₊`,
  `Σᵢ‖QᵢΦ‖² = n₊ = cnPlus`,
  `∫ Φ²ΣᵢUfun(xᵢ) ≤ (1+ε)(W/ℓ³)(n‖Φ‖² − n₊) + (1+ε⁻¹)(sup Ufun)·n₊`
  (and the reverse), so the particle number `n` is recovered from `sig`;
* **the window** (`final_arith`): the `ε`-split at `ε = K_B^{3/2}K_ℓ(μa³)^{1/4}`
  cancels the `n₊` term (bounded by `AprioriHLambdaIneq`) against the CS window,
  leaving `|n − μℓ³| ≤ C·μℓ³·K_B^{3/2}K_ℓ(μa³)^{1/4} = C·nWindow`.

The two kernel facts the chain needs are `wmass u ≤ C(a v)·chiMass u`
(the localised `w₁`-mass is `≍ 8πa·|B|`: Cauchy–Schwarz for the smeared kernel
together with the convolution bounds of `DLSmallKernels`) and `W ≍ 8π(a v)ℓ³`
(the corpus triple identity `dlW1Pair_triple_mass_gap` plus the `χ`-mass law on
the discarded set).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The localised one-body mass `∬ w_{1,B(u)}`** at FS's parameters. -/
def wbMass (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (u : ℝ³) : ℝ :=
  w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u

/-- **`W := ∫_{I₋} ∬ w_{1,B(u)}`**, FS's constant `𝒞 = ∫_{I₋}∬w_{1,B(u)}`
(equal to `8π(a v)ℓ³(1+o(1))`). -/
def wbW (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) : ℝ :=
  ∫ u in interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ, wbMass v h μ u

/-- **FS's `U`** (un-normalised), in the corpus's smooth-cutoff convention:
`U(z) = ∫_{I₋} (∬w_{1,B(u)}/∫χ_{B(u)}²)·χ_{B(u)}(z)² du`.  Its defining property
is the *exact* identity `∫_Λ U = W`, so that the `P`-part of the slot operator
`U(xᵢ)` is `(W/ℓ³)` times the identity. -/
def wbU (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (z : ℝ³) : ℝ :=
  ∫ u in interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
    (wbMass v h μ u / chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)
      * (chiSmallB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u z) ^ 2

/-- **The state-averaged local density** `t(u) = n(u)/|B(u)|` of FS's step 4, in
the repaired normalisation: the `χ_{B(u)}`-weighted count of `Φ` divided by the
cutoff mass and by `‖Φ‖²`. -/
def wbDens (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) (u : ℝ³) : ℝ :=
  (∫ x in abox n (sideAt μ (a v)),
      (Φ x) ^ 2 * nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x)
    / (normB v μ n Φ
        * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)

/-- **`sig := ∫_{I₋} dens·wmass`**: the `u`-average of the local density against
the localised one-body mass — FS's `⟨ΣᵢU(xᵢ)⟩`, up to the factor `W`. -/
def wbSig (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) : ℝ :=
  ∫ u in interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
    wbMass v h μ u * wbDens v h μ n Φ u

/-- FS's `ε = K_B^{3/2}K_ℓ(μa³)^{1/4}` of the final `ε`-split; it is exactly
`nWindow/(μℓ³)`. -/
def wbEps (v : ℝ³ → ℝ) (μ : ℝ) : ℝ :=
  (paramsAt μ (a v)).KB ^ (3 / 2 : ℝ) * (paramsAt μ (a v)).Kl
    * (μ * (a v) ^ 3) ^ (1 / 4 : ℝ)

end Work.BoseFixB1
