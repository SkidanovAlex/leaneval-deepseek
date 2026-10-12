import ChallengeDeps
import Submission.Work.BoseFixB1.BoxA2
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `PerBoxNames` — the per-box vocabulary at FS's parameters

Abbreviations for the per-box objects of `Work.BoseFixB1.perBoxFWeight_holds`, all instantiated
at FS's own parameters `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M`
and at the sliding box `A = dlBox ℓ d u` (volume `V = boxMass ℓ d u`):

* `bSide v μ`, `bD v μ`, `bM v μ` — the three parameters as functions of `μ` (and `v`);
* `bV v μ u` (`= |B(u)|`), `bA v μ u` (`= B(u)`);
* `bFlat` (`= S = ⟨n₀⟩`), `bQ` (`= n₊`), `bI` (`= ∫_{abox}Φ²`);
* `bM1` (`= ∬_{B×B}w_{1,B} = w1MassB`), `bM2` (`= ∬_{B×B}w₂`), `bA2` (`= FS's A₂`);
* `bErr` (the frozen error shape `μ²(a v)Γ·chiMass + (a v)μ`), `A0Box` (FS's unreduced `A₀`).

Nothing here is a theorem; it exists so that the per-box rungs and the final assembly can be
stated readably, and so that every rung is phrased in one and the same vocabulary.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

/-- FS's small-box side `ℓ = sideAt μ (a v)`. -/
noncomputable def bSide (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  Work.BoseBox.sideAt μ (_root_.BoseGases.a v)

/-- FS's `d` at the internal parameter `μ`. -/
noncomputable def bD (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d

/-- FS's regularity `M = mValue` at the internal parameter `μ`. -/
def bM (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℕ :=
  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M

/-- The sliding box `B(u)` at the internal parameter `μ`. -/
noncomputable def bA (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  Submission.BoseGases.dlBox (bSide v μ) (bD v μ) u

/-- The volume `|B(u)|` of the sliding box. -/
noncomputable def bV (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.SmallBoxSliding.boxMass (bSide v μ) (bD v μ) u

/-- The flat (condensate) count `S = ⟨n₀⟩ = Σᵢ∫(P_{B,i}Φ)²`. -/
noncomputable def bFlat (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.BoseFixB1S.boxFlatCount (bV v μ u) (bSide v μ) (bA v μ u) Φ

/-- The excited count `n₊ = Σᵢ∫(Q_{B,i}Φ)²`. -/
noncomputable def bQ (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.BoseFixB1S.boxQCount (bV v μ u) (bSide v μ) (bA v μ u) Φ

/-- The ordered pair-condensate count `Pc = Σ_{i≠j}∫(PᵢPⱼΦ)²`. -/
noncomputable def bPair (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.BoseFixB1S.boxPairCount (bV v μ u) (bSide v μ) (bA v μ u) Φ

/-- The `L²`-mass `I = ∫_{abox n ℓ}Φ²`. -/
noncomputable def bI (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n (bSide v μ), (Φ x) ^ 2

/-- The `w₁`-box mass `∬_{B(u)×B(u)}w_{1,B(u)}` (the fibre mass over the box). -/
noncomputable def bM1 (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.BoseFixB1S.boxM1 (bSide v μ) (bA v μ u)
    (Submission.BoseGases.wSmall1Pair h (bM v μ) (bSide v μ) (bD v μ) u)

/-- The `w₂`-box mass `∬_{B(u)×B(u)}w_{2,B(u)}` (with the `g₂` numerator). -/
noncomputable def bM2 (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.BoseFixB1S.boxM2 (bV v μ u) (bA v μ u)
    (Submission.BoseGases.wSmallPair (bM v μ) (bSide v μ) (bD v μ) u
      (Submission.BoseGases.g2 v h))

/-- FS's pairing word `A₂` at the `w₁`-box mass. -/
noncomputable def bA2 (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  boxA2 (bSide v μ) (bV v μ u) (bA v μ u)
    (Submission.BoseGases.wSmall1Pair h (bM v μ) (bSide v μ) (bD v μ) u) Φ

/-- **FS's unreduced `A₀`** at the box: `½(M₂/V²)Pc − (μS/V + ¼(μ − (S+1)/V)²)M₁`.

This is `eq:A0` of FS `final_v2.tex` (l. 3689) with `n₀/|B| = S/V` and the box masses `M₁, M₂`.
It is the object that keeps the `∬w₂`-slack: `A0Box V μ M₂ M₁ S Pc = boxQ0 − ¼(μ−(S+1)/V)²M₁`
(`boxQ0_value`), and it is *reduced* to `a0MainLocBox` by spending that slack on the square —
which is why the `A₂`-payment must be stated together with `A0Box` and never after the reduction
(`PERBOXF_ANALYSIS.md` §29.1). -/
def A0Box (V μ M₂ M₁ S Pc : ℝ) : ℝ :=
  (1 / 2) * (M₂ / V ^ 2) * Pc - (μ * (S / V) + (1 / 4) * (μ - (S + 1) / V) ^ 2) * M₁

/-- The frozen error shape `μ²(a v)Γ·chiMass + (a v)μ`, where
`Γ = (R/(ℓd))² + K_B³(μ(a v)³)^{1/2}` — i.e. `perBoxErr` divided by `‖Φ‖²`. -/
noncomputable def bErr (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  μ ^ 2 * (_root_.BoseGases.a v)
      * ((R / (bSide v μ * bD v μ)) ^ 2
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
      * Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u
    + μ * (_root_.BoseGases.a v)

/-- The box fibre mass `W = w1MassB` at FS's parameters. -/
noncomputable def bW (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  w1MassB h (bM v μ) (bSide v μ) (bD v μ) u

/-- The smooth local density `t = nCountB/chiMass`. -/
noncomputable def bt (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    {n : ℕ} (x : Submission.BoseGases.X n) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  nCountB (bM v μ) (bSide v μ) (bD v μ) u x
    / Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bD v μ) u

/-- The `F`-weight of the frozen target: `W·∫Φ²·F(t)`. -/
noncomputable def bFWeight (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  bW v h μ u * ∫ x in Submission.BoseGases.abox n (bSide v μ),
      (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ (bt v μ x u)

/-- The `χ`-windowed spectral half of `sbKin` (FS `eq:appTB`'s second term). -/
noncomputable def bSpectral (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.UBBInputs8.tBwordKinInd (bSide v μ) (bA v μ u) (bV v μ u)
    (Submission.BoseGases.chiB (bSide v μ) (bD v μ) u) (sbCut μ (_root_.BoseGases.a v)) Φ

/-- FS's gap coefficient `½ε_T(1+π⁻²)⁻¹(ℓd)⁻²`. -/
noncomputable def bGapCoeff (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  Work.SmallBoxTBWord.tbGapCoeff (bSide v μ * bD v μ)
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT

/-- The localised pair kernel with numerator `v` (the potsplit's `w`). -/
noncomputable def bKernel2w (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
  Submission.BoseGases.wSmallPair (bM v μ) (bSide v μ) (bD v μ) u v

/-- The localised pair kernel with numerator `g₂` (the potsplit's `w₂`). -/
noncomputable def bKernel2 (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
  Submission.BoseGases.wSmallPair (bM v μ) (bSide v μ) (bD v μ) u
    (Submission.BoseGases.g2 v h)

/-- The localised one-body kernel (the potsplit's `w₁`). -/
noncomputable def bKernel1 (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
  Submission.BoseGases.wSmall1Pair h (bM v μ) (bSide v μ) (bD v μ) u

/-- The potsplit's right-hand five-word sum at the localised kernels. -/
noncomputable def bQSum (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.BoseFixB1S.boxQSum (bV v μ u) (bSide v μ) μ (bA v μ u) (bKernel2w v μ u)
    (bKernel1 v h μ u) (bKernel2 v h μ u)
    (Submission.BoseGases.omC (Classical.choose h)) Φ
end Work.BoseFixB1
