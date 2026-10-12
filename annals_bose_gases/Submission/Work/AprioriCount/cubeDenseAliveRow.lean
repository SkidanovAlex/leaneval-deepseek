import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.cubeDiluteFibre
import Submission.Work.BoseB1Cube.denseAliveAssembly
import Submission.Work.BoseB1Cube.denseAliveDeadSplit
import Submission.Work.BoseB1Cube.diluteAux
import Submission.Work.BoseFixB1S.PerBoxGapAbsorbB1
import Submission.Work.BoseFixB1S.fibSum_le_localSup
import Submission.Work.BoseFixB1S.fibSum_le_manifest
import Submission.Work.BoseFixB1S.fluctuationDefsB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.AprioriCount.cubeDenseAliveRow` — the pair-alive half of the dense band arm,
# reduced to the **window variance row**

This file holds the statement `Work.AprioriCount.cubeDenseAliveRow`
(`Work.BoseB1Cube.CubeBandArmDenseAliveRow v h R θ`, the pair-alive half of the dense band arm of
the cube per-box chapter) together with the reduction of that statement to a *single* state-level
row, `Work.AprioriCount.AliveVarWindowRow`.

## The route

`PerBoxFCube` (the cube per-`u` row) is, by `Work.BoseB1Cube.perBoxFCube_iff` and
`Work.BoseFixB1.sbPot_split`,

    c₁·W₁·𝔉 + μ·Fs ≤ ½μ²W₁·N + C·(μ²(a v)Γκ + μ(a v))·N + Ps + sbKinCube ,

with `𝔉 = flatFterm`, `Fs = flatFibSum`, `Ps = flatPairSum`, `W₁ = w1MassB`, `N = normB` and
`Γ = (R/(ℓd))² + K_B³(μ(a v)³)^{1/2}`.  The two *demand* columns are

* the **fibre column** `μ·Fs`: bounded by the PROVED manifest row
  `Work.BoseFixB1S.fibSum_le_manifest`;
* the **`F`-weight column** `c₁W₁𝔉`: bounded by the PROVED crude row
  (`𝔉 ≤ μτN + μ²N`, `Work.BoseB1Cube.flatFterm_le_mu_sq_add`) *off the density window*
  `|S/(VN) − μ| ≳ √c₁·μ`, and by the PROVED sharp row (`𝔉 ≤ N·F(τ) + 4μ²·flatVar/(τ+μ)²`,
  `Work.BoseFixB1.Up.flatFterm_sharp_row`) *inside* it; in the window the two combine to
  `𝔉 ≤ N·F(τ) + (4μ²/(τ+μ)²)·min(flatVar, Nτ(τ+μ))`;

the payers are the PROVED Jensen row `Work.BoseFixB1S.boxFlatSqJensen`, the target's own
pair-alive hypothesis (`Ps ≥ W₁·Pc/(2V²)`), the PROVED gap gate `Work.BoseFixB1.paramsGatesB`
(`Kg·(a v)·μ ≤ tbGapCoeff (ℓd) e_T`) and the PROVED deviation row (the exact slot identity
`∫Φ²·nCountB = (κ/V)S + W`, `|W| ≤ Ξ(2√(Sν)+ν)`).

Inside the window the sharp row evaluated at `τ = μ` is **exact** (`F(μ) = 0`,
`4μ²/(τ+μ)² = 1` at `τ = μ`), so the whole remaining content is the *weighted variance row*

    min (flatVar) (N·τ·(τ+μ))  ≤  C·(Ξ·τ·N/κ + (Pc − S²/N + S)/V² + μ·(a v)·ν)   (window, band),

which is `Work.AprioriCount.AliveVarWindowRow` below.  Every column of that row is payable with a
*fixed* constant: `ΞτN/κ` by the error bracket (`W₁ ≤ 8π(a v)κ`, so `c₁W₁Ξτ/κ ≤ c₁8π(a v)Ξ·μ ≤ μ(a v)`
for `c₁ ≤ 1/(8πΞ)`), `Surplus/V²` by the free half of the pair-alive payer (`c₁C ≤ 1/2`), and
`μ(a v)ν/κ` by the gap (`Kg ≥ c₁·C_w·(a v)·C`, using `W₁ ≤ C_w(a v)κ`).  The `min` — and the
window — are what make the row robust: in the crude branch (`flatVar ≥ Nτ(τ+μ)`) the `ΞτN/κ` and
`μαν/κ` columns cover the whole charge, in the flat branch (`flatVar` small) the row is trivial, and
the window excludes the off-box families (`S = 0`, `flatVar ≫ Nτ(τ+μ)`, `Surplus = 0`) which refute
every window-free form.  (The `1/κ` on the last column is *forced* by the payment side: any column
proportional to `μαν` with a state-free coefficient is multiplied by `W₁ ≤ C_w(a v)κ` in the ledger
and is therefore payable by the gap `Kg·μ(a v)·ν` only after division by `κ`.)

The row is NOT equivalent to the target: it is a statement about the *state* (`flatVar` against the
counts and the shape surplus), independent of the `F`-weight, of the fibre row and of the constant
`c₁` — the whole `F`/fibre/credit/gap ledger is done in the reduction below.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.AprioriCount

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. The box data of the target, as abbreviations -/

/-- `ℓ = sideAt μ (a v)`. -/
noncomputable abbrev bSide (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  Work.BoseBox.sideAt μ (_root_.BoseGases.a v)

/-- `d = (paramsAt μ (a v)).d`. -/
noncomputable abbrev bRatio (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d

/-- `M = (paramsAt μ (a v)).M`. -/
noncomputable abbrev bM (v : E3 → ℝ) (μ : ℝ) : ℕ :=
  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M

/-- The sliding box `B(u)`. -/
noncomputable abbrev bA (v : E3 → ℝ) (μ : ℝ) (u : E3) : Set E3 :=
  Submission.BoseGases.dlBox (bSide v μ) (bRatio v μ) u

/-- `V = |B(u)|` (the true Lebesgue volume). -/
noncomputable abbrev bV (v : E3 → ℝ) (μ : ℝ) (u : E3) : ℝ :=
  Work.SmallBoxSliding.boxMass (bSide v μ) (bRatio v μ) u

/-- `κ = chiMass M ℓ d u` (the `χ_{B(u)}²`-mass). -/
noncomputable abbrev bKap (v : E3 → ℝ) (μ : ℝ) (u : E3) : ℝ :=
  Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bRatio v μ) u

/-- `N = ‖Φ‖²`. -/
noncomputable abbrev bN (v : E3 → ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  Work.BoseBoxFix.normB v μ n Φ

/-- `S = boxFlatCount` (the localised flat count). -/
noncomputable abbrev bS (v : E3 → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  Work.BoseFixB1S.boxFlatCount (bV v μ u) (bSide v μ) (bA v μ u) Φ

/-- `Pc = boxPairCount` (the localised pair-condensate count). -/
noncomputable abbrev bPc (v : E3 → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  Work.BoseFixB1S.boxPairCount (bV v μ u) (bSide v μ) (bA v μ u) Φ

/-- `ν = n₊ = cnPlusBoxInd` (the excited count). -/
noncomputable abbrev bNu (v : E3 → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  Work.UBBInputs8.cnPlusBoxInd (bSide v μ) (bA v μ u) (bV v μ u) Φ

/-- `τ = flatTau` (the smooth box density). -/
noncomputable abbrev bTau (v : E3 → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  Work.BoseFixB1.flatTau (bM v μ) (bSide v μ) (bRatio v μ) u Φ

/-- `Var = flatVar` (the variance of the smooth box count). -/
noncomputable abbrev bVar (v : E3 → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  Work.BoseFixB1.Up.flatVar v μ Φ u

/-- `Ps = flatPairSum` (the pair sum). -/
noncomputable abbrev bPs (v : E3 → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  Work.BoseFixB1.flatPairSum v (bM v μ) (bSide v μ) (bRatio v μ) u Φ

/-- `W₁ = w1MassB` (the localised one-body mass). -/
noncomputable abbrev bW (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (u : E3) : ℝ :=
  Work.BoseFixB1.w1MassB h (bM v μ) (bSide v μ) (bRatio v μ) u

/-- The sup-bound `Ξ = chiSqBound` of the cutoff `χ_{B(u)}²` (the corpus's
`chiSupAbs·chiSmallDecay M`); a fixed constant of `v` (and of the fixed `M`). -/
noncomputable def chiSqBound (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  (Submission.BoseGases.chiSupAbs
    * Submission.BoseGases.chiSmallDecay (bM v μ)) ^ 2

/-- The shape surplus `Pc − S²/N + S` of the density slot. -/
noncomputable abbrev bSurplus (v : E3 → ℝ) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : ℝ :=
  bPc v μ Φ u - (bS v μ Φ u) ^ 2 / bN v μ n Φ + bS v μ Φ u

/-- The error bracket `μ²(a v)Γκ + μ(a v)` of the per-box row. -/
noncomputable abbrev bErr (v : E3 → ℝ) (R μ : ℝ) (u : E3) : ℝ :=
  μ ^ 2 * (_root_.BoseGases.a v)
      * ((R / (bSide v μ * bRatio v μ)) ^ 2
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
      * bKap v μ u
    + μ * (_root_.BoseGases.a v)

/-- The pair-alive hypothesis: `W₁·Pc/(2V²) ≤ Ps`. -/
noncomputable abbrev bAlive (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) : Prop :=
  bW v h μ u * bPc v μ Φ u / (2 * (bV v μ u) ^ 2) ≤ bPs v μ Φ u

/-! ## 1. The residual: the window variance row — and a WARNING

> **WARNING (to any prover of the assembly).**  This module contains the *target*
> `Work.AprioriCount.cubeDenseAliveRow` with a `sorry`.  Any proof of the assembly
> `Work.AprioriCount.aliveRow_of_varWindow` (or of anything else) that *cites*
> `Work.AprioriCount.cubeDenseAliveRow` is worthless: it is a one-line corollary of the axiom it is
> supposed to replace, and `#print axioms` of the final theorem would report `sorryAx`.  The
> assembly must be proved **directly** from the rows listed in `FINDING_cubeDenseAliveRow_session1.md`
> §1–§2 (`paramsGatesB`, `regime_sideAt_ge`, `flatPairMass_sub_w1MassB_ge_const_mul`,
> `fibSum_le_manifest`, `boxFlatSqJensen`, `flatFterm_sharp_row`, `flatFterm_le_mu_sq_add`,
> `perBoxFCube_of_ledgerDelta`, `bFrow_le_min` below) and from `hres`, never from the target. -/

/-- **The window variance row** — the single state-level input of the pair-alive dense band arm.
**Weighted form** (the form the ledger actually consumes: the charge of the `F`-weight column is
`4c₁W₁μ²·min(flatVar, Nτ(τ+μ))/(τ+μ)²`, and the weight must therefore occur on *both* sides; the
unweighted variant is FALSE — see the refuting family of
`FINDING_cubeDenseAliveRow_session1.md`).

For every admissible `μ`, every state `Φ`, every `u` on the good set with a non-thin box, in the
band `n₊ ≤ 10^{-100}·n·‖Φ‖²`, with the density window `|S/(VN) − μ| ≤ μ/2` and the pair-alive
hypothesis `W₁·Pc/(2V²) ≤ Ps`,

    4μ²·min(flatVar, N·τ·(τ+μ))/(τ+μ)²  ≤  4μ²·Ξ·τ·N/(κ(τ+μ)²) + C·(Surplus/V² + μ(a v)ν/κ) .

Here `Ξ = chiSqBound v μ` (the sup of the cutoff), `V = bV`, `κ = bKap`, `τ = bTau`,
`N = bN`, `Surplus = bSurplus` and `ν = bNu`.  The constant `C` is state-free (it may depend on
`v`, `R` and `θ`).  This is precisely session-6's `(VB*)`
(`Work.BoseFixB1.Cube.Loc.flatVar_le_minWindowBandWeighted3`) with the two payable adjustments the
ledger needs: the `Ξ`-column kept *weighted* (`4μ²/(τ+μ)² ≤ 4` makes it payable by the bracket) and
the `ν`-column divided by `κ` (so that `c₁W₁·μαν/κ ≤ c₁C_w(a v)·μαν ≤ Kg·μαν` with the PROVED
`W₁ ≤ C_w(a v)κ`). -/
def AliveVarWindowRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R θ : ℝ) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (bSide v μ)) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (bSide v μ) (bRatio v μ) μ →
        ¬ Work.BoseFixB1.IsThinBox v h μ u →
        0 < bNu v μ (Φ : Submission.BoseGases.X n → ℝ) u →
        bNu v μ (Φ : Submission.BoseGases.X n → ℝ) u
            ≤ Work.BoseB1Cube.cubeBandT * (n : ℝ) * bN v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        θ * μ < bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u →
        |bS v μ (Φ : Submission.BoseGases.X n → ℝ) u
            / (bV v μ u * bN v μ n (Φ : Submission.BoseGases.X n → ℝ)) - μ| ≤ μ / 2 →
        bAlive v h μ (Φ : Submission.BoseGases.X n → ℝ) u →
        4 * μ ^ 2 * min (bVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
              (bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
                * bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u
                * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ))
            / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ) ^ 2
          ≤ 4 * μ ^ 2 * chiSqBound v μ * bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u
                * bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
              / (bKap v μ u * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ) ^ 2)
            + C * (bSurplus v μ (Φ : Submission.BoseGases.X n → ℝ) u / (bV v μ u) ^ 2
                + μ * (_root_.BoseGases.a v)
                    * bNu v μ (Φ : Submission.BoseGases.X n → ℝ) u / bKap v μ u)

/-! ## 2. The `F`-weight row at the `min` — the proved sharp row and crude row combined -/

/-- **The `F`-weight row at the `min`.**  The PROVED sharp row
(`Work.BoseFixB1.Up.flatFterm_sharp_row`,
`𝔉 ≤ N·F(τ) + (4μ²/(τ+μ)²)·flatVar`) and the PROVED crude row
(`Work.BoseB1Cube.flatFterm_le_mu_sq_add`, `𝔉 ≤ μτN + μ²N`, equivalent to
`𝔉 ≤ N·F(τ) + (4μ²/(τ+μ)²)·Nτ(τ+μ)` through the identity
`N·μ(τ−μ)²/(τ+μ) + 4μ²·Nτ(τ+μ)/(τ+μ)² = N(μτ + μ²)`) combine, because both right-hand sides are
upper bounds for `𝔉` and the map `V ↦ N·F(τ) + (4μ²/(τ+μ)²)·V` is monotone, into

    𝔉 ≤ N·F(τ) + (4μ²/(τ+μ)²)·min(flatVar, N·τ·(τ+μ)) .

This is the row the ledger consumes; it is `V`-free (no variance row is used to *produce* it — only
the two proved `F`-rows and the τ-identity). -/
theorem bFrow_le_min {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {ε₀ μ : ℝ}
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (bSide v μ)) (u : E3) :
    Work.BoseFixB1.flatFterm (bM v μ) (bSide v μ) (bRatio v μ) μ u
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
          * (μ * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u - μ) ^ 2
              / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ))
        + 4 * μ ^ 2 / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ) ^ 2
          * min (bVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
              (bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
                * bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u
                * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ)) := by
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hτid : (∫ x in Submission.BoseGases.abox n (bSide v μ),
        (Φ : Submission.BoseGases.X n → ℝ) x ^ 2 *
          Work.BoseFixB1.nCountB (bM v μ) (bSide v μ) (bRatio v μ) u x
          / Work.SmallBoxSliding.chiMass (bM v μ) (bSide v μ) (bRatio v μ) u)
      = bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u
          * bN v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [← Work.BoseB1Cube.DiluteAux.flatScountB_div_eq_flatTau_mul_normB (v := v) (μ := μ)
      (n := n) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) (Work.BoseFixB1.adm_ell_pos hAdm)
      Φ.contDiff.continuous u]
    simp only [Work.BoseFixB1.flatScountB, MeasureTheory.integral_div]
  have hsharp := Work.BoseFixB1.Up.flatFterm_sharp_row (v := v) h hAdm Φ u
  have hcrude := Work.BoseB1Cube.flatFterm_le_mu_sq_add (M := bM v μ) (ℓ := bSide v μ)
    (d := bRatio v μ) (μ := μ) hμ (Φ : Submission.BoseGases.X n → ℝ) Φ.contDiff.continuous u
  rw [hτid] at hcrude
  have hN0 : 0 ≤ bN v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg (v := v) (μ := μ) (n := n) (Φ : Submission.BoseGases.X n → ℝ)
  have hkey : (1 / 2 : ℝ) * 0 = 0 := by norm_num
  -- the two right-hand sides, with `F(τ) = μ(τ−μ)²/(τ+μ)`
  have hsh : Work.BoseFixB1.flatFterm (bM v μ) (bSide v μ) (bRatio v μ) μ u
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
            * (μ * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u - μ) ^ 2
                / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ))
          + 4 * μ ^ 2 / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ) ^ 2
            * bVar v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
    simpa only [Work.BoseFixB1.flatFterm, Work.BoseFixB1.flatTau, Work.BoseBoxFix.normB,
      Work.BoseKinLoc.sqNormB, Work.BoseFixB1.pM, Work.BoseFixB1.pL, Work.BoseFixB1.pD,
      bN, bTau, bVar, bM, bSide, bRatio, Work.BoseFixB1.Up.flatVar] using hsharp
  have hcr : Work.BoseFixB1.flatFterm (bM v μ) (bSide v μ) (bRatio v μ) μ u
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
            * (μ * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u - μ) ^ 2
                / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ))
          + 4 * μ ^ 2 / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ) ^ 2
            * (bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
                * bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u
                * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ)) := by
    have hden : bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ ≠ 0 := by
      have hτ0 : 0 ≤ bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
        rw [bTau, Work.BoseFixB1.flatTau]
        exact div_nonneg
          (by
            rw [Work.BoseFixB1.flatScountB]
            exact MeasureTheory.integral_nonneg fun x =>
              mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
          (mul_nonneg (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _) hN0)
      positivity
    have e : bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
            * (μ * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u - μ) ^ 2
                / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ))
          + 4 * μ ^ 2 / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ) ^ 2
            * (bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
                * bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u
                * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ))
        = μ * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u
              * bN v μ n (Φ : Submission.BoseGases.X n → ℝ))
          + μ ^ 2 * bN v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
      field_simp
      ring
    rw [e]
    exact hcrude
  have hw : 0 ≤ 4 * μ ^ 2 / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ) ^ 2 := by
    have hτ0 : 0 ≤ bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      rw [bTau, Work.BoseFixB1.flatTau]
      exact div_nonneg
        (by
          rw [Work.BoseFixB1.flatScountB]
          exact MeasureTheory.integral_nonneg fun x =>
            mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
        (mul_nonneg (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _) hN0)
    positivity
  refine le_trans (le_min hsh hcr) ?_
  set X : ℝ := bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
      * (μ * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u - μ) ^ 2
          / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ)) with hX
  set w : ℝ := 4 * μ ^ 2 / (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ) ^ 2 with hwdef
  set Mv : ℝ := bN v μ n (Φ : Submission.BoseGases.X n → ℝ)
      * bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u
      * (bTau v μ (Φ : Submission.BoseGases.X n → ℝ) u + μ) with hM
  have hw0 : 0 ≤ w := hw
  rcases le_total (bVar v μ (Φ : Submission.BoseGases.X n → ℝ) u) Mv with h | h
  · rw [min_eq_left h, min_eq_left (by nlinarith [mul_le_mul_of_nonneg_left h hw0])]
  · rw [min_eq_right h, min_eq_right (by nlinarith [mul_le_mul_of_nonneg_left h hw0])]

theorem cubeDenseAliveRow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (θ : ℝ) :
    Work.BoseB1Cube.CubeBandArmDenseAliveRow v h R θ := by sorry

end Work.AprioriCount
