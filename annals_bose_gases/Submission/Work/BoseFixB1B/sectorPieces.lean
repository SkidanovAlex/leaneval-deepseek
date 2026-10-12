import ChallengeDeps
import Submission.Work.BoseFixB1B.sectorCountDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.sectorPieces` — the three pieces of `SectorCountSmallbox`

Written by the holder of `Submission/Work/BoseFixB1B/sectorCountSmallbox.lean`.

## What is here, and why

`Work.BoseFixB1B.SectorCountSmallbox v h` (the count-indexed core of FS `thm:smallbox` at the
sliding box `B(u)`; `Submission/Work/BoseFixB1B/sectorCountDefs.lean`) is FS's per-count
operator bound for an in-box, normalised `n`-particle state:

    (c·F(n/PBV) − (½−c)μ²)·PBW − C(μ²aΓ_B·PBW + μa) ≤ fWord μ n u Φ ,

with `F = psiWeight 1 μ`, `PBV = chiMass M ℓ d u = ∫χ_{B(u)}²` (the `χ_B²`-mass — the normaliser
of the target), `PBW = ∬w_{1,B(u)}`, `Γ_B = K_B³(μa³)^{1/2}`, and `fWord` the frozen sliding word
below.

FS prove it (`final_v2.tex` 3907–4065) by the **two-arm regrouping**: write `n = m n' + n''`
with the group density `n'/|B|` in a *window* `[C_nμ, (C_n+1)μ]`, bound the `n''`-arm by the
`A₀`-square `¼(n''/|B| − μ)²∬w_{1,B}`, bound each of the `m` groups of `n'` particles by the
positive `(1/18)μ(n'/|B|)∬w_{1,B}` (which follows from the same square at the window density), and
finish with the arithmetic `¼(x''−μ)² + (1/18)μ(ρ−x'') ≥ c(ρ−μ)²/(1+ρ/μ⁻¹)`.

Because the corpus's target reads the *density* at the `χ_B²`-mass `PBV` (not at the box volume,
as FS do), the regrouping is available only when `μ·PBV ≳ 1` (otherwise no group of positive
particle number has its density in the window).  The low-`PBV` regime is therefore separated as a
third piece.  This gives **three pieces**, whose statements are mutually independent:

* `LowMassAt v h ε₀ c C` — the **low-mass arm** (`μ·PBV ≤ 1/5`): the target's own inequality;
* `WindowAt v h ε₀ c C Cw` — the **window (one-arm) bound** (`n ≤ Cw·μ·PBV`, window constant
  `Cw ≥ 10`): the `A₀`-square form `(¼(n/PBV − μ)² − (½−c)μ²)·PBW − C(…) ≤ fWord`;
* `TwoArmAt v h ε₀ c C Cw Cb` — the **regrouping step** (`μ·PBV ≥ 1/5`), *given* the window
  bound: there is a partition `n = m n' + n''` (`1 ≤ m`, `n'' < n'`, group density in
  `[4μ, 9μ]`) for which the two-arm form
  `(¼(n''/PBV − μ)² + (1/18)μ((n−n'')/PBV) − (½−c)μ²)·PBW − Cb(…) ≤ fWord`
  holds.

The **assembly** (in `sectorCountSmallbox.lean`, the holder's own work) is then the case split
`μ·PBV ≤ 1/5` / `n ≤ Cw·μ·PBV` / else, the observation that at `c ≤ 1/4` FS's weight is
dominated by the `A₀`-square (`Work.BoseFixB1.perBoxF_F_weight_le`), so that the window arm needs no
arithmetic at all, and the pure-real inequality `c·F(ρ) ≤ ¼(ρ''−μ)² + (1/18)μ(ρ−ρ'')` valid for
`c ≤ 1/20` and `ρ − ρ'' ≥ 4μ`.

## Structural notes

* `LowMassAt` and `WindowAt` are the *only* places where the analytic per-box content (FS's
  `lm:appinteractionestimate` + `lm:appbogolubov` + `eq:appgapestimate` at the box projections) is
  consumed; both are stated at an in-box normalised state and at the frozen word.
* `TwoArmAt` contains only (i) the **fibre/regrouping bookkeeping** (Fubini over the `m+1` groups
  of a slot partition, the positivity of the dropped inter-group pairs, the homogeneity of the word
  in the fibre mass, the mass identity `∫_y m_g(y)dy = 1`) and (ii) FS's "`C_n` large" step
  `¼(ρ'−μ)² − (½−c)μ² ≥ (1/18)μρ'` at the group density `ρ' ≥ 4μ`.  It is stated *conditionally*
  on `WindowAt` (which supplies the per-group bound) and its partition is asserted only in the
  regime `μ·PBV ≥ 1/5`, where a group of positive count with density in `[4μ, 9μ]` exists.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The frozen sliding word** of the target at `(μ, n, u, Φ)`:
FS's per-box word `𝒯_{B(u)} + (the potential word)` at the sliding box `B(u) = PBB v μ u`,
the localised kernels and the FS parameters (`PBℓ, PBd, PBM, PBeT, sbCut`). -/
noncomputable def fWord (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ) (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
      (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u Φ
    + Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u Φ

/-- **The in-box hypothesis** of the target: a.e. every particle of the state lies in `B(u)`. -/
def fSupp (v : E3 → ℝ) (μ : ℝ) (n : ℕ) (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) : Prop :=
  ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (PBℓ v μ))),
    Φ x ≠ 0 → ∀ i : Fin n, x i ∈ PBB v μ u

/-- **The normalisation hypothesis** of the target: `∫_{abox n ℓ}Φ² = 1`. -/
def fNorm (v : E3 → ℝ) (μ : ℝ) (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) : Prop :=
  (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (Φ x) ^ 2) = 1

/-- The target's left-hand side at parameter `c` and error constant `C`. -/
noncomputable def fLHS (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (c C μ : ℝ) (n : ℕ) (u : E3) : ℝ :=
  (c * psiWeight 1 μ ((n : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
    - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u + μ * (_root_.BoseGases.a v))

/-- **Piece 0 — the low-mass arm** (`μ·PBV ≤ 1/5`): the target's own inequality.

In this regime the regrouping of FS is unavailable (no group of positive particle number can have
its density `n'/PBV` in the window `[4μ, 9μ]` when `μ·PBV < 1/4`); the content is the same analytic
per-box estimate, used directly at every count. -/
def LowMassAt (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (ε₀ c C : ℝ) : Prop :=
  0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 50 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3),
        u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        fSupp v μ n u (Φ : Submission.BoseGases.X n → ℝ) →
        fNorm v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        μ * PBV v μ u ≤ 1 / 5 →
        fLHS v h c C μ n u ≤ fWord v h μ n u (Φ : Submission.BoseGases.X n → ℝ)

/-- **Piece 1 — the window (one-arm) bound**: FS's per-group estimate at the frozen box.

For every in-box normalised state whose count density `n/PBV` is at most `Cw·μ` (`Cw ≥ 10`),
the `A₀`-square form holds. -/
def WindowAt (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (ε₀ c C Cw : ℝ) : Prop :=
  0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 50 ∧ 0 ≤ C ∧ 10 ≤ Cw ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3),
        u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        fSupp v μ n u (Φ : Submission.BoseGases.X n → ℝ) →
        fNorm v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        (n : ℝ) ≤ Cw * μ * PBV v μ u →
        (1 / 4 * ((n : ℝ) / PBV v μ u - μ) ^ 2 - (1 / 2 - c) * μ ^ 2) * PBW h μ u
          - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
              + μ * (_root_.BoseGases.a v))
        ≤ fWord v h μ n u (Φ : Submission.BoseGases.X n → ℝ)

/-- **Piece 2 — the regrouping bound**, *given* `WindowAt`, in the regime `μ·PBV ≥ 1/5`.

There `Cb ≥ 0` such that for every in-box normalised state there is a partition
`n = m n' + n''` with `1 ≤ m`, `n'' < n'` and group density `4μ ≤ n'/PBV ≤ 9μ` for which the
two-arm form holds.  (The partition exists whenever `n > Cw·μ·PBV ≥ 10·(1/5) = 2`:
take `n' = ⌈4μ·PBV⌉`, `m = ⌊n/n'⌋`; then `n'/PBV ≤ 4μ + 1/PBV ≤ 9μ` because `1 ≤ 5μ·PBV`.) -/
def TwoArmAt (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (ε₀ c C Cw Cb : ℝ) : Prop :=
  0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 50 ∧ 0 ≤ C ∧ 10 ≤ Cw ∧ 0 ≤ Cb ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3),
        u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        fSupp v μ n u (Φ : Submission.BoseGases.X n → ℝ) →
        fNorm v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        1 / 5 ≤ μ * PBV v μ u →
        Cw * μ * PBV v μ u < (n : ℝ) →
        ∃ m n' n'' : ℕ, n = m * n' + n'' ∧ n'' < n' ∧ 1 ≤ m ∧
          4 * μ ≤ (n' : ℝ) / PBV v μ u ∧ (n' : ℝ) / PBV v μ u ≤ 9 * μ ∧
          (1 / 4 * ((n'' : ℝ) / PBV v μ u - μ) ^ 2
              + (1 / 18) * μ * (((n : ℝ) - (n'' : ℝ)) / PBV v μ u)
              - (1 / 2 - c) * μ ^ 2) * PBW h μ u
            - Cb * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                + μ * (_root_.BoseGases.a v))
          ≤ fWord v h μ n u (Φ : Submission.BoseGases.X n → ℝ)

/-- **Piece 0 (exists-form)**: the low-mass arm holds for some parameters. -/
def FrozenLowMass (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ c C : ℝ, LowMassAt v h ε₀ c C

/-- **Piece 1 (exists-form)**: the window bound holds for some parameters. -/
def FrozenWindow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ c C Cw : ℝ, WindowAt v h ε₀ c C Cw

/-- **Piece 2**: the regrouping step, from the window bound. -/
def FrozenTwoArm (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∀ ε₀ c C Cw : ℝ, WindowAt v h ε₀ c C Cw → ∃ Cb : ℝ, TwoArmAt v h ε₀ c C Cw Cb


/-! ## 4. The repaired pieces (session of `FINDING_sectorCountSmallbox.md` §2-§3)

The pieces `WindowAt` / `TwoArmAt` / `FrozenWindow` / `FrozenTwoArm` above are **refuted as
stated** (FINDING §2 and §3): the `A_0`-square at the *occupancy* density `n/PBV` is strictly
stronger than FS `thm:smallbox` (FS's square sits at the *flat* count density, the excited count
being paid by the credit `C·a(v)·(μ + S/V)·n_+` and by the `ε_T`-gap), and the regrouping cannot
spend the window error once per group with a single error constant because `m = floor(n/n')` is
unbounded.  The two definitions below are the repaired statements: the window piece in the **F-form**
(the target's own shape, so that its proof may use the flat-density `A_0`-square, the credit and the
gap), and the regrouping piece with the **window bound bundled in** so that the error constants are
chosen together. -/

/-- **The repaired window piece (F-form)**: FS `thm:smallbox` at the counts whose density
`n/PBV` is at most `Cw·μ`.

This is the target's own inequality, read in the window; its proof is FS's per-group estimate
(`lm:appinteractionestimate` at the box projections) with the `A_0`-square at the *flat* count
density `boxFlatCount/boxMass`, the excited-count credit `C·a(v)·(μ + S/V)·n_+` and the `ε_T`-gap. -/
def WindowF (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (ε₀ c C Cw : ℝ) : Prop :=
  0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 50 ∧ 0 ≤ C ∧ 10 ≤ Cw ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3),
        u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        fSupp v μ n u (Φ : Submission.BoseGases.X n → ℝ) →
        fNorm v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        (n : ℝ) ≤ Cw * μ * PBV v μ u →
        fLHS v h c C μ n u ≤ fWord v h μ n u (Φ : Submission.BoseGases.X n → ℝ)

/-- **The repaired regrouping piece**, with the window bound bundled so that `(C, Cb)` may be
chosen together (FINDING §3): the window part is `WindowF` at the same `(ε₀, c, C, Cw)`, and the
two-arm part is the regrouping form at the coupled constant `Cb`.

The partition exists in the second part: `μ·PBV ≥ 1/5` gives `1/PBV ≤ 5μ`, so
`n' := ceil(4μ·PBV)` satisfies `4μ ≤ n'/PBV ≤ 9μ`, and `n > Cw·μ·PBV ≥ 10·(1/5) = 2` gives
`n' ≤ n`, `1 ≤ m := floor(n/n')`. -/
def TwoArmC (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (ε₀ c C Cw Cb : ℝ) : Prop :=
  0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 50 ∧ 0 ≤ C ∧ 10 ≤ Cw ∧ 0 ≤ Cb ∧
    WindowF v h ε₀ c C Cw ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3),
        u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        fSupp v μ n u (Φ : Submission.BoseGases.X n → ℝ) →
        fNorm v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        1 / 5 ≤ μ * PBV v μ u →
        Cw * μ * PBV v μ u < (n : ℝ) →
        ∃ m n' n'' : ℕ, n = m * n' + n'' ∧ n'' < n' ∧ 1 ≤ m ∧
          4 * μ ≤ (n' : ℝ) / PBV v μ u ∧ (n' : ℝ) / PBV v μ u ≤ 9 * μ ∧
          (1 / 4 * ((n'' : ℝ) / PBV v μ u - μ) ^ 2
              + (1 / 18) * μ * (((n : ℝ) - (n'' : ℝ)) / PBV v μ u)
              - (1 / 2 - c) * μ ^ 2) * PBW h μ u
            - Cb * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                + μ * (_root_.BoseGases.a v))
          ≤ fWord v h μ n u (Φ : Submission.BoseGases.X n → ℝ)

/-- **The repaired window piece (exists-form).** -/
def FrozenWindowF (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ c C Cw : ℝ, WindowF v h ε₀ c C Cw

/-- **The repaired regrouping piece (exists-form).** -/
def FrozenTwoArmC (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ c C Cw Cb : ℝ, TwoArmC v h ε₀ c C Cw Cb


end Work.BoseFixB1B
