import ChallengeDeps
import Submission.Work.BoseFixB1B.perBoxSectorBound_holds
import Submission.Work.BoseFixB1B.sectorCountDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.sectorCountBoxDefs` — the per-state vocabulary of FS `thm:smallbox` at the count

The per-state two sides `boxLHS`/`boxRHS` of the target
`Work.BoseFixB1B.SectorCountSmallboxBox` (= FS `thm:smallbox` at the count, `boxMass`-normalised),
the in-box and normalisation hypotheses, and the split of the target into the **occupancy cap**
`Cap` (elementary regime, proved in `sectorCountSmallboxBox.lean`) and the **dense arm**
`DenseArm` (the complement of the cap: the content of FS §5 at the box — the interaction estimate
`lm:appinteractionestimate` together with the pairing control `lm:appbogolubov`).

Kept in a module of its own so that the delegated prover of `DenseArm` and the holder of
`sectorCountSmallboxBox.lean` can share the vocabulary without an import cycle.  `Cap` mirrors the
cap of `perBoxSectorBound_holds.perBoxSectorBound_lowDensity` (PROVED) and `DenseArm` mirrors its
residual `PerBoxSectorBoundDense`.
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

/-! ## 1. The per-state two sides of (T) in the frozen vocabulary -/

/-- **The per-state left-hand side of (T)**: FS's scalar
`(c·F(n/|B(u)|) − (½−c)μ²)·∬w_{1,B(u)} − C·(μ²(a v)Γ_B·∬w_{1,B(u)} + μ(a v))`
at FS's own box volume `|B(u)| = PBBV v μ u`. -/
noncomputable def boxLHS {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (c C μ : ℝ) (n : ℕ) (u : E3) : ℝ :=
  (c * psiWeight 1 μ ((n : ℝ) / PBBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
    - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u + μ * (_root_.BoseGases.a v))

/-- **The per-state right-hand side of (T)**: the frozen sliding word
`tBwordBInd + qLHSwordB` (`= sbKin + sbPot`, definitionally). -/
noncomputable def boxRHS {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ) (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
      (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u Φ
    + Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u Φ

/-- `boxRHS` is `sbKin + sbPot` (definitionally). -/
lemma boxRHS_eq_sbWord {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ) (u : E3)
    (Φ : Submission.BoseGases.X n → ℝ) :
    boxRHS h μ n u Φ
      = Work.BoseFixB1.sbKin (v := v) μ (PBM v μ) u Φ + Work.BoseFixB1.sbPot h μ u Φ := rfl

/-- **The in-box hypothesis** of (T) (definitionally the target's own hypothesis). -/
def boxSupp (v : E3 → ℝ) (μ : ℝ) (n : ℕ) (u : E3) (Φ : Submission.BoseGases.X n → ℝ) : Prop :=
  ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (PBℓ v μ))),
    Φ x ≠ 0 → ∀ i : Fin n, x i ∈ PBB v μ u

/-- **The normalisation hypothesis** of (T) (definitionally the target's own hypothesis). -/
def boxNorm (v : E3 → ℝ) (μ : ℝ) (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) : Prop :=
  (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (Φ x) ^ 2) = 1

/-! ## 2. The cap and the dense arm

The cap is the *sufficient condition* of the crude arm-proof below; its complement is the dense
regime, where the content of FS §5 lives.  This mirrors `perBoxSectorBound_holds`'s own split into
`perBoxSectorBound_lowDensity` (PROVED) and `PerBoxSectorBoundDense` (the residual). -/

/-- **The occupancy cap.**  With `t := n/|B(u)|`, `W := ∬w_{1,B(u)}`:

    c·μ·t·W + μ·lowFibK·(a v)·n + C·(μ²(a v)Γ_B·W + μ(a v)) ≤ (½ − 2c)·μ²·W .

This is exactly the condition under which the crude ledger closes (see `capArm`). -/
def Cap (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (c C μ : ℝ) (n : ℕ) (u : E3) : Prop :=
  c * μ * ((n : ℝ) / PBBV v μ u) * PBW h μ u
      + μ * lowFibK * (_root_.BoseGases.a v) * (n : ℝ)
      + C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u + μ * (_root_.BoseGases.a v))
    ≤ (1 / 2 - 2 * c) * μ ^ 2 * PBW h μ u

/-- **The dense arm**: (T) on the complement of the cap.  This is the content of FS §5 at the box
— the interaction estimate `lm:appinteractionestimate` together with the pairing control
`lm:appbogolubov`, which is what pays the `cμ²∬w_{1,B}` shift away from the elementary regime.
The delegated residual; see the FINDING §2 for the reduction to the two named FS lemmas. -/
def DenseArm (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3),
        u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        boxSupp v μ n u (Φ : Submission.BoseGases.X n → ℝ) →
        boxNorm v μ n (Φ : Submission.BoseGases.X n → ℝ) →
        ¬ Cap v h c C μ n u →
        boxLHS h c C μ n u ≤ boxRHS h μ n u (Φ : Submission.BoseGases.X n → ℝ)


end Work.BoseFixB1B
