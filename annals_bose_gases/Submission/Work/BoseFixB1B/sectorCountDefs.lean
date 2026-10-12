import ChallengeDeps
import Submission.Work.BoseFixB1B.PerBoxSectorResidual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.sectorCountDefs` — the count-indexed core of `PerSectorBoundG`

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

`Work.BoseFixB1.PerSectorBoundG` (the termwise per-sector residual of the a-priori chapter,
FS `thm:smallbox` read at the counting operator of the sliding box `B(u)`) is *scale-homogeneous*:
both of its sides are quadratic in the sector piece, and its threshold `T(k)` depends on the sector
index `k` only through the *exact* occupancy.  Consequently its whole analytic content is the
**in-box, normalised** instance: a state all of whose particles sit in `B(u)` has box count exactly
`n`, so FS's count-indexed statement at count `n` applies verbatim, and the general sector case
follows by

* restricting the sector piece to its box-slot set `S` (`|S| = k`),
* Fubini-splitting the outside configuration (the *fibre*),
* normalising the fibre (legitimate because the sector inequality is homogeneous), and
* reassembling.

This module fixes that split as two objects, so that the analytic core and the arity/Fubini
bookkeeping can be attacked independently:

* `SectorCountSmallbox v h` — **the count-indexed core** (`Submission/Work/BoseFixB1B/sectorCountSmallbox.lean`);
* the *reduction* `Work.BoseFixB1B.perSectorBoundG_of_sectorCount`
  (`Submission/Work/BoseFixB1B/perSectorBoundG_of_sectorCount.lean`) — the arity step.

Together they give `Work.BoseFixB1.PerSectorBoundG v h R`, hence (via the PROVED
`Work.BoseFixB1.perBoxSectorBoundG_of_pieces` and the PROVED `sbWordSectorAdditiveAdm`) the
collected per-box residual of the a-priori chapter.

## Why in-box + normalised is the right specialisation (and why it is *not* a restriction of
## the same kind as the refuted fibre residuals)

The delivered fibre residual `Work.SlotWord.FibreWordBoundAt` compared the *faithful* word at the
centred box of side `L·d` with the *sliding* word — two *different* boxes — and was machine-checked
false (`Work.FibreKinPot.Mismatch.not_fibreKinLeShift`; corrected route in
`Work.FibreKinPot.Correction`).  Here **both** sides are read at the sliding box `B(u)`: the state
of `SectorCountSmallbox` lives on `abox n ℓ` with all its particles inside `B(u) ⊆ acube ℓ`, and the
word is the frozen sliding word `tBwordBInd + qLHSwordB` at the very same box.  So the box mismatch
cannot arise.

Likewise the refuted unnormalised forms (`Work.BoseFixB1S.boxCrossJoint`,
`Work.BoseFixB1B.bracketNonnegCrux`, and every unnormalised `A₀`-form dominating them) fail on a
product state supported in a *corner cap* of `acube ℓ` where the localisation cutoff `χ_B` vanishes:
there the manifest square is identically `0`, and the debit is `Θ(N)` against `O(1)` payers.  The
hypotheses `hnorm` and `hsupp` below remove exactly that family: on the corner cap `hsupp` fails
(the particles are *not* in `B(u)`), and after normalisation the scalar credit is of the same order
as the debit.  This is the *documented* repair of the two refutations
(`BoseFixB1S/FINDING_boxCrossJoint_false.md` §"repair", `BoseFixB1B/FINDING_bracketNonnegCrux_FALSE.md`
§4).
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

/-- **The count-indexed core of FS `thm:smallbox` at the sliding box.**

There are `ε₀ > 0`, `0 < c ≤ 1/4` and `C ≥ 0` such that for every admissible `μ` (`Adm v ε₀ μ`),
every particle number `n`, every smooth box state `Φ : BoxState n ℓ` (`ℓ = sideAt μ (a v)`), every
`u ∈ goodSet ℓ d μ`, **with the state normalised** (`∫_{abox n ℓ}Φ² = 1`) and **all its particles
inside the sliding box `B(u) = dlBox ℓ d u`** (`Φ x ≠ 0 → ∀ i, x i ∈ B(u)` a.e.),

    (c·F(n/|B(u)|) − (½ − c)μ²)·∬w_{1,B(u)}
      − C·(μ²(a v)Γ_B·∬w_{1,B(u)} + μ(a v))
    ≤ tBwordBInd n ℓ d ε_T (sbCut μ (a v)) u Φ + qLHSwordB h M ℓ d μ u Φ ,

with `F = psiWeight 1 μ` (FS's `F(t) = c(t−μ)²/(1+tμ⁻¹)`, `final_v2.tex` l. 4121),
`|B(u)| = chiMass M ℓ d u` (the `χ_B²`-mass — the *repaired* normaliser of
`FINDING_windowBridge_RPsiB_normalisation.md`, **not** the nominal volume `boxMass`),
`∬w_{1,B(u)} = w1MassB h M ℓ d u` and `Γ_B = K_B³(μ(a v)³)^{1/2}`.

This is FS `thm:smallbox` (`final_v2.tex` l. 3907) read at the count `n` for the `n`-particle
restriction of `H_{B(u)}(μ)`; the two hypotheses are exactly the paper's setting and are what makes
the count a *datum* rather than a scalarisation of an operator expectation.  It is the
`k = n` instance of `Work.BoseFixB1.PerSectorBoundG` for an in-box state, i.e. the whole analytic
content of that residual. -/
def SectorCountSmallbox (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3),
        u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (PBℓ v μ))),
          (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 → ∀ i : Fin n, x i ∈ PBB v μ u) →
        (∫ x in Submission.BoseGases.abox n (PBℓ v μ),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1 →
        (c * psiWeight 1 μ ((n : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
          - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
              + μ * (_root_.BoseGases.a v))
        ≤ Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
              (Φ : Submission.BoseGases.X n → ℝ)
          + Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
              (Φ : Submission.BoseGases.X n → ℝ)

/-! ## The repaired normaliser (READ `FINDING_sector_density_normaliser.md` FIRST)

`SectorCountSmallbox` above reads FS's `F`-weight at `|B(u)| := chiMass M ℓ d u = ∫χ_B²`, whereas
FS `thm:smallbox` — and the residual's *own* flat-state consistency check
(`BoseFixB1/perSectorBoundG_FINDING.md` §1b, which uses `ρ̂ = k/boxMass`) — read it at the **box
volume** `boxMass`.  The two differ by `χ̂ := chiMass/boxMass ∈ (0, ν²]`, which is **not bounded
below on `goodSet`** (the good set constrains the cube `acube ℓ`, not `supp χ`); since `F` is
increasing for `t ≥ μ`, the `chiMass` form is *strictly stronger*, and on the flat in-box state in
the regime `μ·chiMass ≤ 1/5` the debit is `χ̂`-free (`≈ 8πc(a v)μn`) while every payer is
`χ̂`-weighted or `n`-independent — so the `chiMass` form **fails for every fixed `C`** once
`C/(8πc) ≪ n ≪ μ·boxMass/χ̂` (details and the sharper *pair-dead* witness in
`BoseFixB1B/FINDING_sectorCountSmallbox.md` §6 and `BoseFixB1B/FINDING_sector_density_normaliser.md`).

The definitions below are the **repaired** forms, at FS's own `|B|`:

* `SectorCountSmallboxBox` — the count-indexed core at `boxMass` (= FS `thm:smallbox` verbatim);
* `RepairedPerSectorBoundG` — `Work.BoseFixB1.PerSectorBoundG` with the one-token repair
  `PBV v μ u ↦ boxMass (PBℓ v μ) (PBd v μ) u` in the argument of `psiWeight`. -/

/-- The box volume `|B(u)|` of the sliding box — FS's own normaliser for the `F`-density. -/
abbrev PBBV (v : E3 → ℝ) (μ : ℝ) (u : E3) : ℝ := Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u

/-- **The repaired count-indexed core** (FS `thm:smallbox` at FS's own normaliser).

Identical to `SectorCountSmallbox` except that the `F`-weight is read at the **box volume**
`boxMass (PBℓ v μ) (PBd v μ) u` instead of the `χ_B²`-mass `PBV v μ u`.  This is FS's published
statement at the count `n` for the `n`-particle restriction of `H_{B(u)}(μ)`; the state is
normalised (`∫Φ² = 1`) and in-box, so the box occupancy is exactly `n`. -/
def SectorCountSmallboxBox (v : E3 → ℝ) (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : E3),
        u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n (PBℓ v μ))),
          (Φ : Submission.BoseGases.X n → ℝ) x ≠ 0 → ∀ i : Fin n, x i ∈ PBB v μ u) →
        (∫ x in Submission.BoseGases.abox n (PBℓ v μ),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = 1 →
        (c * psiWeight 1 μ ((n : ℝ) / PBBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
          - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
              + μ * (_root_.BoseGases.a v))
        ≤ Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
              (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
              (Φ : Submission.BoseGases.X n → ℝ)
          + Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
              (Φ : Submission.BoseGases.X n → ℝ)

/-- **The sector residual with the normaliser repaired** — `Work.BoseFixB1.PerSectorBoundG` with
`PBV v μ u` replaced by `boxMass (PBℓ v μ) (PBd v μ) u` in the argument of `psiWeight`
(the `∬w_{1,B}`-coefficient `PBW` is a separate quantity and is unchanged). -/
def RepairedPerSectorBoundG (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
        (u : E3),
        u ∈ goodSet (PBℓ v μ) (PBd v μ) μ →
        ∀ k ∈ Finset.range (n + 1),
          sectorMass (PBℓ v μ) (PBB v μ u) (Φ : Submission.BoseGases.X n → ℝ) k *
              ((c * psiWeight 1 μ ((k : ℝ) / PBBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
                - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                    + μ * (_root_.BoseGases.a v)))
            ≤ Work.UBBInputs8.tBwordBInd n (PBℓ v μ) (PBd v μ) (PBeT v μ)
                  (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
                  (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
              + Work.SmallBoxSliding.qLHSwordB h (PBM v μ) (PBℓ v μ) (PBd v μ) μ u
                  (sectorPiece (PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))

end Work.BoseFixB1B
