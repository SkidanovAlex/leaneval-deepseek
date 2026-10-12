import ChallengeDeps
import Submission.Work.BoseFixB1.boxWords_eq_zero_of_bI_eq_zero
import Submission.Work.BoseFixB1B.groupWordFibreAux2
import Submission.Work.BoseFixB1B.sbWord_integral_eq_zero_of_normB_eq_zero
import Submission.Work.BoseFixB1S.matchedWindowSmul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.sbWordCube_eq_zero_of_bI_eq_zero`

**The degenerate clause of the matched-window (single cube cutoff) sliding word.**

The matched sliding word `sbWordCube = sbKinCube + sbPot` (`matchedWindowDefs`) is the sum of

* the kinetic word `sbKinCube = bGapCoeff · n₊(B) + cubeSpectral`, where
  `cubeSpectral = tBwordKinInd … (chiSmallB …) (sbCut μ (a v))` is the `p`-diagonal kinetic form
  `tBdiagFormInd … χ (fsKinCoeff c)` at the **cube** window `chiSmallB`, and
* the potential word `sbPot = qLHSwordB` at the localised kernels.

Each of these three pieces is an integral over the analysis box `abox n ℓ`
(`ℓ = bSide v μ = sideAt μ (a v)`) — the slot sums are integrated over `abox n ℓ`, and `sbPot`
carries the density `(Φ x)²` — so all three vanish when the boxed `L²`-mass
`bI v μ Φ = ∫_{abox n ℓ} Φ²` vanishes.  This is the clause that lets the un-normalised per-box
ledgers (`CubeSmallNArb`, `InBoxTotalCube`, …) be discharged at a state with vanishing boxed norm,
i.e. it removes the hypothesis `0 < ∫_{abox}Φ²` from those consumers.

## Route

`bI = 0` with `ℓ > 0` and `Φ` smooth forces `Φ ≡ 0` *pointwise* on the box
(`Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero`).  Since the small box sits inside the
analysis cube (`Work.BoseFixB1.bA_subset_acube`), the box projections `Q_{B,i}` only ever evaluate
`Φ` at points of the box, so the excited count, the `p`-diagonal kinetic form (at an *arbitrary*
window) and the potential density all vanish pointwise on the box:

* `Work.BoseFixB1.boxWords_eq_zero_of_eq_zero_on_abox` — `cnPlusBoxInd` and `tBdiagFormInd` (the
  latter for arbitrary `χ`, `F`: the amplitude `tBamp` is an integral of `Q_{B,i}Φ` at updated
  configurations),
* `Work.BoseFixB1B.qLHSwordB_eq_zero_of_eq_zero_on_abox` — the potential word.

The degenerate regime `ℓ ≤ 0` (equivalently `μ · (a v)³ ≤ 0`) is handled separately: there
`abox n ℓ` is null for `n ≥ 1` and the slot sums are empty for `n = 0`, which is exactly
`Work.BoseFixB1B.cnPlusBoxInd_eq_zero_of_card_zero_or_nonpos`,
`…tBdiagFormInd_eq_zero_of_card_zero_or_nonpos` and
`…qLHSword_eq_zero_of_card_zero_or_nonpos`.

Nothing here uses any property of `v`, of `h`, or of `μ`: the statement is a statement about the
box `abox n (bSide v μ)` alone.
-/

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem sbWordCube_eq_zero_of_bI_eq_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hI : Work.BoseFixB1.bI v μ Φ = 0) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1B.sbWordCube v h μ u Φ = 0 := by
  -- the small box sits inside the analysis cube
  have hAc : Work.BoseFixB1.bA v μ u ⊆ Submission.BoseGases.acube (Work.BoseFixB1.bSide v μ) :=
    Work.BoseFixB1.bA_subset_acube v μ u
  -- a state with vanishing boxed `L²`-mass vanishes pointwise on the box
  have hΦ0 : ∀ (_ : 0 < Work.BoseFixB1.bSide v μ),
      ∀ y ∈ Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ), Φ y = 0 := by
    intro hpos
    refine Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero hpos hΦc.continuous ?_
    show Work.BoseKinLoc.sqNormB n (Work.BoseFixB1.bSide v μ) Φ = 0
    rw [Work.BoseKinLoc.sqNormB]
    exact hI
  -- the degenerate index set `n = 0 ∨ (1 ≤ n ∧ ℓ ≤ 0)`
  have hcaseOf : Work.BoseFixB1.bSide v μ ≤ 0 →
      n = 0 ∨ (1 ≤ n ∧ Work.BoseFixB1.bSide v μ ≤ 0) := by
    intro hle
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · exact Or.inr ⟨hn, hle⟩
  -- the cube-windowed spectral slot, unfolded to `tBdiagFormInd`
  have hcsOf : Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
      (Work.BoseFixB1.bV v μ u)
      (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) Φ = 0 →
      Work.BoseFixB1B.cubeSpectral v μ Φ u = 0 := by
    intro h
    rw [Work.BoseFixB1B.cubeSpectral, Work.UBBInputs8.tBwordKinInd]
    exact h
  have hkin : Work.BoseFixB1B.sbKinCube v μ u Φ = 0 := by
    rcases lt_or_ge (0 : ℝ) (Work.BoseFixB1.bSide v μ) with hpos | hnonpos
    · -- non-degenerate side: `Φ` vanishes pointwise on the box
      have h0 := hΦ0 hpos
      have hb := Work.BoseFixB1.boxWords_eq_zero_of_eq_zero_on_abox (N := n)
        (a := Work.BoseFixB1.bSide v μ) (volA := Work.BoseFixB1.bV v μ u)
        (A := Work.BoseFixB1.bA v μ u) hAc
        (fun _ _ => (0 : ℝ))
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u)
        (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) h0
      have hcn : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
          (Work.BoseFixB1.bV v μ u) Φ = 0 := hb.2.2.1
      have hcs := hcsOf hb.2.2.2.2
      unfold Work.BoseFixB1B.sbKinCube
      rw [hcn, hcs]
      ring
    · -- degenerate side: `abox n ℓ` is null (or the slot sums are empty)
      have hcase := hcaseOf hnonpos
      have hcn : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
          (Work.BoseFixB1.bV v μ u) Φ = 0 :=
        Work.BoseFixB1B.cnPlusBoxInd_eq_zero_of_card_zero_or_nonpos hcase
          (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u) Φ
      have hcs := hcsOf (Work.BoseFixB1B.tBdiagFormInd_eq_zero_of_card_zero_or_nonpos hcase
        (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u)
        (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u)
        (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) Φ)
      unfold Work.BoseFixB1B.sbKinCube
      rw [hcn, hcs]
      ring
  have hpot : Work.BoseFixB1.sbPot h μ u Φ = 0 := by
    rcases lt_or_ge (0 : ℝ) (Work.BoseFixB1.bSide v μ) with hpos | hnonpos
    · rw [Work.BoseFixB1.sbPot]
      exact Work.BoseFixB1B.qLHSwordB_eq_zero_of_eq_zero_on_abox (hΦ0 hpos)
    · rw [Work.BoseFixB1.sbPot, Work.SmallBoxSliding.qLHSwordB]
      exact Work.BoseFixB1B.qLHSword_eq_zero_of_card_zero_or_nonpos (hcaseOf hnonpos) μ _ _ Φ
  rw [Work.BoseFixB1B.sbWordCube, hkin, hpot, add_zero]

end Work.BoseB1Cube
