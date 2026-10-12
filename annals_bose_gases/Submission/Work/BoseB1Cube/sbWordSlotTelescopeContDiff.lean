import ChallengeDeps
import Submission.Work.BoseB1Cube.NominalPerBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.sbWordSlotTelescopeContDiff` — the slotted-word telescope at the
# **carrier-free** (`ContDiff`) state class

Provenance: a copy of `Submission/Work/BoseB1Cube/sbWordSlotTelescope.lean` (the definitional
identity `sbWordSlot = bGapCoeff·bQ + bSpectralCube + boxQSum` at the slot `μp`, via `bqPotsplit`)
with the carrier `Work.BoseKinLoc.BoxState` replaced by a plain `Φ : X n → ℝ` with
`hΦcd : ContDiff ℝ ⊤ Φ` (the `BoxState` fields `symm`/`nezero` are unused).  Needed by
`sbWordSlot_ge_payPortContDiff`.
-/


/-!
# `Submission.Work.BoseB1Cube.sbWordSlotTelescopeContDiff` — ARM 1's telescoping identity

**What it says.**  The *slotted* word
`sbWordSlot v h μp μ u = sbKinCube v μ μ u + (pairSum − μp·fibSum)` (definitionally, see
`NominalPerBox.lean`) telescopes into its three payment carriers at the **free** chemical-potential
slot `μp`:

    sbWordSlot v h μp μ u Φ
      = bGapCoeff v μ · boxQCount (bV) (bSide) (bA) Φ
        + bSpectralCube v μ Φ u
        + boxQSum (bV) (bSide) μp (bA) (wSmallPair … v) (wSmall1Pair h …)
            (wSmallPair … (g2 v h)) (omC (choose h)) Φ .

**Proof.**  Three definitional unfoldings and two already-proved corpus identities:

* `sbKinCube v μ u Φ = bGapCoeff v μ · cnPlusBoxInd (bSide) (bA) (bV) Φ + cubeSpectral v μ Φ u`
  (definition), and `cnPlusBoxInd (bSide) (bA) (bV) Φ = boxQCount (bV) (bSide) (bA) Φ` as well as
  `cubeSpectral = bSpectralCube` are both *definitional* (`rfl`), because `boxQCount`/`bSpectralCube`
  are the same bodies as `cnPlusBoxInd`/`cubeSpectral` with the arguments in the other order;
* `pairSum − μp·fibSum = qLHSword ℓ μp w w₁` is the corpus split `qLHSwordB_split` (the integral
  split of the `q`-word at an arbitrary chemical potential), and
  `qLHSword ℓ μp w w₁ = boxQSum …` is the proved localisation `bqPotsplit`.

Note that this is an **identity**, so it needs no sign of `μp − μ`: the chemical potential is a
free parameter of the potential word (which is exactly what makes FS's `m(u)μ` substitution
writable).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB1Cube

set_option autoImplicit false
set_option linter.unusedVariables false

theorem sbWordSlotTelescopeContDiff {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    {μp μ : ℝ}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hR : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3))
    (hvol : 0 < Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (hΦcd : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.BoseB1Cube.sbWordSlot v h μp μ u (Φ : Submission.BoseGases.X n → ℝ)
      = Work.BoseFixB1.bGapCoeff v μ
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X n → ℝ) u
        + Work.BoseFixB1S.boxQSum (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) μp
            (Work.BoseFixB1.bA v μ u)
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u)
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
            (Submission.BoseGases.omC (Classical.choose h))
            (Φ : Submission.BoseGases.X n → ℝ) := by
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := hΦcd.continuous
  -- the corpus split of the `q`-word at the free chemical potential `μp`
  have hsplit := Work.BoseFixB1.qLHSwordB_split (v := v) (h := h) (R0 := R) hv_supp hR0 hv hvrad
    hv1 (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M hM
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μp) hℓ hd hR hRχ u hΦc
  rw [Work.SmallBoxSliding.qLHSwordB] at hsplit
  -- the localisation of `qLHSword` into the five box words
  have hpot := Work.BoseFixB1.bqPotsplit (v := v) (R0 := R) hv_supp hR0 hv hvrad hv1 h
    (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hM
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μp) hℓ hd hR hRχ u hvol hΦc
  -- the potential part of the word, reassembled at the target's vocabulary
  have hmain : Work.BoseFixB1.pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
      - μp * Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
      = Work.BoseFixB1S.boxQSum (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) μp
          (Work.BoseFixB1.bA v μ u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u)
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
          (Submission.BoseGases.omC (Classical.choose h))
          (Φ : Submission.BoseGases.X n → ℝ) := by
    have hmid : -(μp * Work.BoseFixB1.fibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ))
        + Work.BoseFixB1.pairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
        = Work.BoseFixB1S.boxQSum (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) μp
            (Work.BoseFixB1.bA v μ u)
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u)
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
            (Submission.BoseGases.omC (Classical.choose h))
            (Φ : Submission.BoseGases.X n → ℝ) := hsplit.symm.trans hpot
    linarith
  -- the kinetic part: `sbKinCube` is definitionally the gap row plus the cube-windowed spectral slot
  have hkin : Work.BoseFixB1B.sbKinCube v μ u (Φ : Submission.BoseGases.X n → ℝ)
      = Work.BoseFixB1.bGapCoeff v μ
          * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bA v μ u) (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
    simp only [Work.BoseFixB1B.sbKinCube, Work.BoseFixB1B.cubeSpectral,
      Work.BoseFixB1S.bSpectralCube, Work.BoseFixB1S.boxQCount, Work.UBBInputs8.cnPlusBoxInd]
  unfold Work.BoseB1Cube.sbWordSlot
  rw [hmain, hkin]

end Work.BoseB1Cube

end
