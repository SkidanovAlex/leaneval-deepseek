import Mathlib
import Submission.Work.Stems.Collar.MixedCollar
import Submission.Work.Stems.Collar.Plumbing
import Submission.Work.StemsB.Rat.collarSigma_cup_low

/-!
# The **mixed-degree** derivation property of the collar transgression

*(Area STEMS.)*

For the collar pair `Q = ↥(sphLoopBig b) × Y`, `C = sphLoopCollarProd b Y` (`b ≥ 2`), a Thom class
`τ ∈ H^b(Q,C)`, a suspension class `s ∈ H^{b-1}(C)` with `δ s = τ`, `s ⌣ s = 0` and
`σ^* s = 0`, the transgression coefficient map `Σ = collarSigma` (with the top-degree variant
`collarSigmaLow` for the fundamental class of the fibre) satisfies the derivation property in the
**mixed** degrees: for `X ∈ H^{b-1}(C)` and `Y' ∈ H^{m+b}(C)`,

  `Σ (X ⌣ Y') = (-1)^{b-1} (σ^*X) ⌣ Σ Y' + (-1)^{(b-1)(m+b)+(m+b)} (σ^*Y') ⌣ Σ_lo X`.

The tree already has the two extreme cases (`Work.StemsB.Rat.collarSigma_cup_low` for two factors of
degree `b - 1`, `Work.StemsB.Rat.collarSigma_cup_rat` for two factors of degree `m + b`); this file
adds the mixed case, which is the missing input of the unbounded odd step of the `C2` layer
(`Submission/Work/Stems/C2ODD_PLAN.md` §3/§7, `Submission/Work/Stems/Collar/MixedCollar.lean`).

The `δ`-computation is `Work.Stems.Collar.collarDPairCupMixed` (`MixedCollar.lean`); what is done
here is the bookkeeping that transports it to the level of `Σ`, verbatim in the style of
`Submission/Work/StemsB/Rat/collarSigma_cup_rat.lean`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems.Collar

open Work.StemsB.Rat
open Work.StemsB

noncomputable section

/-! ## Local copies of the still-`private` plumbing of the sibling files -/

/-- The definition of `collarSigma`, in the `pairδ` spelling. -/
private lemma collarSigma_eq_def (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y))
    (hτ : CollarThom (Y := Y) b τ) (m : ℕ)
    (z : (CollKC b Y).homology (m + b)) :
    collarSigma b hb Y τ hτ m z
      = (LinearEquiv.ofBijective (collarPhi b Y τ (m + 1)) (hτ (m + 1))).symm
          (collarRelEq b Y m (collarDelta b Y m z)) := rfl

/-- The computation rule of `relCohZeroAdd`. -/
private lemma relCohZeroAdd_eqToHom' (b : ℕ) (Y : Type) [TopologicalSpace Y]
    (z : (CollRC b Y).homology b) :
    relCohZeroAdd (Y := Y) b z
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
          (Nat.zero_add b).symm)) z := rfl

/-- The computation rule of `collarDeltaLow`. -/
private lemma collarDeltaLow_eqToHom' (b : ℕ) (hb : 1 ≤ b) (Y : Type) [TopologicalSpace Y]
    (x : (CollKC b Y).homology (b - 1)) :
    collarDeltaLow b hb Y x
      = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
          (lowCast b hb))) (dPair b Y (b - 1) x) := rfl

/-! ## The main theorem -/

theorem collarSigma_cup_mixed (b : ℕ) (hb : 2 ≤ b) (Y : Type) [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℚ b (↥(Work.StemsB.sphLoopBig b) × Y)
          (Work.StemsB.sphLoopCollarProd b Y))
    (hτ : Work.StemsB.Rat.CollarThom (Y := Y) b τ)
    (s : Work.Thom.Coh ℚ (b - 1) ↥(Work.StemsB.sphLoopCollarProd b Y))
    (hs : Work.StemsB.Rat.CollarTransgresses b (by omega) (Y := Y) s τ)
    (hssq : Work.StemsB.Rat.cupT ↥(Work.StemsB.sphLoopCollarProd b Y) (b - 1) (b - 1) s s = 0)
    (hσ : (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of Y)
            (TopCat.of ↥(Work.StemsB.sphLoopCollarProd b Y))
            (TopCat.ofHom (Work.StemsB.collarSection (Y := Y) b (by omega))) (b - 1)).hom s = 0)
    (m : ℕ) (X : Work.Thom.Coh ℚ (b - 1) ↥(Work.StemsB.sphLoopCollarProd b Y))
    (Y' : Work.Thom.Coh ℚ (m + b) ↥(Work.StemsB.sphLoopCollarProd b Y)) :
    Work.StemsB.Rat.transT Y (by omega : (m + b - 1) + 1 = (b - 1) + (m + 1))
        (Work.StemsB.Rat.collarSigma b (by omega) (Y := Y) τ hτ (m + b - 1)
          (Work.StemsB.Rat.transT ↥(Work.StemsB.sphLoopCollarProd b Y)
            (by omega : (b - 1) + (m + b) = (m + b - 1) + b)
            (Work.StemsB.Rat.cupT ↥(Work.StemsB.sphLoopCollarProd b Y) (b - 1) (m + b) X Y')))
      = ((-1 : ℚ) ^ (b - 1)) •
          Work.StemsB.Rat.cupT Y (b - 1) (m + 1)
            ((Work.Thom.CohMap (Work.StemsB.collarSection (Y := Y) b (by omega)) ℚ (b - 1)).hom X)
            (Work.StemsB.Rat.collarSigma b (by omega) Y τ hτ m Y')
        + ((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) •
            Work.StemsB.Rat.transT Y (by omega : (m + b) + 0 = (b - 1) + (m + 1))
              (Work.StemsB.Rat.cupT Y (m + b) 0
                ((Work.Thom.CohMap (Work.StemsB.collarSection (Y := Y) b (by omega)) ℚ (m + b)).hom Y')
                (Work.StemsB.Rat.collarSigmaLow b (by omega) Y τ hτ X)) := by
  have hb1 : 1 ≤ b := by omega
  -- the degree identities
  have h1 : (b - 1) + (m + b) = (m + b - 1) + b := by omega
  have h2 : (m + b - 1) + 1 = (b - 1) + (m + 1) := by omega
  have h3 : (m + b) + 0 = (b - 1) + (m + 1) := by omega
  have hcar : (((m + b - 1) + b) + 1) = (((m + b - 1) + 1) + b) := by omega
  have hcar1 : (m + b) + 1 = (m + 1) + b := by omega
  have hcar2 : (b - 1) + 1 = 0 + b := by omega
  have hγ1 : (((b - 1) + (m + 1)) + b) = (((m + b - 1) + 1) + b) := by omega
  have hγ2 : (((m + b) + 0) + b) = (((m + b - 1) + 1) + b) := by omega
  have hA1 : (((b - 1) + (m + 1)) + b) = ((b - 1) + ((m + b) + 1)) := by omega
  have hA2 : (((m + b) + 0) + b) = ((m + b) + ((b - 1) + 1)) := by omega
  -- the product of the two collar classes
  set W : (CollKC b Y).homology ((b - 1) + (m + b)) :=
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollC b Y)) (b - 1) (m + b)) X Y' with hW
  -- the two base terms
  set T1 : (Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj (TopCat.of Y))).homology
      ((b - 1) + (m + 1)) :=
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) (b - 1) (m + 1))
      ((Work.Thom.CohMap (collarSection (Y := Y) b hb1) ℚ (b - 1)).hom X)
      (collarSigma b hb1 Y τ hτ m Y') with hT1
  set T2 : (Work.Cohomology.SSetCochainComplex ℚ (TopCat.toSSet.obj (TopCat.of Y))).homology
      ((m + b) + 0) :=
    (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) (m + b) 0)
      ((Work.Thom.CohMap (collarSection (Y := Y) b hb1) ℚ (m + b)).hom Y')
      (collarSigmaLow b hb1 Y τ hτ X) with hT2
  -- the pushed-forward value at degree `(m + b - 1) + 1`
  set U : Work.Thom.Coh ℚ ((m + b - 1) + 1) Y :=
    ((-1 : ℚ) ^ (b - 1)) • (transT Y h2.symm T1)
      + ((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) • (transT Y (h3.trans h2.symm) T2) with hU
  -- the two relative classes the computation ends at
  set Z1 : Work.Thom.RelCoh ℚ (((b - 1) + (m + 1)) + b) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) ((b - 1) + (m + 1)) b)
      (piStar b Y ((b - 1) + (m + 1)) T1) τ with hZ1
  set Z2 : Work.Thom.RelCoh ℚ (((m + b) + 0) + b) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) ((m + b) + 0) b)
      (piStar b Y ((m + b) + 0) T2) τ with hZ2
  -- the common final form
  set Xfin : Work.Thom.RelCoh ℚ (((m + b - 1) + 1) + b) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    ((-1 : ℚ) ^ (b - 1)) •
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hγ1)) Z1)
      + ((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) •
        ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hγ2)) Z2) with hXfin
  -- the two `collarPhi`-images of the transgressions
  set Z1' : Work.Thom.RelCoh ℚ ((m + 1) + b) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    collarPhi b Y τ (m + 1) (collarSigma b hb1 Y τ hτ m Y') with hZ1'
  set Z2' : Work.Thom.RelCoh ℚ (0 + b) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    collarPhi b Y τ 0 (collarSigmaLow b hb1 Y τ hτ X) with hZ2'
  -- the two `δ`-images, in the `Thom.mixedCupC` spelling
  set M1 : Work.Thom.RelCoh ℚ ((b - 1) + ((m + b) + 1)) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) (b - 1) ((m + b) + 1))
      (piStar b Y (b - 1) (sgStar b hb1 Y (b - 1) X))
      (dPair b Y (m + b) Y') with hM1def
  set M2 : Work.Thom.RelCoh ℚ ((m + b) + ((b - 1) + 1)) (↥(sphLoopBig b) × Y)
      (sphLoopCollarProd b Y) :=
    (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) (m + b) ((b - 1) + 1))
      (piStar b Y (m + b) (sgStar b hb1 Y (m + b) Y'))
      (dPair b Y (b - 1) X) with hM2def
  -- ### The left-hand chain
  have hL : collarPhi b Y τ ((m + b - 1) + 1) U = Xfin := by
    rw [hU, collarPhi_apply]
    have hp : piStar b Y ((m + b - 1) + 1)
          (((-1 : ℚ) ^ (b - 1)) • (transT Y h2.symm T1)
            + ((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) • (transT Y (h3.trans h2.symm) T2))
        = ((-1 : ℚ) ^ (b - 1)) •
            ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
              (↥(sphLoopBig b) × Y)) h2.symm)) (piStar b Y ((b - 1) + (m + 1)) T1))
          + ((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) •
            ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
              (↥(sphLoopBig b) × Y)) (h3.trans h2.symm))) (piStar b Y ((m + b) + 0) T2)) := by
      rw [map_add, map_smul, map_smul, piStar_transT, piStar_transT]
    rw [hp]
    have f1 : (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) ((m + b - 1) + 1) b)
          ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
            (↥(sphLoopBig b) × Y)) h2.symm)) (piStar b Y ((b - 1) + (m + 1)) T1)) τ
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
            (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) h2.symm)) Z1 := by
      rw [mixedCupC_cast_left (sphLoopCollarProd b Y) h2.symm b
        (piStar b Y ((b - 1) + (m + 1)) T1) τ, ← hZ1]
    have f2 : (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) ((m + b - 1) + 1) b)
          ((CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.Coh ℚ t
            (↥(sphLoopBig b) × Y)) (h3.trans h2.symm))) (piStar b Y ((m + b) + 0) T2)) τ
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
            (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) (h3.trans h2.symm))) Z2 := by
      rw [mixedCupC_cast_left (sphLoopCollarProd b Y) (h3.trans h2.symm) b
        (piStar b Y ((m + b) + 0) T2) τ, ← hZ2]
    have g1 : (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) h2.symm)) Z1
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hγ1)) Z1 :=
      RelCoh_cast_shift_apply (sphLoopCollarProd b Y) h2.symm hγ1 Z1
    have g2 : (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ (t + b)
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) (h3.trans h2.symm))) Z2
        = (CategoryTheory.eqToHom (congrArg (fun t => Work.Thom.RelCoh ℚ t
          (↥(sphLoopBig b) × Y) (sphLoopCollarProd b Y)) hγ2)) Z2 :=
      RelCoh_cast_shift_apply (sphLoopCollarProd b Y) (h3.trans h2.symm) hγ2 Z2
    rw [mixedCup_add_arg, mixedCup_smul_arg, mixedCup_smul_arg, f1, f2, g1, g2, hXfin]
  -- ### The right-hand chain
  have hR : collarRelEq b Y (m + b - 1)
      (collarDelta b Y (m + b - 1) (transT ↥(sphLoopCollarProd b Y) h1 W)) = Xfin := by
    rw [show collarDelta b Y (m + b - 1) = dPair b Y ((m + b - 1) + b) from rfl]
    rw [collarRelEq_apply b Y (m + b - 1) hcar]
    rw [dPair_transT b Y h1 W]
    rw [CollRC_cast_comp b Y (congrArg (fun t => t + 1) h1) hcar
      (dPair b Y ((b - 1) + (m + b)) W)]
    -- the core computation
    have e3 : dPair b Y ((b - 1) + (m + b)) W
        = ((-1 : ℚ) ^ (b - 1)) • M1
          + (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
              (congrArg (fun t => t + 1) (Nat.add_comm (b - 1) (m + b)).symm)))
            (((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) • M2) := by
      rw [hW, hM1def, hM2def,
        Work.StemsB.Rat.mixedCupC_eq_mixedCup b Y (b - 1) ((m + b) + 1),
        Work.StemsB.Rat.mixedCupC_eq_mixedCup b Y (m + b) ((b - 1) + 1)]
      exact collarDPairCupMixed b hb Y τ hτ s hs hssq hσ m X Y'
    rw [e3]
    rw [CollRC_cast_add (b := b) (Y := Y) ((congrArg (fun t => t + 1) h1).trans hcar),
      CollRC_cast_smul (b := b) (Y := Y) ((congrArg (fun t => t + 1) h1).trans hcar)]
    rw [CollRC_cast_comp b Y (congrArg (fun t => t + 1) (Nat.add_comm (b - 1) (m + b)).symm)
        ((congrArg (fun t => t + 1) h1).trans hcar) _,
      CollRC_cast_smul (b := b) (Y := Y)
        ((congrArg (fun t => t + 1) (Nat.add_comm (b - 1) (m + b)).symm).trans
          ((congrArg (fun t => t + 1) h1).trans hcar))]
    -- the two `δ`-images
    have hd1 : dPair b Y (m + b) Y'
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
            hcar1.symm)) Z1' := by
      refine CollRC_cast_symm b Y hcar1 Z1' (dPair b Y (m + b) Y') ?_
      rw [show Z1' = collarPhi b Y τ (m + 1) (collarSigma b hb1 Y τ hτ m Y') from hZ1']
      rw [collarSigma_spec b hb1 Y τ hτ m Y']
      exact (collarRelEq_apply b Y m hcar1 (dPair b Y (m + b) Y')).symm
    have hd2 : dPair b Y (b - 1) X
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
            hcar2.symm)) Z2' := by
      refine CollRC_cast_symm b Y hcar2 Z2' (dPair b Y (b - 1) X) ?_
      rw [show Z2' = collarPhi b Y τ 0 (collarSigmaLow b hb1 Y τ hτ X) from hZ2']
      rw [collarSigmaLow_spec b hb1 Y τ hτ X, relCohZeroAdd_eqToHom', collarDeltaLow_eqToHom']
      exact (CollRC_cast_comp b Y (lowCast b hb1) (Nat.zero_add b).symm
        (dPair b Y (b - 1) X)).trans
        (CollRC_cast_congr b Y ((lowCast b hb1).trans (Nat.zero_add b).symm) hcar2
          (dPair b Y (b - 1) X))
    have hM1c : M1 = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        hA1)) Z1 := by
      rw [hM1def, hd1]
      rw [mixedCupC_cast_right' (sphLoopCollarProd b Y) (b - 1) hcar1.symm
        (piStar b Y (b - 1) (sgStar b hb1 Y (b - 1) X)) Z1']
      rw [show Z1' = (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) (m + 1) b)
            (piStar b Y (m + 1) (collarSigma b hb1 Y τ hτ m Y')) τ from by
          rw [hZ1', collarPhi_apply]]
      rw [mixedCupC_assoc_cast (sphLoopCollarProd b Y) (b - 1) (m + 1) b
        (piStar b Y (b - 1) (sgStar b hb1 Y (b - 1) X))
        (piStar b Y (m + 1) (collarSigma b hb1 Y τ hτ m Y')) τ]
      rw [RelCoh_cast_eqToHom]
      rw [RelCoh_cast_shiftL (sphLoopCollarProd b Y) (h := hcar1.symm)]
      rw [CollRC_cast_comp b Y (Nat.add_assoc (b - 1) (m + 1) b)
        (congrArg (fun t => (b - 1) + t) hcar1.symm)]
      rw [show (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollQ b Y)) (b - 1) (m + 1))
            (piStar b Y (b - 1) (sgStar b hb1 Y (b - 1) X))
            (piStar b Y (m + 1) (collarSigma b hb1 Y τ hτ m Y'))
          = piStar b Y ((b - 1) + (m + 1)) T1 from by
        rw [hT1]
        exact (Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (collarProjY (Y := Y) b))
          (b - 1) (m + 1) ((Work.Thom.CohMap (collarSection (Y := Y) b hb1) ℚ (b - 1)).hom X)
          (collarSigma b hb1 Y τ hτ m Y')).symm]
    have hM2c : M2 = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        hA2)) Z2 := by
      rw [hM2def, hd2]
      rw [mixedCupC_cast_right' (sphLoopCollarProd b Y) (m + b) hcar2.symm
        (piStar b Y (m + b) (sgStar b hb1 Y (m + b) Y')) Z2']
      rw [show Z2' = (Work.Thom.mixedCupC ℚ (sphLoopCollarProd b Y) 0 b)
            (piStar b Y 0 (collarSigmaLow b hb1 Y τ hτ X)) τ from by
          rw [hZ2', collarPhi_apply]]
      rw [mixedCupC_assoc_cast (sphLoopCollarProd b Y) (m + b) 0 b
        (piStar b Y (m + b) (sgStar b hb1 Y (m + b) Y'))
        (piStar b Y 0 (collarSigmaLow b hb1 Y τ hτ X)) τ]
      rw [RelCoh_cast_eqToHom]
      rw [RelCoh_cast_shiftL (sphLoopCollarProd b Y) (h := hcar2.symm)]
      rw [CollRC_cast_comp b Y (Nat.add_assoc (m + b) 0 b)
        (congrArg (fun t => (m + b) + t) hcar2.symm)]
      rw [show (Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (CollQ b Y)) (m + b) 0)
            (piStar b Y (m + b) (sgStar b hb1 Y (m + b) Y'))
            (piStar b Y 0 (collarSigmaLow b hb1 Y τ hτ X))
          = piStar b Y ((m + b) + 0) T2 from by
        rw [hT2]
        exact (Work.Cohomology.cupNaturalH ℚ (TopCat.ofHom (collarProjY (Y := Y) b))
          (m + b) 0 ((Work.Thom.CohMap (collarSection (Y := Y) b hb1) ℚ (m + b)).hom Y')
          (collarSigmaLow b hb1 Y τ hτ X)).symm]
    -- assemble
    have h1eq : (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        ((congrArg (fun t => t + 1) h1).trans hcar))) M1
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) hγ1)) Z1 := by
      rw [hM1c]
      exact (CollRC_cast_comp b Y hA1 ((congrArg (fun t => t + 1) h1).trans hcar) Z1).trans
        (CollRC_cast_congr b Y (hA1.trans ((congrArg (fun t => t + 1) h1).trans hcar)) hγ1 Z1)
    have h2eq : (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t)
        ((congrArg (fun t => t + 1) (Nat.add_comm (b - 1) (m + b)).symm).trans
          ((congrArg (fun t => t + 1) h1).trans hcar)))) M2
        = (CategoryTheory.eqToHom (congrArg (fun t => (CollRC b Y).homology t) hγ2)) Z2 := by
      rw [hM2c]
      exact (CollRC_cast_comp b Y hA2
          ((congrArg (fun t => t + 1) (Nat.add_comm (b - 1) (m + b)).symm).trans
            ((congrArg (fun t => t + 1) h1).trans hcar)) Z2).trans
        (CollRC_cast_congr b Y (hA2.trans
          ((congrArg (fun t => t + 1) (Nat.add_comm (b - 1) (m + b)).symm).trans
            ((congrArg (fun t => t + 1) h1).trans hcar))) hγ2 Z2)
    rw [h1eq, h2eq, hXfin]
  -- ### Assembly
  have hmain : collarPhi b Y τ ((m + b - 1) + 1) U
      = collarRelEq b Y (m + b - 1)
          (collarDelta b Y (m + b - 1) (transT ↥(sphLoopCollarProd b Y) h1 W)) :=
    hL.trans hR.symm
  have hSig : collarSigma b hb1 Y τ hτ (m + b - 1) (transT ↥(sphLoopCollarProd b Y) h1 W)
      = U := by
    rw [collarSigma_eq_def b hb1 Y τ hτ (m + b - 1) (transT ↥(sphLoopCollarProd b Y) h1 W)]
    rw [show (LinearEquiv.ofBijective (collarPhi b Y τ ((m + b - 1) + 1))
          (hτ ((m + b - 1) + 1))).symm
        (collarRelEq b Y (m + b - 1)
          (collarDelta b Y (m + b - 1) (transT ↥(sphLoopCollarProd b Y) h1 W))) = U from by
      rw [← hmain]
      exact LinearEquiv.symm_apply_apply
        (LinearEquiv.ofBijective (collarPhi b Y τ ((m + b - 1) + 1)) (hτ ((m + b - 1) + 1))) U]
  have hUgoal : transT Y h2 U
      = ((-1 : ℚ) ^ (b - 1)) • T1
        + ((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) • transT Y h3 T2 := by
    rw [hU, transT_add, transT_smul, transT_smul, transT_comp, transT_comp]
    rw [transT_self, transT_congr ((h3.trans h2.symm).trans h2) h3]
  have hgoal : transT Y h2 (collarSigma b hb1 Y τ hτ (m + b - 1)
        (transT ↥(sphLoopCollarProd b Y) h1 W))
      = ((-1 : ℚ) ^ (b - 1)) • T1
        + ((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) • transT Y h3 T2 := by
    rw [hSig, hUgoal]
  -- convert the goal
  show transT Y h2 (collarSigma b hb1 Y τ hτ (m + b - 1)
        (transT ↥(sphLoopCollarProd b Y) h1 W))
      = ((-1 : ℚ) ^ (b - 1)) • T1
        + ((-1 : ℚ) ^ ((b - 1) * (m + b) + (m + b))) • transT Y h3 T2
  exact hgoal

end

end Work.Stems.Collar
