import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseFixB1.Cube.Loc.cnPlusBoxInd_fibreSplit
import Submission.Work.BoseFixB1.Cube.Loc.fsKinPGen_chiSmallB_integrable
import Submission.Work.BoseFixB1.Cube.Loc.qLHSword_fibre_integrable
import Submission.Work.BoseFixB1.Cube.Loc.tBdiagFormInd_fibre_integrable
import Submission.Work.BoseFixB1B.matchedWindowDefs
import Submission.Work.BoseFixB1S.slotSplitCnPlusBoxInd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Cube.Loc.sbWordCube_fibreSplit_of_integrable` — the Step-Loc fibre formula,
# assembled

Holder of `Submission/Work/BoseFixB1/Cube/Loc/sbWordCube_fibreSplit_of_integrable.lean`.

## What is proved here

The functional-level fibre formula for the **matched** (single cube cutoff) word

    sbWordCube v h μ u Φ = ∫ y in Dloc m ℓ (bA v μ u), sbWordCube v h μ u (fibre k m Φ y) ,

at the honest hypothesis set of `Loc/FINDING_sbWordCube_fibreSplit.md` §5: `ContDiff ℝ ⊤ Φ`, the
a.e. sub-sector support `SubsectorSupp`, and the potential slot's integrability `(★) = hint`.

## How it is assembled

* `sbWordCube = sbKinCube + sbPot` and
  `sbKinCube = bGapCoeff·cnPlusBoxInd + cubeSpectral` are **definitional**
  (`Submission/Work/BoseFixB1B/matchedWindowDefs.lean`), and `cubeSpectral` is *definitionally*
  `tBwordKinInd = tBdiagFormInd … (fsKinCoeff ·)`; `sbPot` is *definitionally*
  `qLHSword ℓ μ (wSmallPair …) (wSmall1Pair …)` (`Work.BoseFixB1.sbPot` = `qLHSwordB`).  So the
  left-hand side and the integrand of the right-hand side are the same sum of the three slot
  functionals, and the whole content is the *additivity* of `∫` across that sum.

* The three **slot identities** are the proved
  `cnPlusBoxInd_fibreSplit`, `tBdiagFormInd_fibreSplit`, `qLHSword_fibreSplit_of_integrable`
  (the kinetic `hint` is discharged by the proved `fsKinPGen_chiSmallB_integrable`, the cn slot's
  `Continuous Φ` by `ContDiff ℝ ⊤ Φ`).

* The **integrability** of each of the three fibre marginals on `abox m ℓ` — needed, because
  Mathlib's Bochner integral is additive only for integrable summands — comes from
  * `cnPlusBoxInd_fibre_integrable` (this file) = the per-slot slice integrability
    `Work.BoseFixB1S.integrableOn_slice_boxQInd_fst` summed over the `k` slots;
  * `Work.BoseFixB1.Cube.Loc.tBdiagFormInd_fibre_integrable` (delegated sibling);
  * `Work.BoseFixB1.Cube.Loc.qLHSword_fibre_integrable` (delegated sibling);
  and is transported from `abox m ℓ` to `Dloc m ℓ A ⊆ abox m ℓ` by
  `Measure.restrict_mono` + `Integrable.mono_measure`.

* The **degenerate case** `bSide v μ ≤ 0`: then `abox N (bSide v μ)` is null for `N ≥ 1`, all three
  slot functionals vanish (`cnPlusBoxInd_eq_zero_of_nonpos`, `tBdiagFormInd_eq_zero_of_nonpos`,
  `qLHSword_eq_zero_of_nonpos`), hence so does `sbWordCube` — and the right-hand side is `0` for
  *every* `y` because the fibre state has arity `k ≥ 1`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1.Cube.Loc

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The degenerate case: a non-positive sliding side -/

/-- The excited count vanishes when the ambient box is null. -/
lemma cnPlusBoxInd_eq_zero_of_nonpos {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : a ≤ 0)
    (A : Set E3) (V : ℝ) (Ψ : X N → ℝ) :
    Work.UBBInputs8.cnPlusBoxInd a A V Ψ = 0 := by
  rw [Work.UBBInputs8.cnPlusBoxInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  exact MeasureTheory.setIntegral_measure_zero _ (abox_measure_zero_of_nonpos hN ha)

/-- The windowed `p`-diagonal form vanishes when the ambient box is null. -/
lemma tBdiagFormInd_eq_zero_of_nonpos {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : a ≤ 0)
    (A : Set E3) (V : ℝ) (χ : E3 → ℝ) (F : ℝ → ℝ) (Ψ : X N → ℝ) :
    Work.UBBInputs8.tBdiagFormInd a A V χ F Ψ = 0 := by
  rw [Work.UBBInputs8.tBdiagFormInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hI : (fun p : E3 => F ‖p‖ * ((a ^ 3)⁻¹ *
      ∫ x in abox N a, ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x‖ ^ 2))
      = fun _ : E3 => (0 : ℝ) := by
    funext p
    rw [MeasureTheory.setIntegral_measure_zero _ (abox_measure_zero_of_nonpos hN ha)]
    ring
  rw [hI, MeasureTheory.integral_zero, mul_zero]

/-- The potential word vanishes when the ambient box is null. -/
lemma qLHSword_eq_zero_of_nonpos {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : a ≤ 0) (μ : ℝ)
    (w w1 : E3 → E3 → ℝ) (Ψ : X N → ℝ) :
    Submission.BoseGases.qLHSword (N := N) a μ w w1 Ψ = 0 := by
  show (∫ x in abox N a, Ψ x ^ 2 * Submission.BoseGases.qLHSden N a μ w w1 x) = 0
  exact MeasureTheory.setIntegral_measure_zero _ (abox_measure_zero_of_nonpos hN ha)

/-- **The matched word vanishes on a null box.**  If `bSide v μ ≤ 0` then every slot functional
integrates over the null box `abox N (bSide v μ)`, so `sbWordCube` is `0` for every state of arity
`N ≥ 1`. -/
lemma sbWordCube_eq_zero_of_bSide_nonpos {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    (u : E3) {N : ℕ} (hN : 0 < N) {Ψ : X N → ℝ} (hℓ : Work.BoseFixB1.bSide v μ ≤ 0) :
    Work.BoseFixB1B.sbWordCube v h μ u Ψ = 0 := by
  have h1 : Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
      (Work.BoseFixB1.bV v μ u) Ψ = 0 :=
    cnPlusBoxInd_eq_zero_of_nonpos hN hℓ _ _ _
  have h2 : Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
      (Work.BoseFixB1.bV v μ u)
      (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) Ψ = 0 :=
    tBdiagFormInd_eq_zero_of_nonpos hN hℓ _ _ _ _ _
  have h3 : Submission.BoseGases.qLHSword (N := N) (Work.BoseFixB1.bSide v μ) μ
      (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u v)
      (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u) Ψ = 0 :=
    qLHSword_eq_zero_of_nonpos hN hℓ _ _ _ _
  rw [show Work.BoseFixB1B.sbWordCube v h μ u Ψ
      = (Work.BoseFixB1.bGapCoeff v μ
            * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                (Work.BoseFixB1.bV v μ u) Ψ
          + Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
              (Work.BoseFixB1.bV v μ u)
              (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u)
              (Submission.BoseGases.fsKinCoeff
                (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) Ψ)
        + Submission.BoseGases.qLHSword (N := N) (Work.BoseFixB1.bSide v μ) μ
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u) Ψ from rfl]
  rw [h1, h2, h3]
  ring

/-! ## 2. The CN slot's fibre integrability (from the proved per-slot slice integrability) -/

/-- **The excited count of the fibre is integrable in the out-of-box configuration.**  This is the
sum over the `k` in-box slots of the proved per-slot slice integrability
`Work.BoseFixB1S.integrableOn_slice_boxQInd_fst` (which needs `V = |A|` and `Φ` only
`Continuous`).

The `hV` hypothesis is the identification `V = (volume : Measure E3).real A = |A|` of the box
volume used in the normaliser of `boxQInd` with the Lebesgue measure of the box. -/
theorem cnPlusBoxInd_fibre_integrable {k m : ℕ} {a : ℝ} (ha : 0 < a) (hk : 0 < k)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube a) (V : ℝ)
    (hV : V = (volume : Measure E3).real A)
    {Φ : X (k + m) → ℝ} (hΦc : Continuous Φ) :
    MeasureTheory.IntegrableOn
      (fun y : X m => Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ y))
      (Submission.BoseGases.abox m a) MeasureTheory.volume := by
  classical
  have hint : ∀ j : Fin k, MeasureTheory.IntegrableOn (fun w : X m =>
      ∫ u in Submission.BoseGases.abox k a,
        (Work.UBBInputs8.boxQInd V A j
          (fun u' => Φ (Submission.BoseGases.mergeBlock k m (u', w))) u) ^ 2)
      (Submission.BoseGases.abox m a) MeasureTheory.volume :=
    fun j => Work.BoseFixB1S.integrableOn_slice_boxQInd_fst ha hA hAc hV j hΦc
  have hsum : MeasureTheory.IntegrableOn (fun w : X m =>
      ∑ j : Fin k, ∫ u in Submission.BoseGases.abox k a,
        (Work.UBBInputs8.boxQInd V A j
          (fun u' => Φ (Submission.BoseGases.mergeBlock k m (u', w))) u) ^ 2)
      (Submission.BoseGases.abox m a) MeasureTheory.volume :=
    MeasureTheory.integrable_finsetSum Finset.univ (fun j _ => hint j)
  refine hsum.congr (Filter.Eventually.of_forall fun w => ?_)
  show (∑ j : Fin k, ∫ u in Submission.BoseGases.abox k a,
        (Work.UBBInputs8.boxQInd V A j
          (fun u' => Φ (Submission.BoseGases.mergeBlock k m (u', w))) u) ^ 2)
      = Work.UBBInputs8.cnPlusBoxInd a A V (fibre k m Φ w)
  rw [fibre_eq_sbs_slice]
  rfl

/-! ## 3. The kinetic and potential slots' fibre integrability (delegated siblings) -/

/-- Kinetic slot: the fibre marginal of the windowed `p`-diagonal form is integrable.  Wrapper for
the delegated sibling `Work.BoseFixB1.Cube.Loc.tBdiagFormInd_fibre_integrable`. -/
theorem kinFibre_integrable_aux {k m : ℕ} {a V : ℝ} (ha : 0 < a) (hk : 0 < k)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ Submission.BoseGases.acube a)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχA : ∀ z, z ∉ A → χ z = 0)
    {F : ℝ → ℝ} (hFm : Measurable F) (hFnn : ∀ r, 0 ≤ F r)
    (hint : ∀ (N : ℕ) (Ψ : X N → ℝ), ContDiff ℝ (⊤ : ENat) Ψ → ∀ i : Fin N,
      MeasureTheory.Integrable (fun p : E3 => F ‖p‖ *
        ((a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd V A i Ψ) i x‖ ^ 2)))
    {Φ : X (k + m) → ℝ} (hΦc : ContDiff ℝ (⊤ : ENat) Φ) (hsupp : SubsectorSupp k m a A Φ) :
    MeasureTheory.IntegrableOn
      (fun y : X m => Work.UBBInputs8.tBdiagFormInd a A V χ F (fibre k m Φ y))
      (Submission.BoseGases.abox m a) MeasureTheory.volume := by
  exact Work.BoseFixB1.Cube.Loc.tBdiagFormInd_fibre_integrable ha hk hA hAc hχc hχs hχA hFm hFnn
    hint hΦc hsupp

/-- Potential slot: the fibre marginal of the potential word is integrable.  Wrapper for the
delegated sibling `Work.BoseFixB1.Cube.Loc.qLHSword_fibre_integrable`.  (Its proof is the Fubini step
of the corpus's `qLHSden1_expect_eq_slice` run in the *marginal* direction: hypothesis `hint`
collapses a.e. to the block-1 density `Φ²·qLHSden1` on the sub-sector, which the measure-preserving
block merge pushes to the product measure, whereupon restricted Fubini yields the integrability of
the `y`-marginal `qLHSword (N := k) … (fibre k m Φ y)`.) -/
theorem potFibre_integrable_aux {k m : ℕ} {a μ : ℝ} (ha : 0 < a) (hk : 0 < k)
    {A : Set E3} (hA : MeasurableSet A)
    {w w1 : E3 → E3 → ℝ}
    (hw : ∀ x y, x ∉ A → w x y = 0) (hw' : ∀ x y, y ∉ A → w x y = 0)
    (hw1 : ∀ x, x ∉ A → Submission.BoseGases.w1Fibre a w1 x = 0)
    {Φ : X (k + m) → ℝ} (hΦm : Measurable Φ) (hsupp : SubsectorSupp k m a A Φ)
    (hint : MeasureTheory.IntegrableOn (fun x => (Φ x) ^ 2 *
        Submission.BoseGases.qLHSden (k + m) a μ w w1 x)
        (Submission.BoseGases.abox (k + m) a) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn
      (fun y : X m => Submission.BoseGases.qLHSword (N := k) a μ w w1 (fibre k m Φ y))
      (Submission.BoseGases.abox m a) MeasureTheory.volume := by
  exact Work.BoseFixB1.Cube.Loc.qLHSword_fibre_integrable ha hk hA hw hw' hw1 hΦm hsupp hint

/-! ## 4. The assembly -/

/-- Step Loc, ingredient (iii), assembled: the functional-level fibre formula for the matched word,
at the honest hypothesis set.  Assembles the three PROVED slot splittings
`cnPlusBoxInd_fibreSplit`, `tBdiagFormInd_fibreSplit`, `qLHSword_fibreSplit_of_integrable` (all in
`Submission/Work/BoseFixB1/Cube/Loc/`, axiom-clean) via the definitional split
`sbWordCube = bGapCoeff·cnPlusBoxInd + cubeSpectral + qLHSword`.

`hint` is the potential slot's integrability `(★)` of
`Loc/FINDING_sbWordCube_fibreSplit.md` §5 — load-bearing, and not implied by the state hypotheses.
The prover may add the regularity/integrability side conditions the three slots need (the kinetic
slot's per-slot `p`-integrability is discharged by the PROVED `fsKinPGen_chiSmallB_integrable`;
`ContDiff ℝ ⊤ Φ` supplies `Continuous Φ` for the cn slot), and should case-split `bSide v μ ≤ 0`.
Do not weaken the conclusion and do not drop `hint`. -/
theorem sbWordCube_fibreSplit_of_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {k m : ℕ} (hk : 0 < k) {μ : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    {Φ : Submission.BoseGases.X (k + m) → ℝ} (hΦc : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : Work.BoseFixB1.Cube.Loc.SubsectorSupp k m (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) Φ)
    (hint : MeasureTheory.IntegrableOn (fun x =>
        (Φ x) ^ 2 * Submission.BoseGases.qLHSden (k + m) (Work.BoseFixB1.bSide v μ) μ
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u) x)
      (Submission.BoseGases.abox (k + m) (Work.BoseFixB1.bSide v μ)) MeasureTheory.volume) :
    Work.BoseFixB1B.sbWordCube v h μ u Φ
      = ∫ y in Work.BoseFixB1.Cube.Loc.Dloc m (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u),
          Work.BoseFixB1B.sbWordCube v h μ u (Work.BoseFixB1.Cube.Loc.fibre k m Φ y) := by
  by_cases hside : Work.BoseFixB1.bSide v μ ≤ 0
  · -- ### degenerate case: the box is null and both sides vanish
    have hNkm : 0 < k + m := lt_of_lt_of_le hk (Nat.le_add_right k m)
    have hL : Work.BoseFixB1B.sbWordCube v h μ u Φ = 0 :=
      sbWordCube_eq_zero_of_bSide_nonpos u hNkm hside
    have hR : (∫ y in Work.BoseFixB1.Cube.Loc.Dloc m (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bA v μ u),
          Work.BoseFixB1B.sbWordCube v h μ u (Work.BoseFixB1.Cube.Loc.fibre k m Φ y)) = 0 := by
      rw [MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y =>
        sbWordCube_eq_zero_of_bSide_nonpos u hk hside)]
    rw [hL, hR]
  · -- ### the honest case `0 < bSide v μ`
    have ha : 0 < Work.BoseFixB1.bSide v μ := not_le.mp hside
    have hA : MeasurableSet (Work.BoseFixB1.bA v μ u) :=
      Work.SmallBoxSliding.measurableSet_dlBox _ _ _
    have hAc : Work.BoseFixB1.bA v μ u ⊆ Submission.BoseGases.acube (Work.BoseFixB1.bSide v μ) :=
      Work.SmallBoxSliding.dlBox_subset_acube _ _ _
    have hV : Work.BoseFixB1.bV v μ u
        = (volume : Measure E3).real (Work.BoseFixB1.bA v μ u) :=
      Work.SmallBoxSliding.boxMass_eq_measureReal _ _ _
    have hM1 : 1 ≤ Work.BoseFixB1.bM v μ := by
      rw [bM_eq v μ]; norm_num
    have hd : 0 < Work.BoseFixB1.bD v μ := bD_pos_of_bSide_pos ha
    have hχ0 : ∀ z : E3, z ∉ Work.BoseFixB1.bA v μ u →
        Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u z = 0 :=
      fun z hz => Work.BoseFixB1S.win.chiSmallB_eq_zero_of_not_mem_dlBox hM1 ha hd u z hz
    -- ### the two-sided vanishing of the localised kernels
    have hw : ∀ x y, x ∉ Work.BoseFixB1.bA v μ u →
        Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u v x y = 0 := by
      intro x y hx
      simp only [Submission.BoseGases.wSmallPair, hχ0 x hx, zero_mul]
    have hw' : ∀ x y, y ∉ Work.BoseFixB1.bA v μ u →
        Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u v x y = 0 := by
      intro x y hy
      simp only [Submission.BoseGases.wSmallPair, hχ0 y hy, mul_zero]
    have hw1 : ∀ x, x ∉ Work.BoseFixB1.bA v μ u →
        Submission.BoseGases.w1Fibre (Work.BoseFixB1.bSide v μ)
          (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u) x = 0 := by
      intro x hx
      have hzero : (fun y : E3 => Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ)
          (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u x y) = fun _ : E3 => (0 : ℝ) := by
        funext y
        unfold Submission.BoseGases.wSmall1Pair
        simp only [Submission.BoseGases.wSmallPair, hχ0 x hx, zero_mul]
      show (∫ y in Submission.BoseGases.acube (Work.BoseFixB1.bSide v μ),
          Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u x y) = 0
      rw [hzero]
      simp
    -- ### the three slot identities
    have hCn := cnPlusBoxInd_fibreSplit (k := k) (m := m) (a := Work.BoseFixB1.bSide v μ) ha hk
      (A := Work.BoseFixB1.bA v μ u) hA hAc (Work.BoseFixB1.bV v μ u) hΦc.continuous hsupp
    have hKin := tBdiagFormInd_fibreSplit (k := k) (m := m) (a := Work.BoseFixB1.bSide v μ)
      (V := Work.BoseFixB1.bV v μ u) ha hk hA hAc
      (χ := Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      (by
        have h := Work.BoseFixB1S.win.contDiff_chiSmallB 0 (Work.BoseFixB1.bM v μ)
          (by simpa using hM1) (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ)
          (ne_of_gt ha) (ne_of_gt hd) u
        simpa using h.continuous)
      (Submission.BoseGases.chiSmallB_hasCompactSupport hM1 ha u)
      (fun z hz => hχ0 z hz)
      (F := Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
      (Work.BoseKinLoc.Kinetic.measurable_fsKinCoeff _)
      (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ r)
      (fun N Ψ hΨ i => fsKinPGen_chiSmallB_integrable (h := h) u N Ψ hΨ i)
      hΦc hsupp
    have hPot := qLHSword_fibreSplit_of_integrable (k := k) (m := m)
      (a := Work.BoseFixB1.bSide v μ) (μ := μ) ha hk hA
      (w := Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u v)
      (w1 := Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      hw hw' hw1 hΦc.continuous.measurable hsupp hint
    -- ### integrability of the three fibre marginals on `abox m ℓ`
    have iCn : MeasureTheory.IntegrableOn (fun y : X m =>
        Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
          (Work.BoseFixB1.bV v μ u) (fibre k m Φ y))
        (Submission.BoseGases.abox m (Work.BoseFixB1.bSide v μ)) MeasureTheory.volume :=
      cnPlusBoxInd_fibre_integrable ha hk hA hAc _ hV hΦc.continuous
    have iKin : MeasureTheory.IntegrableOn (fun y : X m =>
        Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
          (Work.BoseFixB1.bV v μ u)
          (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u)
          (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
          (fibre k m Φ y))
        (Submission.BoseGases.abox m (Work.BoseFixB1.bSide v μ)) MeasureTheory.volume :=
      kinFibre_integrable_aux ha hk hA hAc (by
        have h := Work.BoseFixB1S.win.contDiff_chiSmallB 0 (Work.BoseFixB1.bM v μ)
          (by simpa using hM1) (ℓ := Work.BoseFixB1.bSide v μ) (d := Work.BoseFixB1.bD v μ)
          (ne_of_gt ha) (ne_of_gt hd) u
        simpa using h.continuous)
      (Submission.BoseGases.chiSmallB_hasCompactSupport hM1 ha u)
      (fun z hz => hχ0 z hz)
      (Work.BoseKinLoc.Kinetic.measurable_fsKinCoeff _)
      (fun r => Submission.BoseGases.fsKinCoeff_nonneg _ r)
      (fun N Ψ hΨ i => fsKinPGen_chiSmallB_integrable (h := h) u N Ψ hΨ i) hΦc hsupp
    have iPot : MeasureTheory.IntegrableOn (fun y : X m =>
        Submission.BoseGases.qLHSword (N := k) (Work.BoseFixB1.bSide v μ) μ
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u) (fibre k m Φ y))
        (Submission.BoseGases.abox m (Work.BoseFixB1.bSide v μ)) MeasureTheory.volume :=
      potFibre_integrable_aux ha hk hA hw hw' hw1 hΦc.continuous.measurable hsupp hint
    -- ### transport to `Dloc`
    have hμD : (volume : Measure (X m)).restrict
          (Dloc m (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u))
        ≤ (volume : Measure (X m)).restrict
          (Submission.BoseGases.abox m (Work.BoseFixB1.bSide v μ)) :=
      Measure.restrict_mono (Dloc_subset_abox m (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u))
        le_rfl
    have iCnD : Integrable (fun y : X m =>
        Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
          (Work.BoseFixB1.bV v μ u) (fibre k m Φ y))
        ((volume : Measure (X m)).restrict
          (Dloc m (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u))) :=
      (show Integrable (fun y : X m =>
          Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
            (Work.BoseFixB1.bV v μ u) (fibre k m Φ y))
          ((volume : Measure (X m)).restrict
            (Submission.BoseGases.abox m (Work.BoseFixB1.bSide v μ))) from iCn).mono_measure hμD
    have iKinD : Integrable (fun y : X m =>
        Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
          (Work.BoseFixB1.bV v μ u)
          (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u)
          (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
          (fibre k m Φ y))
        ((volume : Measure (X m)).restrict
          (Dloc m (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u))) :=
      (show Integrable (fun y : X m =>
          Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
            (Work.BoseFixB1.bV v μ u)
            (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u)
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
            (fibre k m Φ y))
          ((volume : Measure (X m)).restrict
            (Submission.BoseGases.abox m (Work.BoseFixB1.bSide v μ))) from iKin).mono_measure hμD
    have iPotD : Integrable (fun y : X m =>
        Submission.BoseGases.qLHSword (N := k) (Work.BoseFixB1.bSide v μ) μ
          (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u v)
          (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u) (fibre k m Φ y))
        ((volume : Measure (X m)).restrict
          (Dloc m (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u))) :=
      (show Integrable (fun y : X m =>
          Submission.BoseGases.qLHSword (N := k) (Work.BoseFixB1.bSide v μ) μ
            (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u v)
            (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u) (fibre k m Φ y))
          ((volume : Measure (X m)).restrict
            (Submission.BoseGases.abox m (Work.BoseFixB1.bSide v μ))) from iPot).mono_measure hμD
    have iX : Integrable (fun y : X m =>
        Work.BoseFixB1.bGapCoeff v μ
            * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
              (Work.BoseFixB1.bV v μ u) (fibre k m Φ y))
        ((volume : Measure (X m)).restrict
          (Dloc m (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u))) :=
      iCnD.const_mul (Work.BoseFixB1.bGapCoeff v μ)
    have iXD : Integrable (fun y : X m =>
        Work.BoseFixB1.bGapCoeff v μ
            * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
              (Work.BoseFixB1.bV v μ u) (fibre k m Φ y)
          + Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
              (Work.BoseFixB1.bV v μ u)
              (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u)
              (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
              (fibre k m Φ y))
        ((volume : Measure (X m)).restrict
          (Dloc m (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u))) :=
      iX.add iKinD
    -- ### the definitional splitting of the left-hand side
    have hdefL : Work.BoseFixB1B.sbWordCube v h μ u Φ
        = (Work.BoseFixB1.bGapCoeff v μ
              * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                (Work.BoseFixB1.bV v μ u) Φ
            + Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                (Work.BoseFixB1.bV v μ u)
                (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u)
                (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) Φ)
          + Submission.BoseGases.qLHSword (N := k + m) (Work.BoseFixB1.bSide v μ) μ
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u) Φ := rfl
    -- ### the same splitting of the right-hand side's integrand
    have hdefR : (∫ y in Work.BoseFixB1.Cube.Loc.Dloc m (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bA v μ u),
          Work.BoseFixB1B.sbWordCube v h μ u (Work.BoseFixB1.Cube.Loc.fibre k m Φ y))
        = ∫ y in Work.BoseFixB1.Cube.Loc.Dloc m (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bA v μ u),
            ((Work.BoseFixB1.bGapCoeff v μ
                * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u) (fibre k m Φ y)
              + Work.UBBInputs8.tBdiagFormInd (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                  (Work.BoseFixB1.bV v μ u)
                  (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ)
                    (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
                  (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
                  (fibre k m Φ y))
              + Submission.BoseGases.qLHSword (N := k) (Work.BoseFixB1.bSide v μ) μ
                  (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ)
                    (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u v)
                  (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ)
                    (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
                  (fibre k m Φ y)) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      rfl
    rw [hdefL, hdefR]
    rw [MeasureTheory.integral_add iXD iPotD, MeasureTheory.integral_add iX iKinD,
      MeasureTheory.integral_const_mul, hCn, hKin, hPot]

end Work.BoseFixB1.Cube.Loc
