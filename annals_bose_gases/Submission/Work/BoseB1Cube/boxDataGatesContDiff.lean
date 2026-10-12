import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.NominalPerBox
import Submission.Work.BoseFixB1S.boxBogWeightedV2B1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseB1Cube

theorem boxDataGatesContDiff {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) Φ (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Φ x) ^ 2) = 1 →
          0 < Work.BoseFixB1.bV v μ u
          ∧ Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u)
            = Work.BoseFixB1.bW v h μ u
          ∧ 0 ≤ Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u)
          ∧ Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ)
                  (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
              ≤ Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
                  (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
          ∧ 0 ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ
          ∧ Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ
              * Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ
              - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ
              ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ := by
  -- The three analytic inputs of the box-data gates.
  obtain ⟨εreg, K, hεreg, _hK, hM1info⟩ :=
    Work.BoseFixB1S.boxM1Info (v := v) h hv hv1 hvrad hR hv_supp hav
  refine ⟨εreg, hεreg, ?_⟩
  intro μ hAdm n Φ hΦc u hu hΦ
  -- the three parameter facts from admissibility
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  -- the regularity parameter is the fixed `M = mValue`
  have hM1 : 1 ≤ Work.BoseFixB1.bM v μ := by
    rw [Work.BoseFixB1.bM, Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  -- the two `boxM1` facts supplied by `boxM1Info`
  obtain ⟨hm1nn, _hm1ub, hm1le2⟩ := hM1info μ hAdm u
  -- positivity of the box volume
  have hV : 0 < Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hvan : ∀ x y : EuclideanSpace ℝ (Fin 3),
      (x ∉ Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
        ∨ y ∉ Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u) →
      Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u x y = 0 :=
    fun x y hxy => Work.BoseFixB1.wSmallPair_eq_zero_of_notMem_dlBox hM1 hℓ hd u hxy
  refine ⟨hV, ?_, hm1nn, hm1le2, ?_, ?_⟩
  · -- `boxM1 … = w1MassB … = bW …`
    show Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ)
        (Submission.BoseGases.dlBox (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u)
        (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u)
      = Work.BoseFixB1.bW v h μ u
    rw [Work.BoseFixB1S.boxM1_eq_nested u hvan]
    rfl
  · -- `0 ≤ boxPairCount`: a sum of integrals of squares
    refine Finset.sum_nonneg (fun p _ => ?_)
    exact integral_nonneg (fun x => sq_nonneg _)
  · -- the flat-count Jensen at the normalised state
    have hΦ' : (∫ x in Submission.BoseGases.abox n (Work.BoseFixB1.bSide v μ),
        (Φ x) ^ 2) = 1 := hΦ
    have hJ := Work.BoseFixB1S.boxFlatSqJensen (N := n) (ℓ := Work.BoseFixB1.bSide v μ)
      (volA := Work.BoseFixB1.bV v μ u) (A := Work.BoseFixB1.bA v μ u) hℓ hV
      (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      (Work.SmallBoxSliding.boxMass_eq_measureReal (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      (Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      (hΦc.continuous)
    rw [hΦ', mul_one, one_mul] at hJ
    simpa only [pow_two] using hJ

end Work.BoseB1Cube


/-!
# `Submission.Work.BoseB1Cube.boxDataGatesContDiff` — the six box-data gates at the **carrier-free**
# (plain `ContDiff`) state class

Provenance: a copy of `Submission/Work/BoseB1Cube/boxDataGates.lean` with the state carrier
`Work.BoseKinLoc.BoxState n ℓ` replaced by a plain `Φ : X n → ℝ` plus `hΦc : ContDiff ℝ ⊤ Φ`
(the `BoxState` fields `symm`/`nezero` are unused there: its proof consumes only
`Φ.contDiff.continuous`, cf. `NOTE_to_lead_stateClass.md`).  Needed by the carrier-free rung
`sbWordSlot_ge_payPortContDiff`, in the clash-free import cone (see the docstring of
`slidingBogPortCubeContDiff`).  Statement otherwise identical to `boxDataGates`.
-/
