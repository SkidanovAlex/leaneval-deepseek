import ChallengeDeps
import Submission.Work.BoseB1Cube.NominalPerBox
import Submission.Work.BoseB1Cube.sharpJointCoreSelf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 4000000

theorem paySurplusSlotFreeContDiff {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ μp : ℝ, μ ≤ μp →
        ∀ (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          0 < Work.BoseFixB1.bV v μ u →
          1 ≤ μp * Work.BoseFixB1.bV v μ u →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
            Φ x ≠ 0 →
              ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
          (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Φ x) ^ 2) = 1 →
          Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u)
              = Work.BoseFixB1.bW v h μ u →
          0 ≤ Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u) →
          Work.BoseFixB1S.boxM1 (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u)
              ≤ Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
                  (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h)) →
          0 ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ →
          Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ
              * Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ
              - Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ
              ≤ Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ →
          Work.BoseFixB1.a0MainLocBox (Work.BoseFixB1.bV v μ u) μp (Work.BoseFixB1.bW v h μ u)
              (Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bA v μ u) Φ)
            + (1 / 2) * ((Work.BoseFixB1S.boxM2 (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bA v μ u)
                    (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
                  - Work.BoseFixB1.bW v h μ u)
                / (Work.BoseFixB1.bV v μ u) ^ 2)
                * Work.BoseFixB1S.boxPairCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bA v μ u) Φ
            + Work.BoseFixB1.bA2 v h μ Φ u
            - C * (_root_.BoseGases.a v)
                * (μp + Work.BoseFixB1S.boxFlatCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bA v μ u) Φ / Work.BoseFixB1.bV v μ u)
                * Work.BoseFixB1S.boxQCount (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bA v μ u) Φ
          ≤ Work.BoseFixB1S.boxQSum (Work.BoseFixB1.bV v μ u) (Work.BoseFixB1.bSide v μ) μp
              (Work.BoseFixB1.bA v μ u)
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u v)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u)
              (Submission.BoseGases.wSmallPair (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u (Submission.BoseGases.g2 v h))
              (Submission.BoseGases.omC (Classical.choose h))
              Φ := by
  classical
  -- ## the sharp joint core at a free slot, at `M = mValue`
  obtain ⟨C, hC0, hcore⟩ :=
    Work.BoseFixB1S.boxJointIneqSharpB1 (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h hav
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨εg, hεg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨εg, C, hεg, hC0, ?_⟩
  intro μ hAdm μp hμle n Φ hΦc u hu hvol hμpV hsupp hnorm hW hM1nn hM2 hPcnn hcS2
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hR16, hRχ⟩ := hreg μ hAdm.1 (Work.BoseFixB1.adm_dilute hAdm)
  -- ## normalise the per-box abbreviations
  simp only [Work.BoseFixB1.bV, Work.BoseFixB1.bA, Work.BoseFixB1.bSide, Work.BoseFixB1.bD,
    Work.BoseFixB1.bM, Work.BoseFixB1.bW, Work.BoseFixB1.bA2] at hW hM1nn hM2 hPcnn hcS2 hμpV ⊢
  simp only [Work.BoseFixB1.M_eq_mValue] at hW hM1nn hM2 hPcnn ⊢
  -- ## the sharp core at the slot `μp`
  have hsh := hcore (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μp)
    hℓ hd (lt_of_lt_of_le hμ hμle) hR16 hRχ u hvol hμpV (N := n)
    (Φ := Φ) hΦc.continuous hnorm hsupp
    hM1nn hM2 hPcnn hcS2
  -- ## the geometry of the sliding box
  have hAmeas : MeasurableSet (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox _ _ _
  have hvolA : Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hAc : Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      ⊆ Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :=
    Work.SmallBoxSliding.dlBox_subset_acube _ _ _
  have hMv : 1 ≤ Work.BoseBox.mValue := by norm_num [Work.BoseBox.mValue]
  -- ## the integrability bundles
  obtain ⟨hint0, hint1, hint2, hint3, hint4, hint5⟩ :=
    Work.BoseFixB1.Clean.boxFragmentsIntegrable (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
      hMv hℓ hd hR16 hRχ u (Φ := Φ) hΦc.continuous
  obtain ⟨hBlk, hSq, hCr⟩ :=
    Work.BoseFixB1.boxPairBlockIntegrable (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
      hMv hℓ hd hR16 hRχ u (Φ := Φ) hΦc.continuous
  obtain ⟨hW2i, hFib⟩ :=
    Work.BoseFixB1.boxQ0SlackIntegrable (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
      hMv hℓ hd hR16 hRχ u
  -- ## the kernel identities
  have hw1 : ∀ x y : E3, Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x y
      = Submission.BoseGases.wSmallPair Work.BoseBox.mValue
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v x y
        * (1 - Submission.BoseGases.omC (Classical.choose h) x y) := by
    intro x y
    rw [Work.BoseFixB1.wSmall1Pair_eq_mul h u x y]
    simp only [Submission.BoseGases.omC]
  have hw2 : ∀ x y : E3, Submission.BoseGases.wSmallPair Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h) x y
      = Submission.BoseGases.wSmallPair Work.BoseBox.mValue
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v x y
        * (1 - Submission.BoseGases.omC (Classical.choose h) x y ^ 2) := by
    intro x y
    rw [Work.BoseFixB1.wSmallPair_g2_eq_mul h u x y, Work.BoseFixB1.wSmall1Pair_eq_mul h u x y]
    simp only [Submission.BoseGases.omC]
    ring
  have hwsym : ∀ x y : E3, Submission.BoseGases.wSmallPair Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v x y
      = Submission.BoseGases.wSmallPair Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v y x :=
    fun x y => Submission.BoseGases.wSmallPair_symm hMv u (Submission.BoseGases.radial_even hvrad) x y
  have homsym : ∀ x y : E3, Submission.BoseGases.omC (Classical.choose h) x y
      = Submission.BoseGases.omC (Classical.choose h) y x := by
    intro x y
    have hw0 : ∀ z : E3, Classical.choose h (-z) = Classical.choose h z :=
      Submission.BoseGases.radial_even (Classical.choose_spec h).1
    simp only [Submission.BoseGases.omC]
    rw [show y - x = -(x - y) from by abel, hw0]
  -- ## (R1) at the slot `μp`
  have hred0 := Work.BoseFixB1S.Clean.boxQSum_sub_boxA2_blockSum (N := n)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (volA := Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (μ := μp) (A := Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    hℓ hvol hAmeas hvolA hAc
    (w := Submission.BoseGases.wSmallPair Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v)
    (w₁ := Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (w₂ := Submission.BoseGases.wSmallPair Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h))
    (om := Submission.BoseGases.omC (Classical.choose h))
    hw1 hw2 hwsym homsym (Φ := Φ) hΦc.continuous
    hint0 hint1 hint2 hint3 hint4 hint5
  have hred1 := Work.BoseFixB1.boxSqPart_add_boxCrossPart_eq_blockSum (N := n)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (volA := Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (A := Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (w := Submission.BoseGases.wSmallPair Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v)
    (w₁ := Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (om := Submission.BoseGases.omC (Classical.choose h))
    (Φ := Φ) hSq hCr hBlk hw1
  -- ## the `A₀`-slack at the slot `μp`
  have hslack := Work.BoseFixB1.Clean.boxQ0_sub_a0MainLocBox_eq (N := n)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (volA := Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (μ := μp) (A := Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    hℓ hvol hAmeas hvolA hAc hW2i hFib (Φ := Φ)
    hΦc.continuous
  -- ## assemble: replace `W = bW` in the goal by the box mass `M₁` (the corpus lemmas spell the
  --    pair row with `boxM1`), then the chain `(R1) + sharp core + slack` is linear
  rw [← hW]
  simp only [div_eq_mul_inv] at hsh hred0 hred1 hslack ⊢
  linarith [hsh, hred0, hred1, hslack]

end Work.BoseB1Cube
