import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.PCFU.chAimg_latPer_pairingLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000

namespace Work.BoseBoxFock.PCFU

/-!
# `Work.BoseBoxFock.PCFU.chAimg_sliceLe`

The `univ`-frame kernel `KfrU` is the sum of the `excited`-frame kernel `Kfr` and the `k = 0`
column (`KfrU_eq`).  The two pieces of that decomposition are bounded independently:

* `chAimg_latPer_pairingLe` bounds the periodisation part `∫ g·latPer3 ℓ (W₁fun v h ℓ)` by
  `C₂·√(a v)·ℓ³·√(Dir g)`;
* `taperSlotOne` bounds the *truncation error*
  `∫ g·(KfrU − latPer3 ℓ (W₁fun v h ℓ))` by `C₁·(1+R)³·ℓ³·√((Λ_N)⁻¹·Dir g)` with
  `Λ_N = uvRad ℓ N = πN/(2ℓ)`.

Since `N ≥ 1` gives `(uvRad ℓ N)⁻¹ = 2ℓ/(πN) ≤ 2ℓ/π`, the truncation-error factor is at most
`√(2ℓ/π)·√(Dir g)`, and the triangle inequality produces the stated bound with constant
`C₁ + C₂` (any `C ≥ max C₁ C₂` would do).

The two integrals are combined through the pointwise identity
`g·KfrU = g·(KfrU − latPer3 ℓ W₁) + g·latPer3 ℓ W₁`; both summands are integrable (the frame
`KfrU` is a finite trigonometric sum, `slotTrunc`; the periodisation pairing is `slotFold`), so
`MeasureTheory.integral_add` applies.
-/

/-- Scalar assembly of the two pieces: with all factors nonnegative and `Q ≤ s₁·P`, `L ≥ 1`,
the truncated-error term plus the periodisation term is dominated by
`(C₁+C₂)·L·M·(s₁+s₂)·P`. -/
private lemma chAimg_sliceLe_arith {C1 C2 L M s1 s2 P Q : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hL : 1 ≤ L) (hM : 0 ≤ M)
    (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (hP : 0 ≤ P) (hQle : Q ≤ s1 * P) :
    C1 * L * M * Q + C2 * s2 * M * P ≤ (C1 + C2) * L * M * (s1 + s2) * P := by
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL
  have hC1'' : C1 ≤ C1 + C2 := by linarith
  have hC2' : C2 ≤ C1 + C2 := by linarith
  have h1 : C1 * L * M * Q ≤ C1 * L * M * (s1 * P) := by
    have := mul_le_mul_of_nonneg_left hQle (mul_nonneg (mul_nonneg hC1 hL0) hM)
    nlinarith [this]
  have h1' : C1 * L * M * (s1 * P) ≤ (C1 + C2) * L * M * (s1 * P) := by
    have := mul_le_mul_of_nonneg_right hC1''
      (mul_nonneg (mul_nonneg hL0 hM) (mul_nonneg hs1 hP))
    nlinarith [this]
  have h2 : C2 * s2 * M * P ≤ (C1 + C2) * s2 * M * P * L := by
    have hbase : 0 ≤ C2 * s2 * M * P := by positivity
    have h3 : C2 * s2 * M * P ≤ C2 * s2 * M * P * L := by
      have := mul_le_mul_of_nonneg_left hL hbase
      nlinarith [this]
    have := mul_le_mul_of_nonneg_right hC2'
      (mul_nonneg (mul_nonneg hs2 hM) (mul_nonneg hP hL0))
    nlinarith [h3, this]
  calc C1 * L * M * Q + C2 * s2 * M * P
      ≤ (C1 + C2) * L * M * (s1 * P) + (C1 + C2) * s2 * M * P * L :=
        add_le_add (le_trans h1 h1') h2
    _ = (C1 + C2) * L * M * (s1 + s2) * P := by ring

theorem chAimg_sliceLe (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fu : Work.BoseBoxFix.LowCut) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ : ℝ}, 0 < μ → ∀ {N : ℕ}, 1 ≤ N →
      R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 →
      ∀ (y : EuclideanSpace ℝ (Fin 3)) (g : EuclideanSpace ℝ (Fin 3) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) g →
        tsupport g ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ) →
        ‖∫ w : EuclideanSpace ℝ (Fin 3), ((g w : ℝ) : ℂ) *
            Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y - w)‖
          ≤ C * (1 + R) ^ 3 * (Work.BoseBoxFock.ellH v μ) ^ 3
              * (Real.sqrt (2 * Work.BoseBoxFock.ellH v μ / Real.pi)
                  + Real.sqrt (BoseGases.a v))
              * Real.sqrt (Work.BoseBoxFock.PCFU.slotDir g) := by
  classical
  obtain ⟨C1, hC1nn, h1all⟩ := Work.BoseBoxFock.PCFU.taperSlotOne
  obtain ⟨C2, hC2nn, h2all⟩ :=
    Work.BoseBoxFock.PCFU.chAimg_latPer_pairingLe (v := v) (h := h) (R := R) hR hv hvrad hv_supp
  refine ⟨C1 + C2, by linarith, ?_⟩
  intro μ hμ N hN hRℓ y g hg hgs
  have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hℓpos : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hΛpos : 0 < Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N :=
    Work.BoseBoxFock.uvRad_pos hℓpos hN
  have h1 := h1all (v := v) (h := h) (R := R) (μ := μ) (fu := fu) (N := N)
      hR hside hv hv1 hvrad hv_supp hRℓ hN y g hg hgs
  have h2 := h2all (ℓ := Work.BoseBoxFock.ellH v μ) hℓpos hRℓ y g hg hgs
  -- ## integrability of the two pieces and of the difference
  have hIA : MeasureTheory.Integrable
      (fun w : EuclideanSpace ℝ (Fin 3) =>
        ((g w : ℝ) : ℂ) * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y - w)) := by
    have hh := (Work.BoseBoxFock.PCFU.slotTrunc (v := v) (h := h) (μ := μ) (fu := fu)
      (N := N) (y := y) (g := g) hg hgs).1
    refine (hh.comp_sub_left y).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    rw [show y - (y - t) = t from by abel]
  have hIB : MeasureTheory.Integrable
      (fun w : EuclideanSpace ℝ (Fin 3) => ((g w : ℝ) : ℂ) *
        Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
          (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w)) := by
    obtain ⟨hWint, hWzero, hWev⟩ :=
      Work.BoseBoxFock.PCFU.slotW1_aux (v := v) (h := h) (R := R)
        (ℓ := Work.BoseBoxFock.ellH v μ) hR hvrad hv_supp hℓpos hRℓ
    have hΨcont : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseBoxFock.PCFU.slotPsi y g) :=
      Complex.ofRealCLM.contDiff.comp (hg.comp (contDiff_const.sub contDiff_id))
    have hboxcpt : IsCompact
        {z : EuclideanSpace ℝ (Fin 3) |
          y - z ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)} := by
      have h1c : IsCompact (Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) :=
        Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox (Work.BoseBoxFock.ellH v μ)
      have h2c : IsCompact
          ((fun w : EuclideanSpace ℝ (Fin 3) => y - w) ''
            Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) :=
        h1c.image (continuous_const.sub continuous_id)
      have heq : ((fun w : EuclideanSpace ℝ (Fin 3) => y - w) ''
            Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ))
          = {z : EuclideanSpace ℝ (Fin 3) |
              y - z ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)} := by
        ext z
        simp only [Set.mem_image, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨w, hw, hwz⟩
          rw [← hwz]
          have hh : y - (y - w) = w := by abel
          rw [hh]
          exact hw
        · intro hz
          exact ⟨y - z, hz, by abel⟩
      rw [heq] at h2c
      exact h2c
    have hΨsupp : tsupport (Work.BoseBoxFock.PCFU.slotPsi y g)
        ⊆ {z : EuclideanSpace ℝ (Fin 3) |
            y - z ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)} := by
      refine closure_minimal ?_ hboxcpt.isClosed
      intro z hz
      have hz' : g (y - z) ≠ 0 := by
        intro h0
        exact hz (by simp [Work.BoseBoxFock.PCFU.slotPsi, h0])
      exact hgs (subset_tsupport g (Function.mem_support.mpr hz'))
    have hΨcs : HasCompactSupport (Work.BoseBoxFock.PCFU.slotPsi y g) :=
      IsCompact.of_isClosed_subset hboxcpt (isClosed_tsupport _) hΨsupp
    have hh := (Work.BoseBoxFock.PCFU.slotFold (ℓ := Work.BoseBoxFock.ellH v μ) (R := R) hℓpos
      hWint hWev hWzero hΨcont hΨcs).1
    refine (hh.comp_sub_left y).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Work.BoseBoxFock.PCFU.slotPsi]
    rw [show y - (y - t) = t from by abel]
  have hJint : MeasureTheory.Integrable
      (fun w : EuclideanSpace ℝ (Fin 3) => ((g w : ℝ) : ℂ) *
        (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y - w) -
          Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w))) := by
    refine (hIA.sub hIB).congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.sub_apply]
    ring
  -- ## the pointwise split `g·KfrU = g·(KfrU − latPer3) + g·latPer3`
  have hsplit : (∫ w : EuclideanSpace ℝ (Fin 3),
        ((g w : ℝ) : ℂ) * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y - w))
      = (∫ w : EuclideanSpace ℝ (Fin 3), ((g w : ℝ) : ℂ) *
            (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y - w) -
              Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
                (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w)))
        + (∫ w : EuclideanSpace ℝ (Fin 3), ((g w : ℝ) : ℂ) *
            Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w)) := by
    rw [← MeasureTheory.integral_add hJint hIB]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    ring
  have htri : ‖∫ w : EuclideanSpace ℝ (Fin 3),
        ((g w : ℝ) : ℂ) * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y - w)‖
      ≤ ‖∫ w : EuclideanSpace ℝ (Fin 3), ((g w : ℝ) : ℂ) *
            (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y - w) -
              Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
                (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w))‖
        + ‖∫ w : EuclideanSpace ℝ (Fin 3), ((g w : ℝ) : ℂ) *
            Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w)‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  -- ## the `(uvRad)⁻¹ ≤ 2ℓ/π` arithmetic (`N ≥ 1`)
  have hΛinv_le : (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)⁻¹
      ≤ 2 * Work.BoseBoxFock.ellH v μ / Real.pi := by
    have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hmul : Real.pi ≤ Real.pi * (N : ℝ) := by nlinarith [Real.pi_pos, hN']
    have hdiv := div_le_div_of_nonneg_left
      (by positivity : (0 : ℝ) ≤ 2 * Work.BoseBoxFock.ellH v μ) Real.pi_pos hmul
    have huv : (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)⁻¹
        = 2 * Work.BoseBoxFock.ellH v μ / (Real.pi * (N : ℝ)) := by
      rw [Work.BoseBoxFock.uvRad]
      field_simp
      ring
    rw [huv]
    exact hdiv
  have hQle : Real.sqrt ((Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)⁻¹ *
        Work.BoseBoxFock.PCFU.slotDir g)
      ≤ Real.sqrt (2 * Work.BoseBoxFock.ellH v μ / Real.pi) *
          Real.sqrt (Work.BoseBoxFock.PCFU.slotDir g) := by
    rw [Real.sqrt_mul (inv_nonneg.mpr (le_of_lt hΛpos))]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hΛinv_le) (Real.sqrt_nonneg _)
  -- ## the two bounds, in the shape required by the scalar lemma
  have hJb : ‖∫ w : EuclideanSpace ℝ (Fin 3), ((g w : ℝ) : ℂ) *
        (Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y - w) -
          Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w))‖
      ≤ C1 * (1 + R) ^ 3 * (Work.BoseBoxFock.ellH v μ) ^ 3 *
          Real.sqrt ((Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)⁻¹ *
            Work.BoseBoxFock.PCFU.slotDir g) := by
    simpa only [Work.BoseBoxFock.PCFU.slotDir] using h1
  have hILb : ‖∫ w : EuclideanSpace ℝ (Fin 3), ((g w : ℝ) : ℂ) *
        Work.BoseBoxFock.latPer3 (Work.BoseBoxFock.ellH v μ)
          (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (y - w)‖
      ≤ C2 * Real.sqrt (BoseGases.a v) * (Work.BoseBoxFock.ellH v μ) ^ 3 *
          Real.sqrt (Work.BoseBoxFock.PCFU.slotDir g) := by
    simpa only [Work.BoseBoxFock.PCFU.slotDir] using h2
  have hL1 : (1 : ℝ) ≤ (1 + R) ^ 3 := one_le_pow₀ (by linarith)
  have hscalar := chAimg_sliceLe_arith (C1 := C1) (C2 := C2) (L := (1 + R) ^ 3)
      (M := (Work.BoseBoxFock.ellH v μ) ^ 3)
      (s1 := Real.sqrt (2 * Work.BoseBoxFock.ellH v μ / Real.pi))
      (s2 := Real.sqrt (BoseGases.a v))
      (P := Real.sqrt (Work.BoseBoxFock.PCFU.slotDir g))
      (Q := Real.sqrt ((Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)⁻¹ *
        Work.BoseBoxFock.PCFU.slotDir g))
      hC1nn hC2nn hL1 (by positivity) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) hQle
  exact le_trans htri (le_trans (add_le_add hJb hILb) hscalar)

end Work.BoseBoxFock.PCFU
