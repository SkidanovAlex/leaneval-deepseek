import ChallengeDeps
import Submission.Work.BoseFixB1.boxPairIntGenC2
import Submission.Work.BoseFixB1S.boxBogB1Fix
import Submission.Work.BoseFixB1S.integrable_wSmallScaled_div_convScaleB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxPairIdSlidingB1` — the box pairing identity at the sliding box

The sliding-box (`A = dlBox ℓ d u`, window `chiSmallB M ℓ d u`) instance of the general-profile
box pairing identity, for the localised one-body kernel `wSmall1Pair`:

    `boxA2 ℓ |B(u)| B(u) wSmall1Pair Φ
       = (2π)⁻³ ∫_q pairW (wSmallScaled M (ℓd) g₀ / convScale ℓ) q
           · (|B(u)|⁻¹ · boxWinModeRGen ℓ |B(u)| B(u) (chiSmallB M ℓ d u) Φ q)`.

Route (`Work.BoseFixB1.boxPairIntGenC2`, `BoxPairIntGenC2`):

* `Work.BoseFixB1.boxPairIntGenC2` is the general-profile pairing identity for a `C²` window
  `χ` vanishing off `A`; its only unused hypothesis is the continuity of the profile `𝒲`,
  which is removed here (`boxPairIntGenC2'`) since our profile
  `wSmallScaled M (ℓd) g₀ / convScale ℓ` is only known to be *integrable*
  (`Work.BoseFixB1S.integrable_wSmallScaled_div_convScaleB1`);
* the window data: `chiSmallB M ℓ d u` is `C²` (`Work.BoseFixB1.chiSmallB_contDiff_two`,
  `M ≥ 3`), compactly supported (`Submission.BoseGases.chiSmallB_hasCompactSupport`) and
  supported in `dlBox ℓ d u` (`Work.BoseFixB1S.chiSmallB_eq_zero_of_notMem_dlBox`);
* the box data: `dlBox ℓ d u` is measurable, inside `acube ℓ`, and
  `boxMass ℓ d u = |dlBox ℓ d u|` (`Work.SmallBoxSliding.boxMass_eq_measureReal`);
* if `boxMass ℓ d u = 0` both sides vanish identically (`1/0 = 0` in the box projections and
  `0⁻¹ = 0` on the momentum side), so that case is pure computation.
-/

noncomputable section

namespace Work.BoseFixB1S

open MeasureTheory
open scoped Topology Real BigOperators ENNReal ContDiff

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. The general pairing identity at a `C²` window, without continuity of `𝒲` -/

/-- **The general-profile box pairing identity, no continuity hypothesis on `𝒲`.**

This is `Work.BoseFixB1.boxPairIntGenC2` with the (unused) hypothesis `Continuous 𝒲` dropped;
its proof is the last three lines of that theorem, which only ever use `Integrable 𝒲`. -/
theorem boxPairIntGenC2' {n : ℕ} (hn : 2 ≤ n) {a volA : ℝ} (ha : 0 < a)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : ContDiff ℝ 2 χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0)
    {𝒲 : E3 → ℝ} (h𝒲int : MeasureTheory.Integrable 𝒲)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Work.BoseFixB1.boxA2 a volA Ac (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : E3,
          Submission.BoseGases.pairW 𝒲 q
            * (volA⁻¹ * Work.BoseFixB1.boxWinModeRGen a volA Ac χ Ψ q) := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N + 2 := ⟨n - 2, by omega⟩
  rw [Work.BoseFixB1.BoxPairIntGenC2.boxRelDensC2 hAcm ha hAcsub hvol hvolpos hχc.continuous
    hχs hχsupp hΨ h𝒲int]
  rw [Work.BoseFixB1.boxPlancherelC2 hAcm ha hAcsub hvol hvolpos hχc hχs hχsupp hΨ h𝒲int]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  dsimp only
  rw [Work.BoseFixB1.boxDensFourier_eq_winModeRGenC2 hAcm ha hAcsub hvol hvolpos hχc hχs
    hχsupp hΨ q]

/-! ## 2. The localised one-body kernel in the `χχ𝒲` shape -/

/-- `wSmall1Pair` *is* the `χ_{B(u)}(x)·𝒲(x−y)·χ_{B(u)}(y)` kernel of the pairing identity,
with `𝒲 = wSmallScaled M (ℓd) g₀ / convScale ℓ`; only the order of the three real factors
differs. -/
lemma wSmall1Pair_eq_pairKernel {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (M : ℕ) (ℓ d : ℝ) (u : E3) :
    Submission.BoseGases.wSmall1Pair h M ℓ d u
      = fun x y : E3 => Submission.BoseGases.chiSmallB M ℓ d u x
          * Submission.BoseGases.chiSmallB M ℓ d u y
          * (fun z : E3 =>
              Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
                / Submission.BoseGases.convScale ℓ z) (x - y) := by
  funext x y
  simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair]
  ring

/-! ## 3. The target -/

theorem boxPairIdSlidingB1 {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 3 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3))
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.BoseFixB1.boxA2 ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.pairW
                (fun z => Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
                  / Submission.BoseGases.convScale ℓ z) q
              * ((Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
                  Work.BoseFixB1.boxWinModeRGen ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u)
                    (Submission.BoseGases.chiSmallB M ℓ d u) Φ q) := by
  set 𝒲 : E3 → ℝ := fun z =>
    Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
      / Submission.BoseGases.convScale ℓ z with h𝒲
  rcases lt_or_ge (0 : ℝ) (Work.SmallBoxSliding.boxMass ℓ d u) with hpos | hnonpos
  · have hM1 : 1 ≤ M := by omega
    have hχsupp : ∀ z : E3, z ∉ Submission.BoseGases.dlBox ℓ d u →
        Submission.BoseGases.chiSmallB M ℓ d u z = 0 :=
      fun z hz => Work.BoseFixB1S.chiSmallB_eq_zero_of_notMem_dlBox hM1 hℓ hd u hz
    have hχc2 : ContDiff ℝ 2 (Submission.BoseGases.chiSmallB M ℓ d u) :=
      Work.BoseFixB1.chiSmallB_contDiff_two hM u
    have hχs : HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) :=
      Submission.BoseGases.chiSmallB_hasCompactSupport hM1 hℓ u
    have hvol : Work.SmallBoxSliding.boxMass ℓ d u
        = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
      rw [Work.SmallBoxSliding.boxMass_eq_measureReal]
      rfl
    have hWint : MeasureTheory.Integrable 𝒲 :=
      Work.BoseFixB1S.integrable_wSmallScaled_div_convScaleB1 hv_supp hR0 hM1 hℓ hd hR hRχ h
    have hpair := boxPairIntGenC2' (n := N + 2) (by omega) hℓ
      (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) hvol hpos hχc2 hχs hχsupp hWint hΦ
    rw [wSmall1Pair_eq_pairKernel h M ℓ d u]
    exact hpair
  · have hzero : Work.SmallBoxSliding.boxMass ℓ d u = 0 :=
      le_antisymm hnonpos (Work.BoseFixB1S.boxMass_nonneg ℓ d u)
    rw [hzero]
    rw [Work.BoseFixB1.boxA2]
    simp only [Work.UBBInputs8.boxPInd, div_zero, zero_mul]
    simp

end Work.BoseFixB1S
