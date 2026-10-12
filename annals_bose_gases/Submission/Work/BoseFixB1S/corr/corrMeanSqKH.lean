import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseFixB1B.MeanSqPiece.corrMeanSqRealE3_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.corr

open MeasureTheory
open scoped ENNReal

/-- At an admissible point FS's small parameter `d = (μa³)^{6/323}` is at most `1`, because
`μa³ ≤ ε₀ ≤ 1`. -/
lemma adm_d_le_one {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ} (hε : ε₀ ≤ 1)
    (h : Work.BoseBoxFix.Adm v ε₀ μ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos h
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos h
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos ha 3)
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans (Work.BoseFixB1.adm_dilute h) hε
  show Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6 ≤ 1
  exact Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num)

/-- The `u`-integral of the squared sliding-box mean of a smooth state is controlled by the
*anchored* flat mass: with `L = 1 + (ℓd)⁻¹ + |log d|`,
`∫_u (⍍_{B(u)} w)² ≤ C L³ (ℓd)⁻³ ∫_{acube ℓ} w²`.

Route: Jensen `(⍍_{B(u)}w)² ≤ ⍍_{B(u)} w²`, then Tonelli with the per-`z` geometric weight
`∫_u (boxMass ℓ d u)⁻¹ 1_{dlBox ℓ d u}(z) du ≤ C (1 + (ℓd)⁻¹ + |log d|)³ (ℓd)⁻³` for
`z ∈ acube ℓ` (the `u`-set where `z ∈ dlBox ℓ d u` is a cube of side `1`, and the sliver boxes
with `z` in the boundary layer give the `d⁻¹`, `|log d|` powers).

CAUTION: the identically-stated `Work.BoseFixB1S.corrMeanSq` is itself a `sorry`; proving this by
`exact`ing it would make the proof depend on `sorryAx`.  Prove it from scratch. -/
theorem corrMeanSqKH {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ (⊤ : ENat) w →
          MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
              ((1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                ∫ z in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z) ^ 2)
          ∧ (∫ u : EuclideanSpace ℝ (Fin 3),
              ((1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                ∫ z in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z) ^ 2)
            ≤ C * (1 + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹
                    + |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)|) ^ 3
                * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
                * (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                    (w z) ^ 2) := by
  refine ⟨1, one_pos, (729 : ℝ), by norm_num, ?_⟩
  intro μ hAdm w hw
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  have hℓ : 0 < ℓ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < d := Work.BoseFixB1.adm_d_pos hAdm
  have hd1 : d ≤ 1 := adm_d_le_one le_rfl hAdm
  obtain ⟨hint, hbd⟩ :=
    Work.BoseFixB1B.MeanSqPiece.corrMeanSqRealE3_holds hℓ hd hd1 hw.continuous
  have hQnn : 0 ≤ ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 :=
    MeasureTheory.setIntegral_nonneg (Submission.BoseGases.acube_measurable ℓ)
      (fun z _ => sq_nonneg (w z))
  have hL1 : 1 ≤ 1 + (ℓ * d)⁻¹ + |Real.log d| := by
    have h1 : 0 ≤ (ℓ * d)⁻¹ := inv_nonneg.mpr (le_of_lt (mul_pos hℓ hd))
    have h2 : 0 ≤ |Real.log d| := abs_nonneg _
    linarith
  have hL3 : 1 ≤ (1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 := one_le_pow₀ hL1
  refine ⟨hint, ?_⟩
  calc (∫ u : EuclideanSpace ℝ (Fin 3),
        ((1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ z in Submission.BoseGases.dlBox ℓ d u, w z) ^ 2)
      ≤ (9 / (ℓ * d)) ^ 3 * ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 := hbd
    _ ≤ (729 : ℝ) * (1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 * ((ℓ * d) ^ 3)⁻¹
          * ∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hQnn
        have hEq : (9 / (ℓ * d)) ^ 3 = 729 * ((ℓ * d) ^ 3)⁻¹ := by
          rw [div_pow, div_eq_mul_inv]
          norm_num
        rw [hEq]
        calc 729 * ((ℓ * d) ^ 3)⁻¹
            ≤ 729 * ((1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 * ((ℓ * d) ^ 3)⁻¹) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 729)
              simpa using mul_le_mul_of_nonneg_right hL3
                (inv_nonneg.mpr (pow_nonneg (le_of_lt (mul_pos hℓ hd)) 3))
          _ = 729 * (1 + (ℓ * d)⁻¹ + |Real.log d|) ^ 3 * ((ℓ * d) ^ 3)⁻¹ := by ring

end Work.BoseFixB1S.corr
