import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.slotCS
import Submission.Work.FTS.TransportS.T2Sup.Final
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_mono)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Measure-theoretic bookkeeping -/

theorem restrict_Iθ_eq_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
  Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo

theorem restrict_Iz_eq_Ioi :
    volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
  have h : Set.Ioi (0 : ℝ) =ᵐ[volume] Set.Ici (0 : ℝ) := Ioi_ae_eq_Ici
  simpa [Work.Spaces.Iz] using (MeasureTheory.Measure.restrict_congr_set h).symm

theorem ae_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  rw [restrict_Iθ_eq_Ioo]
  exact ae_restrict_mem measurableSet_Ioo

theorem integral_Iθ_mono_ae {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), f θ ≤ g θ)
    (h0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 ≤ f θ) (hg : IntegrableOn g Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, f θ) ≤ ∫ θ in Work.Spaces.Iθ, g θ := by
  refine integral_mono_of_nonneg ?_ hg ?_
  · rw [restrict_Iθ_eq_Ioo]; exact ae_restrict_of_forall_mem measurableSet_Ioo h0
  · rw [restrict_Iθ_eq_Ioo]; exact ae_restrict_of_forall_mem measurableSet_Ioo h

theorem integral_Iz_mono_ae {f g : ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), f z ≤ g z)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ f z) (hg : IntegrableOn g Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, f z) ≤ ∫ z in Work.Spaces.Iz, g z := by
  refine integral_mono_of_nonneg ?_ hg ?_
  · rw [restrict_Iz_eq_Ioi]; exact ae_restrict_of_forall_mem measurableSet_Ioi h0
  · rw [restrict_Iz_eq_Ioi]; exact ae_restrict_of_forall_mem measurableSet_Ioi h

theorem one_le_alpha_rpow_neg_half {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hα.le, ← Real.sqrt_eq_rpow]
  refine (one_le_inv₀ (Real.sqrt_pos.mpr hα)).mpr ?_
  calc Real.sqrt α ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hα1
    _ = 1 := Real.sqrt_one

theorem gam_pos' {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα

/-- Continuity of the (uncurried) datum on the open quadrant. -/
theorem smoothOpen_continuousOn_Q0 {F : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen F) :
    ContinuousOn (Function.uncurry F) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
  h.continuousOn

/-! ## 2. Comparisons of canonical weights -/

/-- `canonW q ≤ canonW (gam α)` on the open interval for `0 ≤ q ≤ gam α`. -/
theorem canonW_le_gam {α q : ℝ} (hα : 0 < α) (hq0 : 0 ≤ q) (hqγ : q ≤ Work.Spaces.gam α) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      canonW q z θ ≤ canonW (Work.Spaces.gam α) z θ := by
  intro z θ hθ
  rcases eq_or_lt_of_le hq0 with hq | hq
  · rw [← hq]
    have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Work.FTS.TransportS.one_le_rpow_neg (gam_pos' hα).le hθ
    calc canonW 0 z θ = (Work.Spaces.w z) ^ 2 := by
            simp only [canonW, neg_zero, Real.rpow_zero, mul_one]
      _ = (Work.Spaces.w z) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = canonW (Work.Spaces.gam α) z θ := by simp only [canonW]
  · exact canonW_mono hq hqγ (Set.Ioo_subset_Icc_self hθ)

/-- `canonW q ≤ canonW eta` on the open interval for `0 ≤ q ≤ eta`. -/
theorem canonW_le_eta {q : ℝ} (hq0 : 0 ≤ q) (hqη : q ≤ Work.Spaces.eta) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) → canonW q z θ ≤ canonW Work.Spaces.eta z θ := by
  intro z θ hθ
  rcases eq_or_lt_of_le hq0 with hq | hq
  · rw [← hq]
    have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
    calc canonW 0 z θ = (Work.Spaces.w z) ^ 2 := by
            simp only [canonW, neg_zero, Real.rpow_zero, mul_one]
      _ = (Work.Spaces.w z) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = canonW Work.Spaces.eta z θ := by simp only [canonW]
  · exact canonW_mono hq hqη (Set.Ioo_subset_Icc_self hθ)

/-! ## 3. Pointwise slot dominations -/

/-- A mixed slot of order `≤ 6` is dominated by the level-`6` integrand, weighted by
`canonW q` with `0 ≤ q ≤ γ`, on the whole closed angular interval. -/
theorem canonW_mul_mixed_le6 {α : ℝ} (hα : 0 < α) {q : ℝ} (hq0 : 0 ≤ q)
    (hqγ : q ≤ Work.Spaces.gam α) {g : ℝ → ℝ → ℝ} {j' i' : ℕ}
    (hi : 1 ≤ i') (hij : i' + j' ≤ 6) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    canonW q z θ * (Work.Spaces.mixed j' i' g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0pos
  · have hw : canonW q z 0 * (Work.Spaces.mixed j' i' g z 0) ^ 2 = 0 := by
      rw [Work.Spaces.mixed_eq_zero_of_sin_eq_zero (H := g) (z := z) (θ := 0) (by simp) hi]
      ring
    rw [← h0, hw]
    exact Work.Spaces.HkIntegrand_nonneg α 6 g z 0
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2lt
    · have hw : canonW q z (π / 2) * (Work.Spaces.mixed j' i' g z (π / 2)) ^ 2 = 0 := by
        rw [Work.Spaces.mixed_eq_zero_of_sin_eq_zero (H := g) (z := z) (θ := π / 2)
          (by rw [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]) hi]
        ring
      rw [h2, hw]
      exact Work.Spaces.HkIntegrand_nonneg α 6 g z (π / 2)
    · exact le_trans (mul_le_mul_of_nonneg_right
        (canonW_le_gam hα hq0 hqγ z θ ⟨h0pos, h2lt⟩) (sq_nonneg _))
        (Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_mixed_le6 α g
          (gam_pos' hα) le_rfl hθ j' i' hi hij)

/-- A mixed slot of order `≤ 4` is dominated by the level-`4` integrand, weighted by
`canonW q` with `0 ≤ q ≤ γ`, on the whole closed angular interval. -/
theorem canonW_mul_mixed_le4 {α : ℝ} (hα : 0 < α) {q : ℝ} (hq0 : 0 ≤ q)
    (hqγ : q ≤ Work.Spaces.gam α) {g : ℝ → ℝ → ℝ} {j' i' : ℕ}
    (hi : 1 ≤ i') (hij : i' + j' ≤ 4) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    canonW q z θ * (Work.Spaces.mixed j' i' g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0pos
  · have hw : canonW q z 0 * (Work.Spaces.mixed j' i' g z 0) ^ 2 = 0 := by
      rw [Work.Spaces.mixed_eq_zero_of_sin_eq_zero (H := g) (z := z) (θ := 0) (by simp) hi]
      ring
    rw [← h0, hw]
    exact Work.Spaces.HkIntegrand_nonneg α 4 g z 0
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2lt
    · have hw : canonW q z (π / 2) * (Work.Spaces.mixed j' i' g z (π / 2)) ^ 2 = 0 := by
        rw [Work.Spaces.mixed_eq_zero_of_sin_eq_zero (H := g) (z := z) (θ := π / 2)
          (by rw [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]) hi]
        ring
      rw [h2, hw]
      exact Work.Spaces.HkIntegrand_nonneg α 4 g z (π / 2)
    · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hz0
      · rw [← hz0, Work.FTS.TransportS.SlotT2.canonW_zero_z, zero_mul]
        exact Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ
      · exact le_trans (mul_le_mul_of_nonneg_right
          (canonW_le_gam hα hq0 hqγ z θ ⟨h0pos, h2lt⟩) (sq_nonneg _))
          (Work.FTS.TransportS.SlotT2.canonW_mul_mixed_le α g (gam_pos' hα)
            le_rfl hz0 hθ j' i' hi hij)

/-- A pure `D_z`-slot of order `≤ 6` is dominated by the level-`6` integrand on the open
angular interval, for `0 < q ≤ η`. -/
theorem canonW_mul_z_pos_le6 {α q : ℝ} (hq0 : 0 < q) (hqη : q ≤ Work.Spaces.eta)
    {g : ℝ → ℝ → ℝ} {j' : ℕ} (hj : j' ≤ 6) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    canonW q z θ * (Work.Spaces.DzIter j' g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
  le_trans (mul_le_mul_of_nonneg_right (canonW_le_eta hq0.le hqη z θ hθ) (sq_nonneg _))
    (Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_z_le6 α g
      (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl (Set.Ioo_subset_Icc_self hθ) j' hj)

/-- The pure `D_z`-slot bound at the exponent `q = 0`. -/
theorem canonW_mul_z_zero_le6 {α : ℝ} {g : ℝ → ℝ → ℝ} {j' : ℕ} (hj : j' ≤ 6)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    canonW 0 z θ * (Work.Spaces.DzIter j' g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
  le_trans (mul_le_mul_of_nonneg_right
      (canonW_le_eta le_rfl Work.Spaces.eta_nonneg z θ hθ) (sq_nonneg _))
    (Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_z_le6 α g
      (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl (Set.Ioo_subset_Icc_self hθ) j' hj)

/-- A pure `D_z`-slot of order `≤ 6` is dominated by the level-`6` integrand on the open
angular interval, for `0 ≤ q ≤ η`. -/
theorem canonW_mul_z_le6 {α q : ℝ} (hq0 : 0 ≤ q) (hqη : q ≤ Work.Spaces.eta)
    {g : ℝ → ℝ → ℝ} {j' : ℕ} (hj : j' ≤ 6) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    canonW q z θ * (Work.Spaces.DzIter j' g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  rcases eq_or_lt_of_le hq0 with hq | hq
  · rw [← hq]; exact canonW_mul_z_zero_le6 hj hθ
  · exact canonW_mul_z_pos_le6 hq hqη hj hθ

/-- Alias of `canonW_mul_z_pos_le6` (the `0 < q` form). -/
theorem canonW_mul_z_eta_le6 {α q : ℝ} (hq0 : 0 < q) (hqη : q ≤ Work.Spaces.eta)
    {g : ℝ → ℝ → ℝ} {j' : ℕ} (hj : j' ≤ 6) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    canonW q z θ * (Work.Spaces.DzIter j' g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
  canonW_mul_z_pos_le6 hq0 hqη hj hθ

/-! ## 4. Continuity of the weighted slot integrands -/

theorem continuousOn_canonW_slot_mixed {q : ℝ} {g : ℝ → ℝ → ℝ}
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) {j' i' : ℕ} :
    ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2
        * (Work.Spaces.mixed j' i' g p.1 p.2) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
  (Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
    ((hgsm.mixed j' i').continuousOn.pow 2)

theorem continuousOn_canonW_slot_z {q : ℝ} {g : ℝ → ℝ → ℝ}
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) {j' : ℕ} :
    ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2
        * (Work.Spaces.DzIter j' g p.1 p.2) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
  (Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
    ((hgsm.DzIter j').continuousOn.pow 2)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
