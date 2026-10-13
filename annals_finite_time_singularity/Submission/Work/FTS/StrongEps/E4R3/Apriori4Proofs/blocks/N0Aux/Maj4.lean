/-
# `N0Aux.Maj4` — the pointwise majorant and the `HkSq` form for the `ℋ⁴`-integrand

Companion of `N0Aux.Maj4Slots`: assembling the fifteen slot bounds (`zslot4`, `mslot4`) gives

  `HkIntegrand α 4 (X · f) ≤ Maj4C · B² · HkIntegrand α 4 f`

on the open quadrant, and integrating (the weight vanishes at `z = 0`) gives

  `HkSq α 4 (X · f) ≤ (Maj4C + 1) · B² · HkSq α 4 f`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj4Slots
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- **The pointwise majorant of the `ℋ⁴`-integrand of a radial product.** -/
theorem maj4_pt {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hB : 0 ≤ B) (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ j : ℕ, j ≤ 4 → |Work.Elliptic.DzdIter j X z| ≤ B) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => X z * f z θ) z θ
      ≤ Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hBase : 0 ≤ 6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B)) hHk
  have hZ : (∑ i ∈ Finset.range (4 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 5 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
    calc (∑ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (4 + 1),
            (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) :=
          Finset.sum_le_sum fun i hi =>
            zslot4 hB hX hf hz hθ0 hθ1 hR i
              (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 5 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have hM : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0))
      ≤ 25 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
    calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1),
            (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 4
          · rw [if_pos hc]
            exact mslot4 hB hX hf hz hθ0 hθ1 hR i j hc.1 hc.2
          · rw [if_neg hc]
            exact hBase
      _ = 25 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
          ring
  rw [Work.Spaces.HkIntegrand]
  have h5 : (5 : ℝ) ≤ Maj4C := by norm_num [Maj4C]
  have h25 : (25 : ℝ) ≤ Maj4C := by norm_num [Maj4C]
  calc (∑ i ∈ Finset.range (4 + 1),
        (Work.Spaces.DzIter i (fun z θ => X z * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => X z * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
      ≤ 5 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
        + 25 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := add_le_add hZ hM
    _ ≤ Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
        have hY : 0 ≤ B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
          mul_nonneg (sq_nonneg B) hHk
        have hM' : 6400 * 30 ≤ Maj4C := by norm_num [Maj4C]
        calc 5 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
              + 25 * (6400 * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
            = (6400 * 30) * (B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
          _ ≤ Maj4C * (B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) :=
              mul_le_mul_of_nonneg_right hM' hY
          _ = Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by ring

/-- **The level-`4` radial majorant**: `HkSq α 4 (X · f) ≤ C · B² · HkSq α 4 f`. -/
theorem radialMaj4 {α B : ℝ} {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hB : 0 ≤ B) (hX : ContDiffOn ℝ 6 X (Set.Ioi 0))
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f)
    (hR : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Elliptic.DzdIter j X z| ≤ B) :
    Work.Spaces.HkSq α 4 (fun z θ => X z * f z θ)
      ≤ (Maj4C + 1) * B ^ 2 * Work.Spaces.HkSq α 4 f := by
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.HkIntegrand α 4 (fun z θ => X z * f z θ) z θ
        ≤ Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0, HkIntegrand_zero4]
      exact mul_nonneg (mul_nonneg Maj4C_pos.le (sq_nonneg B))
        (Work.Spaces.HkIntegrand_nonneg α 4 f 0 θ)
    · exact maj4_pt hB hX hf hzpos hθ.1 hθ.2
        (fun j hj => hR j hj z (Set.mem_Ioi.mpr hzpos))
  have hIoo : (volume.restrict Work.Spaces.Iθ) = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
      MeasureTheory.Ioo_ae_eq_Icc
    exact Measure.restrict_congr_set haeeq.symm
  have hmaj_slice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Maj4C * B ^ 2 *
      Work.Spaces.HkIntegrand α 4 f z θ) Work.Spaces.Iθ := by
    intro z hz
    simpa only [IntegrableOn] using (hm.1 z hz).const_mul (Maj4C * B ^ 2)
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => X z * f z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz
    refine integral_mono_of_nonneg ?_ (hmaj_slice z hz) ?_
    · exact Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 4 (fun z θ => X z * f z θ) z θ
    · rw [hIoo]
      exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hpt z hz θ hθ)
  have hmaj_z : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) Work.Spaces.Iz := by
    simpa only [IntegrableOn, MeasureTheory.integral_const_mul] using
      (hm.2.const_mul (Maj4C * B ^ 2))
  have houter : (∫ z in Work.Spaces.Iz,
      ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => X z * f z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    refine integral_mono_of_nonneg ?_ hmaj_z ?_
    · exact Filter.Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact hslice z hz
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
      = Maj4C * B ^ 2 * Work.Spaces.HkSq α 4 f := by
    rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Maj4C * B ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
        = (Maj4C * B ^ 2) * ∫ z in Work.Spaces.Iz,
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) from by
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
        simp only [MeasureTheory.integral_const_mul])]
    unfold Work.Spaces.HkSq
    ring
  have h1 : Work.Spaces.HkSq α 4 (fun z θ => X z * f z θ)
      ≤ Maj4C * B ^ 2 * Work.Spaces.HkSq α 4 f := houter.trans (le_of_eq hval)
  have h0 : 0 ≤ B ^ 2 * Work.Spaces.HkSq α 4 f :=
    mul_nonneg (sq_nonneg B) (Work.Spaces.HkSq_nonneg α 4 f)
  calc Work.Spaces.HkSq α 4 (fun z θ => X z * f z θ)
      ≤ Maj4C * B ^ 2 * Work.Spaces.HkSq α 4 f := h1
    _ = Maj4C * (B ^ 2 * Work.Spaces.HkSq α 4 f) := by ring
    _ ≤ (Maj4C + 1) * (B ^ 2 * Work.Spaces.HkSq α 4 f) :=
        mul_le_mul_of_nonneg_right (by linarith) h0
    _ = (Maj4C + 1) * B ^ 2 * Work.Spaces.HkSq α 4 f := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
