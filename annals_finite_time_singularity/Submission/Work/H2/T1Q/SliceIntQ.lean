/-
# `Work.H2.T1Q.SliceIntQ` — the angular slice of `T1Easy` is integrable

The target `Work.H2.T1Q.EasyBoundQ` asserts, as its first conjunct, that for every `z ∈ Iz` the
angular slice `θ ↦ T1Easy α f g z θ` is integrable on `Iθ`.  This file proves it.

Route: on the open quadrant `T1Easy α f g = EasySumQ α f g` (`Work.FTS.H2.T1Easy_expandQ`), a
finite sum of Leibniz summands, each of which is a product `C · V · A · B` of a *bounded* factor
`V` (bounded by `Kf`, by `Kg`, or — in the exceptional summand `(i,j,a,b) = (1,3,0,3)` — by the
slice bound `S` of `D_z³f` from `Work.H2.T1Q.sup_DzIter_three_le`) and two `ℋ⁴`-slots `A`, `B`
(`mixed · Wt` and `D_z · Whz`), whose squares are dominated by `HkIntegrand α 4 f` resp.
`HkIntegrand α 4 g` and hence are integrable by `HkMem`.  The product of two `L²`-slices is
integrable by AM–GM (`integrableOn_slice_two`), and each summand is dominated by a constant
multiple of it.  At `z = 0` the slice vanishes identically (`Whz 0 = Wm α 0 = w 0 = 0`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.T1EasyBound
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.H2.T1Q.QDefs
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.T1Q.ExpandQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.H2

/-! ## Elementary integrability helpers -/

/-- The product of two `L²`-slices is integrable (AM–GM: `2|A B| ≤ A² + B²`). -/
theorem integrableOn_slice_two {A B : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn (fun θ => (A θ) ^ 2) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ => (B θ) ^ 2) Work.Spaces.Iθ)
    (hmeas : AEStronglyMeasurable (fun θ => A θ * B θ) (volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => A θ * B θ) Work.Spaces.Iθ := by
  have hdom : MeasureTheory.Integrable
      (fun θ => (1 / 2 : ℝ) * ((A θ) ^ 2 + (B θ) ^ 2)) (volume.restrict Work.Spaces.Iθ) :=
    (hA.add hB).const_mul (1 / 2)
  refine hdom.mono' hmeas ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|A θ| - |B θ|), sq_abs (A θ), sq_abs (B θ)]

/-- The `θ`-slice of the weighted mixed slot `mixed j i u · Wt α` is a.e. strongly measurable. -/
theorem aesm_slice_mixed_Wt_abs (α : ℝ) (u : ℝ → ℝ → ℝ) (hu : Work.FTS.LocData.SmoothQuad u)
    (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => |Work.Spaces.mixed j i u z θ| * Wm α z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  refine Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => |Work.Spaces.mixed j i u p.1 p.2| * Wm α p.1 p.2) ?_ hz
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i u p.1 p.2)
      Work.FTS.H2.HQ.quadQ :=
    ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hu j i).continuousOn.mono
      Work.FTS.H2.HQ.quadQ_subset_quadU)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Wm α p.1 p.2) Work.FTS.H2.HQ.quadQ :=
    Work.FTS.H2.HQ.continuousOn_Wt_quad α
  exact h1.abs.mul h2

/-- The `θ`-slice of the weighted pure slot `D_z^i u · Whz` is a.e. strongly measurable. -/
theorem aesm_slice_dzIter_Whz_abs (u : ℝ → ℝ → ℝ) (hu : Work.FTS.LocData.SmoothQuad u)
    (i : ℕ) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => |Work.Spaces.DzIter i u z θ| * Whz z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  refine Work.Spaces.aesm_slice_of_continuousOn_Qd
    (fun p : ℝ × ℝ => |Work.Spaces.DzIter i u p.1 p.2| * Whz p.1 p.2) ?_ hz
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i u p.1 p.2)
      Work.FTS.H2.HQ.quadQ :=
    ((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hu i).continuousOn.mono
      Work.FTS.H2.HQ.quadQ_subset_quadU)
  exact h1.abs.mul continuousOn_Whz_quad

/-- The square of the weighted mixed slot is integrable on the slice. -/
theorem integrableOn_slice_mixedWt_sq (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.LocData.SmoothQuad u) (hmem : Work.Spaces.HkMem α 4 u)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.mixed j i u z θ * Wm α z θ) ^ 2)
      Work.Spaces.Iθ :=
  Work.FTS.H2.HQ.integrableOn_slice_mixed_Wt_sq α u hu hmem j i hi hij hz

/-- The square of the weighted pure slot is integrable on the slice. -/
theorem integrableOn_slice_Whz_sq (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.LocData.SmoothQuad u) (hmem : Work.Spaces.HkMem α 4 u)
    (i : ℕ) (hi : i ≤ 4) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter i u z θ * Whz z θ) ^ 2) Work.Spaces.Iθ :=
  (Work.FTS.H2.HQ.L2Mem_light_quad α u hu hmem i hi).1 z hz

/-! ## The main statement -/

/-- **The angular slice of `T1Easy` is integrable at every `z ∈ Iz`.** -/
theorem T1Easy_slice_integrable (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Kf)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Kg) :
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.T1Easy α f g z θ) Work.Spaces.Iθ := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hzpos
  · subst h0
    have hzero : (fun θ => Work.FTS.H2.T1Easy α f g 0 θ) = fun _ => (0 : ℝ) := by
      funext θ
      simp only [Work.FTS.H2.T1Easy, Work.FTS.H2.H4PairInt, Work.FTS.H2.T1Hard,
        Work.FTS.H2.Whz, Work.FTS.H2.Wm, Work.Spaces.Wt, Work.Spaces.wTheta,
        Work.Spaces.w]
      norm_num
    rw [hzero]
    exact integrableOn_zero
  · -- strong measurability of the summands
    have hxD_meas : ∀ i b : ℕ, AEStronglyMeasurable (fun θ => Work.FTS.H2.xD f g i b z θ)
        (volume.restrict Work.Spaces.Iθ) := by
      intro i b
      refine Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.FTS.H2.xD f g i b p.1 p.2) ?_ hzpos
      have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter b f p.1 p.2)
          Work.FTS.H2.HQ.quadQ :=
        ((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hf b).continuousOn.mono
          Work.FTS.H2.HQ.quadQ_subset_quadU)
      have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed (i - b) 1 g p.1 p.2)
          Work.FTS.H2.HQ.quadQ :=
        ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hg (i - b) 1).continuousOn.mono
          Work.FTS.H2.HQ.quadQ_subset_quadU)
      have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i g p.1 p.2)
          Work.FTS.H2.HQ.quadQ :=
        ((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hg i).continuousOn.mono
          Work.FTS.H2.HQ.quadQ_subset_quadU)
      have hfun : (fun p : ℝ × ℝ => Work.FTS.H2.xD f g i b p.1 p.2)
          = fun p : ℝ × ℝ => (i.choose b : ℝ) * (Work.Spaces.DzIter b f p.1 p.2
              * Work.Spaces.mixed (i - b) 1 g p.1 p.2 * Work.Spaces.DzIter i g p.1 p.2
              * (Work.FTS.H2.Whz p.1 p.2) ^ 2) := rfl
      have hW : ContinuousOn (fun p : ℝ × ℝ => (Work.FTS.H2.Whz p.1 p.2) ^ 2)
          Work.FTS.H2.HQ.quadQ := continuousOn_Whz_quad.pow 2
      rw [hfun]
      exact continuousOn_const.mul (((h1.mul h2).mul h3).mul hW)
    have hyM_meas : ∀ i j a b : ℕ, AEStronglyMeasurable (fun θ => Work.FTS.H2.yM α f g i j a b z θ)
        (volume.restrict Work.Spaces.Iθ) := by
      intro i j a b
      refine Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.FTS.H2.yM α f g i j a b p.1 p.2) ?_ hzpos
      have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2)
          Work.FTS.H2.HQ.quadQ :=
        ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf b a).continuousOn.mono
          Work.FTS.H2.HQ.quadQ_subset_quadU)
      have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2)
          Work.FTS.H2.HQ.quadQ :=
        ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hg (j - b) (i - a + 1)).continuousOn.mono
          Work.FTS.H2.HQ.quadQ_subset_quadU)
      have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2)
          Work.FTS.H2.HQ.quadQ :=
        ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hg j i).continuousOn.mono
          Work.FTS.H2.HQ.quadQ_subset_quadU)
      have hfun : (fun p : ℝ × ℝ => Work.FTS.H2.yM α f g i j a b p.1 p.2)
          = fun p : ℝ × ℝ => ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f p.1 p.2
                * Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2
                * Work.Spaces.mixed j i g p.1 p.2 * (Work.FTS.H2.Wm α p.1 p.2) ^ 2) := rfl
      have hW : ContinuousOn (fun p : ℝ × ℝ => (Work.FTS.H2.Wm α p.1 p.2) ^ 2)
          Work.FTS.H2.HQ.quadQ := (continuousOn_Wm_quad α).pow 2
      rw [hfun]
      exact continuousOn_const.mul (((h1.mul h2).mul h3).mul hW)
    -- the slice bound for `D_z³ f`
    obtain ⟨S, hS0, hS⟩ := sup_DzIter_three_le α hα hα1 f hf hmemf z hz
    -- ## the `D_z`-slot summands
    have hxd : ∀ i ∈ Finset.range 5, ∀ b ∈ Finset.range (i + 1),
        MeasureTheory.IntegrableOn
          (fun θ => (if i = 4 ∧ b = 0 then (0 : ℝ) else Work.FTS.H2.xD f g i b z θ))
          Work.Spaces.Iθ := by
      intro i hi b hb
      have hi4 : i ≤ 4 := by have := Finset.mem_range.mp hi; omega
      have hbi : b ≤ i := by have := Finset.mem_range.mp hb; omega
      by_cases hc : i = 4 ∧ b = 0
      · simp only [hc, if_true]
        exact integrableOn_zero
      · simp only [if_neg hc]
        by_cases hb2 : b ≤ 2
        · -- the `f`-factor `D_z^b f` is bounded by `Kf`
          have hib : i - b ≤ 3 := by omega
          have hA : MeasureTheory.IntegrableOn
              (fun θ => (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ) ^ 2)
              Work.Spaces.Iθ := by
            have h := integrableOn_slice_mixedWt_sq α g hg hmemg (i - b) 1 (by norm_num)
              (by omega) hz
            simpa only [mul_pow, sq_abs] using h
          have hB : MeasureTheory.IntegrableOn
              (fun θ => (|Work.Spaces.DzIter i g z θ| * Whz z θ) ^ 2) Work.Spaces.Iθ := by
            have h := integrableOn_slice_Whz_sq α g hg hmemg i hi4 hz
            simpa only [mul_pow, sq_abs] using h
          have hAB : MeasureTheory.IntegrableOn
              (fun θ => (|Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
                * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) Work.Spaces.Iθ :=
            integrableOn_slice_two hA hB
              ((aesm_slice_mixed_Wt_abs α g hg (i - b) 1 hzpos).mul
                (aesm_slice_dzIter_Whz_abs g hg i hzpos))
          have hCd := hAB.const_mul ((i.choose b : ℝ) * Kf)
          refine MeasureTheory.Integrable.mono' hCd (hxD_meas i b) ?_
          filter_upwards [ae_Iθ_mem_Ioo'] with θ hθ
          rw [Real.norm_eq_abs]
          have hpt := xD_Kf_pt α hα f g Kf hKf0 hKf i b hi4 hbi hib hb2 z θ hzpos hθ.1 hθ.2
          simpa only [mul_assoc] using hpt
        · -- the `g`-factor `mixed (i-b) 1 g` is bounded by `Kg`
          have hb3 : 3 ≤ b := by omega
          have hA : MeasureTheory.IntegrableOn
              (fun θ => (|Work.Spaces.DzIter b f z θ| * Whz z θ) ^ 2) Work.Spaces.Iθ := by
            have h := integrableOn_slice_Whz_sq α f hf hmemf b (by omega) hz
            simpa only [mul_pow, sq_abs] using h
          have hB : MeasureTheory.IntegrableOn
              (fun θ => (|Work.Spaces.DzIter i g z θ| * Whz z θ) ^ 2) Work.Spaces.Iθ := by
            have h := integrableOn_slice_Whz_sq α g hg hmemg i hi4 hz
            simpa only [mul_pow, sq_abs] using h
          have hAB : MeasureTheory.IntegrableOn
              (fun θ => (|Work.Spaces.DzIter b f z θ| * Whz z θ)
                * (|Work.Spaces.DzIter i g z θ| * Whz z θ)) Work.Spaces.Iθ :=
            integrableOn_slice_two hA hB
              ((aesm_slice_dzIter_Whz_abs f hf b hzpos).mul
                (aesm_slice_dzIter_Whz_abs g hg i hzpos))
          have hCd := hAB.const_mul ((i.choose b : ℝ) * Kg)
          refine MeasureTheory.Integrable.mono' hCd (hxD_meas i b) ?_
          filter_upwards [ae_Iθ_mem_Ioo'] with θ hθ
          rw [Real.norm_eq_abs]
          have hpt := xD_Kg_pt α hα f g Kg hKg0 hKg i b hi4 hbi hb3 z θ hzpos hθ.1 hθ.2
          simpa only [mul_assoc] using hpt
    -- ## the mixed-slot summands
    have hyM : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5, ∀ a ∈ Finset.range (i + 1),
        ∀ b ∈ Finset.range (j + 1),
        MeasureTheory.IntegrableOn
          (fun θ => (if 1 ≤ i ∧ i + j ≤ 4 then
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then (0 : ℝ)
               else Work.FTS.H2.yM α f g i j a b z θ)
            else 0)) Work.Spaces.Iθ := by
      intro i hi j hj a ha b hb
      have hi4 : i ≤ 4 := by have := Finset.mem_range.mp hi; omega
      have hj4 : j ≤ 4 := by have := Finset.mem_range.mp hj; omega
      have hai : a ≤ i := by have := Finset.mem_range.mp ha; omega
      have hbj : b ≤ j := by have := Finset.mem_range.mp hb; omega
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · simp only [if_pos hc]
        by_cases hex : a = 0 ∧ b = 0 ∧ i + j = 4
        · simp only [if_pos hex]
          exact integrableOn_zero
        · simp only [if_neg hex]
          by_cases hab2 : a + b ≤ 2
          · -- the `f`-factor `mixed b a f` is bounded by `Kf`
            have hord : (i - a + 1) + (j - b) ≤ 4 := by omega
            have hA : MeasureTheory.IntegrableOn
                (fun θ => (|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ) ^ 2)
                Work.Spaces.Iθ := by
              have h := integrableOn_slice_mixedWt_sq α g hg hmemg (j - b) (i - a + 1)
                (by omega) hord hz
              simpa only [mul_pow, sq_abs] using h
            have hB : MeasureTheory.IntegrableOn
                (fun θ => (|Work.Spaces.mixed j i g z θ| * Wm α z θ) ^ 2) Work.Spaces.Iθ := by
              have h := integrableOn_slice_mixedWt_sq α g hg hmemg j i (by omega) hc.2 hz
              simpa only [mul_pow, sq_abs] using h
            have hAB : MeasureTheory.IntegrableOn
                (fun θ => (|Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
                  * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) Work.Spaces.Iθ :=
              integrableOn_slice_two hA hB
                ((aesm_slice_mixed_Wt_abs α g hg (j - b) (i - a + 1) hzpos).mul
                  (aesm_slice_mixed_Wt_abs α g hg j i hzpos))
            have hCd := hAB.const_mul ((i.choose a : ℝ) * (j.choose b : ℝ) * Kf)
            refine MeasureTheory.Integrable.mono' hCd ((hyM_meas i j a b).congr ?_) ?_
            · filter_upwards [ae_Iθ_mem_Ioo'] with θ hθ
              simp only [Work.FTS.H2.yM]
            · filter_upwards [ae_Iθ_mem_Ioo'] with θ hθ
              rw [Real.norm_eq_abs]
              exact yM_Kf_pt α f g Kf hKf0 hKf i j a b hc.1 hc.2 hai hbj hab2 z θ hzpos hθ.1 hθ.2
          · by_cases ha1 : 1 ≤ a
            · -- the `g`-factor `mixed (j-b) (i-a+1) g` is bounded by `Kg`
              have hab3 : 3 ≤ a + b := by omega
              have hA : MeasureTheory.IntegrableOn
                  (fun θ => (|Work.Spaces.mixed b a f z θ| * Wm α z θ) ^ 2) Work.Spaces.Iθ := by
                have h := integrableOn_slice_mixedWt_sq α f hf hmemf b a ha1 (by omega) hz
                simpa only [mul_pow, sq_abs] using h
              have hB : MeasureTheory.IntegrableOn
                  (fun θ => (|Work.Spaces.mixed j i g z θ| * Wm α z θ) ^ 2) Work.Spaces.Iθ := by
                have h := integrableOn_slice_mixedWt_sq α g hg hmemg j i (by omega) hc.2 hz
                simpa only [mul_pow, sq_abs] using h
              have hAB : MeasureTheory.IntegrableOn
                  (fun θ => (|Work.Spaces.mixed b a f z θ| * Wm α z θ)
                    * (|Work.Spaces.mixed j i g z θ| * Wm α z θ)) Work.Spaces.Iθ :=
                integrableOn_slice_two hA hB
                  ((aesm_slice_mixed_Wt_abs α f hf b a hzpos).mul
                    (aesm_slice_mixed_Wt_abs α g hg j i hzpos))
              have hCd := hAB.const_mul ((i.choose a : ℝ) * (j.choose b : ℝ) * Kg)
              refine MeasureTheory.Integrable.mono' hCd ((hyM_meas i j a b).congr ?_) ?_
              · filter_upwards [ae_Iθ_mem_Ioo'] with θ hθ
                simp only [Work.FTS.H2.yM]
              · filter_upwards [ae_Iθ_mem_Ioo'] with θ hθ
                rw [Real.norm_eq_abs]
                exact yM_Kg_mixed_pt α f g Kg hKg0 hKg i j a b hc.1 hc.2 hai hbj ha1 hab3
                  z θ hzpos hθ.1 hθ.2
            · -- the exceptional summand: `a = 0`, `b = 3`, `i = 1`, `j = 3`
              have ha0 : a = 0 := by omega
              have hb3 : 3 ≤ b := by omega
              have hj3 : j = 3 := by omega
              have hi1 : i = 1 := by omega
              have hb3' : b = 3 := by omega
              subst ha0; subst hb3'; subst hj3; subst hi1
              have hA : MeasureTheory.IntegrableOn
                  (fun θ => (|Work.Spaces.mixed 0 2 g z θ| * Wm α z θ) ^ 2) Work.Spaces.Iθ := by
                have h := integrableOn_slice_mixedWt_sq α g hg hmemg 0 2 (by norm_num)
                  (by norm_num) hz
                simpa only [mul_pow, sq_abs] using h
              have hB : MeasureTheory.IntegrableOn
                  (fun θ => (|Work.Spaces.mixed 3 1 g z θ| * Wm α z θ) ^ 2) Work.Spaces.Iθ := by
                have h := integrableOn_slice_mixedWt_sq α g hg hmemg 3 1 (by norm_num)
                  (by norm_num) hz
                simpa only [mul_pow, sq_abs] using h
              have hAB : MeasureTheory.IntegrableOn
                  (fun θ => (|Work.Spaces.mixed 0 2 g z θ| * Wm α z θ)
                    * (|Work.Spaces.mixed 3 1 g z θ| * Wm α z θ)) Work.Spaces.Iθ :=
                integrableOn_slice_two hA hB
                  ((aesm_slice_mixed_Wt_abs α g hg 0 2 hzpos).mul
                    (aesm_slice_mixed_Wt_abs α g hg 3 1 hzpos))
              have hCd := hAB.const_mul ((Nat.choose 3 3 : ℝ) * S)
              refine MeasureTheory.Integrable.mono' hCd ((hyM_meas 1 3 0 3).congr ?_) ?_
              · filter_upwards [ae_Iθ_mem_Ioo'] with θ hθ
                simp only [Work.FTS.H2.yM]
              · filter_upwards [ae_Iθ_mem_Ioo'] with θ hθ
                rw [Real.norm_eq_abs]
                exact yM_pure_pt α f g S hS0 1 3 3 (by norm_num) (by norm_num) (by norm_num)
                  z hzpos (fun θ' h1 h2 => hS θ' h1 h2) θ hθ.1 hθ.2
      · simp only [if_neg hc]
        exact integrableOn_zero
    -- ## assembling `EasySumQ` and transferring to `T1Easy`
    have hsum : MeasureTheory.IntegrableOn (fun θ => Work.H2.T1Q.EasySumQ α f g z θ)
        Work.Spaces.Iθ := by
      show MeasureTheory.IntegrableOn (fun θ =>
        (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
            (if i = 4 ∧ b = 0 then (0 : ℝ) else Work.FTS.H2.xD f g i b z θ))
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then
                ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                  (if a = 0 ∧ b = 0 ∧ i + j = 4 then (0 : ℝ)
                   else Work.FTS.H2.yM α f g i j a b z θ)
               else 0)) Work.Spaces.Iθ
      refine MeasureTheory.Integrable.add ?_ ?_
      · refine MeasureTheory.integrable_finsetSum _ fun i hi => ?_
        exact MeasureTheory.integrable_finsetSum _ fun b hb => hxd i hi b hb
      · refine MeasureTheory.integrable_finsetSum _ fun i hi => ?_
        refine MeasureTheory.integrable_finsetSum _ fun j hj => ?_
        by_cases hc : 1 ≤ i ∧ i + j ≤ 4
        · simp only [if_pos hc]
          refine MeasureTheory.integrable_finsetSum _ fun a ha => ?_
          refine MeasureTheory.integrable_finsetSum _ fun b hb => ?_
          have h := hyM i hi j hj a ha b hb
          simp only [if_pos hc] at h
          exact h
        · simp only [if_neg hc]
          exact integrableOn_zero
    refine MeasureTheory.Integrable.congr hsum ?_
    show ∀ᵐ θ ∂(volume.restrict (Set.Icc (0 : ℝ) (π / 2))),
      Work.H2.T1Q.EasySumQ α f g z θ = Work.FTS.H2.T1Easy α f g z θ
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (Set.Finite.measure_zero
      (by simp : ({0, π / 2} : Set ℝ).Finite) volume)
    intro θ hθ
    simp only [Set.mem_setOf_eq, not_imp, Set.mem_Icc] at hθ
    obtain ⟨hθI, hne⟩ := hθ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h0 : θ = 0
    · exact Or.inl h0
    · right
      by_contra h2
      exact hne ((Work.FTS.H2.T1Easy_expandQ α hα f g hf hg z hz θ
        ⟨lt_of_le_of_ne hθI.1 (Ne.symm h0), lt_of_le_of_ne hθI.2 h2⟩).symm)

end Work.H2.T1Q
