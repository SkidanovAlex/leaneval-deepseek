import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.VopAux.SliceTraceDefs
import Submission.Work.FTS.EllSol.VopAux.sliceF_le_sliceV
import Submission.Work.FTS.EllSol.VopAux.sliceF_deriv_le_sliceV
import Submission.Work.FTS.EllSol.VopAux.TraceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Per-`z` comparison of the `ℋ^k`-integrands for `f`** (the `∂_θ²`-case): the angular
integral of the `ℋ^k`-integrand of `f` is bounded by a constant times that of `∂_θ²f`, and the
integrand of `f` is itself integrable.  The constant is uniform in `α ∈ (0,1]` and in `f`; it
depends only on the level `k`. -/
theorem HkIntegrand_integral_le_pth2_trace (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f →
      (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
        Work.Spaces.Iθ) →
      ∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ)
          Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := by
  classical
  have hcf := fun K => Classical.choose_spec (sliceF_le_sliceV K)
  let C : ℝ := (∑ K ∈ Finset.range (k + 1),
    Classical.choose (sliceF_le_sliceV K)) + 1
  have hCpos : 0 < C := by
    have h1 : 0 < ∑ K ∈ Finset.range (k + 1), Classical.choose (sliceF_le_sliceV K) :=
      Finset.sum_pos (fun K _ => (hcf K).1)
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
    simp only [C]; linarith
  have hCle : ∀ K ≤ k, Classical.choose (sliceF_le_sliceV K) ≤ C := by
    intro K hK
    have hmem : K ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hK)
    have hsum : Classical.choose (sliceF_le_sliceV K)
        ≤ ∑ K' ∈ Finset.range (k + 1), Classical.choose (sliceF_le_sliceV K') :=
      Finset.single_le_sum (fun K' _ => le_of_lt (hcf K').1) hmem
    simp only [C]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro α f hα0 hα1 hf htrace hInt z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · -- `z = 0`: both integrands vanish
    subst hz0
    constructor
    · rw [show (fun θ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ : ℝ => (0 : ℝ) from
        funext fun θ => Work.FTS.EllipticEst.HkIntegrand_zero_left α k f θ]
      exact integrableOn_zero
    · rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f 0 θ) = 0 from by
        rw [show (fun θ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ : ℝ => (0 : ℝ) from
          funext fun θ => Work.FTS.EllipticEst.HkIntegrand_zero_left α k f θ]
        simp]
      exact mul_nonneg (le_of_lt hCpos) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pthIter 2 f) 0 θ))
  · -- `z > 0`
    have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 f) := by
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hf.pth.pth
    have hIntV : ∀ j ≤ k, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
      fun j hj => integrableOn_sliceV_thEta hf hzpos hj (hInt z hz)
    have hIntL : ∀ j ≤ k, ∀ m ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter m
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
      intro j hj m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmj : m + j ≤ k := by
        have h2 := (Finset.mem_Icc.mp hm).2; omega
      exact integrableOn_sliceV_LopIter hf hzpos hm1 hmj (hInt z hz)
    -- the single-slice estimate for every radial level `j ≤ k`
    have hslice : ∀ j ≤ k,
        MeasureTheory.IntegrableOn (fun θ =>
          (fun θ' => Work.Spaces.DzIter j f z θ') θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
            Work.Spaces.Iθ ∧
        (∀ i ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ =>
          (Work.FTS.EllipticEst.LopIter i (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) ∧
        sliceF (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ')
          ≤ Classical.choose (sliceF_le_sliceV (k - j))
            * sliceF (k - j) α
                (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
      fun j hj => (hcf (k - j)).2 α (fun θ' => Work.Spaces.DzIter j f z θ') hα0 hα1
        (contDiffOn_slice_of_smoothOpen (hf.DzIter j) hzpos)
        (htrace j hj z hzpos).1 (htrace j hj z hzpos).2 (hIntV j hj) (hIntL j hj)
    -- integrability of the slice groups of `f`
    have hgrpF : ∀ j ∈ Finset.range (k + 1),
        MeasureTheory.IntegrableOn (fun θ =>
          Work.FTS.EllipticEst.sliceGroup α k j f z θ) Work.Spaces.Iθ := by
      intro j hj
      have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      obtain ⟨h0i, hLi, -⟩ := hslice j hjle
      have hintW : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j) h0i hLi
      refine (hintW.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
      filter_upwards [Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo (u := fun θ =>
          (Work.Spaces.w z) ^ 2
            * sliceW (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') θ)
        (v := fun θ => Work.FTS.EllipticEst.sliceGroup α k j f z θ)
        (fun θ hθ => (sliceGroup_eq_sliceW α k j f hzpos hf.forall θ hθ).symm)] with θ hθ
      exact hθ
    -- integrability of the slice groups of `∂_θ² f`
    have hgrp2 : ∀ j ∈ Finset.range (k + 1),
        MeasureTheory.IntegrableOn (fun θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
          Work.Spaces.Iθ :=
      fun j hj => integrableOn_sliceGroup_of_HkIntegrand hpth2 hzpos
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) (hInt z hz)
    have hdecomp : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        = ∑ j ∈ Finset.range (k + 1),
            ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j f z θ := by
      rw [← MeasureTheory.integral_finsetSum (s := Finset.range (k + 1))
        (f := fun j θ => Work.FTS.EllipticEst.sliceGroup α k j f z θ) hgrpF]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ =>
        Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k f z θ)
    have hdecomp2 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
        = ∑ j ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ := by
      rw [← MeasureTheory.integral_finsetSum (s := Finset.range (k + 1))
        (f := fun j θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) hgrp2]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ =>
        Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k (Work.Spaces.pthIter 2 f) z θ)
    have hgroup_bound : ∀ j ∈ Finset.range (k + 1),
        (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j f z θ)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) := by
      intro j hj
      have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      obtain ⟨h0i, hLi, hbnd⟩ := hslice j hjle
      have hintW : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j) h0i hLi
      have hintW2 : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α
            (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j)
        (hIntV j hjle) (hIntL j hjle)
      rw [integral_sliceGroup_eq_sliceF α k j f hzpos hf hintW,
        integral_sliceGroup_pthIter2_eq_sliceF α k j f hzpos hf hintW2]
      have hFnn : 0 ≤ sliceF (k - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
        sliceF_nonneg _ _ _
      calc (Work.Spaces.w z) ^ 2 * sliceF (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ')
          ≤ (Work.Spaces.w z) ^ 2 * (Classical.choose (sliceF_le_sliceV (k - j))
              * sliceF (k - j) α
                  (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) :=
            mul_le_mul_of_nonneg_left hbnd (sq_nonneg _)
        _ = (Classical.choose (sliceF_le_sliceV (k - j)) * (Work.Spaces.w z) ^ 2)
              * sliceF (k - j) α
                  (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
            ring
        _ ≤ (C * (Work.Spaces.w z) ^ 2) * sliceF (k - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
            refine mul_le_mul_of_nonneg_right ?_ hFnn
            exact mul_le_mul_of_nonneg_right (hCle (k - j) (Nat.sub_le k j)) (sq_nonneg _)
        _ = C * ((Work.Spaces.w z) ^ 2 * sliceF (k - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) := by
            ring
    constructor
    · rw [show (fun θ => Work.Spaces.HkIntegrand α k f z θ)
          = fun θ => ∑ j ∈ Finset.range (k + 1),
              Work.FTS.EllipticEst.sliceGroup α k j f z θ from
        funext fun θ => Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k f z θ]
      exact MeasureTheory.integrable_finsetSum _ hgrpF
    · calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
          = ∑ j ∈ Finset.range (k + 1),
              ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j f z θ :=
            hdecomp
        _ ≤ ∑ j ∈ Finset.range (k + 1), C * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) :=
            Finset.sum_le_sum hgroup_bound
        _ = C * ∑ j ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ :=
            (Finset.mul_sum ..).symm
        _ = C * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := by
            rw [hdecomp2]

/-- **Per-`z` comparison of the `ℋ^k`-integrands for `∂_θ f`** (the `∂_θ`-case). -/
theorem HkIntegrand_integral_le_pth2_pth_trace (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f →
      (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
        Work.Spaces.Iθ) →
      ∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := by
  classical
  have hcd := fun K => Classical.choose_spec (sliceF_deriv_le_sliceV K)
  let C : ℝ := (∑ K ∈ Finset.range (k + 1),
    Classical.choose (sliceF_deriv_le_sliceV K)) + 1
  have hCpos : 0 < C := by
    have h1 : 0 < ∑ K ∈ Finset.range (k + 1), Classical.choose (sliceF_deriv_le_sliceV K) :=
      Finset.sum_pos (fun K _ => (hcd K).1)
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
    simp only [C]; linarith
  have hCle : ∀ K ≤ k, Classical.choose (sliceF_deriv_le_sliceV K) ≤ C := by
    intro K hK
    have hmem : K ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hK)
    have hsum : Classical.choose (sliceF_deriv_le_sliceV K)
        ≤ ∑ K' ∈ Finset.range (k + 1), Classical.choose (sliceF_deriv_le_sliceV K') :=
      Finset.single_le_sum (fun K' _ => le_of_lt (hcd K').1) hmem
    simp only [C]; linarith
  refine ⟨C, hCpos, ?_⟩
  intro α f hα0 hα1 hf htrace hInt z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    constructor
    · rw [show (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) 0 θ)
          = fun _ : ℝ => (0 : ℝ) from
        funext fun θ => Work.FTS.EllipticEst.HkIntegrand_zero_left α k
          (Work.Spaces.pth f) θ]
      exact integrableOn_zero
    · rw [show (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) 0 θ) = 0 from by
        rw [show (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) 0 θ)
            = fun _ : ℝ => (0 : ℝ) from
          funext fun θ => Work.FTS.EllipticEst.HkIntegrand_zero_left α k
            (Work.Spaces.pth f) θ]
        simp]
      exact mul_nonneg (le_of_lt hCpos) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pthIter 2 f) 0 θ))
  · have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 f) := by
      simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hf.pth.pth
    have hIntV : ∀ j ≤ k, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
      fun j hj => integrableOn_sliceV_thEta hf hzpos hj (hInt z hz)
    have hIntL : ∀ j ≤ k, ∀ m ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter m
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
      intro j hj m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmj : m + j ≤ k := by
        have h2 := (Finset.mem_Icc.mp hm).2; omega
      exact integrableOn_sliceV_LopIter hf hzpos hm1 hmj (hInt z hz)
    have hslice : ∀ j ≤ k,
        MeasureTheory.IntegrableOn (fun θ =>
          (deriv (fun θ' => Work.Spaces.DzIter j f z θ') θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ ∧
        (∀ i ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn (fun θ =>
          (Work.FTS.EllipticEst.LopIter i (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) ∧
        sliceF (k - j) α (deriv (fun θ' => Work.Spaces.DzIter j f z θ'))
          ≤ Classical.choose (sliceF_deriv_le_sliceV (k - j))
            * sliceF (k - j) α
                (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
      fun j hj => (hcd (k - j)).2 α (fun θ' => Work.Spaces.DzIter j f z θ') hα0 hα1
        (contDiffOn_slice_of_smoothOpen (hf.DzIter j) hzpos)
        (htrace j hj z hzpos).1 (htrace j hj z hzpos).2 (hIntV j hj) (hIntL j hj)
    have hgrpP : ∀ j ∈ Finset.range (k + 1),
        MeasureTheory.IntegrableOn (fun θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ) Work.Spaces.Iθ := by
      intro j hj
      have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      obtain ⟨h0i, hLi, -⟩ := hslice j hjle
      have hintW : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j) h0i hLi
      refine (hintW.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
      filter_upwards [Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo (u := fun θ =>
          (Work.Spaces.w z) ^ 2
            * sliceW (k - j) α (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
        (v := fun θ => Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ)
        (fun θ hθ => (sliceGroup_pth_eq_sliceW α k j f hzpos hf.forall θ hθ).symm)]
        with θ hθ
      exact hθ
    have hgrp2 : ∀ j ∈ Finset.range (k + 1),
        MeasureTheory.IntegrableOn (fun θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
          Work.Spaces.Iθ :=
      fun j hj => integrableOn_sliceGroup_of_HkIntegrand hpth2 hzpos
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) (hInt z hz)
    have hdecomp : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
        = ∑ j ∈ Finset.range (k + 1),
            ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ := by
      rw [← MeasureTheory.integral_finsetSum (s := Finset.range (k + 1))
        (f := fun j θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ) hgrpP]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ =>
        Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k (Work.Spaces.pth f) z θ)
    have hdecomp2 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
        = ∑ j ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ := by
      rw [← MeasureTheory.integral_finsetSum (s := Finset.range (k + 1))
        (f := fun j θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) hgrp2]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ =>
        Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k (Work.Spaces.pthIter 2 f) z θ)
    have hidentP : ∀ j ∈ Finset.range (k + 1),
        (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ)
          = (Work.Spaces.w z) ^ 2 * sliceF (k - j) α
              (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) := by
      intro j _
      rw [sliceF, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo (u := fun θ =>
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ)
        (v := fun θ => (Work.Spaces.w z) ^ 2 * sliceW (k - j) α
          (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
        (fun θ hθ => sliceGroup_pth_eq_sliceW α k j f hzpos hf.forall θ hθ)] with θ hθ
      exact hθ
    have hgroup_bound : ∀ j ∈ Finset.range (k + 1),
        (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) := by
      intro j hj
      have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      obtain ⟨h0i, hLi, hbnd⟩ := hslice j hjle
      have hintW : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j) h0i hLi
      have hintW2 : MeasureTheory.IntegrableOn
          (fun θ => sliceW (k - j) α
            (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
          Work.Spaces.Iθ := integrableOn_sliceW_of (K := k - j)
        (hIntV j hjle) (hIntL j hjle)
      rw [hidentP j hj,
        integral_sliceGroup_pthIter2_eq_sliceF α k j f hzpos hf hintW2]
      have hFnn : 0 ≤ sliceF (k - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
        sliceF_nonneg _ _ _
      calc (Work.Spaces.w z) ^ 2
              * sliceF (k - j) α (deriv (fun θ' => Work.Spaces.DzIter j f z θ'))
          ≤ (Work.Spaces.w z) ^ 2 * (Classical.choose (sliceF_deriv_le_sliceV (k - j))
              * sliceF (k - j) α
                  (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) :=
            mul_le_mul_of_nonneg_left hbnd (sq_nonneg _)
        _ = (Classical.choose (sliceF_deriv_le_sliceV (k - j)) * (Work.Spaces.w z) ^ 2)
              * sliceF (k - j) α
                  (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
            ring
        _ ≤ (C * (Work.Spaces.w z) ^ 2) * sliceF (k - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
            refine mul_le_mul_of_nonneg_right ?_ hFnn
            exact mul_le_mul_of_nonneg_right (hCle (k - j) (Nat.sub_le k j)) (sq_nonneg _)
        _ = C * ((Work.Spaces.w z) ^ 2 * sliceF (k - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) := by
            ring
    constructor
    · rw [show (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          = fun θ => ∑ j ∈ Finset.range (k + 1),
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ from
        funext fun θ => Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k
          (Work.Spaces.pth f) z θ]
      exact MeasureTheory.integrable_finsetSum _ hgrpP
    · calc (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ)
          = ∑ j ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ := hdecomp
        _ ≤ ∑ j ∈ Finset.range (k + 1), C * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ) :=
            Finset.sum_le_sum hgroup_bound
        _ = C * ∑ j ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ :=
            (Finset.mul_sum ..).symm
        _ = C * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := by
            rw [hdecomp2]

end Work.FTS.EllSol.VopAux
