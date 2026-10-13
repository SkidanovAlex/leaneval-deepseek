import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.RPAe.Defs
import Submission.Work.FTS.EllSol.RPAe.sliceSqEtaInt
import Submission.Work.FTS.EllSol.RPAe.groupBoundF
import Submission.Work.FTS.EllSol.RPAe.groupBoundP
import Submission.Work.FTS.EllSol.VopAux.TraceAux
import Submission.Work.FTS.EllSol.VopAux.SliceDPointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

open scoped Real Topology
open MeasureTheory Set Filter

/-
# The level-`4` angular Poincaré estimate `ropPoincareAe`

For `f` of class `C^∞` on the open quadrant `(0,∞) × (0,π/2)` whose angular slices satisfy the
endpoint trace conditions

* `D_z^j f z · → 0` at both endpoints, for `j ≤ 3` at *every* `z > 0` and for `j = 4` for
  *almost every* `z > 0`,

whose `D_z^j`-slices vanish at the two endpoints as *values* for `j ≤ 4`, and whose second angular
derivative is honestly in `ℋ⁴`, the weighted `ℋ⁴`-norms of `f` and of `∂_θ f` are bounded by a
constant (uniform in `α ∈ (0,1]`) times that of `∂_θ² f`, and `f`, `∂_θ f` are themselves honestly
in `ℋ⁴`.

Route: for almost every `z` the `ℋ⁴`-integrand of `f` (resp. `∂_θ f`) is compared slice group by
slice group with the one of `∂_θ² f` (`RPAe.groupBoundF`, `RPAe.groupBoundP`, both resting on the
single-slice estimates `VopAux.sliceF_le_sliceV` / `VopAux.sliceF_deriv_le_sliceV`), and the
comparison is integrated over `z`.  Pointwise in `z` the integrability of every slice group is
supplied by `RPAe.sliceGroupIntegrable`, which needs no trace hypothesis: the extra ingredient is
that `∫ (u'')² sin(2θ)^{-η} < ∞` forces `u'` to have a finite limit at both endpoints (Hölder
against `sin(2θ)^{η} ∈ L¹`), hence `u` to be bounded there.
-/

theorem ropPoincareAe : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) →
      (∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 f z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      (∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
        Work.Spaces.DzIter j f z 0 = 0 ∧ Work.Spaces.DzIter j f z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α 4 (Work.Spaces.pthIter 2 f) →
      Work.Spaces.HkMem α 4 f ∧ Work.Spaces.HkMem α 4 (Work.Spaces.pth f) ∧
        Work.Spaces.HkNorm α 4 f ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 f) ∧
        Work.Spaces.HkNorm α 4 (Work.Spaces.pth f)
          ≤ C * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 f) := by
  refine ⟨max 1 Work.FTS.EllSol.RPAe.sliceCs,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α f hα0 hα1 hsm htr3 htr4ae hval hmem
  have hSO : Work.FTS.EllipticEst.SmoothOpen f :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hSOp : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth f) := hSO.pth
  have hSO2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 f) := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hSO.pth.pth
  have hrgst : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := 0)).symm
  -- the conull set of `z` carrying all the trace hypotheses
  have hgood : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (0 < z) ∧ (∀ j : ℕ, j ≤ 4 →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
    have h4 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 f z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter 4 f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      rw [hrgst]
      exact htr4ae
    have hpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
      rw [hrgst]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
    filter_upwards [hpos, h4] with z hz h4z
    refine ⟨hz, fun j hj => ?_⟩
    rcases le_or_gt j 3 with h3 | h3
    · exact htr3 j h3 z hz
    · have hj4 : j = 4 := by omega
      subst hj4
      exact h4z
  -- per-`z` integrability of the slice groups
  have hgrp : ∀ z ∈ Work.Spaces.Iz, ∀ j : ℕ, j ≤ 4 →
      MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
        Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ)
        Work.Spaces.Iθ :=
    RPAe.sliceGroupIntegrableEasy α f hα0 hα1 hSO htr3 hmem.1
  -- the slice groups at `z = 0` vanish
  have hgrp0 : ∀ (G : ℝ → ℝ → ℝ) (j : ℕ) (θ : ℝ),
      Work.FTS.EllipticEst.sliceGroup α 4 j G 0 θ = 0 := by
    intro G j θ
    rw [Work.FTS.EllipticEst.sliceGroup, Work.Spaces.Wt, Work.Spaces.w]
    simp
  -- pointwise integrability of the `ℋ⁴`-integrand
  have hint_f : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
        Work.Spaces.Iθ := by
    intro z hz
    rw [show (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
        = fun θ => ∑ j ∈ Finset.range 5,
            Work.FTS.EllipticEst.sliceGroup α 4 j f z θ from
      funext fun θ => Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α 4 f z θ]
    exact MeasureTheory.integrable_finsetSum (Finset.range 5)
      (fun j hj => (hgrp z hz j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1)
  have hint_p : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 (Work.Spaces.pth f) z θ)
        Work.Spaces.Iθ := by
    intro z hz
    rw [show (fun θ => Work.Spaces.HkIntegrand α 4 (Work.Spaces.pth f) z θ)
        = fun θ => ∑ j ∈ Finset.range 5,
            Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ from
      funext fun θ => Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α 4 (Work.Spaces.pth f) z θ]
    exact MeasureTheory.integrable_finsetSum (Finset.range 5)
      (fun j hj => (hgrp z hz j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2)
  -- integrability of the slice groups of `∂_θ²f`
  have hgrp2 : ∀ z ∈ Work.Spaces.Iz, ∀ j : ℕ, j ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ)
        Work.Spaces.Iθ := by
    intro z hz j hj
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      rw [show (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) 0 θ)
          = fun _ : ℝ => (0 : ℝ) from
        funext fun θ => hgrp0 (Work.Spaces.pthIter 2 f) j θ]
      exact integrableOn_zero
    · exact Work.FTS.EllSol.VopAux.integrableOn_sliceGroup_of_HkIntegrand hSO2 hzpos hj
        (hmem.1 z hz)
  -- the three decompositions of the angle integrals into slice groups
  have hdec : ∀ (G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen G →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 4 G z θ) Work.Spaces.Iθ) →
      (∀ z ∈ Work.Spaces.Iz, ∀ j : ℕ, j ≤ 4 → MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j G z θ) Work.Spaces.Iθ) →
      ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 G z θ)
          = ∑ j ∈ Finset.range 5, ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α 4 j G z θ := by
    intro G hG hInt hgrps z hz
    rw [← MeasureTheory.integral_finsetSum (s := Finset.range 5)
      (f := fun j θ => Work.FTS.EllipticEst.sliceGroup α 4 j G z θ)
      (fun j hj => hgrps z hz j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ =>
      Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α 4 G z θ)
  have hdec_f := hdec f hSO hint_f (fun z hz j hj => (hgrp z hz j hj).1)
  have hdec_p := hdec (Work.Spaces.pth f) hSOp hint_p (fun z hz j hj => (hgrp z hz j hj).2)
  have hdec_2 := hdec (Work.Spaces.pthIter 2 f) hSO2 hmem.1 hgrp2
  -- the two a.e. per-`z` comparisons
  have hbd_f : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) := by
    filter_upwards [hgood] with z hz
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz.1
    have hjb : ∀ j ∈ Finset.range 5, j ≤ 4 := fun j hj =>
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        = ∑ j ∈ Finset.range 5,
            ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j f z θ :=
          hdec_f z hzI
      _ ≤ ∑ j ∈ Finset.range 5, Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ) :=
          Finset.sum_le_sum fun j hj =>
            RPAe.groupBoundF α f hα0 hα1 hSO z hz.1 j (hjb j hj)
              (hz.2 j (hjb j hj)).1 (hz.2 j (hjb j hj)).2 (hmem.1 z hzI)
      _ = Work.FTS.EllSol.RPAe.sliceCs * ∑ j ∈ Finset.range 5,
            ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ :=
          (Finset.mul_sum (Finset.range 5)
            (fun j => ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ)
            Work.FTS.EllSol.RPAe.sliceCs).symm
      _ = Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) := by
          rw [hdec_2 z hzI]
  have hbd_p : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (Work.Spaces.pth f) z θ)
        ≤ Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) := by
    filter_upwards [hgood] with z hz
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz.1
    have hjb : ∀ j ∈ Finset.range 5, j ≤ 4 := fun j hj =>
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (Work.Spaces.pth f) z θ)
        = ∑ j ∈ Finset.range 5,
            ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pth f) z θ :=
          hdec_p z hzI
      _ ≤ ∑ j ∈ Finset.range 5, Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ) :=
          Finset.sum_le_sum fun j hj =>
            RPAe.groupBoundP α f hα0 hα1 hSO z hz.1 j (hjb j hj)
              (hz.2 j (hjb j hj)).1 (hz.2 j (hjb j hj)).2 (hmem.1 z hzI)
      _ = Work.FTS.EllSol.RPAe.sliceCs * ∑ j ∈ Finset.range 5,
            ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ :=
          (Finset.mul_sum (Finset.range 5)
            (fun j => ∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ)
            Work.FTS.EllSol.RPAe.sliceCs).symm
      _ = Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) := by
          rw [hdec_2 z hzI]
  -- membership
  have hmemf : Work.Spaces.HkMem α 4 f := by
    refine ⟨hint_f, ?_⟩
    refine MeasureTheory.Integrable.mono' (hmem.2.const_mul Work.FTS.EllSol.RPAe.sliceCs)
      (Work.FTS.EllSol.VopAux.aesm_integral_HkIntegrand α 4 hSO) ?_
    filter_upwards [hbd_f] with z hz
    rw [Real.norm_of_nonneg (MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ)
      measurableSet_Icc (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ))]
    exact hz
  have hmem1 : Work.Spaces.HkMem α 4 (Work.Spaces.pth f) := by
    refine ⟨hint_p, ?_⟩
    refine MeasureTheory.Integrable.mono' (hmem.2.const_mul Work.FTS.EllSol.RPAe.sliceCs)
      (Work.FTS.EllSol.VopAux.aesm_integral_HkIntegrand α 4 hSOp) ?_
    filter_upwards [hbd_p] with z hz
    rw [Real.norm_of_nonneg (MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ)
      measurableSet_Icc (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 (Work.Spaces.pth f) z θ))]
    exact hz
  -- the squared norm comparisons
  have hSq_le : ∀ (G : ℝ → ℝ → ℝ),
      (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 G z θ)
          ≤ Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ)) →
      Work.Spaces.HkSq α 4 G
        ≤ Work.FTS.EllSol.RPAe.sliceCs * Work.Spaces.HkSq α 4 (Work.Spaces.pthIter 2 f) := by
    intro G hbd
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 G z θ) :=
      Filter.Eventually.of_forall fun z => MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ)
        measurableSet_Icc (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 G z θ)
    have hInt : MeasureTheory.Integrable (fun z => Work.FTS.EllSol.RPAe.sliceCs *
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      hmem.2.const_mul Work.FTS.EllSol.RPAe.sliceCs
    have hm := MeasureTheory.integral_mono_of_nonneg hnn hInt hbd
    calc Work.Spaces.HkSq α 4 G
        = ∫ z in Work.Spaces.Iz, (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 G z θ) z := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) := hm
      _ = Work.FTS.EllSol.RPAe.sliceCs * ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) :=
          MeasureTheory.integral_const_mul Work.FTS.EllSol.RPAe.sliceCs _
      _ = Work.FTS.EllSol.RPAe.sliceCs * Work.Spaces.HkSq α 4 (Work.Spaces.pthIter 2 f) := rfl
  have hSq1 := hSq_le f hbd_f
  have hSq2 := hSq_le (Work.Spaces.pth f) hbd_p
  -- the norm comparisons
  have hnorm_le : ∀ (G : ℝ → ℝ → ℝ), Work.Spaces.HkSq α 4 G
        ≤ Work.FTS.EllSol.RPAe.sliceCs * Work.Spaces.HkSq α 4 (Work.Spaces.pthIter 2 f) →
      Work.Spaces.HkNorm α 4 G
        ≤ max 1 Work.FTS.EllSol.RPAe.sliceCs
            * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 f) := by
    intro G hSq
    calc Work.Spaces.HkNorm α 4 G = Real.sqrt (Work.Spaces.HkSq α 4 G) := rfl
      _ ≤ Real.sqrt (Work.FTS.EllSol.RPAe.sliceCs
            * Work.Spaces.HkSq α 4 (Work.Spaces.pthIter 2 f)) := Real.sqrt_le_sqrt hSq
      _ = Real.sqrt Work.FTS.EllSol.RPAe.sliceCs
            * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 f) := by
          rw [Real.sqrt_mul (le_of_lt Work.FTS.EllSol.RPAe.sliceCs_pos), Work.Spaces.HkNorm]
      _ ≤ max 1 Work.FTS.EllSol.RPAe.sliceCs
            * Work.Spaces.HkNorm α 4 (Work.Spaces.pthIter 2 f) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact Work.FTS.EllSol.VopAux.sqrt_le_max_one Work.FTS.EllSol.RPAe.sliceCs
  exact ⟨hmemf, hmem1, hnorm_le f hSq1, hnorm_le (Work.Spaces.pth f) hSq2⟩


end Work.FTS.EllSol
