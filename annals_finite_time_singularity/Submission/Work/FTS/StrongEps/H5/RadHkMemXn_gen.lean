import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.ClassCRHS.RadHkMemXn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The level-`k` version of `Work.FTS.StrongEps.ClassCRHS.RadHkMemXn`**: a radial profile
whose `z∂_z`-iterates up to order `k` are bounded by `C·z²/(1+z)³` is `ℋᵏ`-honest with an
`α`-uniform `ℋ⁴`-norm bound.

Because `r` depends on `z` only, every mixed slot `D_z^jD_θ^i r` with `i ≥ 1` vanishes, so the
`ℋᵏ`-integrand reduces to the pure `D_z`-sum; the weight `w(z) = (1+z)²/z²` converts the
hypothesis into `|D_z^i r · w| ≤ C/(1+z)`, whence the radial density is dominated by
`(k+1)(C/(1+z))²`, which is integrable on `[0,∞)` with integral at most `2`.

(Note `Work.FTS.Nonlin.Xn α g = HkNorm α 4 g` is fixed at level `4`; the intended uses are
`k = 4, 5`, where the conclusion bounds the level-`4` norm of the lift.) -/
theorem RadHkMemXn_gen {r : ℝ → ℝ} {C : ℝ} {k : ℕ} (hC : 0 < C)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0))
    (h : ∀ i : ℕ, i ≤ k → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter i r z| ≤ C * z ^ 2 / (1 + z) ^ 3) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      Work.Spaces.HkMem α k (fun z (_ : ℝ) => r z) ∧
      Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) ≤ C' := by
  -- ### Step 1: the pointwise slot bound `(D_z^i r)² w² ≤ (C/(1+z))²` on `Iz`.
  have hslot : ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (C / (1 + z)) ^ 2 := by
    intro i hi z hz
    have hz0 : 0 ≤ z := hz
    have habs := h i hi z hz0
    have hsq : (Work.Elliptic.DzdIter i r z) ^ 2 ≤ (C * z ^ 2 / (1 + z) ^ 3) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hprod := mul_le_mul_of_nonneg_right hsq (sq_nonneg (Work.Spaces.w z))
    rcases eq_or_lt_of_le hz0 with hz' | hz'
    · rw [← hz']
      have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
      rw [hw0]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, div_one]
      exact sq_nonneg C
    · refine hprod.trans (le_of_eq ?_)
      rw [Work.Spaces.w]
      field_simp
  -- ### Step 2: the `θ`-integral of the level-`k` radial integrand.
  have hKth_pos : 0 < Work.FTS.Nonlinear.RadialProd.Kth :=
    lt_of_lt_of_le one_pos Work.FTS.Nonlinear.RadialProd.one_le_Kth
  refine ⟨max 1 (Real.sqrt (Work.FTS.Nonlinear.RadialProd.Rr r
      * Work.FTS.Nonlinear.RadialProd.Kth)), lt_of_lt_of_le one_pos (le_max_left 1 _), ?_⟩
  intro α _hα
  constructor
  · -- ### Step 3: `HkMem α k (fun z _ => r z)`.
    -- the pointwise bound for the pure `D_z`-sum
    have hsum_le : ∀ z ∈ Work.Spaces.Iz,
        (∑ i ∈ Finset.range (k + 1),
            (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ ((k : ℝ) + 1) * (C / (1 + z)) ^ 2 := by
      intro z hz
      calc (∑ i ∈ Finset.range (k + 1),
              (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ ∑ _i ∈ Finset.range (k + 1), (C / (1 + z)) ^ 2 :=
            Finset.sum_le_sum (fun i hi => hslot i (by
              have := Finset.mem_range.mp hi; omega) z hz)
        _ = ((k : ℝ) + 1) * (C / (1 + z)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    -- the exact value of the angular integral
    have hinner_eq : ∀ z : ℝ,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z (_ : ℝ) => r z) z θ)
          = (∑ i ∈ Finset.range (k + 1),
              (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * Work.FTS.Nonlinear.RadialProd.Kth := by
      intro z
      have hEq : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z (_ : ℝ) => r z) z θ)
          = ∫ θ in Work.Spaces.Iθ,
              (∑ i ∈ Finset.range (k + 1),
                (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
          (fun θ hθ => by
            rw [Work.Elliptic.HkIntegrand_rad α k r z hθ, ← Finset.sum_mul])
      rw [hEq, MeasureTheory.integral_const_mul]
      simp only [Work.FTS.Nonlinear.RadialProd.Kth, Work.FTS.Nonlinear.RadialProd.smE]
    -- the pointwise bound on the angular integral
    have hinner_le : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z (_ : ℝ) => r z) z θ)
          ≤ (((k : ℝ) + 1) * (C / (1 + z)) ^ 2) * Work.FTS.Nonlinear.RadialProd.Kth := by
      intro z hz
      rw [hinner_eq z]
      exact mul_le_mul_of_nonneg_right (hsum_le z hz) hKth_pos.le
    -- the majorant is integrable on `Iz`
    have hmaj_int : MeasureTheory.IntegrableOn
        (fun z : ℝ => (((k : ℝ) + 1) * (C / (1 + z)) ^ 2)
          * Work.FTS.Nonlinear.RadialProd.Kth) Work.Spaces.Iz := by
      have h1 : MeasureTheory.Integrable (fun z : ℝ =>
          ((((k : ℝ) + 1) * C ^ 2) * Work.FTS.Nonlinear.RadialProd.Kth)
            * (1 / (1 + z)) ^ 2) (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        Work.FTS.H2.InvOneAddSq.1.const_mul _
      have h2 : MeasureTheory.Integrable (fun z : ℝ =>
          (((k : ℝ) + 1) * (C / (1 + z)) ^ 2) * Work.FTS.Nonlinear.RadialProd.Kth)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        h1.congr (Filter.Eventually.of_forall fun z => by ring)
      rw [MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h2
      exact h2
    -- a.e. strong measurability of a single radial slot
    have hw_aesm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (by
        have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
            = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
          funext z; rw [Work.Spaces.w]
        rw [hfun]
        fun_prop : Measurable fun z : ℝ => (Work.Spaces.w z) ^ 2).aestronglyMeasurable
    have hDzd_aesm : ∀ i : ℕ, MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      intro i
      by_cases hi0 : i = 0
      · subst hi0
        have hr_aesm : MeasureTheory.AEStronglyMeasurable r
            (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
          have h1 : MeasureTheory.AEStronglyMeasurable r
              (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
            (hsm 0).continuousOn.aestronglyMeasurable measurableSet_Ioi
          rwa [MeasureTheory.Measure.restrict_congr_set
            (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h1
        have hfun : (fun z : ℝ => (Work.Elliptic.DzdIter 0 r z) ^ 2
              * (Work.Spaces.w z) ^ 2)
            = fun z : ℝ => (r z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          funext z; rw [Work.Elliptic.DzdIter_zero]
        rw [hfun]
        exact (hr_aesm.pow 2).mul hw_aesm
      · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        have hmeas : Measurable (Work.Elliptic.DzdIter (n + 1) r) := by
          have hfun : Work.Elliptic.DzdIter (n + 1) r
              = fun z : ℝ => z * deriv (Work.Elliptic.DzdIter n r) z := rfl
          rw [hfun]
          exact measurable_id.mul (measurable_deriv _)
        exact ((hmeas.aestronglyMeasurable).pow 2).mul hw_aesm
    -- a.e. strong measurability of the outer function
    have houter_aesm : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z (_ : ℝ) => r z) z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z (_ : ℝ) => r z) z θ)
          = (fun z : ℝ => (∑ i ∈ Finset.range (k + 1),
              (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * Work.FTS.Nonlinear.RadialProd.Kth) from funext hinner_eq]
      have hfun : (fun z : ℝ => (∑ i ∈ Finset.range (k + 1),
              (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * Work.FTS.Nonlinear.RadialProd.Kth)
          = ∑ i ∈ Finset.range (k + 1),
              fun z : ℝ => ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
                * Work.FTS.Nonlinear.RadialProd.Kth := by
        funext z
        rw [Finset.sum_apply]
        rw [Finset.sum_mul, ← Finset.sum_mul]
      rw [hfun]
      exact Finset.aestronglyMeasurable_sum _ (fun i _ => (hDzd_aesm i).mul_const _)
    refine ⟨?_, ?_⟩
    · -- every angular slice of the integrand is integrable
      intro z _hz
      have hconst : MeasureTheory.IntegrableOn
          (fun θ : ℝ => ((∑ i ∈ Finset.range (k + 1),
            (Work.Elliptic.DzdIter i r z) ^ 2) * (Work.Spaces.w z) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
        ((Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta Work.Spaces.eta_pos
          Work.Spaces.eta_lt_one).1).const_mul _
      refine hconst.congr_fun (fun θ hθ => ?_) measurableSet_Icc
      rw [Work.Elliptic.HkIntegrand_rad α k r z hθ]
    · -- the `z`-integral of the angular slices is integrable
      refine MeasureTheory.Integrable.mono' hmaj_int houter_aesm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg
        (fun θ => Work.Spaces.HkIntegrand_nonneg α k (fun z (_ : ℝ) => r z) z θ))]
      exact hinner_le z hz
  · -- ### Step 4: the `α`-uniform `ℋ⁴`-norm bound (`Xn` is the *level-`4`* norm).
    calc Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => r z)) := by
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
      _ = Real.sqrt (Work.FTS.Nonlinear.RadialProd.Rr r
            * Work.FTS.Nonlinear.RadialProd.Kth) := by
          rw [Work.FTS.Nonlinear.RadialProd.HkSq_rad_eq α r]
      _ ≤ max 1 (Real.sqrt (Work.FTS.Nonlinear.RadialProd.Rr r
            * Work.FTS.Nonlinear.RadialProd.Kth)) := le_max_right _ _

end Work.FTS.StrongEps.H5
