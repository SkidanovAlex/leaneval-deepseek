import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real Topology
open MeasureTheory Set Filter

/-- **A radial profile with the decay `|D_z^i r| ≤ C z²/(1+z)³` (`i ≤ 4`) is an `ℋ⁴`-function,
uniformly in `α ∈ (0,1]`.**

Because `r` depends on `z` only, every mixed slot `D_z^j D_θ^i r` with `i ≥ 1` vanishes, so the
`ℋ⁴`-integrand reduces to the pure `D_z`-sum (`Work.Elliptic.HkIntegrand_rad`).  The weight
`w(z) = (1+z)²/z²` converts the hypothesis into the bound `|D_z^i r · w| ≤ C/(1+z)`, whence
`Rint r ≤ 5 (C/(1+z))²` pointwise; the last quantity is integrable on `[0,∞)` with integral at
most `2` (`Work.FTS.H2.InvOneAddSq`).  Consequently `HkSq α 4 r ≤ 10 C² K_θ` with
`K_θ = ∫_θ sin(2θ)^{-η}`, independently of `α`, and `HkNorm = √(HkSq) ≤ √(10 C² K_θ)`. -/
theorem RadHkMemXn {r : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0))
    (h : ∀ i : ℕ, i ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter i r z| ≤ C * z ^ 2 / (1 + z) ^ 3) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => r z) ∧
      Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) ≤ C' := by
  -- ### Step 1: the pointwise slot bound `(D_z^i r)² w² ≤ (C/(1+z))²` on `Iz`.
  have hslot : ∀ (i : ℕ), i ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
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
  -- ### Step 2: `Rint r = Σ_{i≤4} (D_z^i r)² w²` is pointwise bounded by `5 (C/(1+z))²`.
  have hRint_le : ∀ z ∈ Work.Spaces.Iz,
      Work.FTS.Nonlinear.RadialProd.Rint r z ≤ 5 * (C / (1 + z)) ^ 2 := by
    intro z hz
    rw [Work.FTS.Nonlinear.RadialProd.Rint]
    calc ∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ∑ _i ∈ Finset.range 5, (C / (1 + z)) ^ 2 :=
          Finset.sum_le_sum (fun i hi =>
            hslot i (by have := Finset.mem_range.mp hi; omega) z hz)
      _ = 5 * (C / (1 + z)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ### Step 3: the dominating function is integrable on `Iz`.
  have hg_int : IntegrableOn (fun z : ℝ => 5 * (C / (1 + z)) ^ 2) Work.Spaces.Iz := by
    have h1 : MeasureTheory.Integrable (fun z : ℝ => 5 * C ^ 2 * (1 / (1 + z)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul _
    have h2 : MeasureTheory.Integrable (fun z : ℝ => 5 * (C / (1 + z)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      h1.congr (Filter.Eventually.of_forall fun z => by ring)
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h2
    exact h2
  -- ### Step 4: `Rint r` is a.e. strongly measurable on `Iz`.
  have hRint_aesm : AEStronglyMeasurable (Work.FTS.Nonlinear.RadialProd.Rint r)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hr_aesm : AEStronglyMeasurable r (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h1 : AEStronglyMeasurable r (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        (hsm 0).continuousOn.aestronglyMeasurable measurableSet_Ioi
      rwa [MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h1
    have hw_aesm : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (by
        have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
            = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
          funext z; rw [Work.Spaces.w]
        rw [hfun]
        fun_prop : Measurable fun z : ℝ => (Work.Spaces.w z) ^ 2).aestronglyMeasurable
    rw [show (Work.FTS.Nonlinear.RadialProd.Rint r)
        = ∑ i ∈ Finset.range 5,
            (fun z : ℝ => (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        from by
          funext z
          rw [Work.FTS.Nonlinear.RadialProd.Rint, Finset.sum_apply]]
    refine Finset.aestronglyMeasurable_sum _ (fun i _ => ?_)
    by_cases hi0 : i = 0
    · subst hi0
      have hfun : (fun z : ℝ => (Work.Elliptic.DzdIter 0 r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          = fun z : ℝ => (r z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
        funext z
        rw [Work.Elliptic.DzdIter_zero]
      rw [hfun]
      exact (hr_aesm.pow 2).mul hw_aesm
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      have hmeas : Measurable (Work.Elliptic.DzdIter (k + 1) r) := by
        have hfun : Work.Elliptic.DzdIter (k + 1) r
            = fun z : ℝ => z * deriv (Work.Elliptic.DzdIter k r) z := rfl
        rw [hfun]
        exact measurable_id.mul (measurable_deriv _)
      exact ((hmeas.aestronglyMeasurable).pow 2).mul hw_aesm
  -- ### Step 5: `Rint r` is integrable on `Iz` and `Rr r ≤ 10 C²`.
  have hRint_int : IntegrableOn (Work.FTS.Nonlinear.RadialProd.Rint r) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hg_int hRint_aesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (Work.FTS.Nonlinear.RadialProd.Rint_nonneg r z)]
    exact hRint_le z hz
  have hRr_le : Work.FTS.Nonlinear.RadialProd.Rr r ≤ 10 * C ^ 2 := by
    have hmono : (∫ z in Work.Spaces.Iz, Work.FTS.Nonlinear.RadialProd.Rint r z)
        ≤ ∫ z in Work.Spaces.Iz, 5 * (C / (1 + z)) ^ 2 :=
      MeasureTheory.integral_mono_ae hRint_int hg_int
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hRint_le)
    have hval : (∫ z in Work.Spaces.Iz, 5 * (C / (1 + z)) ^ 2) ≤ 10 * C ^ 2 := by
      have hIoi : (∫ z in Work.Spaces.Iz, 5 * (C / (1 + z)) ^ 2)
          = ∫ z in Set.Ioi (0 : ℝ), 5 * (C / (1 + z)) ^ 2 :=
        MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ))).symm
      rw [hIoi]
      have hstep : (∫ z in Set.Ioi (0 : ℝ), 5 * (C / (1 + z)) ^ 2)
          = (5 * C ^ 2) * ∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2 := by
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun z => by ring)
      rw [hstep]
      have hnn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2 :=
        MeasureTheory.integral_nonneg fun z => sq_nonneg _
      nlinarith [Work.FTS.H2.InvOneAddSq.2, hnn, sq_nonneg C]
    rw [Work.FTS.Nonlinear.RadialProd.Rr]
    exact hmono.trans hval
  -- ### Step 6: `HkSq α 4 r` and `Xn α r` are bounded independently of `α`.
  have hKth_nonneg : 0 ≤ Work.FTS.Nonlinear.RadialProd.Kth := by
    have := Work.FTS.Nonlinear.RadialProd.one_le_Kth
    linarith
  have hHkSq_le : ∀ α : ℝ, Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => r z)
      ≤ 10 * C ^ 2 * Work.FTS.Nonlinear.RadialProd.Kth := by
    intro α
    rw [Work.FTS.Nonlinear.RadialProd.HkSq_rad_eq α r]
    exact mul_le_mul_of_nonneg_right hRr_le hKth_nonneg
  -- ### Assembly.
  refine ⟨max 1 (Real.sqrt (10 * C ^ 2 * Work.FTS.Nonlinear.RadialProd.Kth)),
    lt_of_lt_of_le one_pos (le_max_left 1 _), ?_⟩
  intro α hα
  constructor
  · -- `HkMem α 4 (fun z _ => r z)`
    have hsin_int : IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ :=
      (Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta Work.Spaces.eta_pos
        Work.Spaces.eta_lt_one).1
    constructor
    · -- the `θ`-slices are integrable
      intro z _hz
      have hconst : IntegrableOn
          (fun θ : ℝ => ((∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i r z) ^ 2)
            * (Work.Spaces.w z) ^ 2) * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
          Work.Spaces.Iθ :=
        hsin_int.const_mul _
      refine hconst.congr_fun (fun θ hθ => ?_) measurableSet_Icc
      rw [Work.Elliptic.HkIntegrand_rad α 4 r z hθ]
    · -- the `z`-integral of the `θ`-integrals is integrable
      refine (hRint_int.mul_const Work.FTS.Nonlinear.RadialProd.Kth).congr
        (Filter.Eventually.of_forall fun z => ?_)
      exact (Work.FTS.Nonlinear.RadialProd.integral_HkIntegrand_rad α r z).symm
  · -- the norm bound
    have hsq := hHkSq_le α
    have h1 : Real.sqrt (Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => r z))
        ≤ Real.sqrt (10 * C ^ 2 * Work.FTS.Nonlinear.RadialProd.Kth) := Real.sqrt_le_sqrt hsq
    exact h1.trans (le_max_right 1 _)

end Work.FTS.StrongEps.ClassCRHS
