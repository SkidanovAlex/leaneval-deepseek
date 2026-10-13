import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.Prop.TraceDefs
import Submission.Work.EllipticEst.Core.memLp_two_of_continuousOn_Icc
import Submission.Work.Spaces.cs_integral
import Submission.Work.EllipticEst.Core.derivIntegrableOfEnergy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Pointwise identity (explicit form of `g'`). -/
theorem flux_pointwise' (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun y : ℝ => (f y * chi y) * (deriv f y * chi y + f y * deriv chi y)
        - (f y) ^ 2 * chi y * deriv chi y)
      ((deriv f θ * chi θ + f θ * deriv chi θ) ^ 2
        + f θ * deriv (deriv f) θ * (chi θ) ^ 2 - (f θ) ^ 2 * (deriv chi θ) ^ 2) θ := by
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := Ioo_mem_nhds hθ.1 hθ.2
  have hf1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.deriv_of_isOpen (n := 2) (m := 1) isOpen_Ioo (by norm_num)
  have hdf : DifferentiableAt ℝ f θ := (hf.contDiffAt hmem).differentiableAt (by norm_num)
  have hdf1 : DifferentiableAt ℝ (deriv f) θ := (hf1.contDiffAt hmem).differentiableAt (by norm_num)
  have hchi : DifferentiableAt ℝ chi θ :=
    ((chi_contDiff 1).differentiable (by norm_num)).differentiableAt
  have hchi1 : DifferentiableAt ℝ (deriv chi) θ :=
    ((((chi_contDiff 2).contDiffOn).deriv_of_isOpen (m := 1) isOpen_univ (by norm_num)).contDiffAt
      Filter.univ_mem).differentiableAt (by simp)
  have hg : HasDerivAt (fun y : ℝ => f y * chi y)
      (deriv f θ * chi θ + f θ * deriv chi θ) θ :=
    hdf.hasDerivAt.mul hchi.hasDerivAt
  have hg' : HasDerivAt (fun y : ℝ => deriv f y * chi y + f y * deriv chi y)
      ((deriv (deriv f) θ * chi θ + deriv f θ * deriv chi θ)
        + (deriv f θ * deriv chi θ + f θ * deriv (deriv chi) θ)) θ :=
    (hdf1.hasDerivAt.mul hchi.hasDerivAt).add (hdf.hasDerivAt.mul hchi1.hasDerivAt)
  have hgprod : HasDerivAt
      (fun y : ℝ => (f y * chi y) * (deriv f y * chi y + f y * deriv chi y))
      ((deriv f θ * chi θ + f θ * deriv chi θ) * (deriv f θ * chi θ + f θ * deriv chi θ)
        + (f θ * chi θ) * ((deriv (deriv f) θ * chi θ + deriv f θ * deriv chi θ)
            + (deriv f θ * deriv chi θ + f θ * deriv (deriv chi) θ))) θ :=
    hg.mul hg'
  have hfsq : HasDerivAt (fun y : ℝ => (f y) ^ 2) (2 * (f θ) ^ (2 - 1) * deriv f θ) θ :=
    hdf.hasDerivAt.pow 2
  have hsecond : HasDerivAt (fun y : ℝ => (f y) ^ 2 * chi y * deriv chi y)
      (((2 * (f θ) ^ (2 - 1) * deriv f θ) * chi θ + (f θ) ^ 2 * deriv chi θ) * deriv chi θ
        + (f θ) ^ 2 * chi θ * deriv (deriv chi) θ) θ :=
    (hfsq.mul hchi.hasDerivAt).mul hchi1.hasDerivAt
  exact (hgprod.sub hsecond).congr_deriv (by ring)

/-- The integration-by-parts (FTC) identity on `[1/2, b]`. -/
theorem flux_ftc (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {b : ℝ} (hb1 : 1 < b) (hb2 : b < Real.pi / 2) :
    f b * deriv f b = ∫ y in (1 / 2)..b,
      ((deriv f y * chi y + f y * deriv chi y) ^ 2
        + f y * deriv (deriv f) y * (chi y) ^ 2 - (f y) ^ 2 * (deriv chi y) ^ 2) := by
  set Θ : ℝ → ℝ := fun y => (f y * chi y) * (deriv f y * chi y + f y * deriv chi y)
      - (f y) ^ 2 * chi y * deriv chi y with hΘ
  set F' : ℝ → ℝ := fun y => (deriv f y * chi y + f y * deriv chi y) ^ 2
      + f y * deriv (deriv f) y * (chi y) ^ 2 - (f y) ^ 2 * (deriv chi y) ^ 2 with hF'
  have hhalf : (1 / 2 : ℝ) ≤ b := by linarith
  have hderiv : ∀ x ∈ Set.uIcc (1 / 2) b, HasDerivAt Θ (F' x) x := by
    intro x hx
    rw [Set.uIcc_of_le hhalf] at hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact flux_pointwise' f hf hx'
  have hsubI : Set.uIcc (1 / 2) b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Set.uIcc_of_le hhalf]
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcontf : ContinuousOn f (Set.uIcc (1 / 2) b) := hf.continuousOn.mono hsubI
  have hcontf1 : ContinuousOn (deriv f) (Set.uIcc (1 / 2) b) :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsubI
  have hcontf2 : ContinuousOn (deriv (deriv f)) (Set.uIcc (1 / 2) b) :=
    ((hf.deriv_of_isOpen (n := 2) (m := 1) isOpen_Ioo (by norm_num)).continuousOn_deriv_of_isOpen
      (n := 1) isOpen_Ioo (by norm_num)).mono hsubI
  have hconchi : ContinuousOn chi (Set.uIcc (1 / 2) b) :=
    ((chi_contDiff 1).continuous).continuousOn
  have hcondchi : ContinuousOn (deriv chi) (Set.uIcc (1 / 2) b) :=
    ((chi_contDiff 2).continuous_deriv (by norm_num)).continuousOn
  have hint : IntervalIntegrable F' volume (1 / 2) b := by
    rw [hF']
    refine ContinuousOn.intervalIntegrable ?_
    exact (((hcontf1.mul hconchi).add (hcontf.mul hcondchi)).pow 2).add
      ((hcontf.mul hcontf2).mul (hconchi.pow 2))
      |>.sub ((hcontf.pow 2).mul (hcondchi.pow 2))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc, hΘ]
  have hchi_half : chi (1 / 2) = 0 := chi_zero le_rfl
  have hchi_b : chi b = 1 := chi_one hb1.le
  have hdchi_b : deriv chi b = 0 := deriv_chi_eq_zero_of_one_lt hb1
  simp only [hchi_half, hchi_b, hdchi_b, mul_one, mul_zero, sub_zero, zero_mul, sub_self]
  ring

/-- The uniform lower bound for `f b · f' b` at every scale `b ∈ (1, π/2)`. -/
theorem flux_bound_aux (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ θ : ℝ, (deriv chi θ) ^ 2 ≤ K)
    (hA : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    {b : ℝ} (hb1 : 1 < b) (hb2 : b < Real.pi / 2) :
    -(Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      + K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) ≤ f b * deriv f b := by
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hAdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    with hBdef
  have hhalf : (1 / 2 : ℝ) ≤ b := by linarith
  set S : Set ℝ := Set.Ioo (1 / 2) b with hS
  have hSsub : S ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [hS]
    exact fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- global integrability of the two unweighted energies
  have hAioo : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hA.mono_set Set.Ioo_subset_Icc_self
  have hBioo : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := hB.mono_set Set.Ioo_subset_Icc_self
  have hcont2ioo : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 (Real.pi / 2)) :=
    ((hf.deriv_of_isOpen (n := 2) (m := 1) isOpen_Ioo (by norm_num)).continuousOn_deriv_of_isOpen
      (n := 1) isOpen_Ioo (by norm_num))
  have hFioo : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
    refine Integrable.mono' hAioo ((hf.continuousOn.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    show |(f θ) ^ 2| ≤ (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    rw [abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hθ)
  have hGioo : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine Integrable.mono' hBioo ((hcont2ioo.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    show |(deriv (deriv f) θ) ^ 2| ≤ (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    rw [abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hθ)
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
  have hAeq : A = ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    rw [hAdef, Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioo]
  have hBeq : B = ∫ θ in Set.Ioo 0 (Real.pi / 2),
      (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    rw [hBdef, Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioo]
  -- continuity on `S` and on the compact interval
  have hcontSf : ContinuousOn f S := hf.continuousOn.mono hSsub
  have hcontSf1 : ContinuousOn (deriv f) S :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hSsub
  have hcontSf2 : ContinuousOn (deriv (deriv f)) S := hcont2ioo.mono hSsub
  have hcontSch : ContinuousOn chi S := ((chi_contDiff 1).continuous).continuousOn
  have hcontSch1 : ContinuousOn (deriv chi) S :=
    ((chi_contDiff 2).continuous_deriv (by norm_num)).continuousOn
  have hsubIcc : Set.uIcc (1 / 2) b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Set.uIcc_of_le hhalf]
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcontIf : ContinuousOn f (Set.uIcc (1 / 2) b) := hf.continuousOn.mono hsubIcc
  have hcontIf1 : ContinuousOn (deriv f) (Set.uIcc (1 / 2) b) :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsubIcc
  have hcontIf2 : ContinuousOn (deriv (deriv f)) (Set.uIcc (1 / 2) b) := hcont2ioo.mono hsubIcc
  have hcontIch : ContinuousOn chi (Set.uIcc (1 / 2) b) :=
    ((chi_contDiff 1).continuous).continuousOn
  have hcontIch1 : ContinuousOn (deriv chi) (Set.uIcc (1 / 2) b) :=
    ((chi_contDiff 2).continuous_deriv (by norm_num)).continuousOn
  -- the local weighted `L²` of `f` is dominated by `A`
  have hFleA : (∫ x in S, (f x) ^ 2) ≤ A := by
    have h2a : (∫ x in S, (f x) ^ 2) ≤ ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 :=
      MeasureTheory.setIntegral_mono_set hFioo (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hSsub hx)
    have h2b : (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2)
        ≤ ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x := by
      refine MeasureTheory.integral_mono_ae (hFioo.mono_set (le_refl _)) hAioo ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hx)
    rw [hAeq]
    exact le_trans h2a h2b
  have hGleB : (∫ x in S, (deriv (deriv f) x) ^ 2) ≤ B := by
    have h2a : (∫ x in S, (deriv (deriv f) x) ^ 2)
        ≤ ∫ x in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) x) ^ 2 :=
      MeasureTheory.setIntegral_mono_set hGioo (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hSsub hx)
    have h2b : (∫ x in Set.Ioo 0 (Real.pi / 2), (deriv (deriv f) x) ^ 2)
        ≤ ∫ x in Set.Ioo 0 (Real.pi / 2),
            (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x := by
      refine MeasureTheory.integral_mono_ae (hGioo.mono_set (le_refl _)) hBioo ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact le_mul_of_one_le_right (sq_nonneg _) (Work.EllipticEst.Core.one_le_thEta hx)
    rw [hBeq]
    exact le_trans h2a h2b
  have hP : (∫ x in S, (f x * chi x) ^ 2) ≤ A := by
    have hi : MeasureTheory.IntegrableOn (fun x : ℝ => (f x * chi x) ^ 2) S := by
      refine Integrable.mono' (hFioo.mono_set hSsub)
        (((hcontSf.mul hcontSch).pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x _
      have hcx : (chi x) ^ 2 ≤ 1 := by nlinarith [chi_nonneg x, chi_le_one x]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      nlinarith [hcx, sq_nonneg (f x)]
    have h1 : (∫ x in S, (f x * chi x) ^ 2) ≤ ∫ x in S, (f x) ^ 2 := by
      refine MeasureTheory.setIntegral_mono hi (hFioo.mono_set hSsub) (fun x => ?_)
      have hcx : (chi x) ^ 2 ≤ 1 := by nlinarith [chi_nonneg x, chi_le_one x]
      rw [mul_pow]
      nlinarith [hcx, sq_nonneg (f x)]
    exact le_trans h1 hFleA
  have hQ : (∫ x in S, (deriv (deriv f) x * chi x) ^ 2) ≤ B := by
    have hi : MeasureTheory.IntegrableOn (fun x : ℝ => (deriv (deriv f) x * chi x) ^ 2) S := by
      refine Integrable.mono' (hGioo.mono_set hSsub)
        (((hcontSf2.mul hcontSch).pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x _
      have hcx : (chi x) ^ 2 ≤ 1 := by nlinarith [chi_nonneg x, chi_le_one x]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      nlinarith [hcx, sq_nonneg (deriv (deriv f) x)]
    have h1 : (∫ x in S, (deriv (deriv f) x * chi x) ^ 2) ≤ ∫ x in S, (deriv (deriv f) x) ^ 2 := by
      refine MeasureTheory.setIntegral_mono hi (hGioo.mono_set hSsub) (fun x => ?_)
      have hcx : (chi x) ^ 2 ≤ 1 := by nlinarith [chi_nonneg x, chi_le_one x]
      rw [mul_pow]
      nlinarith [hcx, sq_nonneg (deriv (deriv f) x)]
    exact le_trans h1 hGleB
  -- the cross term by Cauchy–Schwarz
  have hcross : -(∫ x in S, f x * deriv (deriv f) x * (chi x) ^ 2) ≤ Real.sqrt (A * B) := by
    have hsubI : Set.Icc (1 / 2) b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hmem1 : MeasureTheory.MemLp (fun x : ℝ => f x * chi x) 2
        (MeasureTheory.volume.restrict (Set.Icc (1 / 2) b)) :=
      Work.EllipticEst.Core.memLp_two_of_continuousOn_Icc
        ((hf.continuousOn.mono hsubI).mul (((chi_contDiff 1).continuous).continuousOn))
    have hmem2 : MeasureTheory.MemLp (fun x : ℝ => deriv (deriv f) x * chi x) 2
        (MeasureTheory.volume.restrict (Set.Icc (1 / 2) b)) :=
      Work.EllipticEst.Core.memLp_two_of_continuousOn_Icc
        ((hcont2ioo.mono hsubI).mul (((chi_contDiff 1).continuous).continuousOn))
    have hcs := Work.Spaces.cs_integral hmem1 hmem2
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo,
      MeasureTheory.integral_Icc_eq_integral_Ioo,
      MeasureTheory.integral_Icc_eq_integral_Ioo] at hcs
    have hprod : (∫ x in S, (f x * chi x) * (deriv (deriv f) x * chi x))
        = ∫ x in S, f x * deriv (deriv f) x * (chi x) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x _ => ?_)
      ring
    rw [hprod] at hcs
    have hQ0 : 0 ≤ ∫ x in S, (deriv (deriv f) x * chi x) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioo (fun x _ => sq_nonneg _)
    have hAB : (∫ x in S, f x * deriv (deriv f) x * (chi x) ^ 2) ^ 2 ≤ A * B :=
      le_trans hcs (mul_le_mul hP hQ hQ0 hA0)
    have habs := Real.abs_le_sqrt hAB
    linarith [neg_le_abs (∫ x in S, f x * deriv (deriv f) x * (chi x) ^ 2)]
  -- the truncation term
  have hchi2 : (∫ x in S, (f x) ^ 2 * (deriv chi x) ^ 2) ≤ K * A := by
    have hi : MeasureTheory.IntegrableOn (fun x : ℝ => (f x) ^ 2 * (deriv chi x) ^ 2) S := by
      refine Integrable.mono' ((hFioo.mono_set hSsub).const_mul K)
        (((hcontSf.pow 2).mul (hcontSch1.pow 2)).aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x _
      have hbnd : (deriv chi x) ^ 2 ≤ K := hK x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      nlinarith [hbnd, sq_nonneg (f x)]
    have h2 : (∫ x in S, (f x) ^ 2 * (deriv chi x) ^ 2) ≤ ∫ x in S, K * (f x) ^ 2 := by
      refine MeasureTheory.setIntegral_mono hi ((hFioo.mono_set hSsub).const_mul K) (fun x => ?_)
      have hbnd : (deriv chi x) ^ 2 ≤ K := hK x
      nlinarith [hbnd, sq_nonneg (f x)]
    have h3 : (∫ x in S, K * (f x) ^ 2) = K * ∫ x in S, (f x) ^ 2 :=
      MeasureTheory.integral_const_mul K fun x => (f x) ^ 2
    refine le_trans h2 ?_
    rw [h3]
    exact mul_le_mul_of_nonneg_left hFleA hK0
  have hcontI1 : ContinuousOn (fun y : ℝ => (deriv f y * chi y + f y * deriv chi y) ^ 2)
      (Set.uIcc (1 / 2) b) := ((hcontIf1.mul hcontIch).add (hcontIf.mul hcontIch1)).pow 2
  have hcontI2 : ContinuousOn (fun y : ℝ => f y * deriv (deriv f) y * (chi y) ^ 2)
      (Set.uIcc (1 / 2) b) := (hcontIf.mul hcontIf2).mul (hcontIch.pow 2)
  have hcontI3 : ContinuousOn (fun y : ℝ => (f y) ^ 2 * (deriv chi y) ^ 2)
      (Set.uIcc (1 / 2) b) := (hcontIf.pow 2).mul (hcontIch1.pow 2)
  have hftc := flux_ftc f hf hb1 hb2
  have hsplit : (∫ y in (1 / 2)..b, ((deriv f y * chi y + f y * deriv chi y) ^ 2
        + f y * deriv (deriv f) y * (chi y) ^ 2 - (f y) ^ 2 * (deriv chi y) ^ 2))
      = (∫ y in (1 / 2)..b, (deriv f y * chi y + f y * deriv chi y) ^ 2)
        + (∫ y in (1 / 2)..b, f y * deriv (deriv f) y * (chi y) ^ 2)
        - (∫ y in (1 / 2)..b, (f y) ^ 2 * (deriv chi y) ^ 2) := by
    rw [intervalIntegral.integral_sub (hcontI1.intervalIntegrable.add hcontI2.intervalIntegrable)
      hcontI3.intervalIntegrable,
      intervalIntegral.integral_add hcontI1.intervalIntegrable hcontI2.intervalIntegrable]
  have hI1 : 0 ≤ ∫ y in (1 / 2)..b, (deriv f y * chi y + f y * deriv chi y) ^ 2 :=
    intervalIntegral.integral_nonneg hhalf (fun y _ => sq_nonneg _)
  have hI2 : -(∫ y in (1 / 2)..b, f y * deriv (deriv f) y * (chi y) ^ 2)
      ≤ Real.sqrt (A * B) := by
    have hconv : (∫ y in (1 / 2)..b, f y * deriv (deriv f) y * (chi y) ^ 2)
        = ∫ y in S, f y * deriv (deriv f) y * (chi y) ^ 2 := by
      rw [hS, intervalIntegral.integral_of_le hhalf, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [hconv]
    exact hcross
  have hI3 : (∫ y in (1 / 2)..b, (f y) ^ 2 * (deriv chi y) ^ 2) ≤ K * A := by
    have hconv : (∫ y in (1 / 2)..b, (f y) ^ 2 * (deriv chi y) ^ 2)
        = ∫ y in S, (f y) ^ 2 * (deriv chi y) ^ 2 := by
      rw [hS, intervalIntegral.integral_of_le hhalf, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [hconv]
    exact hchi2
  rw [hftc, hsplit]
  linarith


/-- The flux half of `traceBoundRight`, with the constant produced by `chi_deriv_bdd`. -/
theorem TraceFluxAux : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : ℝ → ℝ) (F₁ L₁ : ℝ),
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁) →
    Filter.Tendsto (deriv f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L₁) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ →
    -(F₁ * L₁) ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
        + K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  obtain ⟨K, hK0, hK⟩ := chi_deriv_bdd
  refine ⟨K, hK0, ?_⟩
  intro f F₁ L₁ hf hF hL hA hB
  have hpi : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hev : ∀ᶠ b in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      -(Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
        + K * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      ≤ f b * deriv f b := by
    filter_upwards [self_mem_nhdsWithin,
      (Filter.le_def.mp nhdsWithin_le_nhds (Set.Ioi (1 : ℝ))) (Ioi_mem_nhds hpi)] with b hb2 hb1
    exact flux_bound_aux f hf K hK0 hK hA hB hb1 hb2
  have htend : Filter.Tendsto (fun b : ℝ => f b * deriv f b)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (F₁ * L₁)) := hF.mul hL
  have hlim := ge_of_tendsto htend hev
  linarith

end Work.FTS.EllipticEst.Prop
