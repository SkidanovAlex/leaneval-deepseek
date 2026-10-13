import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.Rl1

set_option autoImplicit false

/-! ## The weighted angular energy of an `ℋ^k`-function

`∫_{z>0} w(z) ∫_θ f(z,θ)² dθ dz ≤ HkSq α k f` is a *one-term* consequence of the definition of
`HkSq`: the `i = 0` term of the `D_z`-part of `HkIntegrand α k f` is
`(f z θ · w z / sin(2θ)^{η/2})²`, and on the open quadrant the factor `w z / sin(2θ)^{η/2}` is
`≥ 1` (indeed `≥ w z ≥ 1`), so it dominates `w z · f z θ²`.  The two `L¹`-conjuncts follow from
the honest integrability of the `ℋ^k`-integrand slice (`HkMem`) by domination; the
`AEStronglyMeasurable` conjunct only needs the smoothness of `f`, through the joint
measurability of `(z,θ) ↦ f z θ²` on the open quadrant (`Spaces.aesm_of_continuousOn_Qd`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`. -/

/-! ### Elementary facts about the radial weight -/

/-- On `z > 0` the radial weight `w z = ((1+z)/z)²` is `≥ 1`. -/
private lemma one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : (0 : ℝ) < z ^ 2 := pow_pos hz 2
  rw [Work.Spaces.w, one_le_div hz2]
  exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2

/-- The radial weight is nonnegative everywhere (at `z = 0` Lean's totalised division
gives the value `0`, which is irrelevant). -/
private lemma w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The open interval `(0,π/2)` and the closed `Iθ` carry the same restriction of Lebesgue
measure (they differ by the two null endpoints). -/
private lemma restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-! ### The pointwise domination -/

/-- **Pointwise domination of the angular energy by the `ℋ^k`-integrand.**  On the open
quadrant, `w z * f z θ ^ 2` is bounded by the `i = 0` term
`(f z θ * (w z / sin(2θ)^{η/2}))²` of `HkIntegrand`: since `sin(2θ)^{η/2} ≤ 1` and `w z ≥ 1`
we have `w z ≤ w z / sin(2θ)^{η/2} ≤ (w z / sin(2θ)^{η/2})²`. -/
private lemma w_mul_sq_le_HkIntegrand {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.w z * (f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  set t : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with ht
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have ht_pos : 0 < t := by rw [ht]; exact Real.rpow_pos_of_pos hsinpos _
  have ht_le : t ≤ 1 := by
    rw [ht]
    exact Real.rpow_le_one (le_of_lt hsinpos) (Real.sin_le_one _)
      (by rw [Work.Spaces.eta]; norm_num)
  have hw1 : 1 ≤ Work.Spaces.w z := one_le_w_of_pos hz
  have hw0 : 0 ≤ Work.Spaces.w z := le_trans zero_le_one hw1
  have hwc : Work.Spaces.w z ≤ (Work.Spaces.w z / t) ^ 2 := by
    have h1 : Work.Spaces.w z ≤ Work.Spaces.w z / t := by
      rw [le_div_iff₀ ht_pos]
      calc Work.Spaces.w z * t ≤ Work.Spaces.w z * 1 := mul_le_mul_of_nonneg_left ht_le hw0
        _ = Work.Spaces.w z := mul_one _
    have h2 : Work.Spaces.w z / t ≤ (Work.Spaces.w z / t) ^ 2 := by
      have h3 : 1 ≤ Work.Spaces.w z / t := le_trans hw1 h1
      calc Work.Spaces.w z / t = Work.Spaces.w z / t * 1 := (mul_one _).symm
        _ ≤ Work.Spaces.w z / t * (Work.Spaces.w z / t) :=
            mul_le_mul_of_nonneg_left h3 (le_trans zero_le_one h3)
        _ = (Work.Spaces.w z / t) ^ 2 := by ring
    exact le_trans h1 h2
  have hterm : (f z θ * (Work.Spaces.w z / t)) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ := by
    simpa only [Work.Spaces.DzIter_zero, ht] using
      (Work.Spaces.sq_le_HkIntegrand_z α k f z θ 0 (Nat.zero_le k))
  calc Work.Spaces.w z * (f z θ) ^ 2
      ≤ (f z θ) ^ 2 * (Work.Spaces.w z / t) ^ 2 := by
        rw [mul_comm (Work.Spaces.w z) ((f z θ) ^ 2)]
        exact mul_le_mul_of_nonneg_left hwc (sq_nonneg _)
    _ = (f z θ * (Work.Spaces.w z / t)) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k f z θ := hterm

/-- The angular energy of a slice, weighted by `w`, is dominated by the angular integral of the
`ℋ^k`-integrand.  (Only `z > 0` is needed.) -/
private lemma w_mul_int_sq_le {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α k f)
    {z : ℝ} (hz : 0 < z) :
    Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
  rw [← MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ)]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => mul_nonneg (w_nonneg z) (sq_nonneg _))
    (hmem.1 z hzIz) ?_
  rw [← restrict_Ioo_eq_restrict_Iθ]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => w_mul_sq_le_HkIntegrand hz hθ)

/-! ### The target -/

theorem WAngEnergyLe {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hreg : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
      MeasureTheory.IntegrableOn
        (fun z => Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)) (Set.Ioi (0 : ℝ)) ∧
      (∫ z in Set.Ioi (0 : ℝ),
          Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2))
        ≤ Work.Spaces.HkSq α k f := by
  -- the integrable majorant: the `θ`-integral of the `ℋ^k`-integrand at `z`
  have hmaj : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hIzm : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (α := ℝ) (a := 0))
    rw [hIzm]
    exact hmem.2
  -- the strong measurability of the angular energy, from joint measurability of `f²`
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hIzm : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (α := ℝ) (a := 0)).symm
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
      have h1 : ContinuousOn (Function.uncurry f)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
        hreg.continuousOn.mono
          (Set.prod_mono (Set.Ioi_subset_Ioi (show (-1 : ℝ) ≤ 0 by norm_num)) (subset_refl _))
      have h2 : (Function.uncurry f) ^ 2 = fun p : ℝ × ℝ => (f p.1 p.2) ^ 2 := rfl
      simpa only [h2] using h1.pow 2
    have hIz : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) := by
      have h := (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) hcont)
        |>.integral_prod_right'
      simpa only using h
    simpa only [hIzm] using hIz
  refine ⟨haesm, ?_, ?_⟩
  · -- `IntegrableOn`: domination a.e. in `z` by the integrable `ℋ^k`-integrand slice
    have hmeasw : Measurable Work.Spaces.w := by
      show Measurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
      fun_prop
    have haesm_prod : AEStronglyMeasurable
        (fun z : ℝ => Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hmeasw.aestronglyMeasurable.mul haesm
    refine MeasureTheory.Integrable.mono' (f := fun z : ℝ =>
      Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)) hmaj haesm_prod ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (w_nonneg z)
      (MeasureTheory.integral_nonneg fun θ => sq_nonneg _))]
    exact w_mul_int_sq_le hmem hz
  · -- the integral inequality: monotonicity of the integral, one slice at a time
    rw [Work.Spaces.HkSq]
    have hconv : (∫ z in Set.Ioi (0 : ℝ),
          Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2))
        = ∫ z in Work.Spaces.Iz,
            Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) :=
      MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (α := ℝ) (a := 0))
    rw [hconv]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (w_nonneg z)
        (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)) hmem.2 ?_
    refine MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) (fun z hz => ?_)
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
    · -- the single slice `z = 0`, where `w 0 = 0`
      subst h
      have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      show Work.Spaces.w 0 * (∫ θ in Work.Spaces.Iθ, f 0 θ ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f 0 θ
      rw [hw0, zero_mul]
      exact MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f 0 θ
    · show Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ
      exact w_mul_int_sq_le hmem h

end Work.FTS.Nonlinear.Pieces.Rl1
