import Mathlib
import Submission.Work.ZeroDensity.LogFree.poleLSDefs
import Submission.Work.ZeroDensity.LogFree.HB7FreezeInterval
import Submission.Work.ZeroDensity.LogFree.HB7WeightSeries
import Submission.Work.ZeroDensity.LogFree.HB7WeightSeriesSummable
import Submission.Work.ZeroDensity.LogFree.HB7TilingIoi

namespace Work.ZeroDensity.LogFree
open MeasureTheory Real
open scoped Classical BigOperators
noncomputable section

lemma HB7IntegrableExpDivRpow {X s : ℝ} (hX : 0 < X) (hs : 0 < s) :
    IntegrableOn (fun y : ℝ => Real.exp (-(y / X)) * y ^ (s - 1)) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := 1 / X)
      (by linarith) one_pos (by positivity)
  refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  rw [mul_comm (y ^ (s - 1))]
  congr 1
  ring_nf

lemma HB7_norm_cpow_class {a γ y : ℝ} (hy : 0 < y) :
    ‖(y : ℂ) ^ ((a : ℂ) - (γ : ℂ) * Complex.I)‖ = y ^ a := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

lemma HB7_ofReal_mul_cpow_class {a γ : ℝ} {Y t : ℝ} (hY : 0 ≤ Y) (ht : 0 ≤ t) :
    (((Y * t : ℝ)) : ℂ) ^ ((a : ℂ) - (γ : ℂ) * Complex.I)
      = (Y : ℂ) ^ ((a : ℂ) - (γ : ℂ) * Complex.I)
        * (t : ℂ) ^ ((a : ℂ) - (γ : ℂ) * Complex.I) := by
  rw [Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg hY ht _

lemma HB7_contOn {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (z : ι → ℂ) :
    ContinuousOn (fun y : ℝ => ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      (Set.Ioi 0) := by
  have hcp : ∀ w : ℂ, ContinuousOn (fun y : ℝ => (y : ℂ) ^ w) (Set.Ioi 0) := fun w y hy =>
    (Complex.continuousAt_ofReal_cpow_const y w (Or.inr (ne_of_gt hy))).continuousWithinAt
  have hsum : ContinuousOn
      (fun y : ℝ => ∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)) (Set.Ioi 0) := by
    refine continuousOn_finsetSum Finset.univ (fun i _ => ?_)
    exact continuousOn_const.mul (hcp _)
  exact ContinuousOn.div (hsum.norm.pow 2) continuousOn_id (fun y hy => ne_of_gt hy)

lemma HB7DampedIntegrable {A X U' : ℝ} {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (z : ι → ℂ)
    (hApos : 0 < A) (ha0 : ∀ i, A / 2 ≤ a i) (hX : 0 < X) (hU' : 1 ≤ U') (hUX : 2 * U' ≤ X) :
    IntegrableOn (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U')))
        * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y) (Set.Ioi 0) := by
  have hU'pos : 0 < U' := lt_of_lt_of_le zero_lt_one hU'
  have h2a : ∀ i, 0 < 2 * a i := fun i => by
    have h : 0 < A / 2 := by positivity
    linarith [ha0 i]
  set M : ℝ → ℝ := fun y => (Fintype.card ι : ℝ)
      * ∑ i, ‖z i‖ ^ 2 * (Real.exp (-(y / X)) * y ^ (2 * a i - 1)) with hM
  have hMint : Integrable M (volume.restrict (Set.Ioi 0)) := by
    rw [hM]
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum (Finset.univ : Finset ι)
      (f := fun i (y : ℝ) => ‖z i‖ ^ 2 * (Real.exp (-(y / X)) * y ^ (2 * a i - 1))) ?_
    intro i _
    exact (HB7IntegrableExpDivRpow hX (h2a i)).const_mul _
  have hFmeas : AEStronglyMeasurable
      (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U')))
        * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      (volume.restrict (Set.Ioi 0)) := by
    have hw1 : Continuous (fun y : ℝ => Real.exp (-(y / X))) :=
      Real.continuous_exp.comp ((continuous_id.div_const X).neg)
    have hw2 : Continuous (fun y : ℝ => Real.exp (-(y / U'))) :=
      Real.continuous_exp.comp ((continuous_id.div_const U').neg)
    have hwc : Continuous (fun y : ℝ => Real.exp (-(y / X)) - Real.exp (-(y / U'))) := hw1.sub hw2
    have hg := (hwc.continuousOn.mul (HB7_contOn a γ z)).aestronglyMeasurable (μ := volume) measurableSet_Ioi
    have hfun : ((fun y : ℝ => Real.exp (-(y / X)) - Real.exp (-(y / U')))
          * (fun y : ℝ => ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y))
        = (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U')))
            * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y) := by
      funext y
      rw [Pi.mul_apply, mul_div_assoc]
    rw [hfun] at hg
    exact hg
  refine Integrable.mono' hMint hFmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos : 0 < y := hy
  have hUXle : U' ≤ X := le_trans (by linarith) hUX
  have hwle : Real.exp (-(y / X)) - Real.exp (-(y / U')) ≤ Real.exp (-(y / X)) := by
    have : 0 ≤ Real.exp (-(y / U')) := le_of_lt (Real.exp_pos _)
    linarith
  have hwnn : 0 ≤ Real.exp (-(y / X)) - Real.exp (-(y / U')) := by
    have h1 : y / X ≤ y / U' := by
      have h2 : 1 / X ≤ 1 / U' := one_div_le_one_div_of_le hU'pos hUXle
      have h3 : y * (1 / X) ≤ y * (1 / U') := mul_le_mul_of_nonneg_left h2 (le_of_lt hypos)
      calc y / X = y * (1 / X) := by rw [div_eq_mul_inv]; ring
        _ ≤ y * (1 / U') := h3
        _ = y / U' := by rw [div_eq_mul_inv]; ring
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg h1))
  have hS2 : ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, (‖z i‖ * y ^ (a i)) ^ 2 := by
    have hS : ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖
        ≤ ∑ i, ‖z i‖ * y ^ (a i) := by
      calc ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖
          ≤ ∑ i, ‖z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ := norm_sum_le _ _
        _ = ∑ i, ‖z i‖ * y ^ (a i) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [norm_mul, HB7_norm_cpow_class hypos]
    refine (pow_le_pow_left₀ (norm_nonneg _) hS 2).trans ?_
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖z i‖ * y ^ (a i)))
  have hpow : ∀ i, (‖z i‖ * y ^ (a i)) ^ 2 = ‖z i‖ ^ 2 * y ^ (2 * a i) := by
    intro i
    rw [mul_pow]
    congr 1
    rw [sq, ← Real.rpow_add hypos, show a i + a i = 2 * a i by ring]
  have hsum2 : ∑ i, (‖z i‖ * y ^ (a i)) ^ 2 = ∑ i, ‖z i‖ ^ 2 * y ^ (2 * a i) :=
    Finset.sum_congr rfl (fun i _ => hpow i)
  have hsum_eq : ∑ i, ‖z i‖ ^ 2 * y ^ (2 * a i)
      = (∑ i, ‖z i‖ ^ 2 * y ^ (2 * a i - 1)) * y := by
    have key : ∀ i, ‖z i‖ ^ 2 * y ^ (2 * a i) = ‖z i‖ ^ 2 * y ^ (2 * a i - 1) * y := by
      intro i
      have h2 : y ^ (2 * a i - 1) * y = y ^ ((2 * a i - 1) + 1) := by
        rw [Real.rpow_add hypos, Real.rpow_one]
      rw [mul_assoc, h2, show 2 * a i - 1 + 1 = 2 * a i by ring]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => key i)
  have hmain : ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y
      ≤ (Fintype.card ι : ℝ) * ∑ i, ‖z i‖ ^ 2 * y ^ (2 * a i - 1) := by
    refine (div_le_div_of_nonneg_right hS2 (le_of_lt hypos)).trans ?_
    rw [hsum2, hsum_eq, mul_div_assoc, mul_div_cancel_right₀ _ hypos.ne']
  have hfac : ∑ i, ‖z i‖ ^ 2 * (Real.exp (-(y / X)) * y ^ (2 * a i - 1))
      = Real.exp (-(y / X)) * ∑ i, ‖z i‖ ^ 2 * y ^ (2 * a i - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hpoint : (Real.exp (-(y / X)) - Real.exp (-(y / U')))
      * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y ≤ M y := by
    rw [hM, mul_div_assoc]
    calc (Real.exp (-(y / X)) - Real.exp (-(y / U')))
          * (‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
        ≤ Real.exp (-(y / X))
          * ((Fintype.card ι : ℝ) * ∑ i, ‖z i‖ ^ 2 * y ^ (2 * a i - 1)) :=
          mul_le_mul hwle hmain (by positivity) (le_of_lt (Real.exp_pos _))
      _ = (Fintype.card ι : ℝ)
          * ∑ i, ‖z i‖ ^ 2 * (Real.exp (-(y / X)) * y ^ (2 * a i - 1)) := by
          rw [hfac]; ring
  have hFnn : 0 ≤ (Real.exp (-(y / X)) - Real.exp (-(y / U')))
      * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y :=
    div_nonneg (mul_nonneg hwnn (sq_nonneg _)) (le_of_lt hypos)
  rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
  exact hpoint

lemma HB7BlockBound {C : ℝ} (hMVT : MvtMul C)
    {ι : Type*} [Fintype ι] {δ η A : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (hηA : η * A ≤ 1)
    (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A)
    (γ : ι → ℝ) (hsep : ∀ i j, i ≠ j → δ ≤ |γ i - γ j|) (z : ι → ℂ)
    {Y : ℝ} (hY : 0 < Y) :
    (∫ y in Set.Ioc (Y * Real.exp (-η)) Y,
        ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      ≤ 16 * (η + C / δ) * ∑ i, Y ^ (2 * a i) * ‖z i‖ ^ 2 := by
  let c : ι → ℂ := fun i => (a i : ℂ) - (γ i : ℂ) * Complex.I
  let ζ : ι → ℂ := fun i => z i * (Y : ℂ) ^ (c i)
  let g : ℝ → ℝ := fun y => ‖∑ i, z i * (y : ℂ) ^ (c i)‖ ^ 2 / y
  let hh : ℝ → ℝ := fun x => ‖∑ i, ζ i * (x : ℂ) ^ (c i)‖ ^ 2 / x
  have heη : Real.exp (-η) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hle : Y * Real.exp (-η) ≤ Y := mul_le_of_le_one_right hY.le heη
  have hYne : Y ≠ 0 := hY.ne'
  have hcomp : (∫ y in (Y * Real.exp (-η))..Y, g y) = Y * ∫ x in (Real.exp (-η))..1, g (Y * x) := by
    have h1 := intervalIntegral.integral_comp_mul_left (f := g) hYne (a := Real.exp (-η)) (b := 1)
    have h2 : (∫ x in (Real.exp (-η))..1, g (Y * x)) = Y⁻¹ * ∫ x in (Y * Real.exp (-η))..Y, g x := by
      simpa using h1
    rw [h2, ← mul_assoc, mul_inv_cancel₀ hYne, one_mul]
  have hcongr : Set.EqOn (fun x => Y * g (Y * x)) hh (Set.uIcc (Real.exp (-η)) 1) := by
    intro x hx
    have hxge : Real.exp (-η) ≤ x := by rw [Set.uIcc_of_le heη] at hx; exact hx.1
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxge
    have hsum : (∑ i, z i * (((Y * x : ℝ)) : ℂ) ^ (c i))
        = ∑ i, ζ i * (x : ℂ) ^ (c i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      change z i * (((Y * x : ℝ)) : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)
        = (z i * (Y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I))
          * (x : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)
      rw [HB7_ofReal_mul_cpow_class hY.le (le_of_lt hxpos)]
      ring
    change Y * (‖∑ i, z i * (((Y * x : ℝ)) : ℂ) ^ (c i)‖ ^ 2 / (Y * x)) = hh x
    rw [hsum]
    change Y * (‖∑ i, ζ i * (x : ℂ) ^ (c i)‖ ^ 2 / (Y * x))
      = ‖∑ i, ζ i * (x : ℂ) ^ (c i)‖ ^ 2 / x
    have hYx : Y * x ≠ 0 := mul_ne_zero hYne (ne_of_gt hxpos)
    field_simp
  rw [← intervalIntegral.integral_of_le hle]
  rw [hcomp]
  rw [← intervalIntegral.integral_const_mul Y (fun x => g (Y * x))]
  rw [intervalIntegral.integral_congr hcongr]
  have hkey := HB7FreezeInterval hMVT hδ hη hA hηA a ha0 haA γ hsep ζ
  have hnorm : (∑ i, ‖ζ i‖ ^ 2) = ∑ i, Y ^ (2 * a i) * ‖z i‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 : ‖ζ i‖ = ‖z i‖ * Y ^ (a i) := by
      change ‖z i * (Y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ = ‖z i‖ * Y ^ (a i)
      rw [norm_mul, HB7_norm_cpow_class hY]
    have hsq : (Y ^ (a i)) ^ 2 = Y ^ (2 * a i) := by
      rw [sq, ← Real.rpow_add hY, show a i + a i = 2 * a i by ring]
    rw [h1, mul_pow, hsq]
    ring
  calc (∫ x in (Real.exp (-η))..1, hh x) ≤ 16 * (η + C / δ) * ∑ i, ‖ζ i‖ ^ 2 := hkey
    _ = 16 * (η + C / δ) * ∑ i, Y ^ (2 * a i) * ‖z i‖ ^ 2 := by rw [hnorm]

lemma HB7WeightedBlock {C : ℝ} (hMVT : MvtMul C)
    {ι : Type*} [Fintype ι] {δ A X U' : ℝ} (hδ : 0 < δ) (hA : 0 < A) (hX : 0 < X)
    (hU' : 1 ≤ U') (hUX : 2 * U' ≤ X)
    (a : ι → ℝ) (ha0 : ∀ i, A / 2 ≤ a i) (haA : ∀ i, a i ≤ A)
    (γ : ι → ℝ) (hsep : ∀ i j, i ≠ j → δ ≤ |γ i - γ j|) (z : ι → ℂ)
    {Y : ℝ} (hY : 0 < Y) :
    (∫ y in Set.Ioc (Y * Real.exp (-(1 / A))) Y,
        (Real.exp (-(y / X)) - Real.exp (-(y / U')))
          * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      ≤ Real.exp (-((Y * Real.exp (-(1 / A))) / X))
        * (16 * (1 / A + C / δ) * ∑ i, Y ^ (2 * a i) * ‖z i‖ ^ 2) := by
  have hYlpos : 0 < Y * Real.exp (-(1 / A)) := mul_pos hY (Real.exp_pos _)
  have ha0' : ∀ i, 0 ≤ a i := fun i => by
    have h : 0 < A / 2 := by positivity
    linarith [ha0 i]
  have hab : Y * Real.exp (-(1 / A)) ≤ Y :=
    mul_le_of_le_one_right hY.le (Real.exp_le_one_iff.mpr (by have := one_div_pos.mpr hA; linarith))
  have hIocsub : Set.Ioc (Y * Real.exp (-(1 / A))) Y ⊆ Set.Ioi 0 := fun y hy =>
    lt_trans hYlpos hy.1
  have huIccsub : Set.uIcc (Y * Real.exp (-(1 / A))) Y ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le hab]; exact fun _ hy => lt_of_lt_of_le hYlpos hy.1
  have hFint : IntegrableOn (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U')))
        * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y) (Set.Ioi 0) :=
    HB7DampedIntegrable a γ z hA ha0 hX hU' hUX
  have hfi : IntervalIntegrable (fun y : ℝ => (Real.exp (-(y / X)) - Real.exp (-(y / U')))
        * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      volume (Y * Real.exp (-(1 / A))) Y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hFint.mono_set hIocsub)
  have hGcont : ContinuousOn
      (fun y : ℝ => ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      (Set.uIcc (Y * Real.exp (-(1 / A))) Y) := (HB7_contOn a γ z).mono huIccsub
  have hgi : IntervalIntegrable (fun y : ℝ =>
      Real.exp (-((Y * Real.exp (-(1 / A))) / X))
        * (‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y))
      volume (Y * Real.exp (-(1 / A))) Y :=
    (continuousOn_const.mul hGcont).intervalIntegrable
  have hpoint : ∀ y ∈ Set.Icc (Y * Real.exp (-(1 / A))) Y,
      (Real.exp (-(y / X)) - Real.exp (-(y / U')))
        * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y
      ≤ Real.exp (-((Y * Real.exp (-(1 / A))) / X))
        * (‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y) := by
    intro y hy
    have hypos : 0 < y := lt_of_lt_of_le hYlpos hy.1
    have hw : Real.exp (-(y / X)) - Real.exp (-(y / U'))
        ≤ Real.exp (-((Y * Real.exp (-(1 / A))) / X)) := by
      have h1 : Real.exp (-(y / X)) ≤ Real.exp (-((Y * Real.exp (-(1 / A))) / X)) := by
        apply Real.exp_le_exp.mpr
        have h2 : (Y * Real.exp (-(1 / A))) / X ≤ y / X := div_le_div_of_nonneg_right hy.1 hX.le
        linarith
      have h3 : 0 ≤ Real.exp (-(y / U')) := le_of_lt (Real.exp_pos _)
      linarith
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hw (div_nonneg (sq_nonneg _) (le_of_lt hypos))
  have hstep := intervalIntegral.integral_mono_on hab hfi hgi hpoint
  rw [← intervalIntegral.integral_of_le hab]
  refine hstep.trans ?_
  rw [intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
  rw [intervalIntegral.integral_of_le hab]
  exact HB7BlockBound hMVT hδ (le_of_lt (one_div_pos.mpr hA)) hA.le
    (by rw [one_div, inv_mul_cancel₀ hA.ne']) a ha0' haA γ hsep z hY

theorem HB7DampedClassBound {C : ℝ} (hC : 0 < C) (hMVT : Work.ZeroDensity.LogFree.MvtMul C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L A X U' : ℝ), 1 ≤ L → 1 / L ≤ A → A ≤ 1 → 0 < X → 1 ≤ U' → 2 * U' ≤ X →
      ∀ {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (z : ι → ℂ),
        (∀ i, A / 2 ≤ a i) → (∀ i, a i ≤ A) →
        (∀ i j, i ≠ j → 1 / L ≤ |γ i - γ j|) →
        (∫ y in Set.Ioi (0 : ℝ), (Real.exp (-(y / X)) - Real.exp (-(y / U')))
            * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y)
          ≤ K * L * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2 := by
  refine ⟨192 * (1 + C) + 1, by positivity, ?_⟩
  intro L A X U' hL hA1 hA2 hX hU' hUX ι _ a γ z ha0 haA hsep
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hApos : 0 < A := lt_of_lt_of_le (one_div_pos.mpr hLpos) hA1
  have hδpos : 0 < 1 / L := one_div_pos.mpr hLpos
  have hηpos : 0 < 1 / A := one_div_pos.mpr hApos
  have hη1 : 1 ≤ 1 / A := by simpa using (one_div_le_one_div_of_le hApos hA2)
  have ha0' : ∀ i, 0 ≤ a i := fun i => by
    have h : 0 < A / 2 := by positivity
    linarith [ha0 i]
  have h2lo : ∀ i, 1 ≤ 2 * a i * (1 / A) := fun i => by
    rw [show 2 * a i * (1 / A) = (2 * a i) / A by ring, le_div_iff₀ hApos]
    linarith [ha0 i]
  have h2hi : ∀ i, 2 * a i * (1 / A) ≤ 2 := fun i => by
    rw [show 2 * a i * (1 / A) = (2 * a i) / A by ring, div_le_iff₀ hApos]
    linarith [haA i]
  let F : ℝ → ℝ := fun y => (Real.exp (-(y / X)) - Real.exp (-(y / U')))
      * ‖∑ i, z i * (y : ℂ) ^ ((a i : ℂ) - (γ i : ℂ) * Complex.I)‖ ^ 2 / y
  change (∫ y in Set.Ioi (0 : ℝ), F y) ≤ (192 * (1 + C) + 1) * L * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2
  have hFint : IntegrableOn F (Set.Ioi 0) := HB7DampedIntegrable a γ z hApos ha0 hX hU' hUX
  have htile := HB7TilingIoi (f := F) hX hηpos hFint
  have hWsumm : ∀ i, Summable (fun j : ℤ => Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
        * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A)))) :=
    fun i => HB7WeightSeriesSummable hη1 (h2lo i) (h2hi i)
  have hWbound : ∀ i, (∑' j : ℤ, Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
        * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A)))) ≤ 12 :=
    fun i => HB7WeightSeries hη1 (h2lo i) (h2hi i)
  have hb : HasSum (fun j : ℤ => 16 * (1 / A + C / (1 / L)) * ∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2)
        * (Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
            * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A)))))
      (16 * (1 / A + C / (1 / L)) * ∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2)
        * (∑' j : ℤ, Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
            * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A))))) := by
    have hinner : HasSum (fun j : ℤ => ∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2)
          * (Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
              * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A)))))
        (∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2)
          * (∑' j : ℤ, Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
              * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A))))) := by
      refine hasSum_sum (s := Finset.univ) (fun i _ => ?_)
      exact ((hWsumm i).hasSum).mul_left _
    exact hinner.mul_left _
  have hcb : ∀ j : ℤ, (∫ y in Set.Ioc (X * Real.exp (-(((j : ℝ) + 1) * (1 / A))))
        (X * Real.exp (-((j : ℝ) * (1 / A)))), F y)
      ≤ 16 * (1 / A + C / (1 / L)) * ∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2)
        * (Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
            * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A)))) := by
    intro j
    have hYjpos : 0 < X * Real.exp (-((j : ℝ) * (1 / A))) := mul_pos hX (Real.exp_pos _)
    have hset : X * Real.exp (-(((j : ℝ) + 1) * (1 / A)))
        = (X * Real.exp (-((j : ℝ) * (1 / A)))) * Real.exp (-(1 / A)) := by
      rw [show -(((j : ℝ) + 1) * (1 / A)) = -((j : ℝ) * (1 / A)) + -(1 / A) by ring,
        Real.exp_add]
      ring
    have hV : Real.exp (-((X * Real.exp (-(((j : ℝ) + 1) * (1 / A)))) / X))
        = Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A))))) := by
      congr 1
      rw [mul_div_cancel_left₀ _ hX.ne']
    have hYpow : ∀ i, (X * Real.exp (-((j : ℝ) * (1 / A)))) ^ (2 * a i)
        = X ^ (2 * a i) * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A))) := by
      intro i
      rw [Real.mul_rpow hX.le (le_of_lt (Real.exp_pos _)), ← Real.exp_mul]
      congr 1
      ring
    have hblock := HB7WeightedBlock hMVT hδpos hApos hX hU' hUX a ha0 haA γ hsep z (Y := X * Real.exp (-((j : ℝ) * (1 / A)))) hYjpos
    rw [← hset, hV] at hblock
    have hsumY : ∑ i, (X * Real.exp (-((j : ℝ) * (1 / A)))) ^ (2 * a i) * ‖z i‖ ^ 2
        = ∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2) * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A))) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hYpow i]; ring
    have hfac2 : ∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2)
          * (Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
              * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A))))
        = Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
          * ∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2)
              * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    refine hblock.trans (le_of_eq ?_)
    rw [hsumY, hfac2]; ring
  have hle := Summable.tsum_le_tsum hcb htile.summable hb.summable
  rw [htile.tsum_eq, hb.tsum_eq] at hle
  have hbnd2 : ∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2)
        * (∑' j : ℤ, Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
            * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A))))
      ≤ 12 * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2 := by
    rw [show (12 : ℝ) * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2
        = ∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2) * 12 by rw [← Finset.sum_mul]; ring]
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact mul_le_mul_of_nonneg_left (hWbound i) (by positivity)
  have h1A : 1 / A ≤ L := by
    have h := one_div_le_one_div_of_le hδpos hA1
    rwa [one_div_one_div] at h
  have hCL : C / (1 / L) = C * L := by rw [one_div, div_inv_eq_mul]
  have hsumCL : 1 / A + C / (1 / L) ≤ (1 + C) * L := by
    rw [hCL]; nlinarith [h1A]
  have hSumNN : 0 ≤ ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2 := by positivity
  have hfin : 16 * (1 / A + C / (1 / L)) * ∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2)
        * (∑' j : ℤ, Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
            * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A))))
      ≤ (192 * (1 + C) + 1) * L * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2 := by
    have h2 : 16 * (1 / A + C / (1 / L)) * ∑ i, (X ^ (2 * a i) * ‖z i‖ ^ 2)
          * (∑' j : ℤ, Real.exp (-(Real.exp (-(((j : ℝ) + 1) * (1 / A)))))
              * Real.exp (-(2 * (a i) * (j : ℝ) * (1 / A))))
        ≤ 16 * (1 / A + C / (1 / L)) * (12 * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbnd2 (by positivity)
    have h3 : 16 * (1 / A + C / (1 / L)) * (12 * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2)
        = 192 * (1 / A + C / (1 / L)) * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2 := by ring
    rw [h3] at h2
    have h4 : 192 * (1 / A + C / (1 / L)) * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2
        ≤ 192 * (1 + C) * L * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2 := by
      have h : 192 * (1 / A + C / (1 / L)) ≤ 192 * (1 + C) * L := by nlinarith [hsumCL]
      exact mul_le_mul_of_nonneg_right h hSumNN
    have h5 : 192 * (1 + C) * L * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2
        ≤ (192 * (1 + C) + 1) * L * ∑ i, X ^ (2 * a i) * ‖z i‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hSumNN
      nlinarith [hLpos]
    exact h2.trans (h4.trans h5)
  exact hle.trans hfin

end
end Work.ZeroDensity.LogFree
