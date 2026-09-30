import Mathlib
import Submission.Work.BMF.parseval.Defs
import Submission.Work.BMF.mwt_transform_bound
import Submission.Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

open MeasureTheory intervalIntegral
open scoped ComplexConjugate

namespace Work.BMF

noncomputable section

/-! ## Elementary continuity helpers -/

private lemma cont_sq (c : ℝ) : Continuous (fun x : ℝ => 1 + (c - x)^2) := by fun_prop

private lemma cont_sq2 : Continuous (fun p : ℝ × ℝ => 1 + (p.1 - p.2)^2) := by fun_prop

private lemma cont_inv_sq (c : ℝ) : Continuous (fun x : ℝ => (1 + (c - x)^2)⁻¹) :=
  (cont_sq c).inv₀ (fun x => by positivity)

private lemma cont_inv_sq2 : Continuous (fun p : ℝ × ℝ => (1 + (p.1 - p.2)^2)⁻¹) :=
  cont_sq2.inv₀ (fun p => by positivity)

/-- For a nonnegative function the interval integral is nonnegative. -/
private lemma intervalIntegral_nonneg {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab]
  exact MeasureTheory.integral_nonneg hf

/-- Monotonicity of the interval integral for nonnegative functions, requiring only that the
majorant be integrable on the interval of integration. -/
private lemma intervalIntegral_mono_of_nonneg {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, 0 ≤ f x) (h : ∀ x ∈ Set.Icc a b, f x ≤ g x)
    (hg : IntegrableOn g (Set.uIoc a b) volume) :
    (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  refine MeasureTheory.setIntegral_mono_of_nonneg ?_ ?_ (hg.mono_set ?_)
  · intro x hx; exact hf x (Set.Ioc_subset_Icc_self hx)
  · intro x hx; exact h x (Set.Ioc_subset_Icc_self hx)
  · rw [Set.uIoc_of_le hab]


/-- A continuous function is integrable on `uIoc a b`. -/
private lemma integrableOn_of_continuous_uIoc {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    IntegrableOn g (Set.uIoc a b) volume :=
  (ContinuousOn.integrableOn_compact (isCompact_uIcc (a := a) (b := b)) hg.continuousOn).mono_set
    (Set.uIoc_subset_uIcc)

/-- The row-sum bound for the Hilbert kernel `1/(1+s^2)`. -/
private lemma row_integral_le_pi (t lo hi : ℝ) (_hlo : lo ≤ hi) :
    (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹) ≤ Real.pi := by
  have hsub : (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹)
      = ∫ s in lo - t..hi - t, (1 + s^2)⁻¹ := by
    have hfun : (fun t' : ℝ => (1 + (t - t')^2)⁻¹)
        = (fun t' : ℝ => (fun s : ℝ => (1 + s^2)⁻¹) (t' - t)) := by
      funext t'
      simp only []
      rw [show (t - t')^2 = (t' - t)^2 by ring]
    rw [hfun]
    exact intervalIntegral.integral_comp_sub_right (fun s : ℝ => (1 + s^2)⁻¹) t
  rw [hsub, integral_inv_one_add_sq]
  have h1 := Real.arctan_lt_pi_div_two (hi - t)
  have h2 := Real.neg_pi_div_two_lt_arctan (lo - t)
  linarith

/-- **The Hilbert/Schur bound** for the kernel `1/(1+(t-t')^2)`. -/
private theorem whf_hilbert (f : ℝ → ℝ) (hf : Continuous f) (hfn : ∀ t, 0 ≤ f t)
    (lo hi : ℝ) (hlo : lo ≤ hi) :
    (∫ t in lo..hi, ∫ t' in lo..hi, f t * f t' / (1 + (t - t')^2))
      ≤ Real.pi * ∫ t in lo..hi, f t^2 := by
  set S : ℝ := ∫ t in lo..hi, f t^2 with hS
  have hAmgm : ∀ t t' : ℝ, f t * f t' ≤ f t^2/2 + f t'^2/2 := by
    intro t t'; nlinarith [sq_nonneg (f t - f t'), hfn t, hfn t']
  have hpt : ∀ t t' : ℝ,
      f t * f t' / (1 + (t - t')^2) ≤ (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹ := by
    intro t t'
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hAmgm t t') (by positivity)
  have cA : Continuous (Function.uncurry (fun t t' : ℝ => f t * f t' / (1 + (t - t')^2))) := by
    have hun : Function.uncurry (fun t t' : ℝ => f t * f t' / (1 + (t - t')^2))
        = (fun p : ℝ × ℝ => f p.1 * f p.2 / (1 + (p.1 - p.2)^2)) := by funext p; rfl
    rw [hun]
    exact ((hf.comp continuous_fst).mul (hf.comp continuous_snd)).div cont_sq2 (fun p => by positivity)
  have cB : Continuous
      (Function.uncurry (fun t t' : ℝ => (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹)) := by
    have hun : Function.uncurry (fun t t' : ℝ => (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹)
        = (fun p : ℝ × ℝ => (f p.1^2/2 + f p.2^2/2) * (1 + (p.1 - p.2)^2)⁻¹) := by
      funext p; rfl
    rw [hun]
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ => f p.1^2/2 + f p.2^2/2)).mul cont_inv_sq2
  have cA1 : ∀ t : ℝ, Continuous (fun t' : ℝ => f t * f t' / (1 + (t - t')^2)) := fun t =>
    (continuous_const.mul hf).div (cont_sq t) (fun t' => by positivity)
  have cB1 : ∀ t : ℝ, Continuous (fun t' : ℝ => (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹) :=
    fun t => (continuous_const.add ((hf.pow 2).div_const 2)).mul (cont_inv_sq t)
  have Aint : IntervalIntegrable
      (fun t : ℝ => ∫ t' in lo..hi, f t * f t' / (1 + (t - t')^2)) volume lo hi :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' cA lo hi).intervalIntegrable lo hi
  have Bint : IntervalIntegrable
      (fun t : ℝ => ∫ t' in lo..hi, (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹) volume lo hi :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' cB lo hi).intervalIntegrable lo hi
  have hmono : (∫ t in lo..hi, ∫ t' in lo..hi, f t * f t' / (1 + (t - t')^2))
      ≤ (∫ t in lo..hi, ∫ t' in lo..hi, (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹) := by
    refine intervalIntegral.integral_mono_on hlo Aint Bint ?_
    intro t _
    refine intervalIntegral.integral_mono_on hlo ((cA1 t).intervalIntegrable lo hi)
      ((cB1 t).intervalIntegrable lo hi) ?_
    intro t' _; exact hpt t t'
  have hsplit1 : ∀ t : ℝ,
      (∫ t' in lo..hi, (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹)
        = (∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
          + (∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹) := by
    intro t
    trans (∫ t' in lo..hi, (f t^2/2 * (1 + (t - t')^2)⁻¹ + f t'^2/2 * (1 + (t - t')^2)⁻¹))
    · apply intervalIntegral.integral_congr
      intro t' _; ring
    · exact intervalIntegral.integral_add
        ((continuous_const.mul (cont_inv_sq t)).intervalIntegrable lo hi)
        ((((hf.pow 2).div_const 2).mul (cont_inv_sq t)).intervalIntegrable lo hi)
  have cT1 : Continuous (fun t : ℝ => ∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t t' : ℝ => f t^2/2 * (1 + (t - t')^2)⁻¹) (by
        have hun : Function.uncurry (fun t t' : ℝ => f t^2/2 * (1 + (t - t')^2)⁻¹)
            = (fun p : ℝ × ℝ => f p.1^2/2 * (1 + (p.1 - p.2)^2)⁻¹) := by funext p; rfl
        rw [hun]
        exact (((hf.comp continuous_fst).pow 2).div_const 2).mul cont_inv_sq2) lo hi
  have cT2 : Continuous (fun t : ℝ => ∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t t' : ℝ => f t'^2/2 * (1 + (t - t')^2)⁻¹) (by
        have hun : Function.uncurry (fun t t' : ℝ => f t'^2/2 * (1 + (t - t')^2)⁻¹)
            = (fun p : ℝ × ℝ => f p.2^2/2 * (1 + (p.1 - p.2)^2)⁻¹) := by funext p; rfl
        rw [hun]
        exact (((hf.comp continuous_snd).pow 2).div_const 2).mul cont_inv_sq2) lo hi
  have hsplit : (∫ t in lo..hi, ∫ t' in lo..hi, (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹)
      = (∫ t in lo..hi, ∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
        + (∫ t in lo..hi, ∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹) := by
    trans (∫ t in lo..hi, ((∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
        + (∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹)))
    · apply intervalIntegral.integral_congr
      intro t _; exact hsplit1 t
    · exact intervalIntegral.integral_add (cT1.intervalIntegrable lo hi) (cT2.intervalIntegrable lo hi)
  have hT1 : (∫ t in lo..hi, ∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
      ≤ Real.pi/2 * S := by
    rw [hS]
    have hsimp : (∫ t in lo..hi, ∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
        = ∫ t in lo..hi, f t^2/2 * (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro t _
      show (∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
          = f t^2/2 * (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹)
      rw [intervalIntegral.integral_const_mul]
    rw [hsimp]
    have hcont1 : Continuous (fun t : ℝ => f t^2/2 * (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹)) :=
      ((hf.pow 2).div_const 2).mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun t t' : ℝ => (1 + (t - t')^2)⁻¹) (by
            have hun : Function.uncurry (fun t t' : ℝ => (1 + (t - t')^2)⁻¹)
                = (fun p : ℝ × ℝ => (1 + (p.1 - p.2)^2)⁻¹) := by funext p; rfl
            rw [hun]; exact cont_inv_sq2) lo hi)
    calc (∫ t in lo..hi, f t^2/2 * (∫ t' in lo..hi, (1 + (t - t')^2)⁻¹))
        ≤ ∫ t in lo..hi, f t^2/2 * Real.pi := by
          refine intervalIntegral.integral_mono_on hlo (hcont1.intervalIntegrable lo hi)
            ((by fun_prop : Continuous (fun t : ℝ => f t^2/2 * Real.pi)).intervalIntegrable lo hi) ?_
          intro t _
          exact mul_le_mul_of_nonneg_left (row_integral_le_pi t lo hi hlo) (by positivity)
      _ = Real.pi/2 * (∫ t in lo..hi, f t^2) := by
          rw [show (∫ t in lo..hi, f t^2/2 * Real.pi)
              = ∫ t in lo..hi, (Real.pi/2) * f t^2 by
            apply intervalIntegral.integral_congr
            intro t _; ring]
          rw [intervalIntegral.integral_const_mul]
  have hT2 : (∫ t in lo..hi, ∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹)
      ≤ Real.pi/2 * S := by
    rw [hS]
    have cBT : Continuous (Function.uncurry (fun t t' : ℝ => f t'^2/2 * (1 + (t - t')^2)⁻¹)) := by
      have hun : Function.uncurry (fun t t' : ℝ => f t'^2/2 * (1 + (t - t')^2)⁻¹)
          = (fun p : ℝ × ℝ => f p.2^2/2 * (1 + (p.1 - p.2)^2)⁻¹) := by funext p; rfl
      rw [hun]
      exact (((hf.comp continuous_snd).pow 2).div_const 2).mul cont_inv_sq2
    have hswap : (∫ t in lo..hi, ∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹)
        = ∫ t' in lo..hi, ∫ t in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹ := by
      apply MeasureTheory.intervalIntegral_intervalIntegral_swap
      refine (ContinuousOn.integrableOn_compact
        ((isCompact_uIcc (a := lo) (b := hi)).prod (isCompact_uIcc (a := lo) (b := hi)))
        cBT.continuousOn).mono_set ?_
      exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
    rw [hswap]
    have hsimp : (∫ t' in lo..hi, ∫ t in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹)
        = ∫ t' in lo..hi, f t'^2/2 * (∫ t in lo..hi, (1 + (t - t')^2)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro t' _
      show (∫ t in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹)
          = f t'^2/2 * (∫ t in lo..hi, (1 + (t - t')^2)⁻¹)
      rw [intervalIntegral.integral_const_mul]
    rw [hsimp]
    have hcont2 : Continuous (fun t' : ℝ => f t'^2/2 * (∫ t in lo..hi, (1 + (t - t')^2)⁻¹)) :=
      ((hf.pow 2).div_const 2).mul
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun t' t : ℝ => (1 + (t - t')^2)⁻¹) (by
            have hun : Function.uncurry (fun t' t : ℝ => (1 + (t - t')^2)⁻¹)
                = (fun p : ℝ × ℝ => (1 + (p.2 - p.1)^2)⁻¹) := by funext p; rfl
            rw [hun]
            exact ((by fun_prop : Continuous (fun p : ℝ × ℝ => 1 + (p.2 - p.1)^2))).inv₀
              (fun p => by positivity)) lo hi)
    calc (∫ t' in lo..hi, f t'^2/2 * (∫ t in lo..hi, (1 + (t - t')^2)⁻¹))
        ≤ ∫ t' in lo..hi, f t'^2/2 * Real.pi := by
          refine intervalIntegral.integral_mono_on hlo (hcont2.intervalIntegrable lo hi)
            ((by fun_prop : Continuous (fun t' : ℝ => f t'^2/2 * Real.pi)).intervalIntegrable lo hi) ?_
          intro t' _
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hcongr : (∫ t in lo..hi, (1 + (t - t')^2)⁻¹)
              = ∫ t in lo..hi, (1 + (t' - t)^2)⁻¹ := by
            apply intervalIntegral.integral_congr
            intro t _
            simp only []
            rw [show (t - t')^2 = (t' - t)^2 by ring]
          rw [hcongr]
          exact row_integral_le_pi t' lo hi hlo
      _ = Real.pi/2 * (∫ t in lo..hi, f t^2) := by
          rw [show (∫ t' in lo..hi, f t'^2/2 * Real.pi)
              = ∫ t' in lo..hi, (Real.pi/2) * f t'^2 by
            apply intervalIntegral.integral_congr
            intro t' _; ring]
          rw [intervalIntegral.integral_const_mul]
  calc (∫ t in lo..hi, ∫ t' in lo..hi, f t * f t' / (1 + (t - t')^2))
      ≤ (∫ t in lo..hi, ∫ t' in lo..hi, (f t^2/2 + f t'^2/2) * (1 + (t - t')^2)⁻¹) := hmono
    _ = (∫ t in lo..hi, ∫ t' in lo..hi, f t^2/2 * (1 + (t - t')^2)⁻¹)
        + (∫ t in lo..hi, ∫ t' in lo..hi, f t'^2/2 * (1 + (t - t')^2)⁻¹) := hsplit
    _ ≤ Real.pi/2 * S + Real.pi/2 * S := add_le_add hT1 hT2
    _ = Real.pi * S := by ring

/-! ## The double-integral expansion of the frozen quadratic form -/

private lemma intervalIntegral_conj (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    (starRingEnd ℂ) (∫ x in a..b, f x) = ∫ x in a..b, (starRingEnd ℂ) (f x) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact (integral_conj (μ := volume.restrict (Set.Ioc a b)) (f := f)).symm

private lemma integral_mul_integral (g h : ℝ → ℂ) (lo hi : ℝ) :
    (∫ t in lo..hi, g t) * (∫ t in lo..hi, h t)
      = ∫ t in lo..hi, ∫ t' in lo..hi, g t * h t' := by
  rw [← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro t _
  exact (intervalIntegral.integral_const_mul (g t) h).symm

private lemma cpow_four_add_I (x Δ : ℝ) (hx : 0 < x) :
    (x:ℂ)^(4 + Complex.I*(Δ:ℂ))
      = (x:ℂ)^4 * Complex.exp ((Complex.I*(Δ:ℂ)) * ((Real.log x : ℝ):ℂ)) := by
  have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h1 : (x:ℂ)^(4 + Complex.I*(Δ:ℂ))
      = (x:ℂ)^(4:ℂ) * (x:ℂ)^(Complex.I*(Δ:ℂ)) :=
    Complex.cpow_add (4:ℂ) (Complex.I*(Δ:ℂ)) hxne
  have h2 : (x:ℂ)^(4:ℂ) = (x:ℂ)^4 := Complex.cpow_natCast (x:ℂ) 4
  have h3 : (x:ℂ)^(Complex.I*(Δ:ℂ))
      = Complex.exp ((Complex.I*(Δ:ℂ)) * ((Real.log x : ℝ):ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hxne, Complex.ofReal_log hx.le]
    congr 1
    ring
  rw [h1, h2, h3]

/-- A globally continuous model for `mwt X` (agreement on `[X e^{-1}, ∞)`). -/
private def mwtG (X x : ℝ) : ℝ :=
  kappa (Real.log (max x (X * Real.exp (-1))) - Real.log X + 1)

private lemma continuous_log_max (c : ℝ) (hc : 0 < c) :
    Continuous (fun x : ℝ => Real.log (max x c)) := by
  have h1 : Continuous (fun x : ℝ => max x c) := by fun_prop
  exact Real.continuousOn_log.comp_continuous h1 (fun x => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (lt_of_lt_of_le hc (le_max_right x c)))

private lemma continuous_mwtG (X : ℝ) (hX : 0 < X) : Continuous (mwtG X) := by
  have hc : 0 < X * Real.exp (-1) := by positivity
  have h2 : Continuous (fun x : ℝ => Real.log (max x (X * Real.exp (-1)))) :=
    continuous_log_max _ hc
  unfold mwtG
  exact continuous_kappa_glue.comp ((h2.sub continuous_const).add continuous_const)

private lemma mwtG_eq_mwt (X x : ℝ) (hX : 0 < X) (hx : X * Real.exp (-1) ≤ x) :
    mwtG X x = mwt X x := by
  have hxc : max x (X * Real.exp (-1)) = x := max_eq_left hx
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity : 0 < X * Real.exp (-1)) hx
  unfold mwtG mwt
  rw [hxc, Real.log_div hxpos.ne' hX.ne']

/-- A globally continuous model for the Mellin kernel `x^{4+iΔ}` (agreement on `[X e^{-1}, ∞)`). -/
private def Kpow (X x Δ : ℝ) : ℂ :=
  (x:ℂ)^4 * Complex.exp ((Complex.I*(Δ:ℂ)) * ((Real.log (max x (X * Real.exp (-1))) : ℝ):ℂ))

private lemma continuous_Kpow (X : ℝ) (hX : 0 < X) :
    Continuous (fun p : ℝ × ℝ => Kpow X p.1 p.2) := by
  have hc : 0 < X * Real.exp (-1) := by positivity
  have hlog : Continuous (fun p : ℝ × ℝ => Real.log (max p.1 (X * Real.exp (-1)))) :=
    (continuous_log_max _ hc).comp continuous_fst
  unfold Kpow
  apply Continuous.mul
  · exact (Complex.continuous_ofReal.comp continuous_fst).pow 4
  · apply Complex.continuous_exp.comp
    apply Continuous.mul
    · exact continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)
    · exact Complex.continuous_ofReal.comp hlog

private lemma Kpow_eq_cpow (X x Δ : ℝ) (hX : 0 < X) (hx : X * Real.exp (-1) ≤ x) :
    Kpow X x Δ = (x:ℂ)^(4 + Complex.I*(Δ:ℂ)) := by
  have hxc : max x (X * Real.exp (-1)) = x := max_eq_left hx
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity : 0 < X * Real.exp (-1)) hx
  unfold Kpow
  rw [hxc, cpow_four_add_I x Δ hxpos]

private lemma Kpow_eq_cpow' (X x t t' : ℝ) (hX : 0 < X) (hx : X * Real.exp (-1) ≤ x) :
    Kpow X x (t - t') = (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ))) := by
  rw [Kpow_eq_cpow X x (t - t') hX hx]
  congr 1
  push_cast
  ring

private lemma conj_cpow_two (x t : ℝ) (hx : 0 ≤ x) :
    (starRingEnd ℂ) ((x:ℂ)^(2 + Complex.I*(t:ℂ))) = (x:ℂ)^(2 - Complex.I*(t:ℂ)) := by
  rw [Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg hx]
  congr 1
  have htwo : (2:ℂ) = (((2:ℝ)) : ℂ) := by norm_num
  rw [show (starRingEnd ℂ) (2 + Complex.I*(t:ℂ)) = (starRingEnd ℂ) (((2:ℝ):ℂ) + Complex.I*(t:ℂ)) by
    rw [htwo]]
  rw [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast
  ring

/-- **The double-integral expansion.**  The weighted quadratic form of the frozen frequency
integral equals the double integral with kernel the Mellin transform of `mwt`. -/
private lemma whf_expand_eq (a : ℝ → ℂ) (ha : Continuous a) (X lo hi : ℝ) (hX : 0 < X)
    (hlo : lo ≤ hi) :
    ((∫ x in X * Real.exp (-1)..X * Real.exp 3,
        (mwt X x) * ‖∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2 : ℝ) : ℂ)
      = ∫ t in lo..hi, ∫ t' in lo..hi, (a t * (starRingEnd ℂ) (a t')) *
          (∫ x in X * Real.exp (-1)..X * Real.exp 3,
            ((mwt X x : ℝ) : ℂ) * (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ)))) := by
  have hIle : X * Real.exp (-1) ≤ X * Real.exp 3 :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) hX.le
  -- Step A: cast the real integral and expand `‖F‖² = F * conj F`
  have hA1 : ((∫ x in X * Real.exp (-1)..X * Real.exp 3,
        (mwt X x) * ‖∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2 : ℝ) : ℂ)
      = ∫ x in X * Real.exp (-1)..X * Real.exp 3, ((mwt X x : ℝ) : ℂ) *
          ((∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))) *
            (starRingEnd ℂ) (∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ)))) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _
    simp only []
    rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  -- Step B: the pointwise expansion at a single `x ∈ [X e^{-1}, X e^{3}]`
  have step2 : ∀ x : ℝ, X * Real.exp (-1) ≤ x →
      (∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))) *
        (starRingEnd ℂ) (∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ)))
      = ∫ t in lo..hi, ∫ t' in lo..hi,
          (a t * (starRingEnd ℂ) (a t')) * Kpow X x (t - t') := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (by positivity : 0 < X * Real.exp (-1)) hx
    rw [intervalIntegral_conj (f := fun t => a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))) hlo]
    rw [integral_mul_integral]
    apply intervalIntegral.integral_congr
    intro t _
    apply intervalIntegral.integral_congr
    intro t' _
    simp only []
    rw [map_mul, conj_cpow_two x t' hxpos.le]
    have hkey : (x:ℂ)^(2 + Complex.I*(t:ℂ)) * (x:ℂ)^(2 - Complex.I*(t':ℂ)) = Kpow X x (t - t') := by
      rw [Kpow_eq_cpow X x (t - t') hX hx]
      rw [← Complex.cpow_add (2 + Complex.I*(t:ℂ)) (2 - Complex.I*(t':ℂ))
        (Complex.ofReal_ne_zero.mpr hxpos.ne')]
      congr 1
      push_cast
      ring
    calc a t * (x:ℂ)^(2 + Complex.I*(t:ℂ)) *
            ((starRingEnd ℂ) (a t') * (x:ℂ)^(2 - Complex.I*(t':ℂ)))
        = a t * (starRingEnd ℂ) (a t') *
            ((x:ℂ)^(2 + Complex.I*(t:ℂ)) * (x:ℂ)^(2 - Complex.I*(t':ℂ))) := by ring
      _ = a t * (starRingEnd ℂ) (a t') * Kpow X x (t - t') := by rw [hkey]
  -- Step C: substitute the expansion, push `mwt` inside, replace it by `mwtG`
  have hC1 : (∫ x in X * Real.exp (-1)..X * Real.exp 3, ((mwt X x : ℝ) : ℂ) *
          ((∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))) *
            (starRingEnd ℂ) (∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ)))))
      = ∫ x in X * Real.exp (-1)..X * Real.exp 3, ∫ t in lo..hi, ∫ t' in lo..hi,
          ((mwtG X x : ℝ) : ℂ) *
            ((a t * (starRingEnd ℂ) (a t')) * Kpow X x (t - t')) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hIle] at hx
    simp only []
    rw [step2 x hx.1, mwtG_eq_mwt X x hX hx.1]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [← intervalIntegral.integral_const_mul]
  -- Step D: Fubini swap of `x` and `t`
  have hGc : Continuous (Function.uncurry (fun p : ℝ × ℝ => fun t' : ℝ =>
      ((mwtG X p.1 : ℝ) : ℂ) * ((a p.2 * (starRingEnd ℂ) (a t')) * Kpow X p.1 (p.2 - t')))) := by
    have hun : Function.uncurry (fun p : ℝ × ℝ => fun t' : ℝ =>
        ((mwtG X p.1 : ℝ) : ℂ) * ((a p.2 * (starRingEnd ℂ) (a t')) * Kpow X p.1 (p.2 - t')))
        = (fun q : (ℝ × ℝ) × ℝ => ((mwtG X q.1.1 : ℝ) : ℂ) *
            ((a q.1.2 * (starRingEnd ℂ) (a q.2)) * Kpow X q.1.1 (q.1.2 - q.2))) := by
      funext q; rfl
    rw [hun]
    have hm1 : Continuous (fun q : (ℝ × ℝ) × ℝ => ((mwtG X q.1.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((continuous_mwtG X hX).comp (continuous_fst.comp continuous_fst))
    have hm2 : Continuous (fun q : (ℝ × ℝ) × ℝ => a q.1.2 * (starRingEnd ℂ) (a q.2)) := by
      have h1 : Continuous (fun q : (ℝ × ℝ) × ℝ => a q.1.2) :=
        ha.comp (continuous_snd.comp continuous_fst)
      have h2 : Continuous (fun q : (ℝ × ℝ) × ℝ => (starRingEnd ℂ) (a q.2)) :=
        Complex.continuous_conj.comp (ha.comp continuous_snd)
      exact h1.mul h2
    have hm3 : Continuous (fun q : (ℝ × ℝ) × ℝ => Kpow X q.1.1 (q.1.2 - q.2)) := by
      have hsub : Continuous (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2 - q.2)) := by fun_prop
      exact (continuous_Kpow X hX).comp hsub
    exact hm1.mul (hm2.mul hm3)
  have hD1 : (∫ x in X * Real.exp (-1)..X * Real.exp 3, ∫ t in lo..hi, ∫ t' in lo..hi,
          ((mwtG X x : ℝ) : ℂ) *
            ((a t * (starRingEnd ℂ) (a t')) * Kpow X x (t - t')))
      = ∫ t in lo..hi, ∫ x in X * Real.exp (-1)..X * Real.exp 3, ∫ t' in lo..hi,
          ((mwtG X x : ℝ) : ℂ) *
            ((a t * (starRingEnd ℂ) (a t')) * Kpow X x (t - t')) := by
    apply MeasureTheory.intervalIntegral_intervalIntegral_swap
    refine (ContinuousOn.integrableOn_compact
      ((isCompact_uIcc (a := X * Real.exp (-1)) (b := X * Real.exp 3)).prod
        (isCompact_uIcc (a := lo) (b := hi))) ?_).mono_set ?_
    · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun p : ℝ × ℝ => fun t' : ℝ =>
          ((mwtG X p.1 : ℝ) : ℂ) * ((a p.2 * (starRingEnd ℂ) (a t')) * Kpow X p.1 (p.2 - t')))
        hGc lo hi).continuousOn
    · exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
  -- Step E: swap `x` and `t'`, then pull the coefficients out
  have hE1 : (∫ t in lo..hi, ∫ x in X * Real.exp (-1)..X * Real.exp 3, ∫ t' in lo..hi,
          ((mwtG X x : ℝ) : ℂ) *
            ((a t * (starRingEnd ℂ) (a t')) * Kpow X x (t - t')))
      = ∫ t in lo..hi, ∫ t' in lo..hi, (a t * (starRingEnd ℂ) (a t')) *
          (∫ x in X * Real.exp (-1)..X * Real.exp 3,
            ((mwtG X x : ℝ) : ℂ) * Kpow X x (t - t')) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    have hswap : (∫ x in X * Real.exp (-1)..X * Real.exp 3, ∫ t' in lo..hi,
          ((mwtG X x : ℝ) : ℂ) * ((a t * (starRingEnd ℂ) (a t')) * Kpow X x (t - t')))
        = ∫ t' in lo..hi, ∫ x in X * Real.exp (-1)..X * Real.exp 3,
          ((mwtG X x : ℝ) : ℂ) * ((a t * (starRingEnd ℂ) (a t')) * Kpow X x (t - t')) := by
      apply MeasureTheory.intervalIntegral_intervalIntegral_swap
      refine (ContinuousOn.integrableOn_compact
        ((isCompact_uIcc (a := X * Real.exp (-1)) (b := X * Real.exp 3)).prod
          (isCompact_uIcc (a := lo) (b := hi))) ?_).mono_set ?_
      · exact (by
          have hc : Continuous (fun p : ℝ × ℝ =>
              ((mwtG X p.1 : ℝ) : ℂ) *
                ((a t * (starRingEnd ℂ) (a p.2)) * Kpow X p.1 (t - p.2))) := by
            have h1 : Continuous (fun p : ℝ × ℝ => ((mwtG X p.1 : ℝ) : ℂ)) :=
              Complex.continuous_ofReal.comp ((continuous_mwtG X hX).comp continuous_fst)
            have h2 : Continuous (fun p : ℝ × ℝ => a t * (starRingEnd ℂ) (a p.2)) :=
              continuous_const.mul (Complex.continuous_conj.comp (ha.comp continuous_snd))
            have h3 : Continuous (fun p : ℝ × ℝ => Kpow X p.1 (t - p.2)) := by
              have hsub : Continuous (fun p : ℝ × ℝ => (p.1, t - p.2)) := by fun_prop
              exact (continuous_Kpow X hX).comp hsub
            exact h1.mul (h2.mul h3)
          exact hc.continuousOn)
      · exact Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc
    rw [hswap]
    apply intervalIntegral.integral_congr
    intro t' _
    simp only []
    rw [show (∫ x in X * Real.exp (-1)..X * Real.exp 3,
            ((mwtG X x : ℝ) : ℂ) * ((a t * (starRingEnd ℂ) (a t')) * Kpow X x (t - t')))
        = ∫ x in X * Real.exp (-1)..X * Real.exp 3, (a t * (starRingEnd ℂ) (a t')) *
            (((mwtG X x : ℝ) : ℂ) * Kpow X x (t - t')) by
      apply intervalIntegral.integral_congr
      intro x _; ring]
    rw [intervalIntegral.integral_const_mul]
  -- Step F: replace the continuous models by the original expressions
  have hF1 : (∫ t in lo..hi, ∫ t' in lo..hi, (a t * (starRingEnd ℂ) (a t')) *
          (∫ x in X * Real.exp (-1)..X * Real.exp 3,
            ((mwtG X x : ℝ) : ℂ) * Kpow X x (t - t')))
      = ∫ t in lo..hi, ∫ t' in lo..hi, (a t * (starRingEnd ℂ) (a t')) *
          (∫ x in X * Real.exp (-1)..X * Real.exp 3,
            ((mwt X x : ℝ) : ℂ) * (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ)))) := by
    apply intervalIntegral.integral_congr
    intro t _
    apply intervalIntegral.integral_congr
    intro t' _
    simp only []
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hIle] at hx
    simp only []
    rw [mwtG_eq_mwt X x hX hx.1, Kpow_eq_cpow' X x t t' hX hx.1]
  calc ((∫ x in X * Real.exp (-1)..X * Real.exp 3,
        (mwt X x) * ‖∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2 : ℝ) : ℂ)
      = _ := hA1
    _ = _ := hC1
    _ = _ := hD1
    _ = _ := hE1
    _ = _ := hF1

/-- **The frozen `L²` bound with the kernel constant supplied by a hypothesis.**
This is `whf_frozen_bound` with the constant of `mwt_transform_bound` replaced by an
arbitrary `C0 > 0` for which the Mellin transform bound is assumed. -/
private theorem frozen_l2_aux (a : ℝ → ℂ) (ha : Continuous a) (X lo hi C0 : ℝ)
    (hC0 : 0 < C0) (hX : 1 ≤ X) (hlo : lo ≤ hi)
    (htrans : ∀ Δ : ℝ, ‖∫ x in X * Real.exp (-1)..X * Real.exp 3,
        (mwt X x : ℂ) * (x:ℂ)^(4 + Complex.I*(Δ:ℂ))‖ ≤ C0 * X^5/(1+Δ^2)) :
    (1/X) * (∫ x in X * Real.exp (-1)..X * Real.exp 3, (Work.BMF.mwt X x) *
        ‖∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
      ≤ C0 * Real.pi * X^4 * (∫ t in lo..hi, ‖a t‖^2) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hXne : X ≠ 0 := hXpos.ne'
  have hIle : X * Real.exp (-1) ≤ X * Real.exp 3 :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) hXpos.le
  set M : ℝ := C0 * X^5 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hexp := whf_expand_eq a ha X lo hi hXpos hlo
  -- the kernel bound
  have hker : ∀ t t' : ℝ, ‖∫ x in X * Real.exp (-1)..X * Real.exp 3,
      ((mwt X x : ℝ) : ℂ) * (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ)))‖ ≤ M / (1 + (t - t')^2) := by
    intro t t'
    rw [show ((t:ℂ) - (t':ℂ)) = (((t - t'):ℝ):ℂ) by push_cast; ring]
    rw [hM]
    exact htrans (t - t')
  -- Step 1: the real integral is the norm of the double integral
  have hnn : 0 ≤ ∫ x in X * Real.exp (-1)..X * Real.exp 3, (mwt X x) *
      ‖∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2 := by
    apply intervalIntegral_nonneg hIle
    intro x
    exact mul_nonneg (mwt_nonneg X x) (sq_nonneg _)
  have hnorm : ∀ r : ℝ, 0 ≤ r → ‖(r : ℂ)‖ = r := by
    intro r hr
    have hsq : ‖(r:ℂ)‖ ^ 2 = r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg ((r:ℂ)), hsq, hr]
  have hstep1 : (∫ x in X * Real.exp (-1)..X * Real.exp 3, (mwt X x) *
        ‖∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
      = ‖∫ t in lo..hi, ∫ t' in lo..hi, (a t * (starRingEnd ℂ) (a t')) *
          (∫ x in X * Real.exp (-1)..X * Real.exp 3,
            ((mwt X x : ℝ) : ℂ) * (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ))))‖ := by
    rw [← hexp]
    exact (hnorm _ hnn).symm
  -- Step 2: triangle inequality and the pointwise kernel bound
  have hstep2 : ‖∫ t in lo..hi, ∫ t' in lo..hi, (a t * (starRingEnd ℂ) (a t')) *
          (∫ x in X * Real.exp (-1)..X * Real.exp 3,
            ((mwt X x : ℝ) : ℂ) * (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ))))‖
      ≤ ∫ t in lo..hi, ∫ t' in lo..hi, ‖a t‖ * ‖a t'‖ * (M / (1 + (t - t')^2)) := by
    have hgc : Continuous (fun t : ℝ => ∫ t' in lo..hi,
        ‖a t‖ * ‖a t'‖ * (M / (1 + (t - t')^2))) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun t t' : ℝ => ‖a t‖ * ‖a t'‖ * (M / (1 + (t - t')^2))) (by
          have hun : Function.uncurry (fun t t' : ℝ => ‖a t‖ * ‖a t'‖ * (M / (1 + (t - t')^2)))
              = (fun p : ℝ × ℝ => ‖a p.1‖ * ‖a p.2‖ * (M / (1 + (p.1 - p.2)^2))) := by
            funext p; rfl
          rw [hun]
          apply Continuous.mul
          · exact (ha.norm.comp continuous_fst).mul (ha.norm.comp continuous_snd)
          · exact continuous_const.div cont_sq2 (fun p => by positivity)) lo hi
    calc ‖∫ t in lo..hi, ∫ t' in lo..hi, (a t * (starRingEnd ℂ) (a t')) *
            (∫ x in X * Real.exp (-1)..X * Real.exp 3,
              ((mwt X x : ℝ) : ℂ) * (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ))))‖
        ≤ ∫ t in lo..hi, ‖∫ t' in lo..hi, (a t * (starRingEnd ℂ) (a t')) *
            (∫ x in X * Real.exp (-1)..X * Real.exp 3,
              ((mwt X x : ℝ) : ℂ) * (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ))))‖ :=
          intervalIntegral.norm_integral_le_integral_norm hlo
      _ ≤ ∫ t in lo..hi, ∫ t' in lo..hi, ‖a t‖ * ‖a t'‖ * (M / (1 + (t - t')^2)) := by
          refine intervalIntegral_mono_of_nonneg hlo (fun t _ => norm_nonneg _) ?_
            (integrableOn_of_continuous_uIoc hgc lo hi)
          intro t _
          calc ‖∫ t' in lo..hi, (a t * (starRingEnd ℂ) (a t')) *
                (∫ x in X * Real.exp (-1)..X * Real.exp 3,
                  ((mwt X x : ℝ) : ℂ) * (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ))))‖
              ≤ ∫ t' in lo..hi, ‖(a t * (starRingEnd ℂ) (a t')) *
                  (∫ x in X * Real.exp (-1)..X * Real.exp 3,
                    ((mwt X x : ℝ) : ℂ) * (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ))))‖ :=
                intervalIntegral.norm_integral_le_integral_norm hlo
            _ = ∫ t' in lo..hi, ‖a t‖ * ‖a t'‖ *
                  ‖∫ x in X * Real.exp (-1)..X * Real.exp 3,
                    ((mwt X x : ℝ) : ℂ) * (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ)))‖ := by
                apply intervalIntegral.integral_congr
                intro t' _
                simp only []
                rw [norm_mul, norm_mul, Complex.norm_conj]
            _ ≤ ∫ t' in lo..hi, ‖a t‖ * ‖a t'‖ * (M / (1 + (t - t')^2)) := by
                refine intervalIntegral_mono_of_nonneg hlo (fun t' _ => by positivity) ?_
                  (integrableOn_of_continuous_uIoc ((continuous_const.mul ha.norm).mul
                    (continuous_const.div (cont_sq t) (fun t' => by positivity))) lo hi)
                intro t' _
                exact mul_le_mul_of_nonneg_left (hker t t') (by positivity)
  -- Step 3: pull out the constants and apply the Hilbert bound
  have hstep3 : (∫ t in lo..hi, ∫ t' in lo..hi, ‖a t‖ * ‖a t'‖ * (M / (1 + (t - t')^2)))
      ≤ M * Real.pi * (∫ t in lo..hi, ‖a t‖^2) := by
    have h1 : (∫ t in lo..hi, ∫ t' in lo..hi, ‖a t‖ * ‖a t'‖ * (M / (1 + (t - t')^2)))
        = M * (∫ t in lo..hi, ∫ t' in lo..hi, ‖a t‖ * ‖a t'‖ / (1 + (t - t')^2)) := by
      rw [show (∫ t in lo..hi, ∫ t' in lo..hi, ‖a t‖ * ‖a t'‖ * (M / (1 + (t - t')^2)))
          = ∫ t in lo..hi, M * (∫ t' in lo..hi, ‖a t‖ * ‖a t'‖ / (1 + (t - t')^2)) by
        apply intervalIntegral.integral_congr
        intro t _
        simp only []
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t' _
        simp only []
        ring]
      rw [intervalIntegral.integral_const_mul]
    rw [h1]
    have hh := whf_hilbert (fun t => ‖a t‖) ha.norm (fun t => norm_nonneg _) lo hi hlo
    calc M * (∫ t in lo..hi, ∫ t' in lo..hi, ‖a t‖ * ‖a t'‖ / (1 + (t - t')^2))
        ≤ M * (Real.pi * ∫ t in lo..hi, ‖a t‖^2) := mul_le_mul_of_nonneg_left hh hMpos.le
      _ = M * Real.pi * (∫ t in lo..hi, ‖a t‖^2) := by ring
  calc (1/X) * (∫ x in X * Real.exp (-1)..X * Real.exp 3, (mwt X x) *
        ‖∫ t in lo..hi, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
      = (1/X) * ‖∫ t in lo..hi, ∫ t' in lo..hi, (a t * (starRingEnd ℂ) (a t')) *
          (∫ x in X * Real.exp (-1)..X * Real.exp 3,
            ((mwt X x : ℝ) : ℂ) * (x:ℂ)^(4 + Complex.I*((t:ℂ) - (t':ℂ))))‖ := by rw [hstep1]
    _ ≤ (1/X) * (∫ t in lo..hi, ∫ t' in lo..hi, ‖a t‖ * ‖a t'‖ * (M / (1 + (t - t')^2))) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ ≤ (1/X) * (M * Real.pi * (∫ t in lo..hi, ‖a t‖^2)) :=
        mul_le_mul_of_nonneg_left hstep3 (by positivity)
    _ = C0 * Real.pi * X^4 * (∫ t in lo..hi, ‖a t‖^2) := by
        rw [hM]
        have hpow : (1/X) * X^5 = X^4 := by
          rw [one_div, inv_mul_eq_div, div_eq_iff hXne]
          ring
        rw [show (1/X) * ((C0 * X^5) * Real.pi * (∫ t in lo..hi, ‖a t‖^2))
            = C0 * Real.pi * ((1/X) * X^5) * (∫ t in lo..hi, ‖a t‖^2) by ring]
        rw [hpow]
/-- The required lemma: the frozen `L²` bound for an arbitrary admissible constant `C0`. -/
theorem frozen_l2_bound_proof (X L : ℝ) (C0 : ℝ) (hC0 : 0 < C0) (hX : 1 ≤ X) (hL : 0 ≤ L)
    (htrans : ∀ Δ : ℝ, ‖∫ x in X * Real.exp (-1)..X * Real.exp 3,
        (mwt X x : ℂ) * (x:ℂ)^(4 + Complex.I*(Δ:ℂ))‖ ≤ C0 * X^5/(1+Δ^2))
    (a : ℝ → ℂ) (ha : Continuous a) :
    (1/X) * (∫ x in X * Real.exp (-1)..X * Real.exp 3,
        mwt X x * ‖∫ t in (-L)..L, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
      ≤ C0 * Real.pi * X^4 * (∫ t in (-L)..L, ‖a t‖^2) :=
  frozen_l2_aux a ha X (-L) L C0 hC0 hX (by linarith) htrans

end

end Work.BMF
