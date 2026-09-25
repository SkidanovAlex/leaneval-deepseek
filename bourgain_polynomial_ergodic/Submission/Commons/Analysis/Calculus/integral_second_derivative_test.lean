import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.monotone_weight_integral_bound

open MeasureTheory intervalIntegral
open scoped Real Topology

namespace Commons.Analysis.Calculus

set_option autoImplicit false

/-! ## Interior regularity from `ContDiffOn ℝ 2` on a closed interval -/

lemma hasDerivAt_of_contDiffOn_Icc {u v x : ℝ} {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc u v)) (hx : x ∈ Set.Ioo u v) :
    HasDerivAt φ (deriv φ x) x := by
  have hnh : Set.Icc u v ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  exact ((hφ.contDiffAt hnh).differentiableAt (by norm_num)).hasDerivAt

lemma hasDerivAt_deriv_of_contDiffOn_Icc {u v x : ℝ} {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc u v)) (hx : x ∈ Set.Ioo u v) :
    HasDerivAt (deriv φ) (deriv (deriv φ) x) x := by
  have hnh : Set.Icc u v ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  have hca : ContDiffAt ℝ 2 φ x := hφ.contDiffAt hnh
  have hc1 : ContDiffAt ℝ 1 (deriv φ) x :=
    hca.derivWithin (by norm_num : ((1 : WithTop ℕ∞) + 1) ≤ 2)
  exact (hc1.differentiableAt (by norm_num)).hasDerivAt

/-! ## Core one-sided estimate -/

/-- Growth of `deriv φ` on an open interval from a lower bound on the second derivative. -/
lemma deriv_sub_ge_of_second_deriv_ge {u v : ℝ} {φ : ℝ → ℝ} {lam : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc u v))
    (h2 : ∀ x ∈ Set.Ioo u v, lam ≤ deriv (deriv φ) x) :
    ∀ x ∈ Set.Ioo u v, ∀ y ∈ Set.Ioo u v, x ≤ y → lam * (y - x) ≤ deriv φ y - deriv φ x := by
  intro x hx y hy hxy
  have hsub : Set.Icc x y ⊆ Set.Ioo u v := by
    intro t ht; exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  have hderiv : ∀ t ∈ Set.uIcc x y, HasDerivAt (deriv φ) (deriv (deriv φ) t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc x y := by rwa [Set.uIcc_of_le hxy] at ht
    exact hasDerivAt_deriv_of_contDiffOn_Icc hφ (hsub ht')
  have hcont : IntervalIntegrable (fun t => deriv (deriv φ) t) volume x y := by
    refine ContinuousOn.intervalIntegrable ?_
    intro t ht
    have ht' : t ∈ Set.Icc x y := by rwa [Set.uIcc_of_le hxy] at ht
    have hx' : t ∈ Set.Ioo u v := hsub ht'
    have hnh : Set.Icc u v ∈ 𝓝 t := Icc_mem_nhds hx'.1 hx'.2
    exact (((hφ.contDiffAt hnh).derivWithin (m := 1) (by norm_num)).derivWithin (m := 0)
      (by norm_num)).continuousAt.continuousWithinAt
  have hFTC : ∫ t in x..y, deriv (deriv φ) t = deriv φ y - deriv φ x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  rw [← hFTC]
  have hconst : (∫ t in x..y, (lam : ℝ)) = lam * (y - x) := by
    rw [intervalIntegral.integral_const]; simp [smul_eq_mul, mul_comm]
  rw [← hconst]
  refine integral_mono_on hxy ((continuous_const).intervalIntegrable _ _) hcont (fun t ht => ?_)
  exact h2 t (hsub ht)


/-- **One-sided second derivative estimate (core).**  If `φ` is `C²` at every point of `[a,b]`,
with `deriv φ > 0` and `deriv (deriv φ) ≥ lam > 0` there, then `‖∫_a^b exp(i φ)‖ ≤ 2/√lam`. -/
lemma norm_intervalIntegral_exp_of_deriv_pos {a b : ℝ} (hab : a < b) {φ : ℝ → ℝ} {lam : ℝ}
    (hlam : 0 < lam)
    (hC : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 2 φ x)
    (hpos : ∀ x ∈ Set.Icc a b, 0 < deriv φ x)
    (h2lam : ∀ x ∈ Set.Icc a b, lam ≤ deriv (deriv φ) x) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ 2 / Real.sqrt lam := by
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have h1 : ∀ x ∈ Set.Icc a b, HasDerivAt φ (deriv φ x) x :=
    fun x hx => ((hC x hx).differentiableAt (by norm_num)).hasDerivAt
  have h2 : ∀ x ∈ Set.Icc a b, HasDerivAt (deriv φ) (deriv (deriv φ) x) x :=
    fun x hx => (((hC x hx).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hGcont : ContinuousOn (deriv φ) (Set.Icc a b) :=
    fun x hx => (h2 x hx).continuousAt.continuousWithinAt
  have h2cont : ContinuousOn (deriv (deriv φ)) (Set.Icc a b) :=
    fun x hx => (((hC x hx).derivWithin (m := 1) (by norm_num)).derivWithin (m := 0)
      (by norm_num)).continuousAt.continuousWithinAt
  -- growth of `deriv φ`
  have hgrowth : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      lam * (y - x) ≤ deriv φ y - deriv φ x := by
    intro x hx y hy hxy
    have hsub : Set.Icc x y ⊆ Set.Icc a b := by
      intro t ht; exact ⟨le_trans hx.1 ht.1, le_trans ht.2 hy.2⟩
    have hsub' : Set.uIcc x y ⊆ Set.Icc a b := by rw [Set.uIcc_of_le hxy]; exact hsub
    have hFTC : ∫ t in x..y, deriv (deriv φ) t = deriv φ y - deriv φ x :=
      integral_deriv_eq_sub (f := deriv φ)
        (fun t ht => (h2 t (hsub' ht)).differentiableAt)
        ((h2cont.mono hsub').intervalIntegrable)
    rw [← hFTC]
    have hconst : (∫ t in x..y, (lam : ℝ)) = lam * (y - x) := by
      rw [intervalIntegral.integral_const]; simp [smul_eq_mul, mul_comm]
    rw [← hconst]
    exact integral_mono_on hxy ((continuous_const).intervalIntegrable _ _)
      ((h2cont.mono hsub').intervalIntegrable) (fun t ht => h2lam t (hsub ht))
  -- basic properties of `A x = φ x - φ a`
  have hA_nonneg : ∀ x ∈ Set.Icc a b, 0 ≤ φ x - φ a := by
    intro x hx
    have hsub : Set.Icc a x ⊆ Set.Icc a b := by
      intro t ht; exact ⟨ht.1, le_trans ht.2 hx.2⟩
    have hsub' : Set.uIcc a x ⊆ Set.Icc a b := by rw [Set.uIcc_of_le hx.1]; exact hsub
    have hFTC : ∫ t in a..x, deriv φ t = φ x - φ a :=
      integral_deriv_eq_sub (f := φ) (fun t ht => (h1 t (hsub' ht)).differentiableAt)
        ((hGcont.mono hsub').intervalIntegrable)
    rw [← hFTC]
    refine intervalIntegral.integral_nonneg hx.1 (fun t ht => ?_)
    exact le_of_lt (hpos t (hsub ht))
  have hA_mono : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → φ x - φ a ≤ φ y - φ a := by
    intro x hx y hy hxy
    have hsub : Set.Icc x y ⊆ Set.Icc a b := by
      intro t ht; exact ⟨le_trans hx.1 ht.1, le_trans ht.2 hy.2⟩
    have hsub' : Set.uIcc x y ⊆ Set.Icc a b := by rw [Set.uIcc_of_le hxy]; exact hsub
    have hFTC : ∫ t in x..y, deriv φ t = φ y - φ x :=
      integral_deriv_eq_sub (f := φ) (fun t ht => (h1 t (hsub' ht)).differentiableAt)
        ((hGcont.mono hsub').intervalIntegrable)
    have hposint : 0 ≤ ∫ t in x..y, deriv φ t :=
      intervalIntegral.integral_nonneg hxy (fun t ht => le_of_lt (hpos t (hsub ht)))
    linarith
  have hA_ge : ∀ x ∈ Set.Icc a b, lam * (x - a) ^ 2 / 2 ≤ φ x - φ a := by
    intro x hx
    have hsub : Set.Icc a x ⊆ Set.Icc a b := by
      intro t ht; exact ⟨ht.1, le_trans ht.2 hx.2⟩
    have hsub' : Set.uIcc a x ⊆ Set.Icc a b := by rw [Set.uIcc_of_le hx.1]; exact hsub
    have hFTC : ∫ t in a..x, deriv φ t = φ x - φ a :=
      integral_deriv_eq_sub (f := φ) (fun t ht => (h1 t (hsub' ht)).differentiableAt)
        ((hGcont.mono hsub').intervalIntegrable)
    rw [← hFTC]
    have hlow : ∀ t ∈ Set.Icc a x, lam * (t - a) ≤ deriv φ t := by
      intro t ht
      have ht' := hsub ht
      have h := hgrowth a ha_mem t ht' ht.1
      have h0 : 0 ≤ deriv φ a := le_of_lt (hpos a ha_mem)
      linarith
    have hcomp : (∫ t in a..x, lam * (t - a)) = lam * (x - a) ^ 2 / 2 := by
      have hderiv : ∀ t ∈ Set.uIcc a x,
          HasDerivAt (fun s : ℝ => lam * ((s - a) ^ 2 / 2)) (lam * (t - a)) t := by
        intro t ht
        have h1' : HasDerivAt (fun s : ℝ => s - a) 1 t := (hasDerivAt_id t).sub_const a
        have h2' : HasDerivAt (fun s : ℝ => (s - a) ^ 2 / 2) ((t - a) * 1) t := by
          simpa using (h1'.pow 2).div_const 2
        have h3 : HasDerivAt (fun s : ℝ => lam * ((s - a) ^ 2 / 2)) (lam * ((t - a) * 1)) t :=
          h2'.const_mul lam
        convert h3 using 2
        ring
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := x) hderiv
        ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _)
      rw [this]; ring
    calc lam * (x - a) ^ 2 / 2 = ∫ t in a..x, lam * (t - a) := hcomp.symm
      _ ≤ ∫ t in a..x, deriv φ t := by
          refine integral_mono_on hx.1
            ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _)
            ((hGcont.mono hsub').intervalIntegrable) (fun t ht => hlow t ht)

  -- continuous versions on `uIcc`
  have hGcont_u : ContinuousOn (deriv φ) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]; exact hGcont
  have h2cont_u : ContinuousOn (deriv (deriv φ)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]; exact h2cont
  have hφcont_u : ContinuousOn φ (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact fun x hx => (h1 x hx).continuousAt.continuousWithinAt
  rcases le_or_gt (φ b - φ a) 2 with hle2 | hgt2
  · -- Case 1: the phase oscillates by at most 2; use the trivial bound
    have htriv : ‖∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ b - a := by
      calc ‖∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ))‖
          ≤ ∫ x in a..b, ‖Complex.exp (Complex.I * (φ x : ℂ))‖ :=
            intervalIntegral.norm_integral_le_integral_norm hab.le
        _ = ∫ x in a..b, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact Complex.norm_exp_I_mul_ofReal (φ x)
        _ = b - a := by rw [intervalIntegral.integral_const]; simp
    have hsq : (b - a) ^ 2 ≤ 4 / lam := by
      rw [le_div_iff₀ hlam]
      have h := hA_ge b hb_mem
      nlinarith [h, hle2]
    have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have hle : b - a ≤ 2 / Real.sqrt lam := by
      rw [le_div_iff₀ hs]
      have h4 : (b - a) ^ 2 * lam ≤ 4 := (le_div_iff₀ hlam).mp hsq
      have h2' : ((b - a) * Real.sqrt lam) ^ 2 ≤ 4 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hlam)]
        simpa using h4
      nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) (le_of_lt hs), h2']
    linarith
  · -- Case 2: the phase varies by more than `2`; find the crossing point
    have hφcont : ContinuousOn φ (Set.Icc a b) :=
      fun x hx => (h1 x hx).continuousAt.continuousWithinAt
    obtain ⟨x₂, hx₂_mem, hx₂_val⟩ : ∃ x₂ ∈ Set.Icc a b, φ x₂ - φ a = 2 := by
      have hcontA : ContinuousOn (fun x => φ x - φ a) (Set.Icc a b) := hφcont.sub continuousOn_const
      have hmem : (2 : ℝ) ∈ Set.Icc (φ a - φ a) (φ b - φ a) := ⟨by simp, le_of_lt hgt2⟩
      obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc hab.le hcontA hmem
      exact ⟨c, hc, hcv⟩
    have hx₂_ge : a ≤ x₂ := hx₂_mem.1
    have hx₂_le : x₂ ≤ b := hx₂_mem.2
    -- the weight `1/φ'` (real) and its derivative
    let wr : ℝ → ℝ := fun y => (deriv φ y)⁻¹
    let wr' : ℝ → ℝ := fun y => -(deriv (deriv φ) y) / (deriv φ y) ^ 2
    have hwr_d : ∀ x ∈ Set.Icc a b, HasDerivAt wr (wr' x) x :=
      fun x hx => (h2 x hx).inv (ne_of_gt (hpos x hx))
    -- complex weight and phase
    let w : ℝ → ℂ := fun y => (((deriv φ y)⁻¹ : ℝ) : ℂ)
    let w' : ℝ → ℂ := fun y => ((-(deriv (deriv φ) y) / (deriv φ y) ^ 2 : ℝ) : ℂ)
    let hh : ℝ → ℂ :=
      fun y => (Complex.exp (Complex.I * (φ y : ℂ)) - Complex.exp (Complex.I * (φ a : ℂ))) * (-Complex.I)
    let hh' : ℝ → ℂ := fun y => Complex.exp (Complex.I * (φ y : ℂ)) * ((deriv φ y : ℝ) : ℂ)
    have hw_d : ∀ x ∈ Set.uIcc a b, HasDerivAt w (w' x) x := by
      intro x hx
      have hxI : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab.le] at hx
      have hthis : HasDerivAt (fun y => (((deriv φ y)⁻¹ : ℝ) : ℂ))
          (((-(deriv (deriv φ) x) / (deriv φ x) ^ 2 : ℝ)) : ℂ) x := (hwr_d x hxI).ofReal_comp
      simpa only [w, w'] using hthis
    have hh_d : ∀ x ∈ Set.uIcc a b, HasDerivAt hh (hh' x) x := by
      intro x hx
      have hxI : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab.le] at hx
      have hc1 : HasDerivAt (fun y => ((φ y : ℝ) : ℂ)) ((deriv φ x : ℝ) : ℂ) x :=
        (h1 x hxI).ofReal_comp
      have hc2 : HasDerivAt (fun y => Complex.exp (Complex.I * ((φ y : ℝ) : ℂ)))
          (Complex.exp (Complex.I * ((φ x : ℝ) : ℂ)) * (Complex.I * ((deriv φ x : ℝ) : ℂ))) x :=
        (hc1.const_mul Complex.I).cexp
      have hc3 : HasDerivAt
          (fun y => (Complex.exp (Complex.I * (φ y : ℂ)) - Complex.exp (Complex.I * (φ a : ℂ))) * (-Complex.I))
          ((Complex.exp (Complex.I * ((φ x : ℝ) : ℂ)) * (Complex.I * ((deriv φ x : ℝ) : ℂ))) * (-Complex.I)) x :=
        (hc2.sub_const (Complex.exp (Complex.I * (φ a : ℂ)))).mul_const (-Complex.I)
      have hfix : (Complex.exp (Complex.I * ((φ x : ℝ) : ℂ)) * (Complex.I * ((deriv φ x : ℝ) : ℂ))) * (-Complex.I)
          = Complex.exp (Complex.I * (φ x : ℂ)) * ((deriv φ x : ℝ) : ℂ) := by
        have hI : (Complex.I : ℂ) * (-Complex.I) = 1 := by
          rw [mul_neg, Complex.I_mul_I, neg_neg]
        calc (Complex.exp (Complex.I * ((φ x : ℝ) : ℂ)) * (Complex.I * ((deriv φ x : ℝ) : ℂ))) * (-Complex.I)
            = Complex.exp (Complex.I * ((φ x : ℝ) : ℂ)) * ((deriv φ x : ℝ) : ℂ) * (Complex.I * (-Complex.I)) := by
              ring
          _ = Complex.exp (Complex.I * ((φ x : ℝ) : ℂ)) * ((deriv φ x : ℝ) : ℂ) := by rw [hI, mul_one]
      rw [hfix] at hc3
      simpa only [hh, hh'] using hc3
    have hw'_cont : ContinuousOn w' (Set.uIcc a b) := by
      have hden : ∀ x ∈ Set.uIcc a b, (deriv φ x) ^ 2 ≠ 0 := by
        intro x hx
        have hxI : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab.le] at hx
        exact pow_ne_zero 2 (ne_of_gt (hpos x hxI))
      have hreal : ContinuousOn (fun x => -(deriv (deriv φ) x) / (deriv φ x) ^ 2) (Set.uIcc a b) :=
        (h2cont_u.neg).div (hGcont_u.pow 2) hden
      exact fun x hx => Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (hreal x hx)
    have hw'_int : IntervalIntegrable w' volume a b := hw'_cont.intervalIntegrable
    have hhexp_cont : ContinuousOn (fun y => Complex.exp (Complex.I * (φ y : ℂ))) (Set.uIcc a b) :=
      Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφcont_u))
    have hh_cont : ContinuousOn hh (Set.uIcc a b) := by
      have hsub : ContinuousOn
          (fun y => Complex.exp (Complex.I * (φ y : ℂ)) - Complex.exp (Complex.I * (φ a : ℂ)))
          (Set.uIcc a b) :=
        hhexp_cont.sub continuousOn_const
      exact hsub.mul continuousOn_const
    have hh'_cont : ContinuousOn hh' (Set.uIcc a b) := by
      intro x hx
      exact (hhexp_cont x hx).mul (Complex.continuous_ofReal.comp_continuousOn hGcont_u x hx)
    have hh'_int : IntervalIntegrable hh' volume a b := hh'_cont.intervalIntegrable
    have hw_mul : ∀ x ∈ Set.Icc a b, w x * hh' x = Complex.exp (Complex.I * (φ x : ℂ)) := by
      intro x hx
      have hne : deriv φ x ≠ 0 := ne_of_gt (hpos x hx)
      simp only [w, hh']
      calc (((deriv φ x)⁻¹ : ℝ) : ℂ) * (Complex.exp (Complex.I * (φ x : ℂ)) * ((deriv φ x : ℝ) : ℂ))
          = Complex.exp (Complex.I * (φ x : ℂ)) * ((((deriv φ x)⁻¹ : ℝ) : ℂ) * ((deriv φ x : ℝ) : ℂ)) := by
            ring
        _ = Complex.exp (Complex.I * (φ x : ℂ)) := by
            rw [← Complex.ofReal_mul, inv_mul_cancel₀ hne, Complex.ofReal_one, mul_one]
    have hibp : ∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ)) = w b * hh b - ∫ x in a..b, w' x * hh x := by
      have h0 := intervalIntegral.integral_mul_deriv_eq_deriv_mul hw_d hh_d hw'_int hh'_int
      have hcong : (∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ))) = ∫ x in a..b, w x * hh' x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hxI : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab.le] at hx
        exact (hw_mul x hxI).symm
      rw [hcong, h0]
      have ha0 : w a * hh a = 0 := by
        have hz : hh a = 0 := by
          simp only [hh]
          rw [sub_self, zero_mul]
        rw [hz, mul_zero]
      rw [ha0]
      ring
    have hbnd : ‖∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ))‖
        ≤ ‖w b‖ * ‖hh b‖ + ∫ x in a..b, ‖w' x‖ * ‖hh x‖ := by
      rw [hibp]
      calc ‖w b * hh b - ∫ x in a..b, w' x * hh x‖
          ≤ ‖w b * hh b‖ + ‖∫ x in a..b, w' x * hh x‖ := norm_sub_le _ _
        _ ≤ ‖w b‖ * ‖hh b‖ + ∫ x in a..b, ‖w' x * hh x‖ :=
            add_le_add (le_of_eq (norm_mul _ _)) (intervalIntegral.norm_integral_le_integral_norm hab.le)
        _ = ‖w b‖ * ‖hh b‖ + ∫ x in a..b, ‖w' x‖ * ‖hh x‖ := by
            congr 1
            apply intervalIntegral.integral_congr
            intro x hx
            simp only [norm_mul]
    -- pointwise norms
    have hw_norm : ∀ x ∈ Set.Icc a b, ‖w x‖ = (deriv φ x)⁻¹ := by
      intro x hx
      calc ‖w x‖ = ‖((((deriv φ x)⁻¹ : ℝ)) : ℂ)‖ := by simp only [w]
        _ = |((deriv φ x)⁻¹ : ℝ)| := RCLike.norm_ofReal _
        _ = (deriv φ x)⁻¹ := abs_of_pos (inv_pos.mpr (hpos x hx))
    have hw'_norm : ∀ x ∈ Set.Icc a b, ‖w' x‖ = deriv (deriv φ) x / (deriv φ x) ^ 2 := by
      intro x hx
      have hg := hpos x hx
      have h2p : 0 < deriv (deriv φ) x := lt_of_lt_of_le hlam (h2lam x hx)
      have hnn : (-(deriv (deriv φ) x) / (deriv φ x) ^ 2 : ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
      calc ‖w' x‖ = ‖((-(deriv (deriv φ) x) / (deriv φ x) ^ 2 : ℝ) : ℂ)‖ := by simp only [w']
        _ = |(-(deriv (deriv φ) x) / (deriv φ x) ^ 2 : ℝ)| := RCLike.norm_ofReal _
        _ = -((-(deriv (deriv φ) x)) / (deriv φ x) ^ 2) := abs_of_nonpos hnn
        _ = deriv (deriv φ) x / (deriv φ x) ^ 2 := by ring
    have hh_norm_two : ∀ x : ℝ, ‖hh x‖ ≤ 2 := by
      intro x
      simp only [hh]
      rw [norm_mul, norm_neg, Complex.norm_I, mul_one]
      calc ‖Complex.exp (Complex.I * (φ x : ℂ)) - Complex.exp (Complex.I * (φ a : ℂ))‖
          ≤ ‖Complex.exp (Complex.I * (φ x : ℂ))‖ + ‖Complex.exp (Complex.I * (φ a : ℂ))‖ := norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal]; norm_num
    have hh_norm_A : ∀ x ∈ Set.Icc a b, ‖hh x‖ ≤ φ x - φ a := by
      intro x hx
      have hA0 : 0 ≤ φ x - φ a := hA_nonneg x hx
      have hfac : Complex.exp (Complex.I * (φ x : ℂ)) - Complex.exp (Complex.I * (φ a : ℂ))
          = Complex.exp (Complex.I * (φ a : ℂ)) *
              (Complex.exp (Complex.I * ((φ x - φ a : ℝ) : ℂ)) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp only [hh]
      rw [norm_mul, norm_neg, Complex.norm_I, mul_one, hfac, norm_mul,
        Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one]
      rw [show ‖(2 * Real.sin ((φ x - φ a) / 2) : ℝ)‖ = |2 * Real.sin ((φ x - φ a) / 2)| from
        RCLike.norm_ofReal _]
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      have hsin : |Real.sin ((φ x - φ a) / 2)| ≤ (φ x - φ a) / 2 := by
        have h1 := Real.abs_sin_le_abs (x := (φ x - φ a) / 2)
        rwa [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg hA0] at h1
      linarith
    -- continuity of the real weight and its derivative on the whole interval
    have hwr_cont : ContinuousOn wr (Set.uIcc a b) := by
      have h : ContinuousOn (fun x => (1:ℝ) / deriv φ x) (Set.uIcc a b) :=
        ContinuousOn.div continuousOn_const hGcont_u (fun x hx => by
          have hxI : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab.le] at hx
          exact ne_of_gt (hpos x hxI))
      simpa only [wr, one_div] using h
    have hwr'_cont : ContinuousOn wr' (Set.uIcc a b) := by
      have h : ContinuousOn (fun x => -(deriv (deriv φ) x) / (deriv φ x) ^ 2) (Set.uIcc a b) :=
        (h2cont_u.neg).div (hGcont_u.pow 2) (fun x hx => by
          have hxI : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab.le] at hx
          exact pow_ne_zero 2 (ne_of_gt (hpos x hxI)))
      simpa only [wr'] using h
    have hsub1 : Set.uIcc a x₂ ⊆ Set.uIcc a b := by
      rw [Set.uIcc_of_le hx₂_ge, Set.uIcc_of_le hab.le]
      exact Set.Icc_subset_Icc le_rfl hx₂_le
    have hsub2 : Set.uIcc x₂ b ⊆ Set.uIcc a b := by
      rw [Set.uIcc_of_le hx₂_le, Set.uIcc_of_le hab.le]
      exact Set.Icc_subset_Icc hx₂_ge le_rfl
    -- integrability of the pieces
    have hint_cont : IntervalIntegrable (fun x => ‖w' x‖ * ‖hh x‖) volume a b :=
      (hw'_cont.norm.mul hh_cont.norm).intervalIntegrable
    have hint_cont1 : IntervalIntegrable (fun x => ‖w' x‖ * ‖hh x‖) volume a x₂ :=
      ((hw'_cont.norm.mul hh_cont.norm).mono hsub1).intervalIntegrable
    have hint_cont2 : IntervalIntegrable (fun x => ‖w' x‖ * ‖hh x‖) volume x₂ b :=
      ((hw'_cont.norm.mul hh_cont.norm).mono hsub2).intervalIntegrable
    have hsplit : ∫ x in a..b, ‖w' x‖ * ‖hh x‖
        = (∫ x in a..x₂, ‖w' x‖ * ‖hh x‖) + ∫ x in x₂..b, ‖w' x‖ * ‖hh x‖ :=
      (intervalIntegral.integral_add_adjacent_intervals hint_cont1 hint_cont2).symm
    -- FTC for `(φ - φ a) · (1/φ')` on `[a, x₂]`
    have hderivA : ∀ x ∈ Set.uIcc a x₂, HasDerivAt (fun y => (φ y - φ a) * wr y)
        (deriv φ x * wr x + (φ x - φ a) * wr' x) x := by
      intro x hx
      have hxI : x ∈ Set.Icc a b := by
        have := hsub1 hx
        rwa [Set.uIcc_of_le hab.le] at this
      exact ((h1 x hxI).sub_const (φ a)).mul (hwr_d x hxI)
    have hcontA : IntervalIntegrable (fun x => deriv φ x * wr x + (φ x - φ a) * wr' x) volume a x₂ :=
      (((hGcont_u.mono hsub1).mul (hwr_cont.mono hsub1)).add
        (((hφcont_u.mono hsub1).sub continuousOn_const).mul (hwr'_cont.mono hsub1))).intervalIntegrable
    have hFTC1 : ∫ x in a..x₂, (deriv φ x * wr x + (φ x - φ a) * wr' x) = 2 * (deriv φ x₂)⁻¹ := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivA hcontA
      rw [h, hx₂_val]
      have h0 : (φ a - φ a) * wr a = 0 := by ring
      rw [h0, sub_zero]
    have hkey1 : ∫ x in a..x₂, (φ x - φ a) * wr' x = 2 * (deriv φ x₂)⁻¹ - (x₂ - a) := by
      have hcA : IntervalIntegrable (fun x => deriv φ x * wr x) volume a x₂ :=
        ((hGcont_u.mono hsub1).mul (hwr_cont.mono hsub1)).intervalIntegrable
      have hcB : IntervalIntegrable (fun x => (φ x - φ a) * wr' x) volume a x₂ :=
        (((hφcont_u.mono hsub1).sub continuousOn_const).mul (hwr'_cont.mono hsub1)).intervalIntegrable
      have hsum := intervalIntegral.integral_add hcA hcB
      have hone : ∫ x in a..x₂, deriv φ x * wr x = x₂ - a := by
        rw [show (∫ x in a..x₂, deriv φ x * wr x) = ∫ x in a..x₂, (1:ℝ) from
          intervalIntegral.integral_congr (fun x hx => ?_)]
        · rw [intervalIntegral.integral_const]; simp
        · have hxI : x ∈ Set.Icc a b := by
            have := hsub1 hx
            rwa [Set.uIcc_of_le hab.le] at this
          simp only [wr]
          exact mul_inv_cancel₀ (ne_of_gt (hpos x hxI))
      linarith [hFTC1, hsum, hone]
    have hpiece1 : ∫ x in a..x₂, ‖w' x‖ * ‖hh x‖ ≤ (x₂ - a) - 2 * (deriv φ x₂)⁻¹ := by
      have hpoint : ∀ x ∈ Set.Icc a x₂, ‖w' x‖ * ‖hh x‖ ≤ (φ x - φ a) * (-(wr' x)) := by
        intro x hx
        have hxI : x ∈ Set.Icc a b := ⟨hx.1, le_trans hx.2 hx₂_le⟩
        have hnn : 0 ≤ deriv (deriv φ) x / (deriv φ x) ^ 2 :=
          div_nonneg (by linarith [lt_of_lt_of_le hlam (h2lam x hxI)]) (sq_nonneg _)
        rw [hw'_norm x hxI]
        calc deriv (deriv φ) x / (deriv φ x) ^ 2 * ‖hh x‖
            ≤ deriv (deriv φ) x / (deriv φ x) ^ 2 * (φ x - φ a) :=
              mul_le_mul_of_nonneg_left (hh_norm_A x hxI) hnn
          _ = (φ x - φ a) * (-(wr' x)) := by simp only [wr']; ring
      calc ∫ x in a..x₂, ‖w' x‖ * ‖hh x‖
          ≤ ∫ x in a..x₂, (φ x - φ a) * (-(wr' x)) := by
            refine integral_mono_on hx₂_ge hint_cont1 ?_ hpoint
            · exact (((hφcont_u.mono hsub1).sub continuousOn_const).mul
                (hwr'_cont.mono hsub1).neg).intervalIntegrable
        _ = (x₂ - a) - 2 * (deriv φ x₂)⁻¹ := by
            rw [show (fun x => (φ x - φ a) * (-(wr' x))) = fun x => -((φ x - φ a) * wr' x) from by
              ext x; ring]
            rw [intervalIntegral.integral_neg, hkey1]; ring
    -- FTC for `1/φ'` on `[x₂, b]`
    have hFTC2 : ∫ x in x₂..b, wr' x = wr b - wr x₂ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hwr_d x (by
          have := hsub2 hx
          rwa [Set.uIcc_of_le hab.le] at this))
        (hwr'_cont.mono hsub2).intervalIntegrable
    have hpiece2 : ∫ x in x₂..b, ‖w' x‖ * ‖hh x‖ ≤ 2 * ((deriv φ x₂)⁻¹ - (deriv φ b)⁻¹) := by
      have hpoint : ∀ x ∈ Set.Icc x₂ b, ‖w' x‖ * ‖hh x‖ ≤ 2 * (-(wr' x)) := by
        intro x hx
        have hxI : x ∈ Set.Icc a b := ⟨le_trans hx₂_ge hx.1, hx.2⟩
        have hnn : 0 ≤ deriv (deriv φ) x / (deriv φ x) ^ 2 :=
          div_nonneg (by linarith [lt_of_lt_of_le hlam (h2lam x hxI)]) (sq_nonneg _)
        rw [hw'_norm x hxI]
        calc deriv (deriv φ) x / (deriv φ x) ^ 2 * ‖hh x‖
            ≤ deriv (deriv φ) x / (deriv φ x) ^ 2 * 2 :=
              mul_le_mul_of_nonneg_left (hh_norm_two x) hnn
          _ = 2 * (-(wr' x)) := by simp only [wr']; ring
      calc ∫ x in x₂..b, ‖w' x‖ * ‖hh x‖
          ≤ ∫ x in x₂..b, 2 * (-(wr' x)) := by
            refine integral_mono_on hx₂_le hint_cont2 ?_ hpoint
            · exact (continuousOn_const.mul (hwr'_cont.mono hsub2).neg).intervalIntegrable
        _ = 2 * ∫ x in x₂..b, (-(wr' x)) := by rw [intervalIntegral.integral_const_mul]
        _ = 2 * ((deriv φ x₂)⁻¹ - (deriv φ b)⁻¹) := by
            congr 1
            rw [intervalIntegral.integral_neg, hFTC2]
            simp only [wr]; ring
    have hb3 : ‖w b‖ * ‖hh b‖ ≤ (deriv φ b)⁻¹ * 2 := by
      rw [hw_norm b hb_mem]
      exact mul_le_mul_of_nonneg_left (hh_norm_two b) (inv_nonneg.mpr (le_of_lt (hpos b hb_mem)))
    have htot : ‖∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ x₂ - a := by
      calc ‖∫ x in a..b, Complex.exp (Complex.I * (φ x : ℂ))‖
          ≤ ‖w b‖ * ‖hh b‖ + ∫ x in a..b, ‖w' x‖ * ‖hh x‖ := hbnd
        _ = ‖w b‖ * ‖hh b‖ + ((∫ x in a..x₂, ‖w' x‖ * ‖hh x‖)
              + ∫ x in x₂..b, ‖w' x‖ * ‖hh x‖) := by rw [hsplit]
        _ ≤ (deriv φ b)⁻¹ * 2 + ((x₂ - a) - 2 * (deriv φ x₂)⁻¹)
              + 2 * ((deriv φ x₂)⁻¹ - (deriv φ b)⁻¹) := by
            linarith [hb3, hpiece1, hpiece2]
        _ = x₂ - a := by ring
    have hsq : (x₂ - a) ^ 2 ≤ 4 / lam := by
      rw [le_div_iff₀ hlam]
      have h := hA_ge x₂ hx₂_mem
      rw [hx₂_val] at h
      nlinarith [h]
    have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have hfin : x₂ - a ≤ 2 / Real.sqrt lam := by
      rw [le_div_iff₀ hs]
      have h4 : (x₂ - a) ^ 2 * lam ≤ 4 := (le_div_iff₀ hlam).mp hsq
      have h2' : ((x₂ - a) * Real.sqrt lam) ^ 2 ≤ 4 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hlam)]
        simpa using h4
      nlinarith [mul_nonneg (sub_nonneg.mpr hx₂_ge) (le_of_lt hs), h2']
    linarith

/-- **One-sided second derivative estimate**, `ContDiffOn` form: if `deriv φ ≥ 0` on the open
interval and `deriv (deriv φ) ≥ lam > 0`, then `‖∫_u^v exp(i φ)‖ ≤ 2/√lam`. -/
lemma norm_intervalIntegral_exp_one_sided {u v : ℝ} (huv : u ≤ v) {φ : ℝ → ℝ} {lam : ℝ}
    (hlam : 0 < lam) (hφ : ContDiffOn ℝ 2 φ (Set.Icc u v))
    (hmono : ∀ x ∈ Set.Ioo u v, 0 ≤ deriv φ x)
    (h2 : ∀ x ∈ Set.Ioo u v, lam ≤ deriv (deriv φ) x) :
    ‖∫ x in u..v, Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ 2 / Real.sqrt lam := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · simp
    positivity
  have hgrowth := deriv_sub_ge_of_second_deriv_ge hφ h2
  -- the derivative is strictly positive on the open interval
  have gpos : ∀ x ∈ Set.Ioo u v, 0 < deriv φ x := by
    intro x hx
    rcases eq_or_lt_of_le (hmono x hx) with hpos | hpos
    · exfalso
      have hx0 : deriv φ x = 0 := hpos.symm
      obtain ⟨z, hz⟩ : ∃ z, z ∈ Set.Ioo u x :=
        ⟨(u + x) / 2, by constructor <;> linarith [hx.1, hx.2]⟩
      have hzuv : z ∈ Set.Ioo u v := ⟨hz.1, lt_trans hz.2 hx.2⟩
      have hg := hgrowth z hzuv x hx (le_of_lt hz.2)
      have hm := hmono z hzuv
      rw [hx0] at hg
      have hlt' : 0 < lam * (x - z) := mul_pos hlam (sub_pos.mpr hz.2)
      linarith
    · exact hpos
  -- bound on any strictly interior subinterval
  have key : ∀ p q : ℝ, u < p → p ≤ q → q < v →
      ‖∫ x in p..q, Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ 2 / Real.sqrt lam := by
    intro p q hup hpq hqv
    rcases eq_or_lt_of_le hpq with heq | hpq'
    · subst heq
      simp
      positivity
    refine norm_intervalIntegral_exp_of_deriv_pos hpq' hlam ?_ ?_ ?_
    · intro x hx
      have hx' : x ∈ Set.Ioo u v := ⟨lt_of_lt_of_le hup hx.1, lt_of_le_of_lt hx.2 hqv⟩
      exact hφ.contDiffAt (Icc_mem_nhds hx'.1 hx'.2)
    · intro x hx
      have hx' : x ∈ Set.Ioo u v := ⟨lt_of_lt_of_le hup hx.1, lt_of_le_of_lt hx.2 hqv⟩
      exact gpos x hx'
    · intro x hx
      have hx' : x ∈ Set.Ioo u v := ⟨lt_of_lt_of_le hup hx.1, lt_of_le_of_lt hx.2 hqv⟩
      exact h2 x hx'
  -- conclude by squeezing the endpoints
  have hexp_cont : ContinuousOn (fun x => Complex.exp (Complex.I * (φ x : ℂ))) (Set.uIcc u v) :=
    ContinuousOn.cexp (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (by rw [Set.uIcc_of_le huv]; exact hφ.continuousOn)))
  have intOn : ∀ p q : ℝ, u ≤ p → p ≤ q → q ≤ v →
      IntervalIntegrable (fun x => Complex.exp (Complex.I * (φ x : ℂ))) volume p q := by
    intro p q hup hpq hqv
    refine ContinuousOn.intervalIntegrable ?_
    refine hexp_cont.mono ?_
    rw [Set.uIcc_of_le hpq, Set.uIcc_of_le huv]
    exact Set.Icc_subset_Icc hup hqv
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  set ε : ℝ := min (δ / 4) ((v - u) / 4) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ : ε ≤ δ / 4 := min_le_left _ _
  have hεv : ε ≤ (v - u) / 4 := min_le_right _ _
  have hup : u < u + ε := by linarith
  have hqv : v - ε < v := by linarith
  have hpq : u + ε ≤ v - ε := by linarith
  have hup' : u ≤ u + ε := le_of_lt hup
  have hqv' : v - ε ≤ v := le_of_lt hqv
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (intOn u (v - ε) le_rfl (by linarith) hqv')
    (intOn (v - ε) v (by linarith) (by linarith) le_rfl)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (intOn u (u + ε) le_rfl hup' (by linarith))
    (intOn (u + ε) (v - ε) hup' hpq hqv')
  have htriv1 : ‖∫ x in u..(u + ε), Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ ε := by
    calc ‖∫ x in u..(u + ε), Complex.exp (Complex.I * (φ x : ℂ))‖
        ≤ ∫ x in u..(u + ε), ‖Complex.exp (Complex.I * (φ x : ℂ))‖ :=
          intervalIntegral.norm_integral_le_integral_norm hup'
      _ = ε := by
          rw [show (∫ x in u..(u + ε), ‖Complex.exp (Complex.I * (φ x : ℂ))‖)
              = ∫ x in u..(u + ε), (1:ℝ) from
            intervalIntegral.integral_congr (fun x hx => Complex.norm_exp_I_mul_ofReal (φ x))]
          rw [intervalIntegral.integral_const]; simp
  have htriv3 : ‖∫ x in (v - ε)..v, Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ ε := by
    calc ‖∫ x in (v - ε)..v, Complex.exp (Complex.I * (φ x : ℂ))‖
        ≤ ∫ x in (v - ε)..v, ‖Complex.exp (Complex.I * (φ x : ℂ))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ = ε := by
          rw [show (∫ x in (v - ε)..v, ‖Complex.exp (Complex.I * (φ x : ℂ))‖)
              = ∫ x in (v - ε)..v, (1:ℝ) from
            intervalIntegral.integral_congr (fun x hx => Complex.norm_exp_I_mul_ofReal (φ x))]
          rw [intervalIntegral.integral_const]; simp
  have hstep : ‖∫ x in u..(v - ε), Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ 2 / Real.sqrt lam + ε := by
    calc ‖∫ x in u..(v - ε), Complex.exp (Complex.I * (φ x : ℂ))‖
        = ‖(∫ x in u..(u + ε), Complex.exp (Complex.I * (φ x : ℂ)))
            + ∫ x in (u + ε)..(v - ε), Complex.exp (Complex.I * (φ x : ℂ))‖ := by rw [hsplit2]
      _ ≤ ‖∫ x in u..(u + ε), Complex.exp (Complex.I * (φ x : ℂ))‖
            + ‖∫ x in (u + ε)..(v - ε), Complex.exp (Complex.I * (φ x : ℂ))‖ := norm_add_le _ _
      _ ≤ 2 / Real.sqrt lam + ε := by
          have := key (u + ε) (v - ε) hup hpq hqv
          linarith
  calc ‖∫ x in u..v, Complex.exp (Complex.I * (φ x : ℂ))‖
      = ‖(∫ x in u..(v - ε), Complex.exp (Complex.I * (φ x : ℂ)))
          + ∫ x in (v - ε)..v, Complex.exp (Complex.I * (φ x : ℂ))‖ := by rw [hsplit1]
    _ ≤ ‖∫ x in u..(v - ε), Complex.exp (Complex.I * (φ x : ℂ))‖
          + ‖∫ x in (v - ε)..v, Complex.exp (Complex.I * (φ x : ℂ))‖ := norm_add_le _ _
    _ ≤ (2 / Real.sqrt lam + ε) + ε := by linarith [hstep, htriv3]
    _ ≤ 2 / Real.sqrt lam + δ := by linarith


/-- One-sided second derivative estimate for a decreasing phase
(`deriv φ ≤ 0` on the open interval).  Obtained from the positive version by the reflection
`x ↦ u + v - x`, which preserves the second derivative lower bound. -/
lemma norm_intervalIntegral_exp_one_sided_neg {u v : ℝ} (huv : u ≤ v) {φ : ℝ → ℝ} {lam : ℝ}
    (hlam : 0 < lam) (hφ : ContDiffOn ℝ 2 φ (Set.Icc u v))
    (hmono : ∀ x ∈ Set.Ioo u v, deriv φ x ≤ 0)
    (h2 : ∀ x ∈ Set.Ioo u v, lam ≤ deriv (deriv φ) x) :
    ‖∫ x in u..v, Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ 2 / Real.sqrt lam := by
  set ψ : ℝ → ℝ := fun x => φ ((u + v) - x) with hψ
  have hmaps : Set.MapsTo (fun x : ℝ => (u + v) - x) (Set.Icc u v) (Set.Icc u v) := by
    intro x hx
    simp only [Set.mem_Icc] at hx ⊢
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hψCD : ContDiffOn ℝ 2 ψ (Set.Icc u v) := by
    have hcomp : ContDiffOn ℝ 2 (φ ∘ (fun x : ℝ => (u + v) - x)) (Set.Icc u v) :=
      hφ.comp ((contDiff_const.sub contDiff_id).contDiffOn) hmaps
    simpa only [hψ, Function.comp_def] using hcomp
  have hflip : ∀ x ∈ Set.Ioo u v, (u + v) - x ∈ Set.Ioo u v := by
    intro x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hψ' : ∀ x ∈ Set.Ioo u v, deriv ψ x = -deriv φ ((u + v) - x) := by
    intro x hx
    have hin : HasDerivAt (fun y : ℝ => (u + v) - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (u + v)
    have hcomp := (hasDerivAt_of_contDiffOn_Icc hφ (hflip x hx)).comp x hin
    have hderiv : deriv (fun y : ℝ => φ ((u + v) - y)) x = deriv φ ((u + v) - x) * (-1) := by
      simpa only [Function.comp_def] using hcomp.deriv
    rw [hψ, hderiv]
    ring
  have hψ2 : ∀ x ∈ Set.Ioo u v, deriv (deriv ψ) x = deriv (deriv φ) ((u + v) - x) := by
    intro x hx
    have hcong : deriv ψ =ᶠ[𝓝 x] (fun y => -deriv φ ((u + v) - y)) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      rw [hψ' y hy]
    have hin : HasDerivAt (fun y : ℝ => (u + v) - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (u + v)
    have h2c : HasDerivAt (deriv φ) (deriv (deriv φ) ((u + v) - x)) ((u + v) - x) :=
      hasDerivAt_deriv_of_contDiffOn_Icc hφ (hflip x hx)
    have hneg : HasDerivAt (fun y => -deriv φ ((u + v) - y))
        (-(deriv (deriv φ) ((u + v) - x) * (-1))) x := (h2c.comp x hin).neg
    rw [(hneg.congr_of_eventuallyEq hcong).deriv]
    ring
  have hnorm : ‖∫ x in u..v, Complex.exp (Complex.I * (φ x : ℂ))‖
      = ‖∫ x in u..v, Complex.exp (Complex.I * (ψ x : ℂ))‖ := by
    have hswap : (∫ x in u..v, Complex.exp (Complex.I * (ψ x : ℂ)))
        = ∫ x in u..v, Complex.exp (Complex.I * (φ x : ℂ)) := by
      have h := intervalIntegral.integral_comp_sub_left
        (f := fun y : ℝ => Complex.exp (Complex.I * (φ y : ℂ))) (a := u) (b := v) (d := u + v)
      simpa only [hψ, add_sub_cancel_right, add_sub_cancel_left] using h
    rw [← hswap]
  rw [hnorm]
  refine norm_intervalIntegral_exp_one_sided huv hlam hψCD ?_ ?_
  · intro x hx
    rw [hψ' x hx]
    linarith [hmono ((u + v) - x) (hflip x hx)]
  · intro x hx
    rw [hψ2 x hx]
    exact h2 ((u + v) - x) (hflip x hx)

/-- **Two-sided second derivative estimate.**  If `deriv (deriv φ) ≥ lam > 0` on the open
interval `(u,v)`, then `‖∫_u^v exp(i φ)‖ ≤ 4/√lam`. -/
lemma norm_intervalIntegral_exp_two_sided {u v : ℝ} (huv : u ≤ v) {φ : ℝ → ℝ} {lam : ℝ}
    (hlam : 0 < lam) (hφ : ContDiffOn ℝ 2 φ (Set.Icc u v))
    (h2 : ∀ x ∈ Set.Ioo u v, lam ≤ deriv (deriv φ) x) :
    ‖∫ x in u..v, Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ 4 / Real.sqrt lam := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · simp
    positivity
  have h2nn : ∀ x ∈ Set.Ioo u v, 0 ≤ deriv (deriv φ) x :=
    fun x hx => le_trans (le_of_lt hlam) (h2 x hx)
  have hψcont : ContinuousOn (derivWithin φ (Set.Icc u v)) (Set.Icc u v) :=
    (ContDiffOn.derivWithin (m := 1) hφ (uniqueDiffOn_Icc hlt)
      (by norm_num)).continuousOn
  have hψmono : MonotoneOn (derivWithin φ (Set.Icc u v)) (Set.Icc u v) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc u v) hψcont ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      have hd : DifferentiableWithinAt ℝ (derivWithin φ (Set.Icc u v)) (Set.Icc u v) x :=
        (ContDiffOn.derivWithin (m := 1) hφ (uniqueDiffOn_Icc hlt) (by norm_num)).differentiableOn
          (by norm_num) x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      exact hd.mono (by rw [interior_Icc]; exact Set.Ioo_subset_Icc_self)
    · intro x hx
      rw [interior_Icc] at hx
      have hcong : (derivWithin φ (Set.Icc u v)) =ᶠ[𝓝 x] deriv φ := by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
        exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
      have hd : HasDerivAt (derivWithin φ (Set.Icc u v)) (deriv (deriv φ) x) x :=
        (hasDerivAt_deriv_of_contDiffOn_Icc hφ hx).congr_of_eventuallyEq hcong
      rw [hd.deriv]
      exact h2nn x hx
  have hu_mem : u ∈ Set.Icc u v := ⟨le_rfl, le_of_lt hlt⟩
  have hv_mem : v ∈ Set.Icc u v := ⟨le_of_lt hlt, le_rfl⟩
  have hpsi : ∀ x ∈ Set.Ioo u v, derivWithin φ (Set.Icc u v) x = deriv φ x :=
    fun x hx => derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
  have h2le : (2:ℝ) / Real.sqrt lam ≤ 4 / Real.sqrt lam :=
    div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg lam)
  rcases le_or_gt 0 (derivWithin φ (Set.Icc u v) u) with hpu | hpu
  · have hmonoo : ∀ x ∈ Set.Ioo u v, 0 ≤ deriv φ x := by
      intro x hx
      have h := hψmono hu_mem ⟨le_of_lt hx.1, le_of_lt hx.2⟩ (le_of_lt hx.1)
      rw [hpsi x hx] at h
      linarith
    exact le_trans (norm_intervalIntegral_exp_one_sided huv hlam hφ hmonoo h2) h2le
  · rcases le_or_gt (derivWithin φ (Set.Icc u v) v) 0 with hpv | hpv
    · have hmonoo : ∀ x ∈ Set.Ioo u v, deriv φ x ≤ 0 := by
        intro x hx
        have h := hψmono ⟨le_of_lt hx.1, le_of_lt hx.2⟩ hv_mem (le_of_lt hx.2)
        rw [hpsi x hx] at h
        linarith
      exact le_trans (norm_intervalIntegral_exp_one_sided_neg huv hlam hφ hmonoo h2) h2le
    · obtain ⟨c, hc_mem, hc_val⟩ : ∃ c ∈ Set.Icc u v, derivWithin φ (Set.Icc u v) c = 0 := by
        have h0 : (0:ℝ) ∈ Set.Icc (derivWithin φ (Set.Icc u v) u) (derivWithin φ (Set.Icc u v) v) :=
          ⟨le_of_lt hpu, le_of_lt hpv⟩
        obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc (le_of_lt hlt) hψcont h0
        exact ⟨c, hc, hcv⟩
      have hcu : u < c := by
        rcases hc_mem.1.eq_or_lt with h | h
        · exfalso
          have hzu : derivWithin φ (Set.Icc u v) u = 0 := by rw [← h] at hc_val; exact hc_val
          linarith [hpu]
        · exact h
      have hcv : c < v := by
        rcases hc_mem.2.eq_or_lt with h | h
        · exfalso
          have hzv : derivWithin φ (Set.Icc u v) v = 0 := by rw [h] at hc_val; exact hc_val
          linarith [hpv]
        · exact h
      have hmonoR : ∀ x ∈ Set.Ioo c v, 0 ≤ deriv φ x := by
        intro x hx
        have h := hψmono hc_mem ⟨le_trans (le_of_lt hcu) (le_of_lt hx.1), le_of_lt hx.2⟩ (le_of_lt hx.1)
        rw [hpsi x ⟨lt_trans hcu hx.1, hx.2⟩] at h
        linarith
      have hmonoL : ∀ x ∈ Set.Ioo u c, deriv φ x ≤ 0 := by
        intro x hx
        have h := hψmono ⟨le_of_lt hx.1, le_trans (le_of_lt hx.2) (le_of_lt hcv)⟩ hc_mem (le_of_lt hx.2)
        rw [hpsi x ⟨hx.1, lt_trans hx.2 hcv⟩] at h
        linarith
      have hexp_cont : ContinuousOn (fun x => Complex.exp (Complex.I * (φ x : ℂ))) (Set.Icc u v) :=
        ContinuousOn.cexp (continuousOn_const.mul
          (Complex.continuous_ofReal.comp_continuousOn hφ.continuousOn))
      have intOn : ∀ p q : ℝ, u ≤ p → p ≤ q → q ≤ v →
          IntervalIntegrable (fun x => Complex.exp (Complex.I * (φ x : ℂ))) volume p q := by
        intro p q hup hpq hqv
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hpq]
        exact hexp_cont.mono (Set.Icc_subset_Icc hup hqv)
      have hright : ‖∫ x in c..v, Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ 2 / Real.sqrt lam :=
        norm_intervalIntegral_exp_one_sided (le_of_lt hcv) hlam
          (hφ.mono (Set.Icc_subset_Icc (le_of_lt hcu) le_rfl)) hmonoR
          (fun x hx => h2 x ⟨lt_trans hcu hx.1, hx.2⟩)
      have hleft : ‖∫ x in u..c, Complex.exp (Complex.I * (φ x : ℂ))‖ ≤ 2 / Real.sqrt lam :=
        norm_intervalIntegral_exp_one_sided_neg (le_of_lt hcu) hlam
          (hφ.mono (Set.Icc_subset_Icc le_rfl (le_of_lt hcv))) hmonoL
          (fun x hx => h2 x ⟨hx.1, lt_trans hx.2 hcv⟩)
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (intOn u c le_rfl (le_of_lt hcu) (le_of_lt hcv))
        (intOn c v (le_of_lt hcu) (le_of_lt hcv) le_rfl)
      calc ‖∫ x in u..v, Complex.exp (Complex.I * (φ x : ℂ))‖
          = ‖(∫ x in u..c, Complex.exp (Complex.I * (φ x : ℂ)))
              + ∫ x in c..v, Complex.exp (Complex.I * (φ x : ℂ))‖ := by rw [hadd]
        _ ≤ ‖∫ x in u..c, Complex.exp (Complex.I * (φ x : ℂ))‖
              + ‖∫ x in c..v, Complex.exp (Complex.I * (φ x : ℂ))‖ := norm_add_le _ _
        _ ≤ 2 / Real.sqrt lam + 2 / Real.sqrt lam := add_le_add hleft hright
        _ = 4 / Real.sqrt lam := by ring


/-- **Second derivative test for oscillatory integrals (van der Corput).**

If `g` is monotone and nonnegative on `[a,b]` and `φ` is twice continuously differentiable on
`[a,b]` with `φ'' ≥ lam > 0` on the open interval, then
`|∫_a^b g(x) cos(φ(x)) dx| ≤ 4 g(b)/√lam`. -/
theorem integral_second_derivative_test {g φ : ℝ → ℝ} {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hg : MonotoneOn g (Set.Icc a b)) (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x)
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc a b))
    (h2 : ∀ x ∈ Set.Ioo a b, lam ≤ deriv (deriv φ) x) :
    |∫ x in a..b, g x * Real.cos (φ x)| ≤ 4 * g b / Real.sqrt lam := by
  have hcos_cont : ContinuousOn (fun x => Real.cos (φ x)) (Set.Icc a b) :=
    Real.continuous_cos.comp_continuousOn hφ.continuousOn
  have hM : ∀ x ∈ Set.Icc a b, |∫ t in x..b, Real.cos (φ t)| ≤ 4 / Real.sqrt lam := by
    intro x hx
    have hxb : x ≤ b := hx.2
    have hsub : Set.Icc x b ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 le_rfl
    have hcomplex : ‖∫ t in x..b, Complex.exp (Complex.I * (φ t : ℂ))‖ ≤ 4 / Real.sqrt lam :=
      norm_intervalIntegral_exp_two_sided hxb hlam (hφ.mono hsub)
        (fun t ht => h2 t ⟨lt_of_le_of_lt hx.1 ht.1, ht.2⟩)
    have hint : IntervalIntegrable (fun t => Complex.exp (Complex.I * (φ t : ℂ))) volume x b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hxb]
      exact ContinuousOn.cexp (continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn (hφ.continuousOn.mono hsub)))
    have hre : (∫ t in x..b, (Complex.exp (Complex.I * (φ t : ℂ))).re)
        = (∫ t in x..b, Complex.exp (Complex.I * (φ t : ℂ))).re := by
      have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint
      simpa only [Complex.reCLM_apply] using this
    have hcong : (∫ t in x..b, Real.cos (φ t))
        = ∫ t in x..b, (Complex.exp (Complex.I * (φ t : ℂ))).re := by
      apply intervalIntegral.integral_congr
      intro t ht
      show Real.cos (φ t) = (Complex.exp (Complex.I * (φ t : ℂ))).re
      rw [show Complex.exp (Complex.I * (φ t : ℂ))
          = Complex.exp (((φ t : ℝ) : ℂ) * Complex.I) by
        congr 1
        ring]
      exact (Complex.exp_ofReal_mul_I_re (φ t)).symm
    rw [hcong, hre]
    exact le_trans (Complex.abs_re_le_norm _) hcomplex
  have hw := monotone_weight_integral_bound hab hg hg0 hcos_cont hM
  calc |∫ x in a..b, g x * Real.cos (φ x)| ≤ g b * (4 / Real.sqrt lam) := hw
    _ = 4 * g b / Real.sqrt lam := by ring


end Commons.Analysis.Calculus