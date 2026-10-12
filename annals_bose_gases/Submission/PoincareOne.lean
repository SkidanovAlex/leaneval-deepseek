import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# One-dimensional Poincaré inequality `poincare_two`

The lemma `Submission.BoseGases.poincare_two` states that a C¹ function
`f : ℝ → ℝ` vanishing for `x ≤ 0` and for `x ≥ L` (`L > 0`) satisfies

    (2 / L²) · ∫ x, (f x)²  ≤  ∫ x, (deriv f x)²        (integrals over ℝ)

Proof sketch.  Reduce to the interval `(0, L)` (`f` and, since `f` is C¹ and
locally constant `0` outside `(0,L)`, also `f'` vanish off `[0,L]`).  For each
`x ∈ [0,L]` the fundamental theorem of calculus gives
`f x = ∫₀ˣ f′`;  Cauchy–Schwarz (implemented below over `intervalIntegral`)
gives `(f x)² ≤ x·∫₀ˣ (f′)² ≤ x·B` with `B := ∫₀ᴸ (f′)²`; integrating over
`x ∈ [0,L]` and using `∫₀ᴸ x = L²/2` yields `∫₀ᴸ f² ≤ (L²/2)·B`.
-/

namespace Submission

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open Filter MeasureTheory
open scoped Topology Real

namespace PoincareOne

/-- Interval Cauchy–Schwarz: for `a ≤ b` and a nonnegative function
`h` continuous on `[a,b]`,  `(∫_a^b h)² ≤ (b-a)·∫_a^b h²`. -/
lemma cs_interval {a b : ℝ} (hab : a ≤ b) {h : ℝ → ℝ}
    (hh : ContinuousOn h (Set.Icc a b)) (h0 : ∀ x, 0 ≤ h x) :
    (∫ x in a..b, h x) ^ 2 ≤ (b - a) * ∫ x in a..b, (h x) ^ 2 := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hfin : IsFiniteMeasure ν := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  letI : IsFiniteMeasure ν := hfin
  have hmh : AEStronglyMeasurable h ν := by
    refine ContinuousOn.aestronglyMeasurable (s := Set.Ioc a b) (μ := volume) ?_ (by simp)
    exact hh.mono (by intro x hx; exact Set.Ioc_subset_Icc_self hx)
  have h0ae : 0 ≤ᵐ[ν] h := ae_of_all _ h0
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
  have hbnd : ∀ᵐ x ∂ν, ‖h x‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact (ae_of_all volume (fun x hx => hC x (Set.Ioc_subset_Icc_self hx)))
  have hmem : MemLp h (ENNReal.ofReal 2) ν := MemLp.of_bound hmh C hbnd
  have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) ν := memLp_const (1 : ℝ)
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (μ := ν)
    Real.HolderConjugate.two_two h0ae (ae_of_all _ (fun _ => by norm_num)) hmem hmem1
  have hA : (∫ x, h x * (1 : ℝ) ∂ν) = ∫ x, h x ∂ν := by simp
  have h2r : (fun x : ℝ => (h x) ^ (2 : ℝ)) = fun x : ℝ => (h x) ^ 2 := by
    funext x; rw [Real.rpow_two]
  have h1r : (fun x : ℝ => (1 : ℝ) ^ (2 : ℝ)) = fun x : ℝ => (1 : ℝ) := by
    funext x; rw [Real.rpow_two]; norm_num
  rw [hA, h2r, h1r] at hmain
  let A := ∫ x, h x ∂ν
  let B := ∫ x, (h x) ^ 2 ∂ν
  let C := ν.real Set.univ
  have hB0 : 0 ≤ B := by dsimp [B]; exact integral_nonneg (fun x => sq_nonneg (h x))
  have hC0 : 0 ≤ C := by simp [C]
  have hA0 : 0 ≤ A := by dsimp [A]; exact integral_nonneg h0
  have hR : A ≤ √B * √C := by
    dsimp [A, B, C]
    simpa [Real.sqrt_eq_rpow] using hmain
  have hsquared : A ^ 2 ≤ B * C := by
    have h1 : |A| ≤ |√B * √C| := by
      calc
        |A| = A := abs_of_nonneg hA0
        _ ≤ √B * √C := hR
        _ = |√B * √C| :=
          (abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).symm
    calc
      A ^ 2 ≤ (√B * √C) ^ 2 := (sq_le_sq.mpr h1)
      _ = B * C := by
        rw [mul_pow, Real.sq_sqrt hB0, Real.sq_sqrt hC0]
  have hCeq : ν.real Set.univ = b - a := by
    dsimp [ν]
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  dsimp [A, B, C] at hsquared
  rw [hCeq] at hsquared
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  simpa [mul_comm] using hsquared

end PoincareOne

namespace BoseGases

/-- One-dimensional Poincaré (crude constant 2): a C¹ function vanishing
outside `(0,L)` satisfies `(2/L²)·∫f² ≤ ∫(f′)²`. -/
lemma poincare_two {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hvan : ∀ x : ℝ, x ≤ 0 ∨ L ≤ x → f x = 0) :
    (2 / L ^ 2) * ∫ x : ℝ, (f x) ^ 2 ≤ ∫ x : ℝ, (deriv f x) ^ 2 := by
  -- basic consequences of C¹
  have hfcont : Continuous f := hf.continuous
  have hfcontd : Continuous (deriv f) := hf.continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
  have hfdiff : Differentiable ℝ f := hf.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hf0 : f 0 = 0 := hvan 0 (Or.inl le_rfl)
  have hfL : f L = 0 := hvan L (Or.inr le_rfl)
  have hf2cont : Continuous (fun x : ℝ => (f x) ^ 2) := hfcont.pow 2
  have hfd2cont : Continuous (fun x : ℝ => (deriv f x) ^ 2) := hfcontd.pow 2
  have hfabscont : Continuous (fun x : ℝ => |deriv f x|) := hfcontd.abs
  -- the interval quantities
  let A : ℝ := ∫ x in 0..L, (f x) ^ 2
  let B : ℝ := ∫ x in 0..L, (deriv f x) ^ 2
  -- the whole-space integral of `(f x)^2` equals `A`
  have hAeq : (∫ x : ℝ, (f x) ^ 2) = A := by
    dsimp [A]
    have h1 : (∫ x : ℝ, (f x) ^ 2) = ∫ x in Set.Icc 0 L, (f x) ^ 2 := by
      exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Set.Icc (0 : ℝ) L) (f := fun x : ℝ => (f x) ^ 2) (by
          intro x hx
          have hz : f x = 0 := hvan x (by
            by_contra h
            push Not at h
            exact hx ⟨h.1.le, (le_of_lt h.2)⟩)
          simp [hz])).symm
    calc
      (∫ x : ℝ, (f x) ^ 2) = ∫ x in Set.Icc 0 L, (f x) ^ 2 := h1
      _ = ∫ x in Set.Ioc 0 L, (f x) ^ 2 := MeasureTheory.integral_Icc_eq_integral_Ioc
      _ = ∫ x in 0..L, (f x) ^ 2 := (intervalIntegral.integral_of_le hL.le).symm
  -- `deriv f` vanishes off `(0,L)`: `f` is locally constant there
  have hderiv_zero_neg {x : ℝ} (hx : x < 0) : deriv f x = 0 := by
    have hEq : (Set.Iio (0 : ℝ)).EqOn f (fun _ : ℝ => 0) := by
      intro y hy
      exact hvan y (Or.inl (le_of_lt hy))
    have hEq' : (Set.Iio (0 : ℝ)).EqOn (deriv f) (fun _ : ℝ => 0) := by
      intro y hy
      have hd : deriv (fun _ : ℝ => (0 : ℝ)) y = 0 := deriv_const y (0 : ℝ)
      simpa [hd] using (hEq.deriv isOpen_Iio) hy
    simpa using hEq' hx
  have hderiv_zero_pos {x : ℝ} (hx : L < x) : deriv f x = 0 := by
    have hEq : (Set.Ioi L).EqOn f (fun _ : ℝ => 0) := by
      intro y hy
      exact hvan y (Or.inr (le_of_lt hy))
    have hEq' : (Set.Ioi L).EqOn (deriv f) (fun _ : ℝ => 0) := by
      intro y hy
      have hd : deriv (fun _ : ℝ => (0 : ℝ)) y = 0 := deriv_const y (0 : ℝ)
      simpa [hd] using (hEq.deriv isOpen_Ioi) hy
    simpa using hEq' hx
  -- the whole-space integral of `(deriv f x)^2` equals `B`
  have hBeq : B = ∫ x : ℝ, (deriv f x) ^ 2 := by
    dsimp [B]
    calc
      (∫ x in 0..L, (deriv f x) ^ 2) = ∫ x in Set.Ioc 0 L, (deriv f x) ^ 2 :=
        intervalIntegral.integral_of_le hL.le
      _ = ∫ x in Set.Icc 0 L, (deriv f x) ^ 2 :=
        (MeasureTheory.integral_Icc_eq_integral_Ioc).symm
      _ = ∫ x : ℝ, (deriv f x) ^ 2 := by
        exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := Set.Icc (0 : ℝ) L) (f := fun x : ℝ => (deriv f x) ^ 2) (by
            intro x hx
            have hz : deriv f x = 0 := by
              by_cases hx0 : x < 0
              · exact hderiv_zero_neg hx0
              · have hLx : L < x := by
                  by_contra h
                  push Not at h
                  exact hx ⟨(le_of_not_gt hx0), h⟩
                exact hderiv_zero_pos hLx
            simp [hz]))
  -- Fundamental theorem of calculus on `[0,x]`
  have hftc {x : ℝ} (hx0 : 0 ≤ x) : f x = ∫ y in 0..x, deriv f y := by
    have hF := intervalIntegral.integral_deriv_of_contDiffOn_Icc
      (f := f) (a := 0) (b := x) (ContDiff.contDiffOn hf) hx0
    -- hF : ∫ y in 0..x, deriv f y = f x - f 0
    rw [hf0] at hF
    simpa using hF.symm
  -- pointwise bound: for `x ∈ [0, L]`,  `(f x)^2 ≤ x * B`
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) L, (f x) ^ 2 ≤ x * B := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hxL : x ≤ L := hx.2
    have hcs := PoincareOne.cs_interval (a := 0) (b := x) hx0
      (h := fun y : ℝ => |deriv f y|) hfabscont.continuousOn (fun _ => abs_nonneg _)
    calc
      (f x) ^ 2 = (∫ y in 0..x, deriv f y) ^ 2 := by rw [hftc hx0]
      _ ≤ (∫ y in 0..x, |deriv f y|) ^ 2 := by
        have habs : |∫ y in 0..x, deriv f y| ≤ ∫ y in 0..x, |deriv f y| :=
          intervalIntegral.abs_integral_le_integral_abs hx0
        have hbnonneg : 0 ≤ ∫ y in 0..x, |deriv f y| :=
          intervalIntegral.integral_nonneg hx0 (fun y _ => abs_nonneg _)
        exact sq_le_sq.mpr (by rwa [abs_of_nonneg hbnonneg])
      _ ≤ (x - 0) * ∫ y in 0..x, (|deriv f y|) ^ 2 := hcs
      _ = x * ∫ y in 0..x, (deriv f y) ^ 2 := by
        have heq : (fun y : ℝ => (|deriv f y|) ^ 2) = fun y : ℝ => (deriv f y) ^ 2 := by
          funext y; rw [sq_abs]
        rw [heq]
        ring
      _ ≤ x * B := by
        have hmono : (∫ y in 0..x, (deriv f y) ^ 2) ≤ ∫ y in 0..L, (deriv f y) ^ 2 := by
          apply intervalIntegral.integral_mono_interval (c := 0) (d := L) (a := 0) (b := x)
          · exact le_rfl
          · exact hx0
          · exact hxL
          · exact (ae_of_all _ (fun _ => sq_nonneg _))
          · exact hfd2cont.intervalIntegrable 0 L
        exact mul_le_mul_of_nonneg_left hmono hx0
  -- integrate the pointwise bound over `x ∈ [0,L]`
  have hA_le : A ≤ (L ^ 2 / 2) * B := by
    dsimp [A]
    have hmono2 : (∫ x in 0..L, (f x) ^ 2) ≤ ∫ x in 0..L, x * B := by
      apply intervalIntegral.integral_mono_on hL.le
      · exact hf2cont.intervalIntegrable 0 L
      · exact (continuous_id.mul continuous_const).intervalIntegrable 0 L
      · exact hpt
    calc
      (∫ x in 0..L, (f x) ^ 2) ≤ ∫ x in 0..L, x * B := hmono2
      _ = (∫ x in 0..L, (fun y : ℝ => y) x) * B := by
        simpa using (intervalIntegral.integral_mul_const (r := B) (f := fun x : ℝ => x))
      _ = (L ^ 2 / 2) * B := by
        have hid : (∫ x in 0..L, (fun y : ℝ => y) x) = L ^ 2 / 2 := by simp
        rw [hid]
  -- multiply by the positive constant `2 / L²`
  have hLne : L ≠ 0 := ne_of_gt hL
  have htwo : (2 / L ^ 2) * ((L ^ 2 / 2) * B) = B := by
    have hc : (2 / L ^ 2) * (L ^ 2 / 2) = 1 := by
      field_simp [hLne]
    calc
      (2 / L ^ 2) * ((L ^ 2 / 2) * B) = ((2 / L ^ 2) * (L ^ 2 / 2)) * B := by ring
      _ = 1 * B := by rw [hc]
      _ = B := by ring
  have hAmul : (2 / L ^ 2) * A ≤ B := by
    have hm := mul_le_mul_of_nonneg_left hA_le (by positivity : 0 ≤ 2 / L ^ 2)
    rwa [htwo] at hm
  -- assemble the conclusion
  calc
    (2 / L ^ 2) * (∫ x : ℝ, (f x) ^ 2) = (2 / L ^ 2) * A := by rw [hAeq]
    _ ≤ B := hAmul
    _ = ∫ x : ℝ, (deriv f x) ^ 2 := hBeq

end BoseGases

end Submission
