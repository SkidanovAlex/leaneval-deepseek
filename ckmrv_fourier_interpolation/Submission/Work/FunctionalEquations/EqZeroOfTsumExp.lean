import Mathlib
import Submission.Work.FunctionalEquations.Basic

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap
open MeasureTheory

/-- `e^{-2π y m} · e^{2π i m t} = e^{2π i m (t + i y)}`. -/
lemma exp_neg_mul_exp_eq (m : ℕ) (y t : ℝ) :
    Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m : ℝ))) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℝ) * (t : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℝ) * ((t : ℂ) + (y : ℂ) * Complex.I)) := by
  rw [← Complex.exp_add]; congr 1; ring_nf
  rw [pow_two, Complex.I_mul_I]; ring

/-- `‖e^{2π i m t}‖ = 1` for real `m`, `t`. -/
lemma norm_exp_two_pi_I (m t : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (t : ℂ))‖ = 1 := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (t : ℂ)
        = ((2 * Real.pi * m * t : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `‖e^{-2π i m t}‖ = 1` for real `m`, `t`. -/
lemma norm_exp_neg_two_pi_I (m t : ℝ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (t : ℂ)))‖ = 1 := by
  rw [Complex.exp_neg, norm_inv, norm_exp_two_pi_I, inv_one]

/-- `e^{2π i n} = 1` for an integer `n`. -/
lemma exp_two_pi_I_int (n : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) = 1 := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
        = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by ring]
  rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

/-- `e^{2π i u t} e^{-2π i v t} = e^{2π i (u - v) t}` for naturals `u`, `v`. -/
lemma exp_mul_exp_neg_int (u v : ℕ) (t : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℝ) * (t : ℂ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (v : ℝ) * (t : ℂ)))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((u : ℤ) - (v : ℤ) : ℤ) : ℂ) * (t : ℂ)) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- Orthogonality of the characters on `(0,1]`: `∫₀¹ b e^{2π i n t} dt = b δ_{n0}`. -/
lemma integral_char (b : ℂ) (n : ℤ) :
    ∫ t in (0 : ℝ)..1, b * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))
      = b * (if n = 0 then 1 else 0) := by
  have hinner : ∫ t in (0 : ℝ)..1,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) = if n = 0 then 1 else 0 := by
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg hn]
      have hc : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ≠ 0 := by
        apply mul_ne_zero
        · apply mul_ne_zero
          · apply mul_ne_zero
            · exact two_ne_zero
            · exact_mod_cast Real.pi_ne_zero
          · exact Complex.I_ne_zero
        · exact_mod_cast hn
      rw [show (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)))
            = (fun t : ℝ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * (t : ℂ))) from by
              funext t; rw [mul_assoc]]
      rw [integral_exp_mul_complex hc]
      simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
            = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by ring]
      rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
      simp
  rw [intervalIntegral.integral_const_mul, hinner]

/-- The two-sided integral over `(0,1]` of `(b e^{2π i u t}) e^{-2π i v t}` is `b δ_{uv}`. -/
lemma integral_fm (b : ℂ) (u v : ℕ) :
    ∫ a : ℝ, (b * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℝ) * (a : ℂ))) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (v : ℝ) * (a : ℂ)))
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = b * (if u = v then 1 else 0) := by
  have hexp : (fun a : ℝ => (b * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (u : ℝ) * (a : ℂ))) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (v : ℝ) * (a : ℂ))))
      = (fun t : ℝ => b * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((u : ℤ) - (v : ℤ) : ℤ) : ℂ) * (t : ℂ))) := by
    funext t
    rw [mul_assoc, exp_mul_exp_neg_int u v t]
  rw [hexp, ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [integral_char]
  congr 1
  rcases eq_or_ne u v with h | h
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hc
    exact h (by have : (u : ℤ) = (v : ℤ) := sub_eq_zero.mp hc; exact_mod_cast this)

theorem EqZeroOfTsumExp {c : Set.Ici (1 : ℕ) → ℂ} {y : ℝ} (hy : 0 < y)
    (hsum : Summable fun m : Set.Ici (1 : ℕ) =>
      c m * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ))))
    (hzero : ∀ t : ℝ, ∑' m : Set.Ici (1 : ℕ), c m * Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * ((t : ℂ) + (y : ℂ) * Complex.I)) = 0) :
    ∀ m, c m = 0 := by
  let b : Set.Ici (1 : ℕ) → ℂ := fun m =>
    c m * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ)))
  have hbsum : Summable b := hsum
  -- Rewrite the vanishing hypothesis into a Fourier series with coefficients `b`.
  have hz : ∀ t : ℝ, ∑' m : Set.Ici (1 : ℕ),
      b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (t : ℂ)) = 0 := by
    intro t
    rw [← hzero t]
    apply tsum_congr
    intro m
    change c m * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (m.1 : ℝ))) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (t : ℂ))
        = c m * Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * ((t : ℂ) + (y : ℂ) * Complex.I))
    rw [mul_assoc, exp_neg_mul_exp_eq m.1 y t]
  intro k
  let fm : Set.Ici (1 : ℕ) → ℝ → ℂ := fun m t =>
    (b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (t : ℂ))) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.1 : ℝ) * (t : ℂ)))
  -- The pointwise Fourier sum is identically zero.
  have hzfm : ∀ t : ℝ, ∑' m : Set.Ici (1 : ℕ), fm m t = 0 := by
    intro t
    rw [show (∑' m : Set.Ici (1 : ℕ), fm m t)
        = (∑' m : Set.Ici (1 : ℕ),
            b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (t : ℂ)))
          * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.1 : ℝ) * (t : ℂ))) from by
      rw [← tsum_mul_right]]
    rw [hz t, zero_mul]
  -- Integrability of each summand.
  have hint : ∀ m : Set.Ici (1 : ℕ),
      Integrable (fm m) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro m
    have hcont : Continuous (fm m) := by
      rw [show fm m = (fun t : ℝ =>
          (b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (t : ℂ))) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.1 : ℝ) * (t : ℂ)))) from rfl]
      fun_prop
    exact (hcont.continuousOn.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set
      (fun x hx => ⟨hx.1.le, hx.2⟩)
  -- The norm integrals are summable, with value `‖b m‖`.
  have hterm : ∀ m : Set.Ici (1 : ℕ),
      ∫ a, ‖fm m a‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = ‖b m‖ := by
    intro m
    have hpt : ∀ a : ℝ, ‖fm m a‖ = ‖b m‖ := by
      intro a
      rw [show fm m a = (b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (a : ℂ))) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.1 : ℝ) * (a : ℂ))) from rfl]
      rw [norm_mul, norm_mul, norm_exp_two_pi_I, norm_exp_neg_two_pi_I]
      ring
    rw [show (fun a : ℝ => ‖fm m a‖) = (fun _ : ℝ => ‖b m‖) from funext hpt]
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real]
  have hF_sum : Summable (fun m : Set.Ici (1 : ℕ) =>
      ∫ a, ‖fm m a‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    hbsum.norm.congr (fun m => (hterm m).symm)
  -- Interchange the integral with the series.
  have hHL := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hF_sum
  have hintzero : ∫ a, ∑' m : Set.Ici (1 : ℕ), fm m a
      ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = 0 := by
    rw [show (fun a : ℝ => ∑' m : Set.Ici (1 : ℕ), fm m a) = 0 from funext hzfm]
    simp
  have hHL0 : HasSum (fun m : Set.Ici (1 : ℕ) =>
      ∫ a, fm m a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) 0 := by
    rw [← hintzero]; exact hHL
  have htsum : ∑' m : Set.Ici (1 : ℕ),
      ∫ a, fm m a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = 0 := hHL0.tsum_eq
  -- Evaluate each integral.
  have hfm_int : ∀ m : Set.Ici (1 : ℕ),
      ∫ a, fm m a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = b m * (if m = k then 1 else 0) := by
    intro m
    have hexp : (fun a : ℝ => fm m a) = (fun a : ℝ =>
        (b m * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℝ) * (a : ℂ))) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.1 : ℝ) * (a : ℂ)))) := by
      funext a; rfl
    rw [hexp, integral_fm]
    congr 1
    rcases eq_or_ne m k with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc => h (Subtype.ext hc))]
  -- Sum the evaluated integrals.
  have hcongr : (∑' m : Set.Ici (1 : ℕ), b m * (if m = k then 1 else 0))
      = ∑' m : Set.Ici (1 : ℕ),
          ∫ a, fm m a ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply tsum_congr
    intro m
    exact (hfm_int m).symm
  have hbk : b k = 0 := by
    have h1 : (∑' m : Set.Ici (1 : ℕ), b m * (if m = k then 1 else 0)) = b k := by
      rw [tsum_eq_single k (fun m hm => by rw [if_neg hm, mul_zero])]
      simp
    rw [h1] at hcongr
    rw [htsum] at hcongr
    exact hcongr
  -- Extract `c k = 0`.
  have hbk_eq : b k = c k * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ) * (k.1 : ℝ))) := rfl
  rw [hbk_eq] at hbk
  rcases mul_eq_zero.mp hbk with h | h
  · exact h
  · exact absurd h (Complex.exp_ne_zero _)

end Work.FunctionalEquations
