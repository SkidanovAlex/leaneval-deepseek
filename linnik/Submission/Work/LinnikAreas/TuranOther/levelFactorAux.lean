/-
# Auxiliary lemmas for the level factor `1 - a·p^{-s}`

Supporting lemmas for `levelFactorDerivZeroSum`:
* the affine chain rule for `iteratedDeriv`;
* the derivative, zero set and vanishing order of the level factor;
* the closed form of its logarithmic derivative;
* generalities on `tsum` supported on an injected copy of `ℤ`.
-/
import Mathlib
import Submission.Work.LinnikAreas.TuranOther.levelFactorDefs

noncomputable section

open scoped BigOperators Topology
open Filter

namespace Work.LinnikAreas.TuranOther

/-! ### The iterated-derivative chain rule for an affine argument -/

theorem iteratedDeriv_comp_const_mul_add {F : ℂ → ℂ} (c b x : ℂ) (n : ℕ)
    (hF : AnalyticAt ℂ F (c * x + b)) :
    iteratedDeriv n (fun s : ℂ => F (c * s + b)) x = c ^ n * iteratedDeriv n F (c * x + b) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hAn : AnalyticAt ℂ (iteratedDeriv n F) (c * x + b) := by
      rw [iteratedDeriv_eq_iterate]
      suffices h : ∀ m, AnalyticAt ℂ (deriv^[m] F) (c * x + b) by exact h n
      intro m
      induction m with
      | zero => simpa using hF
      | succ m ih2 => simpa [Function.iterate_succ_apply'] using ih2.deriv
    have htend : Tendsto (fun y : ℂ => c * y + b) (𝓝 x) (𝓝 (c * x + b)) :=
      (by fun_prop : Continuous (fun y : ℂ => c * y + b)).continuousAt
    have hev : (iteratedDeriv n (fun s : ℂ => F (c * s + b))) =ᶠ[𝓝 x]
        (fun s => c ^ n * iteratedDeriv n F (c * s + b)) := by
      filter_upwards [htend.eventually hF.eventually_analyticAt] with y hy
      exact ih y hy
    rw [hev.deriv_eq]
    rw [deriv_const_mul_field]
    have hd1 : DifferentiableAt ℂ (iteratedDeriv n F) (c * x + b) := hAn.differentiableAt
    have hd2 : DifferentiableAt ℂ (fun s : ℂ => c * s + b) x := by fun_prop
    rw [show (fun s : ℂ => iteratedDeriv n F (c * s + b))
          = (iteratedDeriv n F ∘ (fun s : ℂ => c * s + b)) from rfl, deriv_comp x hd1 hd2]
    have hlin : deriv (fun s : ℂ => c * s + b) x = c := by
      have hd : HasDerivAt (fun s : ℂ => c * s + b) c x := by
        have := (hasDerivAt_id x).const_mul c
        simpa using this.add_const b
      rw [hd.deriv]
    rw [hlin]
    rw [show deriv (iteratedDeriv n F) (c * x + b) = iteratedDeriv (n + 1) F (c * x + b) by
      rw [iteratedDeriv_succ]]
    ring

/-! ### `tsum` over a set contained in the range of an injection -/

theorem tsum_eq_tsum_of_supported {f : ℂ → ℂ} {φ : ℤ → ℂ} (hφ : Function.Injective φ)
    (hsupp : ∀ u : ℂ, (∀ n : ℤ, u ≠ φ n) → f u = 0)
    (hf : Summable fun n : ℤ => f (φ n)) :
    Summable f ∧ (∑' u : ℂ, f u) = ∑' n : ℤ, f (φ n) := by
  have hsupp' : Function.support f ⊆ Set.range φ := by
    intro u hu
    rw [Function.mem_support] at hu
    by_contra h
    exact hu (hsupp u (fun n hn => h ⟨n, hn.symm⟩))
  have key : HasSum f (∑' n : ℤ, f (φ n)) := by
    refine (hasSum_iff_hasSum_of_ne_zero_bij
      (f := f) (g := fun n : ℤ => f (φ n))
      (i := fun x : {n : ℤ // (fun n : ℤ => f (φ n)) n ≠ 0} => φ x.1) ?_ ?_ ?_).mpr hf.hasSum
    · intro x y hxy
      exact Subtype.ext (hφ hxy)
    · intro u hu
      obtain ⟨n, hn⟩ := hsupp' hu
      exact ⟨⟨n, by show f (φ n) ≠ 0; rw [hn]; exact hu⟩, hn⟩
    · intro x
      rfl
  exact ⟨key.summable, key.tsum_eq⟩

/-! ### Summability of the translated lattice `∑ (z + n)^{-(k+1)}` -/

theorem summable_int_add_zpow {z : ℂ} {k : ℕ} (hk : 1 ≤ k) :
    Summable fun n : ℤ => (z + (n : ℂ)) ^ (-(k + 1) : ℤ) := by
  have h := EisensteinSeries.linear_right_summable z 1 (k := ((k : ℤ) + 1)) (by omega)
  have he : (-(k + 1) : ℤ) = -(((k : ℤ) + 1)) := by push_cast; ring
  refine h.congr (fun n => ?_)
  rw [he, zpow_neg]
  congr 1
  push_cast
  ring_nf

/-! ### The level factor: derivative, zeros, order and logarithmic derivative -/

lemma deriv_lvlE (p : ℕ) (a : ℂ) (s : ℂ) :
    deriv (lvlE p a) s = a * (lvlL p : ℂ) * Complex.exp (-((lvlL p : ℂ) * s)) := by
  have h1 : HasDerivAt (fun t : ℂ => -((lvlL p : ℂ) * t)) (-(lvlL p : ℂ)) s := by
    simpa using (hasDerivAt_id s).const_mul (-(lvlL p : ℂ))
  have h2 : HasDerivAt (fun t : ℂ => Complex.exp (-((lvlL p : ℂ) * t)))
      (Complex.exp (-((lvlL p : ℂ) * s)) * (-(lvlL p : ℂ))) s := by simpa using h1.cexp
  have h3 : HasDerivAt (fun t : ℂ => a * Complex.exp (-((lvlL p : ℂ) * t)))
      (a * (Complex.exp (-((lvlL p : ℂ) * s)) * (-(lvlL p : ℂ)))) s := h2.const_mul a
  have h4 : HasDerivAt (lvlE p a)
      (-(a * (Complex.exp (-((lvlL p : ℂ) * s)) * (-(lvlL p : ℂ))))) s := h3.const_sub 1
  rw [h4.deriv]; ring

lemma nei_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) : a ≠ 0 := by
  intro h; rw [h, norm_zero] at ha; norm_num at ha

lemma lvlE_zero_iff {p : ℕ} (hp : p.Prime) (a : ℂ) (ha : ‖a‖ = 1) (u : ℂ) :
    lvlE p a u = 0 ↔ ∃ n : ℤ, u = lvlZero p a n := by
  have hL := lvlL_ne_zero hp
  have ha0 : a ≠ 0 := nei_of_norm_eq_one ha
  have hLc : (lvlL p : ℂ) ≠ 0 := by exact_mod_cast hL
  constructor
  · intro hu
    rw [lvlE_apply] at hu
    have h1 : a * Complex.exp (-((lvlL p : ℂ) * u)) = 1 := by
      have := sub_eq_zero.mp hu; rw [eq_comm] at this; exact this
    have h2a : Complex.exp (-((lvlL p : ℂ) * u)) = a⁻¹ := by
      have hh := congrArg (fun z => a⁻¹ * z) h1
      simp only [mul_one] at hh
      rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul] at hh
      exact hh
    have h2b : Complex.exp (-((lvlL p : ℂ) * lvlRoot p a)) = a⁻¹ := by
      rw [Complex.exp_neg, exp_lvlL_mul_lvlRoot hL ha0]
    obtain ⟨n, hn⟩ := (Complex.exp_eq_exp_iff_exists_int
      (x := -((lvlL p : ℂ) * u)) (y := -((lvlL p : ℂ) * lvlRoot p a))).mp (h2a.trans h2b.symm)
    refine ⟨-n, ?_⟩
    apply mul_left_cancel₀ hLc
    have hR : (lvlL p : ℂ) * lvlZero p a (-n)
        = (lvlL p : ℂ) * lvlRoot p a - (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [lvlZero, mul_add]
      rw [show (lvlL p : ℂ) * ((↑(-n) : ℂ) * lvlPeriod p)
            = ((↑(-n) : ℂ)) * ((lvlL p : ℂ) * lvlPeriod p) by ring]
      rw [lvlL_mul_lvlPeriod hL]
      push_cast; ring
    have h3 : (lvlL p : ℂ) * u
        = (lvlL p : ℂ) * lvlRoot p a - (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      linear_combination -hn
    rw [hR, h3]
  · rintro ⟨n, rfl⟩
    exact lvlE_lvlZero hL ha0 n

lemma analyticOrderNatAt_lvlE_lvlZero {p : ℕ} (hp : p.Prime) (a : ℂ) (ha : ‖a‖ = 1)
    (n : ℤ) :
    analyticOrderNatAt (lvlE p a) (lvlZero p a n) = 1 := by
  have hL := lvlL_ne_zero hp
  have ha0 : a ≠ 0 := nei_of_norm_eq_one ha
  have hLc : (lvlL p : ℂ) ≠ 0 := by exact_mod_cast hL
  have hz : lvlE p a (lvlZero p a n) = 0 := lvlE_lvlZero hL ha0 n
  have hd : deriv (lvlE p a) (lvlZero p a n) ≠ 0 := by
    rw [deriv_lvlE, Complex.exp_neg, exp_lvlL_mul_lvlZero hL ha0 n]
    exact mul_ne_zero (mul_ne_zero ha0 hLc) (inv_ne_zero ha0)
  have h1 : analyticOrderAt (lvlE p a) (lvlZero p a n) = 1 :=
    AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (analyticAt_lvlE p a _) hz hd
  rw [analyticOrderNatAt, h1]
  exact ENat.toNat_one

lemma logDeriv_lvlE {p : ℕ} (hp : p.Prime) (a : ℂ) (ha : ‖a‖ = 1) (s : ℂ)
    (h : lvlE p a s ≠ 0) :
    logDeriv (lvlE p a) s
      = lvlC p * (Real.pi * Complex.cot (Real.pi * (lvlC p * (s - lvlRoot p a))))
        - (lvlL p : ℂ) / 2 := by
  have hL := lvlL_ne_zero hp
  have ha0 : a ≠ 0 := nei_of_norm_eq_one ha
  have hw2 : a * Complex.exp (-((lvlL p : ℂ) * s))
      = Complex.exp (-((lvlL p : ℂ) * (s - lvlRoot p a))) := by
    rw [show -((lvlL p : ℂ) * (s - lvlRoot p a))
          = -((lvlL p : ℂ) * s) + (lvlL p : ℂ) * lvlRoot p a by ring]
    rw [Complex.exp_add, exp_lvlL_mul_lvlRoot hL ha0]
    ring
  have hw1 : Complex.exp (-((lvlL p : ℂ) * (s - lvlRoot p a))) ≠ 1 := by
    intro hh
    apply h
    rw [lvlE_apply, hw2, hh]
    ring
  rw [logDeriv, Pi.div_apply, deriv_lvlE]
  rw [show a * (lvlL p : ℂ) * Complex.exp (-((lvlL p : ℂ) * s))
        = (lvlL p : ℂ) * (a * Complex.exp (-((lvlL p : ℂ) * s))) by ring]
  rw [lvlE_apply, hw2]
  rw [Complex.cot_pi_eq_exp_ratio]
  rw [show Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (lvlC p * (s - lvlRoot p a)))
        = Complex.exp (-((lvlL p : ℂ) * (s - lvlRoot p a))) by rw [two_pi_I_mul_lvlC_mul]]
  rw [lvlC]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf

end Work.LinnikAreas.TuranOther
