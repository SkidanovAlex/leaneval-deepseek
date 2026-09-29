import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Basic

open MeasureTheory intervalIntegral
open Work.TMC16Core

noncomputable section

/-!
# The top Fourier coefficient of the Dirichlet determinant `pd`

For the continuant `pd α lam θ E (k+1)` (`= P_k(θ)`, the determinant of `(E - H)`
restricted to `k` sites with Dirichlet boundary conditions, AJ §9) we prove that the
Fourier coefficient of phase-frequency `k` in the phase variable `θ` has modulus
`|lam| ^ k`, and consequently that `|lam| ^ k` is a lower bound for the sup-norm of
`pd α lam θ E (k+1)` over `θ`.

The proof tracks the "top" Fourier coefficient through the three-term recurrence
`P_{k+2} = (E - A_k) P_{k+1} - P_k`, where `A_j(θ) = 2 lam cos(2π(θ + jα))`.
-/

/-- The Fourier kernel `e m θ = exp(-(2π i m θ))`. -/
def efac (m : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp ((-(2 * Real.pi * Complex.I * (m : ℝ))) * θ)

/-- `Om α = exp(2π i α)`, so that `Om α ^ j = exp(2π i j α)`. -/
def Om (α : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (α : ℂ))

/-- The `m`-th Fourier coefficient of `pd α lam · E (n+1)`:
`AF n m = ∫_0^1 pd α lam θ E (n+1) · e m θ dθ`. -/
def AF (α lam : ℝ) (E : ℂ) (n : ℕ) (m : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1, pd α lam θ E (n+1) * efac m θ

lemma efac_add (a b : ℤ) (θ : ℝ) : efac a θ * efac b θ = efac (a+b) θ := by
  unfold efac
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma continuous_efac (m : ℤ) : Continuous (fun θ => efac m θ) := by
  unfold efac; fun_prop

lemma norm_efac (m : ℤ) (θ : ℝ) : ‖efac m θ‖ = 1 := by
  unfold efac
  rw [Complex.norm_exp]
  have h : ((-(2 * Real.pi * Complex.I * (m:ℝ))) * θ).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [h, Real.exp_zero]

lemma exp_int_neg (m : ℤ) : Complex.exp (-(2 * Real.pi * Complex.I * (m:ℝ))) = 1 := by
  rw [show -(2 * Real.pi * Complex.I * (m:ℝ))
        = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) from by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I (-m)

lemma coeff_ne_zero (m : ℤ) (hm : m ≠ 0) : (-(2 * Real.pi * Complex.I * (m:ℝ)) : ℂ) ≠ 0 := by
  intro h
  have h2 := congrArg Complex.im h
  simp at h2
  exact hm h2

lemma af_integral_e (m : ℤ) : (∫ θ in (0:ℝ)..1, efac m θ) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [efac]
  · rw [if_neg hm]
    simp only [efac]
    rw [integral_exp_mul_complex (coeff_ne_zero m hm)]
    rw [show (-(2 * Real.pi * Complex.I * (m:ℝ)) : ℂ) * (1:ℝ)
          = -(2 * Real.pi * Complex.I * (m:ℝ)) from by push_cast; ring]
    rw [show (-(2 * Real.pi * Complex.I * (m:ℝ)) : ℂ) * (0:ℝ) = 0 from by push_cast; ring]
    rw [exp_int_neg m, Complex.exp_zero, sub_self, zero_div]

lemma Om_ne_zero (α : ℝ) : Om α ≠ 0 := by
  unfold Om; exact Complex.exp_ne_zero _

lemma norm_Om (α : ℝ) : ‖Om α‖ = 1 := by
  unfold Om
  rw [Complex.norm_exp]
  have h : (2 * Real.pi * Complex.I * (α:ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [h, Real.exp_zero]

/-- The expansion of the potential as sum of two exponentials. -/
lemma amoPot_cast (α lam : ℝ) (j : ℕ) (θ : ℝ) :
    ((amoPot α lam θ ((j:ℕ):ℤ) : ℝ) : ℂ)
      = lam * (Om α ^ j * efac (-1) θ + (Om α ^ j)⁻¹ * efac (1) θ) := by
  have h1 : Om α ^ j * efac (-1) θ
      = Complex.exp (Complex.ofReal (2 * Real.pi * (θ + (j:ℝ) * α)) * Complex.I) := by
    unfold Om efac
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have h2 : (Om α ^ j)⁻¹ * efac 1 θ
      = Complex.exp (-(Complex.ofReal (2 * Real.pi * (θ + (j:ℝ) * α)) * Complex.I)) := by
    unfold Om efac
    rw [← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [h1, h2]
  have hcos : Complex.exp (Complex.ofReal (2 * Real.pi * (θ + (j:ℝ) * α)) * Complex.I)
      + Complex.exp (-(Complex.ofReal (2 * Real.pi * (θ + (j:ℝ) * α)) * Complex.I))
      = 2 * (Real.cos (2 * Real.pi * (θ + (j:ℝ) * α)) : ℂ) := by
    rw [show -(Complex.ofReal (2 * Real.pi * (θ + (j:ℝ) * α)) * Complex.I)
          = Complex.ofReal (-(2 * Real.pi * (θ + (j:ℝ) * α))) * Complex.I from by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_cos]
    simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]; ring
  rw [hcos]
  unfold amoPot
  push_cast
  ring

/-- The potential times the Fourier kernel distributes over the two shifts. -/
lemma amoPot_mul_efac (α lam : ℝ) (j : ℕ) (m : ℤ) (θ : ℝ) :
    ((amoPot α lam θ ((j:ℕ):ℤ) : ℝ) : ℂ) * efac m θ
      = lam * (Om α ^ j * efac (m-1) θ + (Om α ^ j)⁻¹ * efac (m+1) θ) := by
  rw [amoPot_cast]
  have hA : Om α ^ j * efac (-1) θ * efac m θ = Om α ^ j * efac (m-1) θ := by
    rw [mul_assoc, efac_add, show ((-1:ℤ) + m) = m - 1 from by ring]
  have hB : (Om α ^ j)⁻¹ * efac 1 θ * efac m θ = (Om α ^ j)⁻¹ * efac (m+1) θ := by
    rw [mul_assoc, efac_add, show ((1:ℤ) + m) = m + 1 from by ring]
  rw [mul_assoc, add_mul, hA, hB]

lemma continuous_pd (α lam : ℝ) (E : ℂ) : ∀ n, Continuous (fun θ => pd α lam θ E n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa [pd] using continuous_const
    | 1 => simpa [pd] using continuous_const
    | k+2 =>
      have h2 : Continuous (fun θ => pd α lam θ E (k+1)) := ih (k+1) (by omega)
      have h1 : Continuous (fun θ => pd α lam θ E k) := ih k (by omega)
      have hp : Continuous (fun θ => (E - ((amoPot α lam θ ((k:ℕ):ℤ) : ℝ) : ℂ))) := by
        unfold amoPot; fun_prop
      rw [show (fun θ => pd α lam θ E (k+2))
            = (fun θ => (E - ((amoPot α lam θ ((k:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam θ E (k+1)
                - pd α lam θ E k)
            from by funext θ; rw [pd]]
      exact (hp.mul h2).sub h1

/-- Pointwise step for the recurrence of the Fourier coefficients. -/
lemma pd_step (α lam : ℝ) (E : ℂ) (j : ℕ) (m : ℤ) (θ : ℝ) :
    ((E - ((amoPot α lam θ ((j:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam θ E (j+1) - pd α lam θ E j) * efac m θ
      = E * (pd α lam θ E (j+1) * efac m θ)
        - lam * Om α ^ j * (pd α lam θ E (j+1) * efac (m-1) θ)
        - lam * (Om α ^ j)⁻¹ * (pd α lam θ E (j+1) * efac (m+1) θ)
        - pd α lam θ E j * efac m θ := by
  have hA2 : ((amoPot α lam θ ((j:ℕ):ℤ) : ℝ) : ℂ) * (pd α lam θ E (j+1) * efac m θ)
      = lam * Om α ^ j * (pd α lam θ E (j+1) * efac (m-1) θ)
        + lam * (Om α ^ j)⁻¹ * (pd α lam θ E (j+1) * efac (m+1) θ) := by
    rw [show ((amoPot α lam θ ((j:ℕ):ℤ) : ℝ) : ℂ) * (pd α lam θ E (j+1) * efac m θ)
          = pd α lam θ E (j+1) * (((amoPot α lam θ ((j:ℕ):ℤ) : ℝ) : ℂ) * efac m θ) from by ring]
    rw [amoPot_mul_efac]
    ring
  rw [show (((E - ((amoPot α lam θ ((j:ℕ):ℤ) : ℝ) : ℂ)) * pd α lam θ E (j+1)
          - pd α lam θ E j) * efac m θ)
        = E * (pd α lam θ E (j+1) * efac m θ)
          - ((amoPot α lam θ ((j:ℕ):ℤ) : ℝ) : ℂ) * (pd α lam θ E (j+1) * efac m θ)
          - pd α lam θ E j * efac m θ from by ring]
  rw [hA2]
  ring

/-- Integration of a four-term linear combination of continuous functions. -/
lemma int_sub_four {l r : ℝ} (f g h k : ℝ → ℂ) (A B C D : ℂ)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (hk : Continuous k) :
    (∫ θ in l..r, (A * f θ - B * g θ - C * h θ - D * k θ))
      = A * (∫ θ in l..r, f θ) - B * (∫ θ in l..r, g θ)
        - C * (∫ θ in l..r, h θ) - D * (∫ θ in l..r, k θ) := by
  have hfA : IntervalIntegrable (fun θ => A * f θ) volume l r := (continuous_const.mul hf).intervalIntegrable l r
  have hgB : IntervalIntegrable (fun θ => B * g θ) volume l r := (continuous_const.mul hg).intervalIntegrable l r
  have hhC : IntervalIntegrable (fun θ => C * h θ) volume l r := (continuous_const.mul hh).intervalIntegrable l r
  have hkD : IntervalIntegrable (fun θ => D * k θ) volume l r := (continuous_const.mul hk).intervalIntegrable l r
  have hAB : IntervalIntegrable (fun θ => A * f θ - B * g θ) volume l r := hfA.sub hgB
  have hCD : IntervalIntegrable (fun θ => C * h θ + D * k θ) volume l r := hhC.add hkD
  have e1 : (∫ θ in l..r, A * f θ) = A * (∫ θ in l..r, f θ) := intervalIntegral.integral_const_mul A f
  have e2 : (∫ θ in l..r, B * g θ) = B * (∫ θ in l..r, g θ) := intervalIntegral.integral_const_mul B g
  have e3 : (∫ θ in l..r, C * h θ) = C * (∫ θ in l..r, h θ) := intervalIntegral.integral_const_mul C h
  have e4 : (∫ θ in l..r, D * k θ) = D * (∫ θ in l..r, k θ) := intervalIntegral.integral_const_mul D k
  have h1 : (∫ θ in l..r, (A * f θ - B * g θ - C * h θ - D * k θ))
      = (∫ θ in l..r, (A * f θ - B * g θ)) - (∫ θ in l..r, (C * h θ + D * k θ)) := by
    rw [show (fun θ => A * f θ - B * g θ - C * h θ - D * k θ)
          = (fun θ => (A * f θ - B * g θ) - (C * h θ + D * k θ)) from by funext θ; ring]
    exact intervalIntegral.integral_sub hAB hCD
  have h2 : (∫ θ in l..r, (A * f θ - B * g θ)) = (∫ θ in l..r, A * f θ) - (∫ θ in l..r, B * g θ) :=
    intervalIntegral.integral_sub hfA hgB
  have h3 : (∫ θ in l..r, (C * h θ + D * k θ))
      = (∫ θ in l..r, C * h θ) + (∫ θ in l..r, D * k θ) :=
    intervalIntegral.integral_add hhC hkD
  rw [h1, h2, h3, e1, e2, e3, e4]
  ring

lemma AF_zero (α lam : ℝ) (E : ℂ) (m : ℤ) :
    AF α lam E 0 m = if m = 0 then 1 else 0 := by
  have h0 : AF α lam E 0 m = ∫ θ in (0:ℝ)..1, efac m θ := by
    unfold AF; simp only [pd, one_mul]
  rw [h0]; exact af_integral_e m

lemma AF_one (α lam : ℝ) (E : ℂ) (m : ℤ) :
    AF α lam E 1 m = E * AF α lam E 0 m - lam * AF α lam E 0 (m-1)
      - lam * AF α lam E 0 (m+1) := by
  have h0 : ∀ j : ℤ, AF α lam E 0 j = ∫ θ in (0:ℝ)..1, efac j θ := by
    intro j; unfold AF; simp only [pd, one_mul]
  have hpt : ∀ θ : ℝ, pd α lam θ E (1+1) * efac m θ
      = E * efac m θ - lam * (efac (m-1) θ + efac (m+1) θ) := by
    intro θ
    have h2 : pd α lam θ E (1+1) = E - ((amoPot α lam θ ((0:ℕ):ℤ) : ℝ) : ℂ) := by
      rw [show (1:ℕ)+1 = (0:ℕ)+2 from rfl]; simp only [pd]; ring
    rw [h2, sub_mul, amoPot_mul_efac]
    simp only [pow_zero, inv_one, one_mul]
  have hL : AF α lam E 1 m = ∫ θ in (0:ℝ)..1, (E * efac m θ - lam * (efac (m-1) θ + efac (m+1) θ)) := by
    unfold AF
    exact intervalIntegral.integral_congr (fun θ _ => hpt θ)
  rw [hL]
  have hsub : (∫ θ in (0:ℝ)..1, (E * efac m θ - lam * (efac (m-1) θ + efac (m+1) θ)))
      = (∫ θ in (0:ℝ)..1, E * efac m θ) - (∫ θ in (0:ℝ)..1, lam * (efac (m-1) θ + efac (m+1) θ)) :=
    intervalIntegral.integral_sub ((continuous_const.mul (continuous_efac m)).intervalIntegrable 0 1)
      ((continuous_const.mul ((continuous_efac (m-1)).add (continuous_efac (m+1)))).intervalIntegrable 0 1)
  rw [hsub, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hadd : (∫ θ in (0:ℝ)..1, (efac (m-1) θ + efac (m+1) θ))
      = (∫ θ in (0:ℝ)..1, efac (m-1) θ) + (∫ θ in (0:ℝ)..1, efac (m+1) θ) :=
    intervalIntegral.integral_add ((continuous_efac (m-1)).intervalIntegrable 0 1)
      ((continuous_efac (m+1)).intervalIntegrable 0 1)
  rw [hadd, ← h0 m, ← h0 (m-1), ← h0 (m+1)]
  ring

lemma AF_rec (α lam : ℝ) (E : ℂ) (k : ℕ) (m : ℤ) :
    AF α lam E (k+2) m = E * AF α lam E (k+1) m
      - lam * Om α ^ (k+1) * AF α lam E (k+1) (m-1)
      - lam * (Om α ^ (k+1))⁻¹ * AF α lam E (k+1) (m+1)
      - AF α lam E k m := by
  have hpt : ∀ θ : ℝ, pd α lam θ E (k+3) * efac m θ
      = E * (pd α lam θ E (k+2) * efac m θ)
        - lam * Om α ^ (k+1) * (pd α lam θ E (k+2) * efac (m-1) θ)
        - lam * (Om α ^ (k+1))⁻¹ * (pd α lam θ E (k+2) * efac (m+1) θ)
        - 1 * (pd α lam θ E (k+1) * efac m θ) := by
    intro θ
    rw [show (k+3:ℕ) = (k+1)+2 from by omega, pd]
    rw [pd_step α lam E (k+1) m θ]
    ring
  have hL : AF α lam E (k+2) m = ∫ θ in (0:ℝ)..1,
      (E * (pd α lam θ E (k+2) * efac m θ)
        - lam * Om α ^ (k+1) * (pd α lam θ E (k+2) * efac (m-1) θ)
        - lam * (Om α ^ (k+1))⁻¹ * (pd α lam θ E (k+2) * efac (m+1) θ)
        - 1 * (pd α lam θ E (k+1) * efac m θ)) := by
    unfold AF
    exact intervalIntegral.integral_congr (fun θ _ => hpt θ)
  have h4 : (∫ θ in (0:ℝ)..1,
      (E * (pd α lam θ E (k+2) * efac m θ)
        - lam * Om α ^ (k+1) * (pd α lam θ E (k+2) * efac (m-1) θ)
        - lam * (Om α ^ (k+1))⁻¹ * (pd α lam θ E (k+2) * efac (m+1) θ)
        - 1 * (pd α lam θ E (k+1) * efac m θ)))
      = E * (∫ θ in (0:ℝ)..1, pd α lam θ E (k+2) * efac m θ)
        - (lam * Om α ^ (k+1)) * (∫ θ in (0:ℝ)..1, pd α lam θ E (k+2) * efac (m-1) θ)
        - (lam * (Om α ^ (k+1))⁻¹) * (∫ θ in (0:ℝ)..1, pd α lam θ E (k+2) * efac (m+1) θ)
        - 1 * (∫ θ in (0:ℝ)..1, pd α lam θ E (k+1) * efac m θ) :=
    int_sub_four (l := 0) (r := 1)
      (fun θ => pd α lam θ E (k+2) * efac m θ)
      (fun θ => pd α lam θ E (k+2) * efac (m-1) θ)
      (fun θ => pd α lam θ E (k+2) * efac (m+1) θ)
      (fun θ => pd α lam θ E (k+1) * efac m θ)
      E (lam * Om α ^ (k+1)) (lam * (Om α ^ (k+1))⁻¹) 1
      ((continuous_pd α lam E (k+2)).mul (continuous_efac m))
      ((continuous_pd α lam E (k+2)).mul (continuous_efac (m-1)))
      ((continuous_pd α lam E (k+2)).mul (continuous_efac (m+1)))
      ((continuous_pd α lam E (k+1)).mul (continuous_efac m))
  rw [hL, h4]
  have e1 : (∫ θ in (0:ℝ)..1, pd α lam θ E (k+2) * efac m θ) = AF α lam E (k+1) m := rfl
  have e2 : (∫ θ in (0:ℝ)..1, pd α lam θ E (k+2) * efac (m-1) θ) = AF α lam E (k+1) (m-1) := rfl
  have e3 : (∫ θ in (0:ℝ)..1, pd α lam θ E (k+2) * efac (m+1) θ) = AF α lam E (k+1) (m+1) := rfl
  have e4 : (∫ θ in (0:ℝ)..1, pd α lam θ E (k+1) * efac m θ) = AF α lam E k m := rfl
  rw [e1, e2, e3, e4, one_mul]

/-- The Fourier coefficients of `pd (n+1)` vanish above frequency `n`, and the top
coefficient has modulus `|lam| ^ n`. -/
theorem AF_vanish_and_top (α lam : ℝ) (E : ℂ) : ∀ n : ℕ,
    (∀ m : ℤ, (n:ℤ) < |m| → AF α lam E n m = 0) ∧ ‖AF α lam E n n‖ = |lam|^n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      constructor
      · intro m hm
        have hm0 : m ≠ 0 := by rintro rfl; simp at hm
        rw [AF_zero, if_neg hm0]
      · rw [AF_zero]; simp
    | 1 =>
      constructor
      · intro m hm
        have hm0 : m ≠ 0 := by rintro rfl; simp at hm
        have hm1 : m - 1 ≠ 0 := by
          rintro h
          have h' : m = 1 := by omega
          rw [h'] at hm
          norm_num at hm
        have hm2 : m + 1 ≠ 0 := by
          rintro h
          have h' : m = -1 := by omega
          rw [h'] at hm
          norm_num at hm
        rw [AF_one, AF_zero, AF_zero, AF_zero, if_neg hm0, if_neg hm1, if_neg hm2]
        ring
      · rw [AF_one, AF_zero, AF_zero, AF_zero]; simp
    | k+2 =>
      have ih1 := ih (k+1) (by omega)
      have ih0 := ih k (by omega)
      constructor
      · intro m hm
        have hA : ((k+1:ℕ):ℤ) < |m| := by omega
        have hB : ((k+1:ℕ):ℤ) < |m-1| := by
          have h2 : |m| - 1 ≤ |m - 1| := by simpa using abs_sub_abs_le_abs_sub m (1:ℤ)
          omega
        have hC : ((k+1:ℕ):ℤ) < |m+1| := by
          have h2 : |m| - 1 ≤ |m + 1| := by simpa using abs_sub_abs_le_abs_sub m (-1:ℤ)
          omega
        have hD : ((k:ℕ):ℤ) < |m| := by omega
        rw [AF_rec, ih1.1 m hA, ih1.1 (m-1) hB, ih1.1 (m+1) hC, ih0.1 m hD]
        ring
      · have hk : ((k+2:ℕ):ℤ) - 1 = ((k+1:ℕ):ℤ) := by omega
        have hk2 : ((k+2:ℕ):ℤ) + 1 = ((k+3:ℕ):ℤ) := by omega
        have hA : ((k+1:ℕ):ℤ) < |(((k+2:ℕ):ℤ))| := by rw [abs_of_nonneg (by positivity)]; omega
        have hB : ((k+1:ℕ):ℤ) < |(((k+3:ℕ):ℤ))| := by rw [abs_of_nonneg (by positivity)]; omega
        have hD : ((k:ℕ):ℤ) < |(((k+2:ℕ):ℤ))| := by rw [abs_of_nonneg (by positivity)]; omega
        rw [AF_rec, hk, hk2]
        rw [ih1.1 (((k+2:ℕ):ℤ)) hA, ih1.1 (((k+3:ℕ):ℤ)) hB, ih0.1 (((k+2:ℕ):ℤ)) hD]
        have htop : ‖AF α lam E (k+1) (((k+1:ℕ):ℤ))‖ = |lam|^(k+1) := ih1.2
        rw [show E * 0 - lam * Om α ^ (k+1) * AF α lam E (k+1) (((k+1:ℕ):ℤ))
              - lam * (Om α ^ (k+1))⁻¹ * 0 - 0
              = -(lam * Om α ^ (k+1) * AF α lam E (k+1) (((k+1:ℕ):ℤ))) from by ring]
        rw [norm_neg]
        simp only [norm_mul, norm_pow, norm_Om, one_pow, Complex.norm_real, Real.norm_eq_abs]
        rw [htop, pow_succ]
        ring

theorem pd_fourier_large (α lam : ℝ) (E : ℂ) (k : ℕ) :
    (‖∫ θ in (0 : ℝ)..1, Work.TMC16Core.pd α lam θ E (k + 1) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * θ))‖ = |lam| ^ k) ∧
      (∃ θ : ℝ, |lam| ^ k ≤ ‖Work.TMC16Core.pd α lam θ E (k + 1)‖) := by
  have hmain := AF_vanish_and_top α lam E k
  constructor
  · have hEq : (∫ θ in (0:ℝ)..1, pd α lam θ E (k + 1)
          * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * θ))) = AF α lam E k ((k:ℤ)) := by
      unfold AF efac
      apply intervalIntegral.integral_congr
      intro θ _
      show pd α lam θ E (k + 1) * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * θ))
          = pd α lam θ E (k + 1) * Complex.exp ((-(2 * Real.pi * Complex.I * ((k:ℤ):ℝ))) * θ)
      rw [show (-(2 * Real.pi * Complex.I * (k : ℝ) * θ))
            = ((-(2 * Real.pi * Complex.I * ((k:ℤ):ℝ))) * θ) from by push_cast; ring]
    rw [hEq, hmain.2]
  · obtain ⟨θ₀, hθ₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 1))
      ((continuous_pd α lam E (k+1)).norm.continuousOn)
    refine ⟨θ₀, ?_⟩
    have hbound : ∀ θ ∈ Set.Icc (0:ℝ) 1,
        ‖pd α lam θ E (k+1)‖ ≤ ‖pd α lam θ₀ E (k+1)‖ := fun θ hθ => hmax hθ
    have h1 : IntervalIntegrable (fun θ => ‖pd α lam θ E (k+1)‖) volume 0 1 :=
      ((continuous_pd α lam E (k+1)).norm).intervalIntegrable 0 1
    have h2 : IntervalIntegrable (fun _ : ℝ => ‖pd α lam θ₀ E (k+1)‖) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    calc |lam|^k = ‖AF α lam E k ((k:ℤ))‖ := hmain.2.symm
      _ = ‖∫ θ in (0:ℝ)..1, pd α lam θ E (k+1) * efac ((k:ℤ)) θ‖ := rfl
      _ ≤ ∫ θ in (0:ℝ)..1, ‖pd α lam θ E (k+1) * efac ((k:ℤ)) θ‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ = ∫ θ in (0:ℝ)..1, ‖pd α lam θ E (k+1)‖ := by
            apply intervalIntegral.integral_congr
            intro θ _
            change ‖pd α lam θ E (k+1) * efac ((k:ℤ)) θ‖ = ‖pd α lam θ E (k+1)‖
            rw [norm_mul, norm_efac]
            ring
      _ ≤ ‖pd α lam θ₀ E (k+1)‖ := by
            have := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) h1 h2
              (fun x hx => hbound x hx)
            simpa using this

end

end Work.TMC16Core.Basic
