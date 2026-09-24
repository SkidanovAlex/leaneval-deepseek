import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.periodization_identity

/-!
# The shifted lattice sum of `‖Fhat h‖²` is maximal at the lattice points

For `h : ℝ → ℝ` continuous, nonnegative and compactly supported, and every `u : ℝ`,

`∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + u)‖ ^ 2 ≤ ∑' ℓ : ℤ, ‖Fhat h (ℓ : ℝ)‖ ^ 2`,

i.e. a shift of the sampling lattice never increases the sampled `L²`-mass of `Fhat h`.

## The mathematics

Both sides are `L²`-masses of periodizations.  For `g u = e(-u t) h t` (`e(x) = exp(2πix)`) we have
`∫ y, e(-n y) g y = Fhat h (n+u)`, and the classical "sampling = periodization" identity (Parseval
on the circle for the `1`-periodic periodization, which here is a *finite* sum because `h` is
compactly supported) gives

`∑' n, ‖Fhat h (n+u)‖² = ∫_0^1 ‖∑_ℓ g (x+ℓ)‖² dx`.

Since

`∑_ℓ g (x+ℓ) = ∑_ℓ e(-u(x+ℓ)) h (x+ℓ) = e(-ux) · ∑_ℓ e(-uℓ) h (x+ℓ)`

is a unimodular factor times a sum of *nonnegative* terms whose moduli are `h (x+ℓ)`, the
triangle inequality gives `‖∑_ℓ g (x+ℓ)‖ ≤ ∑_ℓ h (x+ℓ)`, and the latter periodization has
`L²`-mass `∑' n, ‖Fhat h n‖²` by the real periodization Parseval `per_integral_sq`.

The two ingredients used below are: a complex-valued version of the "periodization Fourier
coefficient" identity (determined by the finite sum representation), and `per_integral_sq`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-! ## Elementary facts about `efun` -/

private lemma cont_efun' : Continuous efun := by unfold efun; fun_prop

private lemma efun_int' (z : ℤ) : efun (z : ℝ) = 1 := by
  rw [efun]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((z : ℝ) : ℂ))
        = (z : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I z

private lemma Fhat_eq_integral' (f : ℝ → ℝ) (ξ : ℝ) :
    Fhat f ξ = ∫ y : ℝ, efun (-(ξ * y)) * ((f y : ℝ) : ℂ) := by
  rw [Fhat, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Real.inner_apply, smul_eq_mul, efun]
  congr 1
  push_cast
  ring_nf

/-! ## The Fourier coefficient of a finite periodization (complex-valued version) -/

private lemma single_term_shift {g : ℝ → ℂ} (n : ℤ) (z : ℝ) :
    ∫ x in (0:ℝ)..1, efun (-((n:ℝ)*x)) * g (x + z)
      = ∫ y in z..(z+1), efun (-((n:ℝ) * (y - z))) * g y := by
  set H : ℝ → ℂ := fun y => efun (-((n:ℝ) * (y - z))) * g y with hH
  have hid : (fun x : ℝ => efun (-((n:ℝ)*x)) * g (x + z)) = fun x : ℝ => H (z + x) := by
    funext x
    show efun (-((n:ℝ)*x)) * g (x + z) = efun (-((n:ℝ) * (z + x - z))) * g (z + x)
    rw [add_comm x z]
    congr 1
    ring_nf
  rw [hid, intervalIntegral.integral_comp_add_left H z]
  simp

/-- The `n`-th Fourier coefficient of the `(2K+1)`-term periodisation of a complex-valued `g`
(vanishing off `[-R,R]`) equals the Fourier integral `∫ g(y) e(-ny) dy`. -/
private lemma fourierCoeff_finsum_eq_integral {g : ℝ → ℂ} (hg : Continuous g) {R : ℝ}
    (hRg : ∀ y : ℝ, R < |y| → g y = 0) {K : ℕ} (hK : R ≤ (K:ℝ)) (n : ℤ) :
    ∫ x in (0:ℝ)..1, efun (-((n:ℝ) * x)) *
        (∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ))))
      = ∫ y : ℝ, efun (-((n:ℝ) * y)) * g y := by
  set Ψ : ℝ → ℂ := fun y => efun (-((n:ℝ) * y)) * g y with hΨ
  set a : ℕ → ℝ := fun j => (j:ℝ) - (K:ℝ) with ha
  have hΨc : Continuous Ψ := by
    rw [hΨ]
    exact (cont_efun'.comp (by fun_prop)).mul hg
  have hsplit : (∫ x in (0:ℝ)..1, efun (-((n:ℝ) * x)) *
        (∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ)))))
      = ∑ j ∈ Finset.range (2*K+1),
          ∫ x in (0:ℝ)..1, efun (-((n:ℝ) * x)) * g (x + ((j:ℤ) - (K:ℤ))) := by
    have hrw : (fun x : ℝ => efun (-((n:ℝ) * x)) *
          (∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ)))))
        = fun x : ℝ => ∑ j ∈ Finset.range (2*K+1),
            efun (-((n:ℝ) * x)) * g (x + ((j:ℤ) - (K:ℤ))) := by
      funext x
      rw [Finset.mul_sum]
    rw [hrw, intervalIntegral.integral_finsetSum]
    intro i hi
    exact Continuous.intervalIntegrable ((cont_efun'.comp (by fun_prop)).mul
      (hg.comp (by fun_prop))) 0 1
  have hterm : ∀ j ∈ Finset.range (2*K+1),
      (∫ x in (0:ℝ)..1, efun (-((n:ℝ) * x)) * g (x + ((j:ℤ) - (K:ℤ))))
        = ∫ y in a j..a (j+1), Ψ y := by
    intro j hj
    have hgen := single_term_shift (g := g) n (((j:ℤ):ℝ) - ((K:ℤ):ℝ))
    rw [hgen]
    have hz : (((j:ℤ):ℝ) - ((K:ℤ):ℝ)) = a j := by simp only [ha]; push_cast; ring
    rw [hz]
    have hz1 : a j + 1 = a (j+1) := by simp only [ha]; push_cast; ring_nf
    rw [hz1]
    refine intervalIntegral.integral_congr fun y hy => ?_
    simp only [hΨ]
    have hexp : -((n:ℝ) * (y - ((j:ℝ) - (K:ℝ))))
        = -((n:ℝ) * y) + (((n * ((j:ℤ) - (K:ℤ))) : ℤ) : ℝ) := by
      push_cast; ring
    rw [hexp, efun_add, efun_int', mul_one]
  rw [hsplit, Finset.sum_congr rfl hterm]
  rw [intervalIntegral.sum_integral_adjacent_intervals (f := Ψ) (a := a) (n := 2*K+1)
      (fun k hk => hΨc.intervalIntegrable _ _)]
  have ha0 : a 0 = -(K:ℝ) := by simp only [ha]; push_cast; ring
  have haN : a (2*K+1) = (K:ℝ)+1 := by simp only [ha]; push_cast; ring
  have hle : a 0 ≤ a (2*K+1) := by rw [ha0, haN]; linarith
  have hsupp : ∀ y ∉ Set.Icc (a 0) (a (2*K+1)), Ψ y = 0 := by
    intro y hy
    have hzero : g y = 0 := by
      apply hRg
      simp only [Set.mem_Icc, not_and_or, not_le] at hy
      rcases hy with h | h
      · rw [ha0] at h
        have h2 : y < -R := by linarith
        rw [abs_of_neg (by linarith)]; linarith
      · rw [haN] at h
        have h2 : R < y := by linarith
        rw [abs_of_pos (by linarith)]; linarith
    rw [hΨ]; simp only; rw [hzero]; simp
  have hfin : ∫ y in a 0..a (2*K+1), Ψ y = ∫ y, Ψ y := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp
  rw [hfin]

/-- **Sampling = periodization**, complex-valued form: the sum of the squared moduli of the
Fourier integrals of `g` at the integers equals the `L²`-mass of one period of the finite
periodization of `g` (Parseval on the circle). -/
private lemma tsum_fourier_integral_sq_eq_periodization_integral {g : ℝ → ℂ} (hg : Continuous g)
    {R : ℝ} (_hR₀ : 0 ≤ R) (hRg : ∀ y : ℝ, R < |y| → g y = 0) {K : ℕ} (hK : R ≤ (K:ℝ)) :
    ∑' n : ℤ, ‖∫ y : ℝ, efun (-((n:ℝ) * y)) * g y‖ ^ 2
      = ∫ x in (0:ℝ)..1, ‖∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ)))‖ ^ 2 := by
  set P : ℝ → ℂ := fun x => ∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ))) with hP
  have hPc : Continuous P := by rw [hP]; fun_prop
  have hmem : MemLp P 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hPc.continuousOn
    refine MemLp.of_bound hPc.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x (Set.Ioc_subset_Icc_self hx)
  have hcoeff : ∀ i : ℤ, fourierCoeffOn (by norm_num : (0:ℝ) < 1) P i
      = ∫ y : ℝ, efun (-((i:ℝ) * y)) * g y := by
    intro i
    rw [fourierCoeffOn_eq_integral]
    simp only [sub_zero, div_one, one_smul]
    rw [← fourierCoeff_finsum_eq_integral hg hRg hK i]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [smul_eq_mul, fourier_coe_apply, efun]
    simp only [hP]
    congr 1
    push_cast; ring_nf
  have h1 : ∑' n : ℤ, ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) P n‖ ^ 2
      = ∑' n : ℤ, ‖∫ y : ℝ, efun (-((n:ℝ) * y)) * g y‖ ^ 2 :=
    tsum_congr (fun n => by rw [hcoeff n])
  rw [← h1, tsum_sq_fourierCoeffOn (by norm_num : (0:ℝ) < 1) hmem]
  rw [hP]
  simp

/-! ## The main inequality -/

theorem tsum_shift_fhat_sq_le {h : ℝ → ℝ} (hcont : Continuous h) (hnn : ∀ t, 0 ≤ h t)
    (hcs : HasCompactSupport h) (u : ℝ) :
    ∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + u)‖ ^ 2 ≤ ∑' ℓ : ℤ, ‖Fhat h (ℓ : ℝ)‖ ^ 2 := by
  obtain ⟨R, hR₀, hRf⟩ := exists_support_bound hcs
  obtain ⟨K, hK⟩ : ∃ K : ℕ, R + 1 ≤ (K : ℝ) := ⟨⌈R + 1⌉₊, Nat.le_ceil _⟩
  have hK' : R ≤ (K : ℝ) := by linarith
  -- the twisted function
  set g : ℝ → ℂ := fun t => efun (-(t * u)) * ((h t : ℝ) : ℂ) with hg_def
  have hgc : Continuous g := by
    rw [hg_def]
    exact (cont_efun'.comp (by fun_prop)).mul (Complex.continuous_ofReal.comp hcont)
  have hgsupp : ∀ y : ℝ, R < |y| → g y = 0 := by
    intro y hy
    rw [hg_def]
    simp only []
    rw [hRf y hy]
    simp
  -- Step 1: the LHS is the sum of the Fourier integrals of `g`
  have hLHS : (∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + u)‖ ^ 2)
      = ∑' n : ℤ, ‖∫ y : ℝ, efun (-((n:ℝ) * y)) * g y‖ ^ 2 := by
    refine tsum_congr fun n => ?_
    have hkey : Fhat h ((n:ℝ) + u) = ∫ y : ℝ, efun (-((n:ℝ) * y)) * g y := by
      rw [Fhat_eq_integral' h ((n:ℝ) + u)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      rw [hg_def]
      simp only []
      rw [show -(((n:ℝ) + u) * y) = (-((n:ℝ) * y)) + (-(y * u)) by ring, efun_add]
      ring
    rw [hkey]
  rw [hLHS, tsum_fourier_integral_sq_eq_periodization_integral hgc hR₀ hgsupp hK']
  -- Step 2: pointwise domination by the untwisted periodization
  have hpt : ∀ x : ℝ, ‖∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ)))‖ ^ 2
      ≤ (∑ j ∈ Finset.range (2*K+1), h (x + ((j:ℤ) - (K:ℤ)))) ^ 2 := by
    intro x
    have h1 : ‖∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ)))‖
        ≤ ∑ j ∈ Finset.range (2*K+1), h (x + ((j:ℤ) - (K:ℤ))) := by
      calc ‖∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ)))‖
          ≤ ∑ j ∈ Finset.range (2*K+1), ‖g (x + ((j:ℤ) - (K:ℤ)))‖ := norm_sum_le _ _
        _ = ∑ j ∈ Finset.range (2*K+1), h (x + ((j:ℤ) - (K:ℤ))) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hg_def]
            simp only []
            rw [norm_mul, norm_efun, one_mul, Complex.norm_of_nonneg (hnn _)]
    simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) h1
  have hInt1 : IntervalIntegrable
      (fun x : ℝ => ‖∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ)))‖ ^ 2) volume
      (0:ℝ) 1 := by
    have hc : Continuous
        (fun x : ℝ => ‖∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ)))‖ ^ 2) := by
      fun_prop
    exact hc.intervalIntegrable _ _
  have hInt2 : IntervalIntegrable
      (fun x : ℝ => (∑ j ∈ Finset.range (2*K+1), h (x + ((j:ℤ) - (K:ℤ)))) ^ 2) volume
      (0:ℝ) 1 := by
    have hc : Continuous
        (fun x : ℝ => (∑ j ∈ Finset.range (2*K+1), h (x + ((j:ℤ) - (K:ℤ)))) ^ 2) := by
      fun_prop
    exact hc.intervalIntegrable _ _
  -- Step 3: the untwisted periodization `L²`-mass is the unshifted lattice sum
  have hRHS : ∫ x in (0:ℝ)..1, (∑ j ∈ Finset.range (2*K+1), h (x + ((j:ℤ) - (K:ℤ)))) ^ 2
      = ∑' ℓ : ℤ, ‖Fhat h (ℓ : ℝ)‖ ^ 2 := by
    have hK1 : (1:ℝ) * R + 1 ≤ (K:ℝ) := by linarith
    have hfe : ∀ x ∈ Set.Icc (0:ℝ) 1,
        per h 1 x = ∑ j ∈ Finset.range (2*K+1), h (x + ((j:ℤ) - (K:ℤ))) := by
      intro x hx
      simpa [div_one] using per_eq_finsum (f := h) (m := 1) (R := R) one_pos hRf hK1 x hx
    have hcongr : ∫ x in (0:ℝ)..1, (per h 1 x) ^ 2
        = ∫ x in (0:ℝ)..1,
            (∑ j ∈ Finset.range (2*K+1), h (x + ((j:ℤ) - (K:ℤ)))) ^ 2 := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
      rw [hfe x hx]
    rw [← hcongr, per_integral_sq hcont one_pos hRf hK1, one_pow, one_mul]
    exact tsum_congr (fun n => by rw [mul_one])
  calc ∫ x in (0:ℝ)..1, ‖∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ)))‖ ^ 2
      ≤ ∫ x in (0:ℝ)..1,
          (∑ j ∈ Finset.range (2*K+1), h (x + ((j:ℤ) - (K:ℤ)))) ^ 2 :=
        intervalIntegral.integral_mono_on (by norm_num) hInt1 hInt2 (fun x _ => hpt x)
    _ = ∑' ℓ : ℤ, ‖Fhat h (ℓ : ℝ)‖ ^ 2 := hRHS

end

end Work.GM.Affine
