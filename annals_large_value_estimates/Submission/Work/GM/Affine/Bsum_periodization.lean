import Mathlib
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.tsum_shift_fhat_sq_le
import Submission.Work.GM.Affine.periodization_identity

/-!
# `Work.GM.Affine.Bsum_periodization` (GM §9, region II)

The sampled `L²`-mass of the `m₂`-sum `Bsum f M₂ = Σ_{m₂ ∈ R2 M₂} m₂ f̂(m₂ ·)` on the lattice
`ℤ + t` equals the `L²`-mass over one period of the *twisted periodization* of the `m₂`-profile
`Hprof f M₂ = Σ_{m₂ ∈ R2 M₂} f (·/m₂)`:

`∑'_ℓ ‖Bsum f M₂ (ℓ + t)‖² = ∫_0^1 ‖∑'_ℓ Hprof f M₂ (u + ℓ) · e (ℓ t)‖² du`.

Two ingredients:

* `Bsum f M₂ = Fhat (Hprof f M₂)` (`Bsum_eq_Fhat_Hprof`) — `Bsum` is the Fourier transform of the
  profile (dilation `u ↦ u/m₂` turns `f̂ (m₂ ξ)` into `m₂ f̂ (m₂ ξ)`);
* the **twisted sampling = periodization identity** `periodization_twisted_eq_b` below, for a real
  continuous compactly supported `h`:

  `∑'_ℓ ‖Fhat h (ℓ + t)‖² = ∫_0^1 ‖∑'_ℓ h (u + ℓ) e (ℓ t)‖² du`.

The latter is Parseval on the circle applied to `g y = e (-t y) · h y`, whose periodization is
`e (-t u)` times the (pointwise) conjugate of the twisted periodization
`u ↦ ∑_ℓ h (u + ℓ) e (ℓ t)` of the *real* function `h`; hence the two have the same modulus.  The
complex-valued circle Parseval (`tsum_parseval_b`) is proved from scratch below (in the spirit of
the real-valued `per_integral_sq` of `periodization_identity`, but for complex weights), and the
finite-support reduction of the periodization on `[0,1]` is done with `tsum_eq_sum`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-! ## Elementary facts about `efun` -/

private lemma cefun_cont : Continuous efun := by unfold efun; fun_prop

private lemma cefun_int (z : ℤ) : efun (z : ℝ) = 1 := by
  rw [efun]
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((z : ℝ) : ℂ))
        = (z : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I z

private lemma Fhat_eq_integral_b (f : ℝ → ℝ) (ξ : ℝ) :
    Fhat f ξ = ∫ y : ℝ, efun (-(ξ * y)) * ((f y : ℝ) : ℂ) := by
  rw [Fhat, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Real.inner_apply, smul_eq_mul, efun]
  congr 1
  push_cast
  ring_nf

/-! ## The Fourier coefficient of a finite periodization (complex-valued version) -/

private lemma single_term_shift_b {g : ℝ → ℂ} (n : ℤ) (z : ℝ) :
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
private lemma fourierCoeff_finsum_eq_integral_b {g : ℝ → ℂ} (hg : Continuous g) {R : ℝ}
    (hRg : ∀ y : ℝ, R < |y| → g y = 0) {K : ℕ} (hK : R ≤ (K:ℝ)) (n : ℤ) :
    ∫ x in (0:ℝ)..1, efun (-((n:ℝ) * x)) *
        (∑ j ∈ Finset.range (2*K+1), g (x + ((j:ℤ) - (K:ℤ))))
      = ∫ y : ℝ, efun (-((n:ℝ) * y)) * g y := by
  set Ψ : ℝ → ℂ := fun y => efun (-((n:ℝ) * y)) * g y with hΨ
  set a : ℕ → ℝ := fun j => (j:ℝ) - (K:ℝ) with ha
  have hΨc : Continuous Ψ := by
    rw [hΨ]
    exact (cefun_cont.comp (by fun_prop)).mul hg
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
    exact Continuous.intervalIntegrable ((cefun_cont.comp (by fun_prop)).mul
      (hg.comp (by fun_prop))) 0 1
  have hterm : ∀ j ∈ Finset.range (2*K+1),
      (∫ x in (0:ℝ)..1, efun (-((n:ℝ) * x)) * g (x + ((j:ℤ) - (K:ℤ))))
        = ∫ y in a j..a (j+1), Ψ y := by
    intro j hj
    have hgen := single_term_shift_b (g := g) n (((j:ℤ):ℝ) - ((K:ℤ):ℝ))
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
    rw [hexp, efun_add, cefun_int, mul_one]
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
private lemma tsum_parseval_b {g : ℝ → ℂ} (hg : Continuous g)
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
    rw [← fourierCoeff_finsum_eq_integral_b hg hRg hK i]
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
/-! ## The twisted periodization identity -/

private lemma star_efun_b (x : ℝ) : star (efun x) = efun (-x) := by
  rw [efun_neg x, Complex.inv_eq_conj (norm_efun x), Complex.star_def]

/-- Termwise relation between the twisted periodization and the conjugate of the (finite) twisted
sum: `e (-t (u+x)) h (u+x) = e (-t u) · conj (h (u+x) e (x t))`. -/
private lemma efun_neg_add_mul_star (h : ℝ → ℝ) (t u x : ℝ) :
    efun (-(t * (u + x))) * ((h (u + x) : ℝ) : ℂ)
      = efun (-(t * u)) * star (((h (u + x) : ℝ) : ℂ) * efun (x * t)) := by
  rw [star_mul, star_efun_b]
  have hstar : star (((h (u + x) : ℝ) : ℂ)) = ((h (u + x) : ℝ) : ℂ) := by
    change (starRingEnd ℂ) (((h (u + x) : ℝ) : ℂ)) = _
    exact Complex.conj_ofReal _
  rw [hstar, show -(t * (u + x)) = (-(t * u)) + (-(x * t)) by ring, efun_add]
  ring

/-- **Twisted sampling = periodization.**  For `h : ℝ → ℝ` continuous with compact support and any
`t : ℝ`, the sampled `L²`-mass of `Fhat h` on the shifted lattice `ℤ + t` equals the `L²`-mass of
one period of the twisted periodization `u ↦ ∑'_ℓ h (u + ℓ) e (ℓ t)`. -/
private lemma periodization_twisted_eq_b {h : ℝ → ℝ} (hh : Continuous h)
    (hcs : HasCompactSupport h) (t : ℝ) :
    (∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + t)‖ ^ 2)
      = ∫ u in (0 : ℝ)..1,
          ‖∑' ℓ : ℤ, ((h (u + (ℓ : ℝ)) : ℝ) : ℂ) * efun ((ℓ : ℝ) * t)‖ ^ 2 := by
  obtain ⟨R, hR0, hRf⟩ := exists_support_bound hcs
  obtain ⟨K, hK⟩ : ∃ K : ℕ, R + 1 ≤ (K : ℝ) := ⟨⌈R + 1⌉₊, Nat.le_ceil _⟩
  have hK' : R ≤ (K : ℝ) := by linarith
  -- the twisted function whose periodization is `e(-t·)` times the conjugate of the twisted one
  set g : ℝ → ℂ := fun y => efun (-(t * y)) * ((h y : ℝ) : ℂ) with hg_def
  have hgc : Continuous g := by
    rw [hg_def]
    exact (cefun_cont.comp (by fun_prop)).mul (Complex.continuous_ofReal.comp hh)
  have hgsupp : ∀ y : ℝ, R < |y| → g y = 0 := by
    intro y hy
    rw [hg_def]
    simp only []
    rw [hRf y hy]
    simp
  -- Step 1: the left-hand side is the sum of the Fourier integrals of `g`
  have hLHS : (∑' ℓ : ℤ, ‖Fhat h ((ℓ : ℝ) + t)‖ ^ 2)
      = ∑' n : ℤ, ‖∫ y : ℝ, efun (-((n : ℝ) * y)) * g y‖ ^ 2 := by
    refine tsum_congr fun n => ?_
    have hkey : Fhat h ((n : ℝ) + t) = ∫ y : ℝ, efun (-((n : ℝ) * y)) * g y := by
      rw [Fhat_eq_integral_b h ((n : ℝ) + t)]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      rw [hg_def]
      simp only []
      rw [show -(((n : ℝ) + t) * y) = (-((n : ℝ) * y)) + (-(t * y)) by ring, efun_add]
      ring
    rw [hkey]
  rw [hLHS, tsum_parseval_b hgc hR0 hgsupp hK']
  -- Step 2: pointwise comparison of the two periodizations
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
  have hu0 : (0 : ℝ) ≤ u := hu.1
  have hu1 : u ≤ 1 := hu.2
  -- the profile vanishes outside the window `[-K, K]` on `[0,1]`
  have hvan : ∀ ℓ : ℤ, (K : ℝ) < |(ℓ : ℝ)| → h (u + (ℓ : ℝ)) = 0 := by
    intro ℓ hℓ
    apply hRf
    rcases lt_or_ge ℓ 0 with hneg | hpos
    · have h1 : (ℓ : ℝ) < 0 := by exact_mod_cast hneg
      rw [abs_of_neg h1] at hℓ
      have h3 : (ℓ : ℤ) ≤ -(K : ℤ) - 1 := by
        have : (K : ℤ) < -ℓ := by exact_mod_cast (by linarith : (K : ℝ) < -(ℓ : ℝ))
        omega
      have h4 : (ℓ : ℝ) ≤ -(K : ℝ) - 1 := by exact_mod_cast h3
      rw [abs_of_neg (by linarith : u + (ℓ : ℝ) < 0)]
      linarith
    · have h1 : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hpos
      rw [abs_of_nonneg h1] at hℓ
      rw [abs_of_pos (by linarith : (0 : ℝ) < u + (ℓ : ℝ))]
      linarith
  -- the summand of the twisted periodization, as a function of the index `ℓ : ℤ`
  set F : ℤ → ℂ := fun ℓ => ((h (u + (ℓ : ℝ)) : ℝ) : ℂ) * efun ((ℓ : ℝ) * t) with hF
  set s : Finset ℤ := (Finset.range (2 * K + 1)).image (fun j : ℕ => (j : ℤ) - (K : ℤ)) with hs
  have hmem : ∀ b : ℤ, b ∉ s → F b = 0 := by
    intro b hb
    have hbK : (K : ℝ) < |(b : ℝ)| := by
      by_contra hcon
      rw [not_lt] at hcon
      have hb1 : b ≤ (K : ℤ) := by exact_mod_cast (abs_le.mp hcon).2
      have hb2 : -(K : ℤ) ≤ b := by exact_mod_cast (abs_le.mp hcon).1
      have hj : b ∈ s := by
        rw [hs, Finset.mem_image]
        refine ⟨Int.toNat (b + (K : ℤ)), ?_, ?_⟩
        · rw [Finset.mem_range]
          have h3 : 0 ≤ b + (K : ℤ) := by omega
          have h4 : ((Int.toNat (b + (K : ℤ)) : ℤ)) = b + (K : ℤ) := Int.toNat_of_nonneg h3
          have h5 : ((Int.toNat (b + (K : ℤ)) : ℤ)) ≤ (2 * K : ℤ) := by omega
          have h6 : Int.toNat (b + (K : ℤ)) ≤ 2 * K := by exact_mod_cast h5
          omega
        · have h3 : 0 ≤ b + (K : ℤ) := by omega
          have h4 : ((Int.toNat (b + (K : ℤ)) : ℤ)) = b + (K : ℤ) := Int.toNat_of_nonneg h3
          omega
      exact absurd hj hb
    rw [hF]
    simp only []
    rw [hvan b hbK]
    simp
  have hinj : Set.InjOn (fun j : ℕ => (j : ℤ) - (K : ℤ)) ↑(Finset.range (2 * K + 1)) := by
    intro a _ b _ hab
    have hab' : ((a : ℤ) - (K : ℤ)) = ((b : ℤ) - (K : ℤ)) := hab
    have h2 : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast h2
  -- the twisted periodization is a finite sum on `[0,1]`
  have htsum : (∑' ℓ : ℤ, F ℓ) = ∑ j ∈ Finset.range (2 * K + 1), F ((j : ℤ) - (K : ℤ)) := by
    rw [tsum_eq_sum hmem, hs, Finset.sum_image hinj]
  -- the finite sum of `g` is `e(-tu)` times the conjugate of the finite twisted sum
  have hgs : ∑ j ∈ Finset.range (2 * K + 1), g (u + ((j : ℤ) - (K : ℤ)))
      = efun (-(t * u)) * star (∑ j ∈ Finset.range (2 * K + 1), F ((j : ℤ) - (K : ℤ))) := by
    rw [star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg_def, hF]
    simp only []
    rw [show (u + ((j : ℤ) - (K : ℤ)) : ℝ)
        = (u + (((j : ℤ) - (K : ℤ) : ℤ) : ℝ)) by push_cast; ring]
    exact efun_neg_add_mul_star h t u (((j : ℤ) - (K : ℤ) : ℤ) : ℝ)
  rw [hgs, ← htsum, norm_mul, norm_efun, one_mul, norm_star, hF]

/-- **Periodization of the sampled `L²`-mass of `Bsum`** (GM §9, region II). -/
theorem Bsum_periodization {C₀ M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hM₂ : 0 < M₂) {f : ℝ → ℝ}
    (hf : Continuous f) (hsup : SuppHyp C₀ f) (t : ℝ) :
    (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2)
      = ∫ u in (0 : ℝ)..1,
          ‖∑' ℓ : ℤ, ((Hprof f M₂ (u + (ℓ : ℝ)) : ℝ) : ℂ)
              * Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ)))‖ ^ 2 := by
  have hcont : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
  have hcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hsup hC₀ hM₂.le
  have hgen := periodization_twisted_eq_b hcont hcs t
  rw [show (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2)
        = ∑' ℓ : ℤ, ‖Fhat (Hprof f M₂) ((ℓ : ℝ) + t)‖ ^ 2 from
      tsum_congr (fun ℓ => by rw [Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂]), hgen]
  refine intervalIntegral.integral_congr fun u _ => ?_
  have : (∑' ℓ : ℤ, ((Hprof f M₂ (u + (ℓ : ℝ)) : ℝ) : ℂ) * efun ((ℓ : ℝ) * t))
      = ∑' ℓ : ℤ, ((Hprof f M₂ (u + (ℓ : ℝ)) : ℝ) : ℂ)
          * Complex.exp (2 * ↑Real.pi * Complex.I * ((ℓ : ℂ) * (t : ℂ))) := by
    refine tsum_congr fun ℓ => ?_
    rw [efun]
    have harg : (((ℓ : ℝ) * t : ℝ) : ℂ) = (ℓ : ℂ) * (t : ℂ) := by push_cast; ring
    rw [harg]
  rw [this]
end

end Work.GM.Affine
