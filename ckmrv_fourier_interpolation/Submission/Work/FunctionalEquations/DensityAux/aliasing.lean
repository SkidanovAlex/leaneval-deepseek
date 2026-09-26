import Mathlib

/-!
# The aliasing identity (Poisson summation in the form needed for CKMRV)

For Schwartz functions `ψ`, `hS` on `ℝ` related by `𝓕 ψ = hS ∘ (-2 * ·)`, the Riemann
sum of mesh `1 / N` of the "twisted" samples of `ψ`,
`(1/N) * ∑'_n ψ (n/N) * exp (π i (n/N) t)`, equals the periodisation `∑'_m hS (t - 2 N m)`
of `hS`.  This is Poisson summation applied to the modulated Schwartz function
`g u = (1/N) ψ (u/N) exp (π i (u/N) t)` (for the general Weyl transform of the standard
Poisson summation on the circle, see `Real.tsum_eq_tsum_fourier`); here we compute
`𝓕 g ξ = hS (t - 2 N ξ)` and apply `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`
at `x = 0`.
-/

open Filter MeasureTheory Asymptotics
open scoped FourierTransform SchwartzMap Topology

namespace Work.FunctionalEquations.DensityAux

/-- Pointwise `(1 + |x|)^{-2}`-decay of a univariate Schwartz function. -/
lemma schwartz_norm_le_one_add_sq (ψ : SchwartzMap ℝ ℂ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, ‖ψ x‖ ≤ D / (1 + |x|) ^ 2 := by
  refine ⟨2 ^ ((2:ℕ), (0:ℕ)).1 *
    ((Finset.Iic ((2:ℕ), (0:ℕ))).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ,
    by positivity, fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((2:ℕ), (0:ℕ)))
    (k := 2) (n := 0) le_rfl le_rfl ψ x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, mul_comm] at h
  rw [le_div_iff₀ (by positivity)]
  linarith [h]

/-- A complex function on `ℝ` bounded by `D / (1 + |x|)^2` has summable integer samples. -/
lemma summable_int_of_norm_le {f : ℝ → ℂ} {D : ℝ}
    (hD : ∀ x : ℝ, ‖f x‖ ≤ D / (1 + |x|) ^ 2) :
    Summable fun n : ℤ => f n := by
  have hbase : Summable fun n : ℤ => ((1 + |(n:ℝ)|)^2)⁻¹ := by
    have hg : Summable fun n : ℤ => |(n:ℝ)|^(-2:ℝ) := Real.summable_abs_int_rpow (by norm_num)
    refine Summable.of_norm_bounded_eventually hg ?_
    rw [eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton (0:ℤ)) ?_
    intro n hn
    simp only [Set.mem_singleton_iff]
    by_contra hne
    apply hn
    have hn1 : (1:ℝ) ≤ |(n:ℝ)| := by
      have h1 : (1:ℤ) ≤ |n| := Int.one_le_abs hne
      exact_mod_cast h1
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (abs_nonneg _), Real.rpow_two]
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith [hn1, abs_nonneg (n:ℝ)]
  refine Summable.of_norm_bounded_eventually (hbase.mul_left (max D 0)) ?_
  filter_upwards with n
  calc ‖f (n:ℝ)‖ ≤ D / (1 + |(n:ℝ)|)^2 := hD _
    _ = D * ((1 + |(n:ℝ)|)^2)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ max D 0 * ((1 + |(n:ℝ)|)^2)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left D 0) (by positivity)

theorem aliasing (ψ hS : SchwartzMap ℝ ℂ)
    (hψ : ∀ σ : ℝ, (FourierTransform.fourier ψ) σ = hS (-2 * σ))
    (N : ℕ) (hN : 0 < N) (t : ℝ) :
    (1 / (N : ℂ)) * ∑' n : ℤ, ψ ((n : ℝ) / N) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℝ) / N : ℂ) * t)
      = ∑' m : ℤ, hS (t - 2 * (N : ℝ) * m) := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNne : ((N:ℂ)) ≠ 0 := by exact_mod_cast hN.ne'
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  obtain ⟨Dψ, hDψ0, hDψ⟩ := schwartz_norm_le_one_add_sq ψ
  obtain ⟨DhS, hDhS0, hDhS⟩ := schwartz_norm_le_one_add_sq hS
  set g : ℝ → ℂ := fun u => (1/(N:ℂ)) * ψ (u/N) *
        Complex.exp ((Real.pi:ℂ) * Complex.I * ((u/N : ℝ) : ℂ) * t) with hg
  -- the Fourier transform of the modulated function
  have hFg : ∀ ξ : ℝ, 𝓕 g ξ = hS (t - 2 * (N:ℝ) * ξ) := by
    intro ξ
    set G : ℝ → ℂ := fun y => Complex.exp (↑(-2 * Real.pi * y * (N*ξ - t/2)) * Complex.I) * ψ y
      with hG
    have hpoint : ∀ v : ℝ, Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) •
        ((1/(N:ℂ)) * ψ (v/N) * Complex.exp ((Real.pi:ℂ) * Complex.I * ((v/N : ℝ) : ℂ) * t))
        = (1/(N:ℂ)) * G (v/N) := by
      intro v
      rw [hG]
      simp only [smul_eq_mul]
      have hAB : Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) *
          Complex.exp ((Real.pi:ℂ) * Complex.I * ((v/N : ℝ) : ℂ) * t)
          = Complex.exp (↑(-2 * Real.pi * (v/N) * (N*ξ - t/2)) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        field_simp
        ring
      calc Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) *
            (1 / ↑N * ψ (v / ↑N) * Complex.exp (↑Real.pi * Complex.I * ↑(v / ↑N) * ↑t))
          = 1 / ↑N * (Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) *
              Complex.exp (↑Real.pi * Complex.I * ↑(v / ↑N) * ↑t)) * ψ (v / ↑N) := by ring
        _ = 1 / ↑N * (Complex.exp (↑(-2 * Real.pi * (v / ↑N) * (↑N * ξ - t / 2)) * Complex.I)) *
              ψ (v / ↑N) := by rw [hAB]
        _ = 1 / ↑N * (Complex.exp (↑(-2 * Real.pi * (v / ↑N) * (↑N * ξ - t / 2)) * Complex.I) *
              ψ (v / ↑N)) := by ring
    rw [Real.fourier_real_eq_integral_exp_smul]
    rw [show (∫ (v : ℝ), Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) •
        ((1 / ↑N) * ψ (v / ↑N) * Complex.exp (↑Real.pi * Complex.I * ↑(v / ↑N) * ↑t)))
        = ∫ (v : ℝ), (1/(N:ℂ)) * G (v/N) from integral_congr_ae (Eventually.of_forall hpoint)]
    rw [integral_const_mul]
    rw [Measure.integral_comp_div]
    rw [abs_of_pos hNr]
    rw [Complex.real_smul, Complex.ofReal_natCast]
    rw [div_eq_mul_inv, one_mul, inv_mul_cancel_left₀ hNne]
    have hGf : (∫ (y : ℝ), G y) = (𝓕 (ψ : ℝ → ℂ)) (N*ξ - t/2) := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      rw [hG]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [smul_eq_mul]
    rw [hGf]
    rw [← SchwartzMap.fourier_coe, hψ (N*ξ - t/2)]
    congr 1
    ring
  have hcont : Continuous g := by rw [hg]; fun_prop
  have hnormg : ∀ u : ℝ, ‖g u‖ = (1/(N:ℝ)) * ‖ψ (u/N)‖ := by
    intro u
    rw [hg]
    simp only [norm_mul]
    have hexp : Complex.exp ((Real.pi:ℂ)*Complex.I*((u/N : ℝ):ℂ)*t)
        = Complex.exp (↑(Real.pi*(u/N)*t) * Complex.I) := by
      congr 1; push_cast; ring
    rw [hexp, Complex.norm_exp_ofReal_mul_I, mul_one, norm_div]
    simp
  -- decay of `g` at infinity
  have hgbound : ∀ u : ℝ, (1:ℝ) ≤ |u| → ‖g u‖ ≤ Dψ * (N:ℝ) * |u|^(-2:ℝ) := by
    intro u hu1
    have hu0 : (0:ℝ) < |u| := by linarith
    have h1 : ‖ψ (u/N)‖ ≤ Dψ / (1 + |u|/(N:ℝ))^2 := by
      have := hDψ (u/N)
      rwa [abs_div, abs_of_pos hNr] at this
    have ha : (0:ℝ) ≤ |u|/(N:ℝ) := by positivity
    have hkey : 1 / (1 + |u|/(N:ℝ))^2 ≤ 1 / (|u|/(N:ℝ))^2 := by
      apply one_div_le_one_div_of_le
      · positivity
      · nlinarith [ha]
    calc ‖g u‖ = (1/(N:ℝ)) * ‖ψ (u/N)‖ := hnormg u
      _ ≤ (1/(N:ℝ)) * (Dψ / (1 + |u|/(N:ℝ))^2) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Dψ * (1/(N:ℝ)) * (1/(1 + |u|/(N:ℝ))^2) := by ring
      _ ≤ Dψ * (1/(N:ℝ)) * (1/(|u|/(N:ℝ))^2) := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = Dψ * (N:ℝ) * |u|^(-2:ℝ) := by
          rw [Real.rpow_neg hu0.le, Real.rpow_two]
          field_simp
  have hdec : g =O[cocompact ℝ] (fun x : ℝ => |x|^(-2:ℝ)) := by
    rw [cocompact_eq_atBot_atTop, isBigO_sup]
    constructor
    · refine IsBigO.of_bound (Dψ * (N:ℝ)) ?_
      filter_upwards [eventually_le_atBot (-1:ℝ)] with u hu
      have hu1 : (1:ℝ) ≤ |u| := by rw [abs_of_nonpos (by linarith)]; linarith
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg u) _)]
      exact hgbound u hu1
    · refine IsBigO.of_bound (Dψ * (N:ℝ)) ?_
      filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
      have hu1 : (1:ℝ) ≤ |u| := by rw [abs_of_nonneg (by linarith)]; linarith
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg u) _)]
      exact hgbound u hu1
  -- summability of the Fourier samples
  have hsum : Summable fun n : ℤ => 𝓕 g (n:ℝ) := by
    refine summable_int_of_norm_le (f := fun x : ℝ => 𝓕 g x) (D := DhS * (1 + |t|)^2)
      (fun x => ?_)
    rw [hFg x, le_div_iff₀ (by positivity)]
    have h1 : ‖hS (t - 2*(N:ℝ)*x)‖ ≤ DhS / (1 + |t - 2*(N:ℝ)*x|)^2 := hDhS _
    have h2 : (1 + |x|)^2 ≤ (1 + |t|)^2 * (1 + |t - 2*(N:ℝ)*x|)^2 := by
      have h3 : (2*(N:ℝ))*|x| ≤ |t| + |t - 2*(N:ℝ)*x| := by
        have h4 : (2*(N:ℝ))*|x| = |2*(N:ℝ)*x| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*(N:ℝ))]
        rw [h4]
        have h5 : |2*(N:ℝ)*x| = |t - (t - 2*(N:ℝ)*x)| := by congr 1; ring
        rw [h5]
        simpa [abs_sub_comm] using abs_sub_le t 0 (t - 2*(N:ℝ)*x)
      have h5 : (1:ℝ) ≤ 2*(N:ℝ) := by linarith
      have h6 : |x| ≤ (2*(N:ℝ))*|x| := by nlinarith [abs_nonneg x]
      have hx : |x| ≤ |t| + |t - 2*(N:ℝ)*x| := by linarith
      have h7 : 1 + |x| ≤ (1 + |t|) * (1 + |t - 2*(N:ℝ)*x|) :=
        by nlinarith [hx, abs_nonneg t, abs_nonneg (t - 2*(N:ℝ)*x), abs_nonneg x]
      nlinarith [h7, abs_nonneg t, abs_nonneg (t - 2*(N:ℝ)*x), abs_nonneg x]
    have h3 : (DhS / (1 + |t - 2*(N:ℝ)*x|)^2) * ((1 + |t|)^2 * (1 + |t - 2*(N:ℝ)*x|)^2)
        = DhS * (1 + |t|)^2 := by
      have hc : (1 + |t - 2*(N:ℝ)*x|)^2 ≠ 0 := by positivity
      field_simp
    calc ‖hS (t - 2*(N:ℝ)*x)‖ * (1 + |x|)^2
        ≤ (DhS / (1 + |t - 2*(N:ℝ)*x|)^2) * ((1 + |t|)^2 * (1 + |t - 2*(N:ℝ)*x|)^2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = DhS * (1 + |t|)^2 := h3
  -- Poisson summation at `x = 0`
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hcont (b := 2)
    (by norm_num) hdec hsum 0
  simp only [zero_add] at hp
  have hp' : (∑' n : ℤ, g (n:ℝ)) = ∑' n : ℤ, 𝓕 g (n:ℝ) := by simpa using hp
  have hL : (∑' n : ℤ, g (n:ℝ)) = (1/(N:ℂ)) * ∑' n : ℤ, ψ ((n:ℝ)/N) *
      Complex.exp ((Real.pi:ℂ) * Complex.I * ((n:ℝ)/N : ℂ) * t) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [hg]
    push_cast
    ring
  rw [← hL, hp']
  exact tsum_congr fun n => hFg n

end Work.FunctionalEquations.DensityAux
