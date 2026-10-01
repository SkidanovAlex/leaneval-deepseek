import Mathlib
import Submission.Work.ZeroDensity.Montgomery.zeroDetAltPerronAux
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay
import Submission.Work.LinnikAreas.Density4.gamma_vertical_integrable_of_bound

open scoped Classical BigOperators

namespace Work.ZeroDensity.Montgomery

open MeasureTheory

noncomputable section

/-- The truncated Möbius convolution coefficient is bounded by the number of integers in `[1, X]`:
every summand is `μ d` with `‖μ d‖ ≤ 1`, and the summation index set
`{d | d ∣ n, (d : ℝ) ≤ X}` is contained in `Finset.Icc 1 ⌊X⌋₊`.  In particular the bound is
uniform in `n`. -/
lemma norm_mCoef_le (X : ℝ) (n : ℕ) : ‖mCoef X n‖ ≤ (⌊X⌋₊ + 1 : ℝ) := by
  have hfilter : ((Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X)).card ≤ ⌊X⌋₊ := by
    have hsub : (Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X) ⊆ Finset.Icc 1 ⌊X⌋₊ := by
      intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hdmem, hdle⟩ := hd
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_mem_divisors hdmem, Nat.le_floor hdle⟩
    calc ((Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X)).card
        ≤ (Finset.Icc 1 ⌊X⌋₊).card := Finset.card_le_card hsub
      _ = ⌊X⌋₊ := by rw [Nat.card_Icc]; simp
  have hterm : ∀ d ∈ (Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X),
      ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    intro d _
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc ‖mCoef X n‖
      ≤ ∑ d ∈ (Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X),
          ‖(ArithmeticFunction.moebius d : ℂ)‖ := by
        rw [mCoef]; exact norm_sum_le _ _
    _ ≤ ∑ _d ∈ (Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X), (1 : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (((Nat.divisors n).filter (fun d : ℕ => (d : ℝ) ≤ X)).card : ℝ) := by simp
    _ ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hfilter
    _ ≤ (⌊X⌋₊ + 1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) ⌊X⌋₊]

/-- `u ↦ ‖Γ (c + i u)‖` is integrable for every `c > 0`, by the uniform vertical estimate
`‖Γ (c + it)‖ ≤ C (1+|t|)^c e^{-(π/2)|t|}` of `gamma_vertical_exp_decay`. -/
lemma integrable_norm_gamma_vertical (c : ℝ) (hc : 0 < c) :
    Integrable (fun u : ℝ => ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖) := by
  obtain ⟨C, hCpos, hCbd⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay c hc
  have h := Work.LinnikAreas.Density4.gamma_vertical_integrable_of_bound c C hCpos (fun t => by
    have ht := hCbd t
    rw [mul_comm Complex.I (t : ℂ)] at ht
    exact ht)
  exact h.norm

/-- `u ↦ perronTerm χ ρ X Y c n u` is continuous (it is `0` for `n = 0` and a product of
continuous factors — a `cpow` with nonzero base `n`, the Gamma function along the pole-free line
`Re w = c > 0`, and a `cpow` with base `Y > 0` — for `n ≥ 1`). -/
lemma continuous_perronTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (X Y c : ℝ) (hc : 0 < c) (hY : 0 < Y) (n : ℕ) :
    Continuous (fun u : ℝ => perronTerm χ ρ X Y c n u) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : (fun u : ℝ => perronTerm χ ρ X Y c 0 u) = fun _ => (0 : ℂ) := by
      funext u; simp [perronTerm_def, mCoef_zero]
    rw [h0]; exact continuous_const
  · have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpow : Continuous
        (fun u : ℝ => (n : ℂ) ^ (-(ρ + ((c : ℂ) + (u : ℂ) * Complex.I)))) :=
      Continuous.const_cpow (by fun_prop) (Or.inl hn0)
    have hΓ : Continuous (fun u : ℝ => Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro u
      have hinner : ContinuousAt (fun u : ℝ => (c : ℂ) + (u : ℂ) * Complex.I) u := by fun_prop
      refine ContinuousAt.comp (f := fun u : ℝ => (c : ℂ) + (u : ℂ) * Complex.I) (x := u)
        (g := Complex.Gamma) (Complex.continuousAt_Gamma ((c : ℂ) + (u : ℂ) * Complex.I) ?_) hinner
      intro m hm
      have hre := congrArg Complex.re hm
      simp at hre
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hYc : Continuous (fun u : ℝ => (Y : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I)) :=
      Continuous.const_cpow (by fun_prop)
        (Or.inl (by rw [Complex.ofReal_ne_zero]; exact ne_of_gt hY))
    simp only [perronTerm_def]
    exact (((continuous_const.mul continuous_const).mul hpow).mul hΓ).mul hYc

/-- Pointwise domination of the Perron summands: for every `n` (both sides vanish at `n = 0`)
`‖perronTerm χ ρ X Y c n u‖ ≤ (⌊X⌋₊ + 1) · n^{-(Re ρ + c)} · Y^c · ‖Γ (c + i u)‖`. -/
lemma norm_perronTerm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (X Y c : ℝ) (hY : 0 < Y) (n : ℕ) (u : ℝ) :
    ‖perronTerm χ ρ X Y c n u‖
      ≤ (⌊X⌋₊ + 1 : ℝ) * (n : ℝ) ^ (-(ρ.re + c)) * Y ^ c
          * ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [perronTerm_def, mCoef_zero, zero_mul, norm_zero, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _))
      (Real.rpow_nonneg hY.le _)) (norm_nonneg _)
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [perronTerm_def]
    simp only [norm_mul]
    rw [Complex.norm_natCast_cpow_of_pos hn, Complex.norm_cpow_eq_rpow_re_of_pos hY]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
    have hχ : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hmc : ‖mCoef X n‖ ≤ (⌊X⌋₊ + 1 : ℝ) := norm_mCoef_le X n
    have hA : (0 : ℝ) ≤ (n : ℝ) ^ (-(ρ.re + c)) := Real.rpow_nonneg (le_of_lt hnpos) _
    have hy : (0 : ℝ) ≤ Y ^ c := Real.rpow_nonneg hY.le _
    have hG : (0 : ℝ) ≤ ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ := norm_nonneg _
    have h1 : ‖mCoef X n‖ * ‖χ (n : ZMod q)‖ ≤ (⌊X⌋₊ + 1 : ℝ) := by
      calc ‖mCoef X n‖ * ‖χ (n : ZMod q)‖ ≤ (⌊X⌋₊ + 1) * 1 :=
            mul_le_mul hmc hχ (norm_nonneg _) (by positivity)
        _ = (⌊X⌋₊ + 1 : ℝ) := by ring
    calc ‖mCoef X n‖ * ‖χ (n : ZMod q)‖
            * (n : ℝ) ^ (-(ρ.re + c))
            * ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * Y ^ c
        = (‖mCoef X n‖ * ‖χ (n : ZMod q)‖)
            * ((n : ℝ) ^ (-(ρ.re + c))
                * ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * Y ^ c) := by ring
      _ ≤ (⌊X⌋₊ + 1 : ℝ)
            * ((n : ℝ) ^ (-(ρ.re + c))
                * ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * Y ^ c) :=
            mul_le_mul_of_nonneg_right h1 (mul_nonneg (mul_nonneg hA hG) hy)
      _ = (⌊X⌋₊ + 1 : ℝ) * (n : ℝ) ^ (-(ρ.re + c)) * Y ^ c
            * ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ := by ring

/-- Every summand `u ↦ perronTerm χ ρ X Y c n u` is integrable on `ℝ`, and the sequence of their
`L¹`-norms is summable in `n`.  This is the domination estimate that justifies exchanging the
infinite Dirichlet series with the vertical integral in `zeroDetAltPerron`.

The bound is `‖perronTerm χ ρ X Y c n u‖ ≤ (⌊X⌋₊+1) · n^{-Re ρ - c} · Y^c · ‖Γ (c + iu)‖`,
and `∫_ℝ ‖Γ (c + iu)‖ du < ∞` while `Re ρ + c > 1`. -/
theorem perronTerm_bounds {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (X Y c : ℝ) (hc : 0 < c) (hc2 : 1 - ρ.re < c) (hY : 0 < Y) :
    (∀ n : ℕ, MeasureTheory.Integrable (fun u : ℝ => perronTerm χ ρ X Y c n u))
      ∧ Summable (fun n : ℕ => ∫ u : ℝ, ‖perronTerm χ ρ X Y c n u‖) := by
  have hΓint := integrable_norm_gamma_vertical c hc
  have hrpow : Summable (fun n : ℕ => (n : ℝ) ^ (-(ρ.re + c))) := by
    rw [Real.summable_nat_rpow]
    linarith
  have hCsum : Summable
      (fun n : ℕ => (⌊X⌋₊ + 1 : ℝ) * (n : ℝ) ^ (-(ρ.re + c)) * Y ^ c) := by
    have h1 : Summable
        (fun n : ℕ => ((⌊X⌋₊ + 1 : ℝ) * Y ^ c) * (n : ℝ) ^ (-(ρ.re + c))) :=
      Summable.mul_left _ hrpow
    exact h1.congr (fun n => by ring)
  have hFint : ∀ n : ℕ, Integrable (fun u : ℝ => perronTerm χ ρ X Y c n u) := by
    intro n
    refine (hΓint.const_mul ((⌊X⌋₊ + 1 : ℝ) * (n : ℝ) ^ (-(ρ.re + c)) * Y ^ c)).mono'
      ((continuous_perronTerm χ ρ X Y c hc hY n).aestronglyMeasurable) ?_
    filter_upwards with u
    exact norm_perronTerm_le χ ρ X Y c hY n u
  refine ⟨hFint, ?_⟩
  have hmaj : Summable (fun n : ℕ =>
      ((⌊X⌋₊ + 1 : ℝ) * (n : ℝ) ^ (-(ρ.re + c)) * Y ^ c)
        * ∫ u : ℝ, ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖) :=
    Summable.mul_right _ hCsum
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun u => norm_nonneg _)) ?_ hmaj
  intro n
  have h1 : Integrable (fun u : ℝ => ‖perronTerm χ ρ X Y c n u‖) := (hFint n).norm
  have h2 : Integrable (fun u : ℝ =>
      ((⌊X⌋₊ + 1 : ℝ) * (n : ℝ) ^ (-(ρ.re + c)) * Y ^ c)
        * ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖) :=
    hΓint.const_mul _
  calc ∫ u : ℝ, ‖perronTerm χ ρ X Y c n u‖
      ≤ ∫ u : ℝ, ((⌊X⌋₊ + 1 : ℝ) * (n : ℝ) ^ (-(ρ.re + c)) * Y ^ c)
          * ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ :=
        integral_mono h1 h2 (fun u => norm_perronTerm_le χ ρ X Y c hY n u)
    _ = ((⌊X⌋₊ + 1 : ℝ) * (n : ℝ) ^ (-(ρ.re + c)) * Y ^ c)
          * ∫ u : ℝ, ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ := by
        rw [integral_const_mul]

end

end Work.ZeroDensity.Montgomery
