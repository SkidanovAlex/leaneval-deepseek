import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.DirichletPolynomial

open Finset Complex
open MeasureTheory intervalIntegral
open scoped BigOperators
set_option autoImplicit false

/-- **Elementary `L²`-Cauchy–Schwarz on an interval of length `≤ 1`.** For a continuous
nonnegative `h` on `[a,b]` with `b - a ≤ 1`, `(∫_a^b h)² ≤ ∫_a^b h²`.

This is the only place where the "unit cell" length is used: the AM–GM inequality
`2 A h x ≤ A² + h x²` with `A = ∫_a^b h` integrates to `2A² ≤ A² (b-a) + ∫ h²`. -/
private lemma sq_integral_le_integral_sq_of_len_le_one {h : ℝ → ℝ} (hh : Continuous h)
    (hnn : ∀ x, 0 ≤ h x) {a b : ℝ} (hle : a ≤ b) (hab : b - a ≤ 1) :
    (∫ x in a..b, h x) ^ 2 ≤ ∫ x in a..b, h x ^ 2 := by
  set A : ℝ := ∫ x in a..b, h x with hA
  have hAnn : 0 ≤ A := by
    rw [hA]; exact intervalIntegral.integral_nonneg hle (fun u _ => hnn u)
  have h1 : A * A = ∫ x in a..b, A * h x := by
    rw [hA]
    exact (intervalIntegral.integral_const_mul (a := a) (b := b) (∫ x in a..b, h x) h).symm
  have hle' : (∫ x in a..b, A * h x) ≤ ∫ x in a..b, (A^2 + h x^2)/2 := by
    apply intervalIntegral.integral_mono_on hle
    · exact (continuous_const.mul hh).intervalIntegrable _ _
    · exact ((continuous_const.add (hh.pow 2)).div_const 2).intervalIntegrable _ _
    · intro u _
      nlinarith [sq_nonneg (A - h u)]
  have h2 : (∫ x in a..b, (A^2 + h x^2)/2)
      = A^2 * (b - a)/2 + (1/2) * (∫ x in a..b, h x^2) := by
    have hcongr : (∫ x in a..b, (A^2 + h x^2)/2)
        = ∫ x in a..b, (A^2/2 + (1/2) * h x^2) := by
      apply intervalIntegral.integral_congr; intro u _; ring
    rw [hcongr, intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]; ring
    · exact intervalIntegrable_const
    · exact (continuous_const.mul (hh.pow 2)).intervalIntegrable _ _
  rw [← h1, h2] at hle'
  show A ^ 2 ≤ ∫ x in a..b, h x ^ 2
  nlinarith

/-- **Gallagher's pointwise inequality.** If `g` is the derivative of `f`, then the value of `f`
at `t` is controlled by the mean square of `f` and of `f'` over the unit cell centred at `t`. -/
private lemma pointwise_deriv_bound {f g : ℝ → ℂ} (hg : ∀ x, HasDerivAt f (g x) x)
    (hgc : Continuous g) (t : ℝ) :
    ‖f t‖ ^ 2 ≤ 2 * (∫ x in (t-1/2)..(t+1/2), ‖f x‖ ^ 2)
        + 2 * (∫ x in (t-1/2)..(t+1/2), ‖g x‖ ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hfsq : Continuous (fun x => ‖f x‖ ^ 2) := hfc.norm.pow 2
  set A : ℝ := ∫ x in (t-1/2)..(t+1/2), ‖g x‖ with hA
  have hAnn : 0 ≤ A := by
    rw [hA]; exact intervalIntegral.integral_nonneg (by linarith) (fun u _ => norm_nonneg _)
  have hAsq : A^2 ≤ ∫ x in (t-1/2)..(t+1/2), ‖g x‖ ^ 2 := by
    rw [hA]
    exact sq_integral_le_integral_sq_of_len_le_one hgc.norm (fun u => norm_nonneg _)
      (by linarith) (by linarith)
  have hpt : ∀ x ∈ Set.Icc (t-1/2) (t+1/2), ‖f t‖^2 ≤ 2 * ‖f x‖^2 + 2 * A^2 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hdiff : ‖f t - f x‖ ≤ A := by
      rcases lt_or_ge x t with hxt | htx
      · have hFTC : (∫ y in x..t, g y) = f t - f x :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hg y)
            (hgc.intervalIntegrable x t)
        rw [← hFTC]
        calc ‖∫ y in x..t, g y‖ ≤ ∫ y in x..t, ‖g y‖ :=
              intervalIntegral.norm_integral_le_integral_norm hxt.le
          _ ≤ A := by
              rw [hA]
              apply intervalIntegral.integral_mono_interval (c := t-1/2) (d := t+1/2)
                (a := x) (b := t) hx1 hxt.le (by linarith)
              · exact Filter.Eventually.of_forall (fun u => norm_nonneg _)
              · exact hgc.norm.intervalIntegrable _ _
      · have hFTC : (∫ y in t..x, g y) = f x - f t :=
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hg y)
            (hgc.intervalIntegrable t x)
        have h1 : ‖f t - f x‖ = ‖∫ y in t..x, g y‖ := by
          rw [hFTC, show f x - f t = -(f t - f x) by ring, norm_neg]
        rw [h1]
        calc ‖∫ y in t..x, g y‖ ≤ ∫ y in t..x, ‖g y‖ :=
              intervalIntegral.norm_integral_le_integral_norm htx
          _ ≤ A := by
              rw [hA]
              apply intervalIntegral.integral_mono_interval (c := t-1/2) (d := t+1/2)
                (a := t) (b := x) (by linarith) htx hx2
              · exact Filter.Eventually.of_forall (fun u => norm_nonneg _)
              · exact hgc.norm.intervalIntegrable _ _
    have hsplit : ‖f t‖ ≤ ‖f x‖ + A := by
      calc ‖f t‖ = ‖f x + (f t - f x)‖ := by ring_nf
        _ ≤ ‖f x‖ + ‖f t - f x‖ := norm_add_le _ _
        _ ≤ ‖f x‖ + A := by linarith
    nlinarith [norm_nonneg (f t), norm_nonneg (f x), hAnn,
      sq_nonneg (‖f x‖ - A), sq_nonneg (‖f t‖ - (‖f x‖ + A))]
  have hInt : (∫ x in (t-1/2)..(t+1/2), ‖f t‖^2)
      ≤ ∫ x in (t-1/2)..(t+1/2), (2 * ‖f x‖^2 + 2 * A^2) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact intervalIntegrable_const
    · exact ((continuous_const.mul hfsq).add continuous_const).intervalIntegrable _ _
    · intro u hu
      exact hpt u hu
  have hLHS : (∫ x in (t-1/2)..(t+1/2), ‖f t‖^2) = ‖f t‖^2 := by
    rw [intervalIntegral.integral_const]; norm_num
  have hRHS : (∫ x in (t-1/2)..(t+1/2), (2 * ‖f x‖^2 + 2 * A^2))
      = 2 * (∫ x in (t-1/2)..(t+1/2), ‖f x‖^2) + 2 * A^2 := by
    rw [intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      norm_num
    · exact (continuous_const.mul hfsq).intervalIntegrable _ _
    · exact intervalIntegrable_const
  rw [hLHS, hRHS] at hInt
  linarith

/-- Summing over `1`-separated unit cells is at most the integral over the enclosing interval. -/
private lemma sum_cells_le_integral {K : ℝ} (hK : 0 ≤ K) {R : ℕ} (t : Fin R → ℝ)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|) (ht : ∀ i, t i ∈ Set.Icc 0 K)
    {h : ℝ → ℝ} (hcont : Continuous h) (hnn : ∀ x, 0 ≤ h x) :
    (∑ r, ∫ x in (t r - 1/2)..(t r + 1/2), h x) ≤ ∫ x in (-1:ℝ)..(K+1), h x := by
  classical
  set s : Fin R → Set ℝ := fun r => Set.Ioc (t r - 1/2) (t r + 1/2) with hs
  have hmeas : ∀ r, NullMeasurableSet (s r) volume := fun r =>
    measurableSet_Ioc.nullMeasurableSet
  have hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j) := by
    intro i j hij
    have hne : t i ≠ t j := by
      intro h; have := hsep i j hij; rw [h, sub_self, abs_zero] at this; linarith
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [hs, Set.mem_Ioc] at hx1 hx2
    obtain ⟨hx1a, hx1b⟩ := hx1
    obtain ⟨hx2a, hx2b⟩ := hx2
    have h1 : 1 ≤ |t i - t j| := hsep i j hij
    rcases (le_abs.mp h1) with hcase | hcase <;> linarith
  have hpair : Pairwise (Function.onFun (AEDisjoint volume) s) := by
    intro i j hij
    exact (hdisj i j hij).aedisjoint
  have hsub : (⋃ r, s r) ⊆ Set.Icc (-1:ℝ) (K+1) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨r, hr⟩ := hx
    simp only [hs, Set.mem_Ioc] at hr
    obtain ⟨hr1, hr2⟩ := hr
    have ht0 : 0 ≤ t r := (ht r).1
    have htK : t r ≤ K := (ht r).2
    exact ⟨by linarith, by linarith⟩
  have hint : IntegrableOn h (⋃ r, s r) volume :=
    (hcont.integrableOn_Icc (a := (-1:ℝ)) (b := K+1)).mono_set hsub
  have hUnion : ∫ x in (⋃ r, s r), h x = ∑' r, ∫ x in s r, h x :=
    integral_iUnion_ae hmeas hpair hint
  have hcell : ∀ r, (∫ x in s r, h x) = ∫ x in (t r - 1/2)..(t r + 1/2), h x := by
    intro r
    simp only [hs]
    exact (intervalIntegral.integral_of_le (by linarith : t r - 1/2 ≤ t r + 1/2)).symm
  have hmono : (∫ x in (⋃ r, s r), h x) ≤ ∫ x in Set.Icc (-1:ℝ) (K+1), h x :=
    setIntegral_mono_set (hcont.integrableOn_Icc (a := (-1:ℝ)) (b := K+1))
      (Filter.Eventually.of_forall hnn)
      (by rw [ae_le_set, Set.sdiff_eq_empty.mpr hsub]; simp)
  have hIcc : (∫ x in Set.Icc (-1:ℝ) (K+1), h x) = ∫ x in (-1:ℝ)..(K+1), h x := by
    rw [integral_Icc_eq_integral_Ioc]
    exact (intervalIntegral.integral_of_le (by linarith)).symm
  calc (∑ r, ∫ x in (t r - 1/2)..(t r + 1/2), h x)
      = ∑' r, ∫ x in s r, h x := by
        rw [tsum_fintype]; exact Finset.sum_congr rfl (fun r _ => (hcell r).symm)
    _ = ∫ x in (⋃ r, s r), h x := hUnion.symm
    _ ≤ ∫ x in Set.Icc (-1:ℝ) (K+1), h x := hmono
    _ = ∫ x in (-1:ℝ)..(K+1), h x := hIcc

/-- **Gallagher's well-spaced sampling inequality (sum form).** For `1`-separated `t r` in
`[0,K]` and a `C¹` function `f` with derivative `g`, the sampled sum is controlled by the
integrals of `‖f‖²` and `‖g‖²`. -/
private lemma gallagher_sum_bound {f g : ℝ → ℂ} (hg : ∀ x, HasDerivAt f (g x) x)
    (hgc : Continuous g) {K : ℝ} (hK : 0 ≤ K) {R : ℕ} (t : Fin R → ℝ)
    (hsep : ∀ i j, i ≠ j → 1 ≤ |t i - t j|) (ht : ∀ i, t i ∈ Set.Icc 0 K) :
    (∑ r, ‖f (t r)‖ ^ 2) ≤ 2 * (∫ x in (-1:ℝ)..(K+1), ‖f x‖ ^ 2)
      + 2 * (∫ x in (-1:ℝ)..(K+1), ‖g x‖ ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hpt : ∀ r, ‖f (t r)‖ ^ 2
      ≤ 2 * (∫ x in (t r - 1/2)..(t r + 1/2), ‖f x‖ ^ 2)
        + 2 * (∫ x in (t r - 1/2)..(t r + 1/2), ‖g x‖ ^ 2) :=
    fun r => pointwise_deriv_bound hg hgc (t r)
  have hsum : (∑ r, ‖f (t r)‖ ^ 2)
      ≤ 2 * (∑ r, ∫ x in (t r - 1/2)..(t r + 1/2), ‖f x‖ ^ 2)
        + 2 * (∑ r, ∫ x in (t r - 1/2)..(t r + 1/2), ‖g x‖ ^ 2) := by
    calc (∑ r, ‖f (t r)‖ ^ 2)
        ≤ ∑ r, (2 * (∫ x in (t r - 1/2)..(t r + 1/2), ‖f x‖ ^ 2)
              + 2 * (∫ x in (t r - 1/2)..(t r + 1/2), ‖g x‖ ^ 2)) :=
          Finset.sum_le_sum (fun r _ => hpt r)
      _ = 2 * (∑ r, ∫ x in (t r - 1/2)..(t r + 1/2), ‖f x‖ ^ 2)
            + 2 * (∑ r, ∫ x in (t r - 1/2)..(t r + 1/2), ‖g x‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have h1 : (∑ r, ∫ x in (t r - 1/2)..(t r + 1/2), ‖f x‖ ^ 2)
      ≤ ∫ x in (-1:ℝ)..(K+1), ‖f x‖ ^ 2 :=
    sum_cells_le_integral hK t hsep ht (h := fun x => ‖f x‖ ^ 2)
      (by show Continuous ((fun x : ℝ => ‖f x‖) ^ 2); exact hfc.norm.pow 2)
      (fun x => sq_nonneg _)
  have h2 : (∑ r, ∫ x in (t r - 1/2)..(t r + 1/2), ‖g x‖ ^ 2)
      ≤ ∫ x in (-1:ℝ)..(K+1), ‖g x‖ ^ 2 :=
    sum_cells_le_integral hK t hsep ht (h := fun x => ‖g x‖ ^ 2)
      (by show Continuous ((fun x : ℝ => ‖g x‖) ^ 2); exact hgc.norm.pow 2)
      (fun x => sq_nonneg _)
  linarith

/-- Reindex a sum over the integer block `[N, 2N]` as a sum over `Fin (N+1)`. -/
private lemma sum_Icc_eq_sum_fin (N : ℕ) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ n ∈ Finset.Icc N (2*N), f n) = ∑ k : Fin (N+1), f (N + (k:ℕ)) := by
  have hIco : Finset.Icc N (2*N) = Finset.Ico N (2*N+1) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIco, Finset.sum_Ico_eq_sum_range f N (2*N+1)]
  rw [show 2*N+1 - N = N+1 from by omega]
  exact (Fin.sum_univ_eq_sum_range (fun k => f (N + k)) (N+1)).symm

/-- The `cpow` bridge: `n^{it} = exp (I * log n * t)` for `n ≥ 1`. -/
private lemma cpow_I_eq_exp (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (Complex.I * (t : ℂ))
      = Complex.exp (Complex.I * ((Real.log n : ℂ) * (t : ℂ))) := by
  have hcast : Complex.log (n : ℂ) = (Real.log (n:ℝ) : ℂ) := by
    have h1 : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; ring
    rw [h1]
    exact (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn : (n:ℂ) ≠ 0), hcast]
  congr 1
  ring

/-- **Block identity.** The `cpow` sum over `[N,2N]` equals a phase times an exponential sum
whose frequencies `log ((N+k)/N)` lie in the window `[0, log 2]`. -/
private lemma block_cpow_eq (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (t : ℝ) :
    (∑ n ∈ Finset.Icc N (2*N), a n * (n : ℂ) ^ (Complex.I * (t : ℂ)))
      = Complex.exp (Complex.I * ((Real.log N : ℂ) * (t:ℂ)))
        * (∑ k : Fin (N+1), a (N + (k:ℕ))
            * Complex.exp (Complex.I * ((Real.log (((N:ℝ)+(k:ℕ))/(N:ℝ)) : ℂ) * (t:ℂ)))) := by
  have hN0 : N ≠ 0 := by omega
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hstep : ∀ n ∈ Finset.Icc N (2*N),
      a n * (n:ℂ)^(Complex.I * (t:ℂ))
        = Complex.exp (Complex.I * ((Real.log N : ℂ) * (t:ℂ)))
          * (a n * Complex.exp (Complex.I * ((Real.log ((n:ℝ)/N) : ℂ) * (t:ℂ)))) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [cpow_I_eq_exp n hn0 t]
    rw [show Real.log n = Real.log N + Real.log ((n:ℝ)/N) from by
        rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hNpos)]; ring]
    rw [show Complex.I * ((((Real.log N + Real.log ((n:ℝ)/N) : ℝ)) : ℂ) * (t:ℂ))
        = Complex.I * ((Real.log N : ℂ) * (t:ℂ))
          + Complex.I * ((Real.log ((n:ℝ)/N) : ℂ) * (t:ℂ)) from by push_cast; ring,
      Complex.exp_add]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.mul_sum]
  rw [sum_Icc_eq_sum_fin N (fun n => Complex.exp (Complex.I * ((Real.log N : ℂ) * (t:ℂ)))
        * (a n * Complex.exp (Complex.I * ((Real.log ((n:ℝ)/N) : ℂ) * (t:ℂ)))))]
  apply Finset.sum_congr rfl
  intro k _
  rw [show Real.log (((N + (k:ℕ) : ℕ) : ℝ) / (N:ℝ)) = Real.log (((N:ℝ)+(k:ℕ))/(N:ℝ)) from by
    congr 1; push_cast; ring]

/-- Bound on the norm of the phase factor. -/
private lemma norm_phase (N : ℕ) (t : ℝ) :
    ‖Complex.exp (Complex.I * ((Real.log N : ℂ) * (t:ℂ)))‖ = 1 := by
  rw [show Complex.exp (Complex.I * ((Real.log N : ℂ) * (t:ℂ)))
      = Complex.exp (((Real.log N * t : ℝ) : ℂ) * Complex.I) from by congr 1; push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Well-spaced mean value estimate for a dyadic block, with a free constant.**

For `1`-separated `t r ∈ [0,K]` and coefficients on the block `[N,2N]`,
`Σ_r ‖Σ_{n∈[N,2N]} a n · n^{i t r}‖² ≤ C·(K+N)·Σ_{n∈[N,2N]}‖a n‖²`.

Proof route (see the commons for the two ingredients): apply Gallagher's pointwise inequality to
`G(s) = Σ_{n∈[N,2N]} a n · exp(I·log(n/N)·s)` (so `‖G(s)‖ = ‖F(s)‖` pointwise), whose frequencies
`log(n/N) ∈ [0, log 2]` — like those of `G'` — are `1/(2N)`-separated; the integral mean value
theorem (`Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies`) bounds
`∫_0^{K+2}‖G‖²` and `∫_0^{K+2}‖G'‖²` by `(K+2+C·N)·Σ‖a n‖²`, while the local integrals are converted
to global ones using the `1`-separation. -/
theorem well_spaced_block_mean_value :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N K : ℕ) (a : ℕ → ℂ) (R : ℕ) (t : Fin R → ℝ),
        1 ≤ N →
        (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
        (∀ i, t i ∈ Set.Icc (0 : ℝ) (K : ℝ)) →
        (∑ r, ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (Complex.I * (t r : ℂ))‖ ^ 2)
          ≤ C * ((K : ℝ) + (N : ℝ)) * (∑ n ∈ Finset.Icc N (2 * N), ‖a n‖ ^ 2) := by
  obtain ⟨C_MV, hC_MV_pos, hMV⟩ :=
    Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies
  refine ⟨(2 + 2 * (Real.log 2)^2) * (2 + 4 * C_MV), ?_, ?_⟩
  · have h1 : (0:ℝ) < 2 + 2 * (Real.log 2)^2 := by
      nlinarith [sq_nonneg (Real.log 2)]
    have h2 : (0:ℝ) < 2 + 4 * C_MV := by linarith
    exact mul_pos h1 h2
  · intro N K a R t hN hsep ht
    classical
    have hK0 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
    have hN0 : N ≠ 0 := by omega
    let μ : Fin (N+1) → ℝ := fun k => Real.log (((N:ℝ) + (k:ℕ)) / (N:ℝ))
    let cc : Fin (N+1) → ℂ := fun k => a (N + (k:ℕ))
    let Gf : ℝ → ℂ := fun s => ∑ k : Fin (N+1),
      cc k * Complex.exp (Complex.I * ((μ k : ℂ) * (s:ℂ)))
    let Gd : ℝ → ℂ := fun s => ∑ k : Fin (N+1),
      (cc k * (Complex.I * (μ k : ℂ))) * Complex.exp (Complex.I * ((μ k : ℂ) * (s:ℂ)))
    -- frequency separation
    have hbasic : ∀ i j : Fin (N+1), (i:ℕ) < (j:ℕ) → (1/(4*(N:ℝ))) ≤ μ j - μ i := by
      intro i j hij
      have hji : (1:ℝ) ≤ (j:ℕ) - (i:ℕ) := by
        have h2 : (i:ℕ) + 1 ≤ (j:ℕ) := hij
        have h3 : (((i:ℕ):ℝ) + 1) ≤ ((j:ℕ):ℝ) := by exact_mod_cast h2
        linarith
      have hjle : (j:ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
      have hden : ((N:ℝ) + (j:ℕ)) ≤ 2*(N:ℝ) := by
        have : (j:ℝ) ≤ (N:ℝ) := by exact_mod_cast hjle
        linarith
      have hdenpos : (0:ℝ) < (N:ℝ) + (j:ℕ) := by positivity
      have hxpos : (0:ℝ) < (((N:ℝ) + (i:ℕ)) / ((N:ℝ) + (j:ℕ))) := by positivity
      have hlogj : μ j = Real.log ((N:ℝ)+(j:ℕ)) - Real.log (N:ℝ) := by
        simp only [μ]; rw [Real.log_div (by positivity) (by positivity)]
      have hlogi : μ i = Real.log ((N:ℝ)+(i:ℕ)) - Real.log (N:ℝ) := by
        simp only [μ]; rw [Real.log_div (by positivity) (by positivity)]
      have hlog : Real.log (((N:ℝ)+(i:ℕ)) / ((N:ℝ)+(j:ℕ))) = -(μ j - μ i) := by
        rw [Real.log_div (by positivity) (by positivity), hlogj, hlogi]
        ring
      have hle := Real.log_le_sub_one_of_pos hxpos
      have hfrac : 1 - ((N:ℝ)+(i:ℕ))/((N:ℝ)+(j:ℕ)) = ((j:ℕ)-(i:ℕ))/((N:ℝ)+(j:ℕ)) := by
        field_simp; ring
      have hstep1 : (1:ℝ)/((N:ℝ)+(j:ℕ)) ≤ ((j:ℕ)-(i:ℕ))/((N:ℝ)+(j:ℕ)) :=
        div_le_div_of_nonneg_right hji (le_of_lt hdenpos)
      have hstep2 : (1:ℝ)/(2*(N:ℝ)) ≤ 1/((N:ℝ)+(j:ℕ)) :=
        one_div_le_one_div_of_le hdenpos hden
      have hstep3 : (1:ℝ)/(4*(N:ℝ)) ≤ 1/(2*(N:ℝ)) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      linarith [hlog, hle, hfrac, hstep1, hstep2, hstep3]
    have hq : (0:ℝ) < 1/(4*(N:ℝ)) := by positivity
    have hsepμ : ∀ i j : Fin (N+1), i ≠ j → (1/(4*(N:ℝ))) ≤ |μ i - μ j| := by
      intro i j hij
      have hne : (i:ℕ) ≠ (j:ℕ) := fun h => hij (Fin.ext h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h := hbasic i j hlt
        have hneg : μ i - μ j < 0 := by linarith
        rw [abs_of_neg hneg]; linarith
      · have h := hbasic j i hgt
        have hpos : 0 < μ i - μ j := by linarith
        rw [abs_of_pos hpos]; linarith
    -- bounds on the frequencies
    have hμnn : ∀ k : Fin (N+1), 0 ≤ μ k := by
      intro k
      simp only [μ]
      apply Real.log_nonneg
      have hk : (k:ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
      rw [le_div_iff₀ hNpos]
      linarith [show (0:ℝ) ≤ (k:ℕ) by positivity]
    have hμle : ∀ k : Fin (N+1), μ k ≤ Real.log 2 := by
      intro k
      simp only [μ]
      apply Real.log_le_log (by positivity)
      have hk : (k:ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
      rw [div_le_iff₀ hNpos]
      have : ((k:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hk
      linarith
    -- continuity and derivative
    have hGf_cont : Continuous Gf := by
      have : Continuous (fun s : ℝ => ∑ k : Fin (N+1),
          cc k * Complex.exp (Complex.I * ((μ k : ℂ) * (s:ℂ)))) := by
        apply continuous_finsetSum
        intro k _
        fun_prop
      simpa only [Gf] using this
    have hGd_cont : Continuous Gd := by
      have : Continuous (fun s : ℝ => ∑ k : Fin (N+1),
          (cc k * (Complex.I * (μ k : ℂ))) * Complex.exp (Complex.I * ((μ k : ℂ) * (s:ℂ)))) := by
        apply continuous_finsetSum
        intro k _
        fun_prop
      simpa only [Gd] using this
    have hterm_deriv : ∀ k : Fin (N+1), ∀ s : ℝ,
        HasDerivAt (fun y : ℝ => cc k * Complex.exp (Complex.I * ((μ k : ℂ) * (y : ℂ))))
          ((cc k * (Complex.I * (μ k : ℂ))) * Complex.exp (Complex.I * ((μ k : ℂ) * (s : ℂ)))) s := by
      intro k s
      have hlin : HasDerivAt (fun y : ℝ => (Complex.I * (μ k : ℂ)) * (y : ℂ))
          (Complex.I * (μ k : ℂ)) s := by
        have h0 := (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (Complex.I * (μ k : ℂ))
        simpa using h0
      have hexp : HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * ((μ k : ℂ) * (y : ℂ))))
          (Complex.exp (Complex.I * ((μ k : ℂ) * (s : ℂ))) * (Complex.I * (μ k : ℂ))) s := by
        have h1 := (Complex.hasDerivAt_exp ((Complex.I * (μ k : ℂ)) * (s : ℂ))).comp s hlin
        have hfun : (Complex.exp ∘ fun y : ℝ => (Complex.I * (μ k : ℂ)) * (y : ℂ))
            = (fun y : ℝ => Complex.exp (Complex.I * ((μ k : ℂ) * (y : ℂ)))) := by
          funext y; simp only [Function.comp_apply]; congr 1; ring
        have hval : Complex.exp ((Complex.I * (μ k : ℂ)) * (s : ℂ)) * (Complex.I * (μ k : ℂ))
            = Complex.exp (Complex.I * ((μ k : ℂ) * (s : ℂ))) * (Complex.I * (μ k : ℂ)) := by
          congr 1; ring
        rw [hfun, hval] at h1
        exact h1
      have h2 := hexp.const_mul (cc k)
      refine h2.congr_deriv ?_
      ring
    have hGf_deriv : ∀ s : ℝ, HasDerivAt Gf (Gd s) s := by
      intro s
      have h := HasDerivAt.sum (u := Finset.univ) (fun k _ => hterm_deriv k s)
      have hfun : (∑ i : Fin (N+1), fun y : ℝ => cc i * Complex.exp (Complex.I * ((μ i : ℂ) * (y:ℂ))))
          = Gf := by
        funext y; simp only [Finset.sum_apply, Gf]
      have hval : (∑ i : Fin (N+1), cc i * (Complex.I * (μ i:ℂ))
            * Complex.exp (Complex.I * ((μ i:ℂ) * (s:ℂ)))) = Gd s := by
        simp only [Gd]
      rw [hfun, hval] at h
      exact h
    -- integral mean value bounds
    have hIntGf : (∫ x in (-1:ℝ)..((K:ℝ)+1), ‖Gf x‖^2)
        ≤ (((K:ℝ)+2) + 4*C_MV*(N:ℝ)) * (∑ k : Fin (N+1), ‖cc k‖^2) := by
      have h := hMV (1/(4*(N:ℝ))) (by positivity) (N+1) μ cc hsepμ (-1) ((K:ℝ)+1) (by linarith)
      have heq : (((K:ℝ)+1) - (-1) + C_MV / (1/(4*(N:ℝ)))) = ((K:ℝ)+2) + 4*C_MV*(N:ℝ) := by
        field_simp
        ring
      rw [heq] at h
      simpa only [Gf] using h
    have hbnd : (∑ k : Fin (N+1), ‖cc k * (Complex.I * (μ k : ℂ))‖^2)
        ≤ (Real.log 2)^2 * (∑ k : Fin (N+1), ‖cc k‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      have h1 : ‖cc k * (Complex.I * (μ k : ℂ))‖ = ‖cc k‖ * ‖μ k‖ := by
        simp
      have h2 : ‖μ k‖ ≤ Real.log 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hμnn k)]; exact hμle k
      calc ‖cc k * (Complex.I * (μ k : ℂ))‖^2 = (‖cc k‖ * ‖μ k‖)^2 := by rw [h1]
        _ ≤ (‖cc k‖ * Real.log 2)^2 := by
              apply sq_le_sq'
              · have hnn1 : 0 ≤ ‖cc k‖ * ‖μ k‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
                have hnn2 : 0 ≤ ‖cc k‖ * Real.log 2 :=
                  mul_nonneg (norm_nonneg _) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
                linarith
              · exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = (Real.log 2)^2 * ‖cc k‖^2 := by ring
    have hIntGd : (∫ x in (-1:ℝ)..((K:ℝ)+1), ‖Gd x‖^2)
        ≤ (((K:ℝ)+2) + 4*C_MV*(N:ℝ)) * ((Real.log 2)^2 * (∑ k : Fin (N+1), ‖cc k‖^2)) := by
      have h := hMV (1/(4*(N:ℝ))) (by positivity) (N+1) μ
        (fun k => cc k * (Complex.I * (μ k : ℂ))) hsepμ (-1) ((K:ℝ)+1) (by linarith)
      have heq : (((K:ℝ)+1) - (-1) + C_MV / (1/(4*(N:ℝ)))) = ((K:ℝ)+2) + 4*C_MV*(N:ℝ) := by
        field_simp
        ring
      rw [heq] at h
      have hGdeq : (fun x : ℝ => ‖Gd x‖^2)
          = fun x : ℝ => ‖∑ k : Fin (N+1), (cc k * (Complex.I * (μ k : ℂ)))
              * Complex.exp (Complex.I * ((μ k : ℂ) * (x:ℂ)))‖^2 := by
        funext x; simp only [Gd]
      rw [hGdeq]
      have hcoef : (0:ℝ) ≤ ((K:ℝ)+2) + 4*C_MV*(N:ℝ) := by
        have := hC_MV_pos.le; nlinarith [hK0, hNpos.le]
      exact le_trans h (mul_le_mul_of_nonneg_left hbnd hcoef)
    -- assemble
    have hgal := gallagher_sum_bound hGf_deriv hGd_cont hK0 t hsep ht
    have hmain : (∑ r, ‖Gf (t r)‖^2)
        ≤ (((K:ℝ)+2) + 4*C_MV*(N:ℝ)) * (2 + 2*(Real.log 2)^2)
            * (∑ k : Fin (N+1), ‖cc k‖^2) := by
      have : (∑ r, ‖Gf (t r)‖^2)
          ≤ 2 * ((((K:ℝ)+2) + 4*C_MV*(N:ℝ)) * (∑ k : Fin (N+1), ‖cc k‖^2))
            + 2 * ((((K:ℝ)+2) + 4*C_MV*(N:ℝ)) * ((Real.log 2)^2 * (∑ k : Fin (N+1), ‖cc k‖^2))) := by
        linarith [hgal, hIntGf, hIntGd]
      calc (∑ r, ‖Gf (t r)‖^2)
          ≤ 2 * ((((K:ℝ)+2) + 4*C_MV*(N:ℝ)) * (∑ k : Fin (N+1), ‖cc k‖^2))
            + 2 * ((((K:ℝ)+2) + 4*C_MV*(N:ℝ)) * ((Real.log 2)^2 * (∑ k : Fin (N+1), ‖cc k‖^2))) := this
        _ = (((K:ℝ)+2) + 4*C_MV*(N:ℝ)) * (2 + 2*(Real.log 2)^2)
              * (∑ k : Fin (N+1), ‖cc k‖^2) := by ring
    -- identify the two sides
    have hLHS : (∑ r, ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (Complex.I * (t r : ℂ))‖ ^ 2)
        = ∑ r, ‖Gf (t r)‖^2 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [block_cpow_eq N hN a (t r), norm_mul, norm_phase, one_mul]
    have hcoef : (∑ k : Fin (N+1), ‖cc k‖^2) = ∑ n ∈ Finset.Icc N (2 * N), ‖a n‖^2 := by
      rw [← sum_Icc_eq_sum_fin N (fun n => ‖a n‖^2)]
    have hmain' : (∑ r, ‖Gf (t r)‖^2)
        ≤ (((K:ℝ)+2) + 4*C_MV*(N:ℝ)) * (2 + 2*(Real.log 2)^2)
            * (∑ n ∈ Finset.Icc N (2 * N), ‖a n‖^2) := by
      rw [← hcoef]; exact hmain
    have hstep : (((K:ℝ)+2) + 4*C_MV*(N:ℝ)) ≤ (2 + 4*C_MV) * ((K:ℝ)+(N:ℝ)) := by
      have h1 : (0:ℝ) ≤ (K:ℝ) := hK0
      have h2 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      nlinarith [hC_MV_pos.le]
    have h3 : (0:ℝ) ≤ 2 + 2*(Real.log 2)^2 := by nlinarith [sq_nonneg (Real.log 2)]
    have h4 : (0:ℝ) ≤ ∑ n ∈ Finset.Icc N (2*N), ‖a n‖^2 :=
      Finset.sum_nonneg (fun n _ => sq_nonneg _)
    have hfin : (((K:ℝ)+2) + 4*C_MV*(N:ℝ)) * (2 + 2*(Real.log 2)^2)
          * (∑ n ∈ Finset.Icc N (2*N), ‖a n‖^2)
        ≤ ((2 + 2*(Real.log 2)^2) * (2 + 4 * C_MV)) * ((K:ℝ)+(N:ℝ))
          * (∑ n ∈ Finset.Icc N (2*N), ‖a n‖^2) := by
      apply mul_le_mul_of_nonneg_right _ h4
      calc (((K:ℝ)+2) + 4*C_MV*(N:ℝ)) * (2 + 2*(Real.log 2)^2)
          ≤ ((2 + 4*C_MV) * ((K:ℝ)+(N:ℝ))) * (2 + 2*(Real.log 2)^2) :=
            mul_le_mul_of_nonneg_right hstep h3
        _ = ((2 + 2*(Real.log 2)^2) * (2 + 4*C_MV)) * ((K:ℝ)+(N:ℝ)) := by ring
    rw [hLHS]
    exact le_trans hmain' hfin

end Commons.Analysis.DirichletPolynomial
