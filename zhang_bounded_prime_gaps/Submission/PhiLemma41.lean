import Submission.PhiFourier
import Submission.PairwiseLemma41
import Submission.Commons.Analysis.Normed.tailProduct_norm_sub_one_le

open scoped BigOperators Topology FourierTransform SchwartzMap
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

/-!
# The `φ`-denominator Lemma 4.1 (the prime-sum divisor asymptotics)

Polymath8a Lemma 4.1: "the same claim holds if the denominators `[d_j,d'_j]` are
replaced by `φ([d_j,d'_j])`".  The `φ`-Euler kernel `pairKernelPhi`
(`Submission.PhiKernel`) differs from the plain one by the factor
`∏(K^φ_p/K_p)`, whose local factors satisfy `K^φ_p/K_p = 1 + O(p⁻²)` uniformly
in the sieve weights; since the sieve's modulus family excludes *all* primes up
to `w x → ∞`, the two kernels agree to relative order `exp(C/w x) − 1 → 0`.

Hence the `φ`-denominator divisor sum has the same main term as the plain one
(`pairwiseLemma41`): `(1+o(1))·(prefactor)^k·∏∫₀^∞ F_j′G_j′`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The `φ`-denominator kernel in the `ξ`-parametrization of the truncation. -/
noncomputable def pairKernelPhiP {k : ℕ} (W N : ℕ → ℕ) (x : ℕ) (p : Fin k → ℝ × ℝ) : ℂ :=
  pairKernelPhi ((W x) * (N x)) (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
    (fun j => logZ (-(2 * Real.pi * (p j).2)) x)

/-! ## Comparison of the local factors -/

/-- The plain local factor is at least `1/2` in norm when `p > 6k`. -/
lemma norm_coordLocalK_ge_half {k : ℕ} (p : ℕ) (hp2 : 2 ≤ p) (hp6 : 6 * k < p)
    (a b : Fin k → ℂ) (ha : ∀ j, 0 ≤ (a j).re) (hb : ∀ j, 0 ≤ (b j).re) :
    (1 / 2 : ℝ) ≤ ‖coordLocalK p a b‖ := by
  have hp0 : p ≠ 0 := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have h6k : (6 * (k : ℝ)) < (p : ℝ) := by
    have : ((6 * k : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast hp6
    simpa using this
  have hsig : ‖∑ j : Fin k, (-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
      ((p : ℂ) ^ (-(1 + a j + b j))))‖ ≤ 3 * (k : ℝ) / (p : ℝ) := by
    calc ‖∑ j : Fin k, (-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
          ((p : ℂ) ^ (-(1 + a j + b j))))‖
        ≤ ∑ j : Fin k, ‖-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
            ((p : ℂ) ^ (-(1 + a j + b j)))‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin k, (3 / (p : ℝ)) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have h1 : ‖(p : ℂ) ^ (-(1 + a j))‖ ≤ (p : ℝ)⁻¹ :=
            norm_cpow_neg_le_inv hp2 (s := 1 + a j) (by
              rw [Complex.add_re, Complex.one_re]; linarith [ha j])
          have h2 : ‖(p : ℂ) ^ (-(1 + b j))‖ ≤ (p : ℝ)⁻¹ :=
            norm_cpow_neg_le_inv hp2 (s := 1 + b j) (by
              rw [Complex.add_re, Complex.one_re]; linarith [hb j])
          have h3 : ‖(p : ℂ) ^ (-(1 + a j + b j))‖ ≤ (p : ℝ)⁻¹ :=
            norm_cpow_neg_le_inv hp2 (s := 1 + a j + b j) (by
              rw [Complex.add_re, Complex.add_re, Complex.one_re]; linarith [ha j, hb j])
          have h4 : ‖-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j)))‖ ≤
              ‖(p : ℂ) ^ (-(1 + a j))‖ + ‖(p : ℂ) ^ (-(1 + b j))‖ := by
            have := norm_add_le (-((p : ℂ) ^ (-(1 + a j)))) (-((p : ℂ) ^ (-(1 + b j))))
            rw [norm_neg, norm_neg] at this
            simpa [sub_eq_add_neg] using this
          have h5 := norm_add_le (-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))))
            ((p : ℂ) ^ (-(1 + a j + b j)))
          calc ‖-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
                ((p : ℂ) ^ (-(1 + a j + b j)))‖
              ≤ ‖-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j)))‖ +
                ‖(p : ℂ) ^ (-(1 + a j + b j))‖ := h5
            _ ≤ (‖(p : ℂ) ^ (-(1 + a j))‖ + ‖(p : ℂ) ^ (-(1 + b j))‖) +
                ‖(p : ℂ) ^ (-(1 + a j + b j))‖ := by linarith [h4]
            _ ≤ 3 * (p : ℝ)⁻¹ := by linarith [h1, h2, h3]
            _ = 3 / (p : ℝ) := by rw [div_eq_mul_inv]
      _ = 3 * (k : ℝ) / (p : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [coordLocalK_eq p hp0 a b]
  set sig : ℂ := ∑ j : Fin k, (-((p : ℂ) ^ (-(1 + a j))) - ((p : ℂ) ^ (-(1 + b j))) +
    ((p : ℂ) ^ (-(1 + a j + b j)))) with hsigdef
  have hsig' : ‖sig‖ ≤ 3 * (k : ℝ) / (p : ℝ) := hsig
  have h := norm_sub_norm_le (1 : ℂ) (-sig)
  rw [norm_neg, norm_one] at h
  have hsub : (1 : ℂ) - (-sig) = 1 + sig := by ring
  rw [hsub] at h
  have h3k : 3 * (k : ℝ) / (p : ℝ) ≤ (1 : ℝ) / 2 := by
    rw [div_le_iff₀ hpR]
    linarith [h6k]
  linarith

/-- Pointwise comparison of the `φ`-local factor with the plain one:
`‖K^φ_p/K_p − 1‖ ≤ 12k/p²` for `p > 6k`. -/
lemma norm_phiLocal_div_plainLocal_sub_one_le {k : ℕ} (p : ℕ) (hp2 : 2 ≤ p) (hp6 : 6 * k < p)
    (a b : Fin k → ℂ) (ha : ∀ j, 0 ≤ (a j).re) (hb : ∀ j, 0 ≤ (b j).re) :
    ‖coordLocalKPhi p a b / coordLocalK p a b - 1‖ ≤ 12 * k / (p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hp1R : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hKge : (1 / 2 : ℝ) ≤ ‖coordLocalK p a b‖ :=
    norm_coordLocalK_ge_half p hp2 hp6 a b ha hb
  have hpos : 0 < ‖coordLocalK p a b‖ := by linarith
  have hdiff := norm_coordLocalKPhi_sub_coordLocalK_le p hp2 a b ha hb
  have hne : coordLocalK p a b ≠ 0 := by
    intro h0
    rw [h0] at hpos
    norm_num at hpos
  rw [div_sub_one hne, norm_div]
  have hstep : (3 * (k : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) / ((1 : ℝ) / 2) ≤
      12 * (k : ℝ) / (p : ℝ) ^ 2 := by
    have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hpp1 : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    have hden : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) * ((1 : ℝ) / 2) := by positivity
    have hsq : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [div_div, div_le_div_iff₀ hden hsq]
    have hred : 12 * (k : ℝ) * ((p : ℝ) * ((p : ℝ) - 1) * ((1 : ℝ) / 2)) =
        6 * (k : ℝ) * ((p : ℝ) * ((p : ℝ) - 1)) := by ring
    rw [hred]
    have hp2' : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
    have hfac : (0 : ℝ) ≤ 3 * (k : ℝ) * (p : ℝ) * ((p : ℝ) - 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk) hpR.le) hp2'
    nlinarith [hfac]
  calc ‖coordLocalKPhi p a b - coordLocalK p a b‖ / ‖coordLocalK p a b‖
      ≤ (3 * (k : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) / ((1 : ℝ) / 2) := by
        apply div_le_div₀ (by positivity) hdiff (by norm_num) hKge
    _ ≤ 12 * (k : ℝ) / (p : ℝ) ^ 2 := hstep

/-! ## Comparison of the `φ`-kernel with the plain kernel -/

/-- The primes of `Sfilter q n` are all `> m` when every prime `≤ m` divides
`q`. -/
lemma Sfilter_gt_of_prime_dvd {q m n : ℕ} (hm : ∀ p : ℕ, p.Prime → p ≤ m → p ∣ q)
    {p : ℕ} (hp : p ∈ Sfilter q n) : m < p := by
  by_contra hle
  push Not at hle
  have hprime : p.Prime := Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
  have hpndvd : ¬ p ∣ q := (Finset.mem_filter.mp hp).2
  exact hpndvd (hm p hprime hle)

/-- **Comparison of the `φ`-Euler kernel with the plain one.**  When every prime
`≤ m` divides `q` (with `m ≥ 6k`), the two Euler products agree to relative
order `exp(12k/m) − 1`. -/
theorem norm_pairKernelPhi_sub_pairKernel_le {k : ℕ} (hk : 1 ≤ k) (q m : ℕ) (hq : q ≠ 0)
    (hm : ∀ p : ℕ, p.Prime → p ≤ m → p ∣ q) (hm6 : 6 * k ≤ m)
    {a b : Fin k → ℂ} (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) :
    ‖pairKernelPhi q a b - pairKernel q a b‖ ≤
      (Real.exp (12 * (k : ℝ) / (m : ℝ)) - 1) * ‖pairKernel q a b‖ := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hfactor : ∀ n : ℕ, ‖(∏ p ∈ Sfilter q n, coordLocalKPhi p a b) -
        (∏ p ∈ Sfilter q n, coordLocalK p a b)‖ ≤
      (Real.exp (12 * (k : ℝ) / (m : ℝ)) - 1) * ‖∏ p ∈ Sfilter q n, coordLocalK p a b‖ := by
    intro n
    have hKne : ∀ p ∈ Sfilter q n, coordLocalK p a b ≠ 0 := by
      intro p hp
      have hpgt : m < p := Sfilter_gt_of_prime_dvd hm hp
      have hp6 : 6 * k < p := by omega
      have hp2 : 2 ≤ p := by omega
      have hge := norm_coordLocalK_ge_half p hp2 hp6 a b (fun j => (ha j).le) (fun j => (hb j).le)
      intro h0
      rw [h0] at hge
      norm_num at hge
    have hsplit : (∏ p ∈ Sfilter q n, coordLocalKPhi p a b) =
        (∏ p ∈ Sfilter q n, coordLocalK p a b) *
          (∏ p ∈ Sfilter q n, coordLocalKPhi p a b / coordLocalK p a b) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun p hp => ?_)
      field_simp [hKne p hp]
    have hratio : ‖(∏ p ∈ Sfilter q n, coordLocalKPhi p a b / coordLocalK p a b) - 1‖ ≤
        Real.exp (12 * (k : ℝ) / (m : ℝ)) - 1 := by
      have hz : ∀ p ∈ Sfilter q n,
          ‖coordLocalKPhi p a b / coordLocalK p a b - 1‖ ≤
            12 * (k : ℝ) / (p : ℝ) ^ 2 := by
        intro p hp
        have hpgt : m < p := Sfilter_gt_of_prime_dvd hm hp
        have hp6 : 6 * k < p := by omega
        have hp2 : 2 ≤ p := by omega
        exact norm_phiLocal_div_plainLocal_sub_one_le p hp2 hp6 a b
          (fun j => (ha j).le) (fun j => (hb j).le)
      have hS : ∀ p ∈ Sfilter q n, m < p := fun p hp => Sfilter_gt_of_prime_dvd hm hp
      have h := Commons.Analysis.Normed.tailProduct_norm_sub_one_le
        (C := 12 * (k : ℝ)) (by positivity) (w := m) hm1 hS
        (z := fun p => coordLocalKPhi p a b / coordLocalK p a b - 1) hz
      simpa using h
    calc ‖(∏ p ∈ Sfilter q n, coordLocalKPhi p a b) -
          (∏ p ∈ Sfilter q n, coordLocalK p a b)‖
        = ‖(∏ p ∈ Sfilter q n, coordLocalK p a b) *
            ((∏ p ∈ Sfilter q n, coordLocalKPhi p a b / coordLocalK p a b) - 1)‖ := by
          rw [hsplit]
          congr 1
          ring
      _ = ‖∏ p ∈ Sfilter q n, coordLocalK p a b‖ *
            ‖(∏ p ∈ Sfilter q n, coordLocalKPhi p a b / coordLocalK p a b) - 1‖ :=
          norm_mul _ _
      _ ≤ ‖∏ p ∈ Sfilter q n, coordLocalK p a b‖ *
            (Real.exp (12 * (k : ℝ) / (m : ℝ)) - 1) :=
          mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
      _ = (Real.exp (12 * (k : ℝ) / (m : ℝ)) - 1) *
            ‖∏ p ∈ Sfilter q n, coordLocalK p a b‖ := by ring
  have hA := tendsto_pairKernelPhi q hq ha hb
  have hB := tendsto_pairKernel q hq ha hb
  have h1 : Tendsto (fun n : ℕ => ‖(∏ p ∈ Sfilter q n, coordLocalKPhi p a b) -
      (∏ p ∈ Sfilter q n, coordLocalK p a b)‖) atTop
      (𝓝 ‖pairKernelPhi q a b - pairKernel q a b‖) := (hA.sub hB).norm
  have h2 : Tendsto (fun n : ℕ => (Real.exp (12 * (k : ℝ) / (m : ℝ)) - 1) *
      ‖∏ p ∈ Sfilter q n, coordLocalK p a b‖) atTop
      (𝓝 ((Real.exp (12 * (k : ℝ) / (m : ℝ)) - 1) * ‖pairKernel q a b‖)) :=
    hB.norm.const_mul _
  exact le_of_tendsto_of_tendsto' h1 h2 (fun n => hfactor n)


/-! ## An absolute integrability bound for the plain kernel -/

/-- The `ξ`-integral of `‖pole·Φ‖` over the truncation cube is bounded by
`prefactor^k·∏(pairCF)`. -/
lemma pole_cube_integral_le {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    {x : ℕ} (hx2 : 2 ≤ x) :
    (∫ p in truncCubeK k x,
        ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖) ≤
      prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) := by
  have hx1 : 1 < x := by omega
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
  have hIntP := integrable_pairPoleP_mul_pairPhase F G hcsF hsmF hcsG hsmG W N hW hN hx2
  have hIntDom := integrable_pairDom F G hcsF hsmF hcsG hsmG
  have hpt : ∀ p : Fin k → ℝ × ℝ,
      ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖ ≤
        prefactor W N x ^ k * pairDom F G p := by
    intro p
    rw [norm_mul, norm_pairPhase_eq F G p]
    have hw := norm_pairPoleP_le W N hW hN hlogpos p
    have hid := prodW_mul_phaseNorm_eq_pairDom F G p
    calc ‖pairPoleP (k := k) W N x p‖ * pairPhaseNorm F G p
        ≤ (prefactor W N x ^ k * ∏ j : Fin k, (pairW (p j).1 * pairW (p j).2)) *
            pairPhaseNorm F G p :=
          mul_le_mul_of_nonneg_right hw (pairPhaseNorm_nonneg F G p)
      _ = prefactor W N x ^ k *
            ((∏ j : Fin k, (pairW (p j).1 * pairW (p j).2)) * pairPhaseNorm F G p) := by ring
      _ = prefactor W N x ^ k * pairDom F G p := by rw [hid]
  calc (∫ p in truncCubeK k x,
        ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖)
      ≤ ∫ p in truncCubeK k x, prefactor W N x ^ k * pairDom F G p :=
        setIntegral_mono_on hIntP.norm.integrableOn (hIntDom.const_mul _).integrableOn
          (measurableSet_truncCubeK k x) (fun p _ => hpt p)
    _ ≤ ∫ p : Fin k → ℝ × ℝ, prefactor W N x ^ k * pairDom F G p :=
        setIntegral_le_integral (hIntDom.const_mul _)
          (Eventually.of_forall (fun p => mul_nonneg (pow_nonneg (prefactor_nonneg W N hW hN hx2) k)
            (pairDom_nonneg F G p)))
    _ = prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) := by
        rw [MeasureTheory.integral_const_mul, integral_pairDom]

/-- **Absolute bound for the plain kernel integral.** -/
theorem pairKernelP_abs_integral_le {k : ℕ} (hk : 1 ≤ k) (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, x₀ ≤ x →
      (∫ p : Fin k → ℝ × ℝ,
          ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖) ≤
        C * prefactor W N x ^ k := by
  classical
  set m : ℕ := 8 * k + 2 with hmdef
  obtain ⟨x₀c, εc, hεc, hcube⟩ :=
    pairCube_integral_le hk F G hcsF hsmF hcsG hsmG W N hW hN hcop w hw hsmall hlq
  obtain ⟨x₀k, Ck, hCkpos, hoffk⟩ := pairOffCube_le hk F G hcsF hsmF hcsG hsmG W N hW hN m
  obtain ⟨x₀K, CK, hCKpos, hKbd⟩ := pairKernelP_bound_eventually k
  have hεabs : Tendsto (fun x : ℕ => |εc x|) atTop (𝓝 (0 : ℝ)) := by
    simpa using hεc.abs
  have hε1ev : ∀ᶠ x : ℕ in atTop, |εc x| ≤ 1 :=
    (hεabs.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)).mono
      (fun x hx => le_of_lt hx)
  obtain ⟨x₀ε, hεev⟩ := Filter.eventually_atTop.mp hε1ev
  refine ⟨max (max (max x₀c x₀k) (max x₀K x₀ε)) 4,
    2 * (∏ j : Fin k, (pairCF (F j) * pairCF (G j))) + Ck * (2 * Real.pi) ^ m + 1, ?_, ?_⟩
  · have hCfg0 : (0 : ℝ) ≤ ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) :=
      Finset.prod_nonneg (fun j _ => mul_nonneg (pairCF_nonneg F j) (pairCF_nonneg G j))
    have h3 : (0 : ℝ) ≤ Ck * (2 * Real.pi) ^ m := by positivity
    linarith
  · intro x hx
    have hx2 : 2 ≤ x := by omega
    have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
    have hx1 : 1 < x := by omega
    have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
    have hxc : x₀c ≤ x := le_trans (le_trans (le_trans (le_max_left x₀c x₀k)
      (le_max_left _ _)) (le_max_left _ _)) hx
    have hxk : x₀k ≤ x := le_trans (le_trans (le_max_right x₀c x₀k)
      (le_max_left _ _)) (le_trans (le_max_left _ _) hx)
    have hxK : x₀K ≤ x := le_trans (le_trans (le_max_left x₀K x₀ε)
      (le_max_right _ _)) (le_trans (le_max_left _ _) hx)
    have hxε : x₀ε ≤ x := le_trans (le_trans (le_max_right x₀K x₀ε)
      (le_max_right _ _)) (le_trans (le_max_left _ _) hx)
    have hε1 : |εc x| ≤ 1 := hεev x hxε
    have hpre0 := prefactor_nonneg W N hW hN hx2
    have hIntK := integrable_pairKernelP_mul_pairPhase F G hcsF hsmF hcsG hsmG W N
      (hKbd x hxK W N hW hN)
    have hIntP := integrable_pairPoleP_mul_pairPhase F G hcsF hsmF hcsG hsmG W N hW hN hx2
    have hsplit : (∫ p : Fin k → ℝ × ℝ,
          ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖) =
        (∫ p in truncCubeK k x,
            ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖) +
          (∫ p in (truncCubeK k x)ᶜ,
            ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖) :=
      (MeasureTheory.integral_add_compl (measurableSet_truncCubeK k x) hIntK.norm).symm
    rw [hsplit]
    -- the cube part
    have hcubeB : (∫ p in truncCubeK k x,
          ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖) ≤
        2 * (∏ j : Fin k, (pairCF (F j) * pairCF (G j))) * prefactor W N x ^ k := by
      have hpt : ∀ p : Fin k → ℝ × ℝ,
          ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖ ≤
            ‖(pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) *
              pairPhase (k := k) F G p‖ +
              ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖ := by
        intro p
        have h := norm_add_le ((pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) *
          pairPhase (k := k) F G p) (pairPoleP (k := k) W N x p * pairPhase (k := k) F G p)
        calc ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖
            = ‖(pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) *
                pairPhase (k := k) F G p + pairPoleP (k := k) W N x p *
                pairPhase (k := k) F G p‖ := by
              congr 1; ring
          _ ≤ _ := h
      have hIntA : Integrable fun p : Fin k → ℝ × ℝ =>
          ‖(pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) *
            pairPhase (k := k) F G p‖ := by
        have hfun : (fun p : Fin k → ℝ × ℝ =>
            ‖(pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) *
              pairPhase (k := k) F G p‖) =
            fun p => ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p -
              pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖ := by
          funext p
          congr 1
          ring
        rw [hfun]
        exact (hIntK.sub hIntP).norm
      have hInt1 : Integrable fun p : Fin k → ℝ × ℝ =>
          ‖(pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) *
            pairPhase (k := k) F G p‖ +
          ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖ :=
        hIntA.add hIntP.norm
      have hmono := setIntegral_mono_on hIntK.norm.integrableOn hInt1.integrableOn
        (measurableSet_truncCubeK k x) (fun p _ => hpt p)
      have hsum : (∫ p in truncCubeK k x,
            (‖(pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) *
                pairPhase (k := k) F G p‖ +
              ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖)) =
          (∫ p in truncCubeK k x,
              ‖(pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) *
                pairPhase (k := k) F G p‖) +
            (∫ p in truncCubeK k x,
              ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖) :=
        MeasureTheory.integral_add hIntA.integrableOn hIntP.norm.integrableOn
      rw [hsum] at hmono
      refine hmono.trans ?_
      have h1 := hcube x hxc
      have h2 := pole_cube_integral_le F G hcsF hsmF hcsG hsmG W N hW hN hx2
      have hadd : (∫ p in truncCubeK k x,
              ‖(pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) *
                pairPhase (k := k) F G p‖) +
            (∫ p in truncCubeK k x,
              ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖) ≤
            |εc x| * prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) +
              prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) :=
        add_le_add h1 h2
      have hCfg0 : (0 : ℝ) ≤ ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) :=
        Finset.prod_nonneg (fun j _ => mul_nonneg (pairCF_nonneg F j) (pairCF_nonneg G j))
      calc (∫ p in truncCubeK k x,
              ‖(pairKernelP (k := k) W N x p - pairPoleP (k := k) W N x p) *
                pairPhase (k := k) F G p‖) +
            (∫ p in truncCubeK k x,
              ‖pairPoleP (k := k) W N x p * pairPhase (k := k) F G p‖)
          ≤ |εc x| * prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) +
              prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) := hadd
        _ ≤ 2 * (∏ j : Fin k, (pairCF (F j) * pairCF (G j))) * prefactor W N x ^ k := by
            have h1 : |εc x| * prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) ≤
                1 * prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hε1 (pow_nonneg hpre0 k)) hCfg0
            have h2 : prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) =
                1 * prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) := by ring
            rw [h2]
            calc |εc x| * prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) +
                  1 * prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j))
                ≤ 1 * prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) +
                  1 * prefactor W N x ^ k * ∏ j : Fin k, (pairCF (F j) * pairCF (G j)) :=
                  add_le_add h1 le_rfl
              _ = 2 * (∏ j : Fin k, (pairCF (F j) * pairCF (G j))) * prefactor W N x ^ k := by ring
    -- the off-cube part
    have hoffB : (∫ p in (truncCubeK k x)ᶜ,
          ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖) ≤
        Ck * (2 * Real.pi) ^ m * prefactor W N x ^ k := by
      refine (hoffk x hxk).trans ?_
      have hm2 : m = 2 * (4 * k + 1) := by omega
      have hroot : (Real.sqrt (Real.log (x : ℝ))) ^ m =
          (Real.log (x : ℝ)) ^ (4 * k + 1) := by
        rw [hm2, pow_mul, Real.sq_sqrt hlogpos.le]
      have hden : (Real.sqrt (Real.log (x : ℝ)) / (2 * Real.pi)) ^ m =
          (Real.log (x : ℝ)) ^ (4 * k + 1) / (2 * Real.pi) ^ m := by
        rw [div_pow, hroot]
      rw [hden]
      have hred : Ck * (Real.log (x : ℝ)) ^ (3 * k) /
            ((Real.log (x : ℝ)) ^ (4 * k + 1) / (2 * Real.pi) ^ m) =
          Ck * (2 * Real.pi) ^ m * ((Real.log (x : ℝ))⁻¹) ^ (k + 1) := by
        rw [show (Real.log (x : ℝ)) ^ (4 * k + 1) =
            (Real.log (x : ℝ)) ^ (3 * k) * (Real.log (x : ℝ)) ^ (k + 1) from by
          rw [← pow_add]; congr 1; omega,
          inv_pow]
        field_simp
      rw [hred]
      have hlog1 : 1 ≤ Real.log (x : ℝ) := by
        have h2 := Real.log_two_gt_d9
        have hle : Real.log 4 ≤ Real.log (x : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hx4)
        rw [show Real.log (4 : ℝ) = 2 * Real.log 2 from by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num] at hle
        linarith
      have hinv1 : (Real.log (x : ℝ))⁻¹ ≤ 1 := by
        rw [inv_le_one₀ hlogpos]
        exact hlog1
      have hmon1 : ((Real.log (x : ℝ))⁻¹) ^ (k + 1) ≤ ((Real.log (x : ℝ))⁻¹) ^ k := by
        rw [pow_succ]
        have hnn : (0 : ℝ) ≤ ((Real.log (x : ℝ))⁻¹) ^ k :=
          pow_nonneg (by positivity) k
        nlinarith [hinv1, hnn]
      have hmon2 : ((Real.log (x : ℝ))⁻¹) ^ k ≤ prefactor W N x ^ k :=
        pow_le_pow_left₀ (by positivity) (inv_log_le_prefactor W N hW hN hx2) k
      calc Ck * (2 * Real.pi) ^ m * ((Real.log (x : ℝ))⁻¹) ^ (k + 1)
          ≤ Ck * (2 * Real.pi) ^ m * ((Real.log (x : ℝ))⁻¹) ^ k := by
            apply mul_le_mul_of_nonneg_left hmon1
            positivity
        _ ≤ Ck * (2 * Real.pi) ^ m * prefactor W N x ^ k := by
            apply mul_le_mul_of_nonneg_left hmon2
            positivity
    have hsum2 : (∫ p in truncCubeK k x,
          ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖) +
        (∫ p in (truncCubeK k x)ᶜ,
          ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖) ≤
        (2 * (∏ j : Fin k, (pairCF (F j) * pairCF (G j))) * prefactor W N x ^ k) +
          (Ck * (2 * Real.pi) ^ m * prefactor W N x ^ k) := add_le_add hcubeB hoffB
    refine hsum2.trans ?_
    have hpre : (0 : ℝ) ≤ prefactor W N x ^ k := pow_nonneg hpre0 k
    have heq : (2 * (∏ j : Fin k, (pairCF (F j) * pairCF (G j))) * prefactor W N x ^ k) +
          (Ck * (2 * Real.pi) ^ m * prefactor W N x ^ k) =
        (2 * (∏ j : Fin k, (pairCF (F j) * pairCF (G j))) + Ck * (2 * Real.pi) ^ m) *
          prefactor W N x ^ k := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (by linarith) hpre


/-! ## Measurability and integrability of the `φ`-kernel integrand -/

/-- Continuity of the `φ`-local factor in the two weight tuples. -/
lemma continuous_coordLocalKPhi {k : ℕ} (p : ℕ) (hp : p ≠ 0) :
    Continuous fun z : (Fin k → ℂ) × (Fin k → ℂ) => coordLocalKPhi p z.1 z.2 := by
  have hcast : (((p - 1 : ℕ)) : ℂ) = (p : ℂ) - 1 := by
    have h1 : 1 ≤ p := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hEq : (fun z : (Fin k → ℂ) × (Fin k → ℂ) => coordLocalKPhi p z.1 z.2) =
      fun z => 1 + ∑ j : Fin k, (-(((p : ℂ) ^ (-(z.1 j))) * (((p - 1 : ℕ)) : ℂ)⁻¹) -
        (((p : ℂ) ^ (-(z.2 j))) * (((p - 1 : ℕ)) : ℂ)⁻¹) +
        (((p : ℂ) ^ (-(z.1 j + z.2 j))) * (((p - 1 : ℕ)) : ℂ)⁻¹)) := by
    funext z
    rw [coordLocalKPhi_eq p hp z.1 z.2]
  rw [hEq]
  refine continuous_const.add (continuous_finsetSum _ (fun j _ => ?_))
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have h1 : Continuous fun z : (Fin k → ℂ) × (Fin k → ℂ) => -(z.1 j) := by fun_prop
  have h2 : Continuous fun z : (Fin k → ℂ) × (Fin k → ℂ) => -(z.2 j) := by fun_prop
  have h3 : Continuous fun z : (Fin k → ℂ) × (Fin k → ℂ) => -(z.1 j + z.2 j) := by fun_prop
  exact (((h1.const_cpow (Or.inl hp0)).mul continuous_const).neg.sub
    ((h2.const_cpow (Or.inl hp0)).mul continuous_const)).add
    ((h3.const_cpow (Or.inl hp0)).mul continuous_const)

/-- The partial products of the `φ`-kernel are strongly measurable in `p`. -/
lemma stronglyMeasurable_pairKernelPhiP_step {k : ℕ} (W N : ℕ → ℕ) (x n : ℕ) :
    StronglyMeasurable fun p : Fin k → ℝ × ℝ =>
      ∏ pr ∈ Sfilter (W x * N x) n, coordLocalKPhi (k := k) pr
        (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
        (fun j => logZ (-(2 * Real.pi * (p j).2)) x) := by
  have hξ : Continuous fun p : Fin k → ℝ × ℝ =>
      (fun j : Fin k => logZ (-(2 * Real.pi * (p j).1)) x) := by
    refine continuous_pi (fun j => ?_)
    show Continuous fun p : Fin k → ℝ × ℝ => logZ (-(2 * Real.pi * (p j).1)) x
    unfold logZ
    fun_prop
  have hξ' : Continuous fun p : Fin k → ℝ × ℝ =>
      (fun j : Fin k => logZ (-(2 * Real.pi * (p j).2)) x) := by
    refine continuous_pi (fun j => ?_)
    show Continuous fun p : Fin k → ℝ × ℝ => logZ (-(2 * Real.pi * (p j).2)) x
    unfold logZ
    fun_prop
  have hpairs : Continuous fun p : Fin k → ℝ × ℝ =>
      ((fun j : Fin k => logZ (-(2 * Real.pi * (p j).1)) x),
        (fun j : Fin k => logZ (-(2 * Real.pi * (p j).2)) x)) := hξ.prodMk hξ'
  have hcont : Continuous fun p : Fin k → ℝ × ℝ =>
      ∏ pr ∈ Sfilter (W x * N x) n, coordLocalKPhi (k := k) pr
        (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
        (fun j => logZ (-(2 * Real.pi * (p j).2)) x) := by
    refine continuous_finsetProd _ (fun pr hpr => ?_)
    have h := (continuous_coordLocalKPhi (k := k) pr
      (Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_filter pr hpr)).ne_zero).comp hpairs
    exact h
  exact hcont.stronglyMeasurable

/-- Measurability of the `φ`-kernel in the `ξ`-variables. -/
lemma measurable_pairKernelPhiP {k : ℕ} (W N : ℕ → ℕ) (x : ℕ) :
    Measurable (pairKernelPhiP (k := k) W N x) := by
  have hstep := stronglyMeasurable_pairKernelPhiP_step (k := k) W N x
  have heq : pairKernelPhiP (k := k) W N x = fun p : Fin k → ℝ × ℝ =>
      (atTop : Filter ℕ).limUnder (fun n : ℕ =>
        ∏ pr ∈ Sfilter (W x * N x) n, coordLocalKPhi (k := k) pr
          (fun j => logZ (-(2 * Real.pi * (p j).1)) x)
          (fun j => logZ (-(2 * Real.pi * (p j).2)) x)) := rfl
  rw [heq]
  exact (StronglyMeasurable.limUnder hstep).measurable

/-- Integrability of the `φ`-kernel integrand, given the crude bound. -/
lemma integrable_pairKernelPhiP_mul_pairPhase {k : ℕ} (F G : Fin k → ℝ → ℝ)
    (hcsF : ∀ j, HasCompactSupport (F j)) (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j))
    (hcsG : ∀ j, HasCompactSupport (G j)) (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) {x : ℕ} {C : ℝ}
    (hC : ∀ p : Fin k → ℝ × ℝ,
      ‖pairKernelPhiP (k := k) W N x p‖ ≤ C * (Real.log (x : ℝ)) ^ (3 * k)) :
    Integrable fun p : Fin k → ℝ × ℝ =>
      pairKernelPhiP (k := k) W N x p * pairPhase (k := k) F G p := by
  have hbase : Integrable fun p : Fin k → ℝ × ℝ =>
      C * (Real.log (x : ℝ)) ^ (3 * k) * pairDom F G p :=
    (integrable_pairDom F G hcsF hsmF hcsG hsmG).const_mul _
  refine Integrable.mono' hbase ?_ (Filter.Eventually.of_forall (fun p => ?_))
  · exact ((measurable_pairKernelPhiP (k := k) W N x).mul
      (measurable_pairPhase F G hcsF hsmF hcsG hsmG)).aestronglyMeasurable
  · rw [norm_mul, norm_pairPhase_eq F G p]
    have h1 := hC p
    have h2 := pairPhaseNorm_le_pairDom F G p
    have h3 : 0 ≤ C * (Real.log (x : ℝ)) ^ (3 * k) := le_trans (norm_nonneg _) h1
    exact mul_le_mul h1 h2 (pairPhaseNorm_nonneg F G p) h3


/-! ## The `φ`-denominator Lemma 4.1 -/

/-- **The `φ`-denominator Lemma 4.1** (integral form).  For a family of moduli
`W, N` with all primes `≤ w x → ∞` dividing `W x·N x` and
`log(W x·N x) = o(√log x)`, the `φ`-kernel integral has the same main term as
the plain one: `(1+o(1))·(prefactor)^k·∏∫₀^∞ F_j′G_j′`. -/
theorem phiPairKernelIntegral_asymptotic {k : ℕ} (hk : 1 ≤ k)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ j, HasCompactSupport (F j))
    (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j)) (hcsG : ∀ j, HasCompactSupport (G j))
    (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x →
        ‖(∫ p : Fin k → ℝ × ℝ,
            pairKernelPhiP (k := k) W N x p * pairPhase (k := k) F G p) -
            ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
              ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖ ≤
          ε x * prefactor W N x ^ k := by
  classical
  obtain ⟨x₀p, εp, hεp, hplain⟩ :=
    pairKernelIntegral_asymptotic hk F G hcsF hsmF hcsG hsmG W N hW hN hcop w hw hsmall hlq
  obtain ⟨x₀a, Ca, hCapos, habs⟩ :=
    pairKernelP_abs_integral_le hk F G hcsF hsmF hcsG hsmG W N hW hN hcop w hw hsmall hlq
  obtain ⟨x₀K, CK, hCKpos, hKbd⟩ := pairKernelP_bound_eventually k
  have hδ : Tendsto (fun x : ℕ => Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℕ => (12 * (k : ℝ)) / (w x : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hw)
    have h2 : Tendsto (fun x : ℕ => Real.exp (12 * (k : ℝ) / (w x : ℝ))) atTop
        (𝓝 (Real.exp 0)) := (Real.continuous_exp.tendsto 0).comp h1
    rw [Real.exp_zero] at h2
    have h3 := h2.sub (tendsto_const_nhds (x := (1 : ℝ)))
    simpa using h3
  have hδ1ev : ∀ᶠ x : ℕ in atTop,
      Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1 ≤ 1 :=
    (hδ.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)).mono (fun x hx => le_of_lt hx)
  obtain ⟨x₀δ, hδ1⟩ := Filter.eventually_atTop.mp hδ1ev
  obtain ⟨x₀w, hw6⟩ := Filter.eventually_atTop.mp (hw.eventually_ge_atTop (6 * k))
  have hall : ∀ᶠ x : ℕ in atTop, (x₀p ≤ x) ∧ (x₀a ≤ x) ∧ (x₀K ≤ x) ∧ (x₀δ ≤ x) ∧
      (x₀w ≤ x) ∧ (2 ≤ x) := by
    filter_upwards [eventually_ge_atTop x₀p, eventually_ge_atTop x₀a,
      eventually_ge_atTop x₀K, eventually_ge_atTop x₀δ, eventually_ge_atTop x₀w,
      eventually_ge_atTop 2] with x hp ha hK hd hwp h2
    exact ⟨hp, ha, hK, hd, hwp, h2⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨x₀, fun x => (Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) * Ca + εp x,
    ?_, ?_⟩
  · simpa using ((hδ.mul_const Ca).add hεp)
  · intro x hx
    obtain ⟨hxp, hxa, hxK, hxδ, hxw, hx2⟩ := hx₀ x hx
    have hx1 : 1 < x := by omega
    have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
    have hlog0 : (0 : ℝ) ≤ Real.log (x : ℝ) := hlogpos.le
    have hq : W x * N x ≠ 0 := mul_ne_zero (hW x) (hN x)
    have hδle : Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1 ≤ 1 := hδ1 x hxδ
    have hδnn : 0 ≤ Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1 := by
      apply sub_nonneg.mpr
      apply Real.one_le_exp
      apply div_nonneg _ (by positivity)
      positivity
    have hL3 : (0 : ℝ) ≤ (Real.log (x : ℝ)) ^ (3 * k) := pow_nonneg hlog0 _
    -- pointwise comparison of the kernels
    have hcmp : ∀ p : Fin k → ℝ × ℝ,
        ‖pairKernelPhiP (k := k) W N x p - pairKernelP (k := k) W N x p‖ ≤
          (Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) * ‖pairKernelP (k := k) W N x p‖ := by
      intro p
      have hre : ∀ j : Fin k, 0 < (logZ (-(2 * Real.pi * (p j).1)) x).re := fun j => by
        rw [logZ_re]; exact div_pos one_pos hlogpos
      have hre' : ∀ j : Fin k, 0 < (logZ (-(2 * Real.pi * (p j).2)) x).re := fun j => by
        rw [logZ_re]; exact div_pos one_pos hlogpos
      have h := norm_pairKernelPhi_sub_pairKernel_le hk (W x * N x) (w x) hq
        (fun p hp hle => hsmall x p hp hle) (hw6 x hxw) hre hre'
      simpa only [pairKernelPhiP, pairKernelP] using h
    -- crude bound for the φ-kernel
    have hcrudephi : ∀ p : Fin k → ℝ × ℝ,
        ‖pairKernelPhiP (k := k) W N x p‖ ≤ (2 * CK) * (Real.log (x : ℝ)) ^ (3 * k) := by
      intro p
      have h1 := hcmp p
      have h2 : ‖pairKernelP (k := k) W N x p‖ ≤ CK * (Real.log (x : ℝ)) ^ (3 * k) :=
        hKbd x hxK W N hW hN p
      have h3 : ‖pairKernelPhiP (k := k) W N x p‖ ≤
          ‖pairKernelP (k := k) W N x p‖ +
            ‖pairKernelPhiP (k := k) W N x p - pairKernelP (k := k) W N x p‖ := by
        have h := norm_add_le (pairKernelP (k := k) W N x p)
          (pairKernelPhiP (k := k) W N x p - pairKernelP (k := k) W N x p)
        have he : pairKernelP (k := k) W N x p + (pairKernelPhiP (k := k) W N x p -
            pairKernelP (k := k) W N x p) = pairKernelPhiP (k := k) W N x p := by ring
        rwa [he] at h
      have hCK3 : (0 : ℝ) ≤ CK * (Real.log (x : ℝ)) ^ (3 * k) := by positivity
      calc ‖pairKernelPhiP (k := k) W N x p‖
          ≤ ‖pairKernelP (k := k) W N x p‖ +
              ‖pairKernelPhiP (k := k) W N x p - pairKernelP (k := k) W N x p‖ := h3
        _ ≤ CK * (Real.log (x : ℝ)) ^ (3 * k) +
              (Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) * ‖pairKernelP (k := k) W N x p‖ :=
            add_le_add h2 h1
        _ ≤ CK * (Real.log (x : ℝ)) ^ (3 * k) + 1 * (CK * (Real.log (x : ℝ)) ^ (3 * k)) := by
            refine add_le_add le_rfl ?_
            exact mul_le_mul hδle h2 (norm_nonneg _) (by norm_num)
        _ = 2 * CK * (Real.log (x : ℝ)) ^ (3 * k) := by ring
    have hIntP : Integrable fun p : Fin k → ℝ × ℝ =>
        pairKernelP (k := k) W N x p * pairPhase (k := k) F G p :=
      integrable_pairKernelP_mul_pairPhase F G hcsF hsmF hcsG hsmG W N
        (hKbd x hxK W N hW hN)
    have hIntPhi : Integrable fun p : Fin k → ℝ × ℝ =>
        pairKernelPhiP (k := k) W N x p * pairPhase (k := k) F G p :=
      integrable_pairKernelPhiP_mul_pairPhase F G hcsF hsmF hcsG hsmG W N hcrudephi
    -- the difference of the two kernel integrals
    have hdiff : ‖(∫ p : Fin k → ℝ × ℝ,
          pairKernelPhiP (k := k) W N x p * pairPhase (k := k) F G p) -
        (∫ p : Fin k → ℝ × ℝ,
          pairKernelP (k := k) W N x p * pairPhase (k := k) F G p)‖ ≤
        (Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) * (Ca * prefactor W N x ^ k) := by
      have heq : (∫ p : Fin k → ℝ × ℝ,
            pairKernelPhiP (k := k) W N x p * pairPhase (k := k) F G p) -
          (∫ p : Fin k → ℝ × ℝ,
            pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) =
          ∫ p : Fin k → ℝ × ℝ,
            (pairKernelPhiP (k := k) W N x p - pairKernelP (k := k) W N x p) *
              pairPhase (k := k) F G p := by
        rw [← MeasureTheory.integral_sub hIntPhi hIntP]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        dsimp only
        ring
      rw [heq]
      refine (norm_integral_le_integral_norm _).trans ?_
      calc (∫ p : Fin k → ℝ × ℝ,
            ‖(pairKernelPhiP (k := k) W N x p - pairKernelP (k := k) W N x p) *
              pairPhase (k := k) F G p‖)
          ≤ ∫ p : Fin k → ℝ × ℝ,
              (Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) *
                (‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖) := by
            refine integral_mono_of_nonneg (Eventually.of_forall (fun p => norm_nonneg _))
              (hIntP.norm.const_mul _) (Eventually.of_forall (fun p => ?_))
            dsimp only
            rw [norm_mul]
            have h := hcmp p
            calc ‖pairKernelPhiP (k := k) W N x p - pairKernelP (k := k) W N x p‖ *
                  ‖pairPhase (k := k) F G p‖
                ≤ ((Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) *
                    ‖pairKernelP (k := k) W N x p‖) * ‖pairPhase (k := k) F G p‖ :=
                  mul_le_mul_of_nonneg_right h (norm_nonneg _)
              _ = (Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) *
                    (‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖) := by
                  rw [norm_mul]; ring
        _ = (Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) *
              (∫ p : Fin k → ℝ × ℝ,
                ‖pairKernelP (k := k) W N x p * pairPhase (k := k) F G p‖) :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ (Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) * (Ca * prefactor W N x ^ k) :=
            mul_le_mul_of_nonneg_left (habs x hxa) hδnn
    -- assemble
    have hmain := hplain x hxp
    have htri : ‖(∫ p : Fin k → ℝ × ℝ,
          pairKernelPhiP (k := k) W N x p * pairPhase (k := k) F G p) -
        ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
          ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖ ≤
        ‖(∫ p : Fin k → ℝ × ℝ,
            pairKernelPhiP (k := k) W N x p * pairPhase (k := k) F G p) -
          (∫ p : Fin k → ℝ × ℝ,
            pairKernelP (k := k) W N x p * pairPhase (k := k) F G p)‖ +
        ‖(∫ p : Fin k → ℝ × ℝ,
            pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
          ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
            ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖ := by
      have h := norm_add_le
        ((∫ p : Fin k → ℝ × ℝ,
          pairKernelPhiP (k := k) W N x p * pairPhase (k := k) F G p) -
          (∫ p : Fin k → ℝ × ℝ,
            pairKernelP (k := k) W N x p * pairPhase (k := k) F G p))
        ((∫ p : Fin k → ℝ × ℝ,
            pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
          ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
            ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)))
      calc ‖(∫ p : Fin k → ℝ × ℝ,
            pairKernelPhiP (k := k) W N x p * pairPhase (k := k) F G p) -
          ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
            ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖
          = ‖((∫ p : Fin k → ℝ × ℝ,
            pairKernelPhiP (k := k) W N x p * pairPhase (k := k) F G p) -
            (∫ p : Fin k → ℝ × ℝ,
              pairKernelP (k := k) W N x p * pairPhase (k := k) F G p)) +
            ((∫ p : Fin k → ℝ × ℝ,
              pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
            ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
              ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)))‖ := by
            congr 1; ring
        _ ≤ _ := h
    exact htri.trans (by
      calc ‖(∫ p : Fin k → ℝ × ℝ,
              pairKernelPhiP (k := k) W N x p * pairPhase (k := k) F G p) -
            (∫ p : Fin k → ℝ × ℝ,
              pairKernelP (k := k) W N x p * pairPhase (k := k) F G p)‖ +
          ‖(∫ p : Fin k → ℝ × ℝ,
              pairKernelP (k := k) W N x p * pairPhase (k := k) F G p) -
            ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
              ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖
          ≤ (Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) * (Ca * prefactor W N x ^ k) +
              εp x * prefactor W N x ^ k := add_le_add hdiff hmain
        _ = ((Real.exp (12 * (k : ℝ) / (w x : ℝ)) - 1) * Ca + εp x) *
              prefactor W N x ^ k := by ring)

/-- **The `φ`-denominator Lemma 4.1** (divisor-sum form). -/
theorem phiPairwiseLemma41 {k : ℕ} (hk : 1 ≤ k)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ j, HasCompactSupport (F j))
    (hsmF : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F j)) (hcsG : ∀ j, HasCompactSupport (G j))
    (hsmG : ∀ j, ContDiff ℝ (↑(⊤ : ℕ∞)) (G j))
    (W N : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (hN : ∀ x, N x ≠ 0)
    (hcop : ∀ x, (W x).Coprime (N x))
    (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x * N x)
    (hlq : Tendsto (fun x : ℕ =>
        Real.log (((W x) * (N x) : ℕ) : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x →
        ‖(∑' d : Fin k → ℕ × ℕ, pairWeightDivPhi F G (W x * N x) x d) -
            ((prefactor W N x : ℝ) : ℂ) ^ k * ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
              ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))‖ ≤
          ε x * prefactor W N x ^ k := by
  classical
  obtain ⟨x₀, ε, hε, hbd⟩ :=
    phiPairKernelIntegral_asymptotic hk F G hcsF hsmF hcsG hsmG W N hW hN hcop w hw hsmall hlq
  refine ⟨max x₀ 2, ε, hε, fun x hx => ?_⟩
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 < x := by omega
  have hq : W x * N x ≠ 0 := mul_ne_zero (hW x) (hN x)
  rw [pairwiseDivisorSumPhi_eq_kernelIntegralPhi F G hcsF hsmF hcsG hsmG (W x * N x) x hq hx1]
  exact hbd x hx0

end Commons.NumberTheory.MaynardSieve
