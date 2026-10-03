import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd
import Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.heckeLval_logDeriv_norm_le_of_one_lt_re
import Submission.Work.FIArea6Hecke.R.chiTrivLocalPrime
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Filter
open Work.FIArea5.S16Hecke

noncomputable section


/-! ## 1. The primes dividing the conductor -/

/-- The finitely many rational primes dividing `N`, viewed as elements of `Nat.Primes`. -/
def primeFactorFinset (N : ℕ) : Finset Nat.Primes :=
  (N.primeFactors.attach).map
    ⟨fun q : {x // x ∈ N.primeFactors} => ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩,
      fun a b h => Subtype.ext (congrArg (fun x : Nat.Primes => (x : ℕ)) h)⟩

lemma mem_primeFactorFinset {N : ℕ} (hN : N ≠ 0) {p : Nat.Primes} :
    p ∈ primeFactorFinset N ↔ (p : ℕ) ∣ N := by
  constructor
  · intro hp
    obtain ⟨q, -, hq⟩ := Finset.mem_map.mp hp
    have hq' : ((⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩ : Nat.Primes) : ℕ) = (p : ℕ) :=
      congrArg (fun x : Nat.Primes => (x : ℕ)) hq
    rw [← hq']
    exact (Nat.mem_primeFactors.mp q.2).2.1
  · intro hp
    exact Finset.mem_map.mpr
      ⟨⟨(p : ℕ), Nat.mem_primeFactors.mpr ⟨p.prop, hp, hN⟩⟩, Finset.mem_attach _ _,
        Subtype.ext rfl⟩

/-! ## 2. The local Hecke eigenvalues at a prime dividing neither modulus -/

theorem heckeLam_eq_of_agree_on_primary_units
    {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    {chi₁ chi₂ : GaussianInt → ℂ}
    (hχ₁ : IsCharMod4dStrict d₁ chi₁) (hχ₂ : IsCharMod4dStrict d₂ chi₂)
    (hagree : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      IsUnitMod4d d₁ z → IsUnitMod4d d₂ z → chi₁ z = chi₂ z)
    {p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ 4 * d₁ * d₂) (e : ℕ) :
    heckeLam chi₁ 0 (p ^ e) = heckeLam chi₂ 0 (p ^ e) := by
  classical
  have hpair : (4 * d₁) * d₂ = 4 * d₁ * d₂ := rfl
  have hpd₁ : ¬ p ∣ 4 * d₁ := fun h => hpd (hpair ▸ h.mul_right d₂)
  have hpd₂ : ¬ p ∣ 4 * d₂ := fun h => hpd (by
    have := h.mul_right d₁
    rwa [show (4 * d₂) * d₁ = 4 * d₁ * d₂ from by ring] at this)
  by_cases he : e = 0
  · subst he
    rw [pow_zero, heckeLam_one, heckeLam_one, hχ₁.1.1, hχ₂.1.1]
  · have he0 : 0 < e := Nat.pos_of_ne_zero he
    unfold heckeLam
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hprim, hgn⟩ := hz
    rw [psi_zero, psi_zero]
    exact hagree z hprim
      (isUnitMod4d_of_gnorm_eq_prime_pow h₁ hp hpd₁ he0 hgn)
      (isUnitMod4d_of_gnorm_eq_prime_pow h₂ hp hpd₂ he0 hgn)

/-- At a good prime the local Euler factors agree as functions. -/
lemma heckeFp_eq_of_not_dvd {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    {chi₁ chi₂ : GaussianInt → ℂ}
    (hχ₁ : IsCharMod4dStrict d₁ chi₁) (hχ₂ : IsCharMod4dStrict d₂ chi₂)
    (hagree : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      IsUnitMod4d d₁ z → IsUnitMod4d d₂ z → chi₁ z = chi₂ z)
    {p : Nat.Primes} (hpd : ¬ (p : ℕ) ∣ 4 * d₁ * d₂) :
    heckeFp chi₁ 0 p = heckeFp chi₂ 0 p := by
  funext s
  rw [heckeFp_eq_tsum, heckeFp_eq_tsum]
  exact tsum_congr (fun e => by
    rw [heckeLam_eq_of_agree_on_primary_units h₁ h₂ hχ₁ hχ₂ hagree p.prop hpd e])

/-! ## 3. The product of the reciprocal local factors over the bad primes -/

/-- The product, over the rational primes dividing `4d₁d₂`, of the reciprocal local Euler factors
`G_p(s) = 1 - λ(p)p^{-s} + (λ(p)² - λ(p²))p^{-2s}` of `χ`.  It is entire in `s`. -/
def localGpProd (d₁ d₂ : ℕ) (chi : GaussianInt → ℂ) (s : ℂ) : ℂ :=
  ∏ p ∈ primeFactorFinset (4 * d₁ * d₂), heckeGp chi 0 p s

lemma differentiable_heckeGp (chi : GaussianInt → ℂ) (k : ℤ) (p : Nat.Primes) :
    Differentiable ℂ (fun s : ℂ => heckeGp chi k p s) := by
  have hc : (((p : ℕ) : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact p.prop.pos.ne'
  have hbase : Differentiable ℂ (fun w : ℂ => (((p : ℕ) : ℂ) ^ (-w))) :=
    (differentiable_id.neg).const_cpow (Or.inl hc)
  unfold heckeGp
  exact ((differentiable_const (1 : ℂ)).sub (hbase.const_mul _)).add ((hbase.pow 2).const_mul _)

lemma differentiable_localGpProd (d₁ d₂ : ℕ) (chi : GaussianInt → ℂ) :
    Differentiable ℂ (localGpProd d₁ d₂ chi) := by
  classical
  unfold localGpProd
  exact Differentiable.fun_finsetProd (fun p _ => differentiable_heckeGp chi 0 p)

lemma localGpProd_ne_zero {d₁ d₂ : ℕ} {chi : GaussianInt → ℂ}
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    localGpProd d₁ d₂ chi s ≠ 0 := by
  classical
  rw [localGpProd]
  exact Finset.prod_ne_zero_iff.mpr (fun p _ => heckeGp_ne_zero h1 hmul hb hs)

/-! ## 4. The cleared Euler-product identity on `re s > 1` -/

theorem heckeLSeries_mul_localGpProd {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    {chi₁ chi₂ : GaussianInt → ℂ}
    (hχ₁ : IsCharMod4dStrict d₁ chi₁) (hχ₂ : IsCharMod4dStrict d₂ chi₂)
    (hagree : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      IsUnitMod4d d₁ z → IsUnitMod4d d₂ z → chi₁ z = chi₂ z)
    {s : ℂ} (hs : 1 < s.re) :
    heckeLSeries chi₂ 0 s * localGpProd d₁ d₂ chi₂ s
      = localGpProd d₁ d₂ chi₁ s * heckeLSeries chi₁ 0 s := by
  classical
  obtain ⟨h1₁, hmul₁, hb₁, -, -⟩ := hχ₁.1
  obtain ⟨h1₂, hmul₂, hb₂, -, -⟩ := hχ₂.1
  have hbad : 4 * d₁ * d₂ ≠ 0 := by
    have hpos : 0 < 4 * d₁ * d₂ := by
      have h1 : 0 < d₁ := by omega
      have h2 : 0 < d₂ := by omega
      positivity
    exact hpos.ne'
  have hL₂ : HasProd (fun p : Nat.Primes => heckeFp chi₂ 0 p s) (heckeLSeries chi₂ 0 s) :=
    heckeLSeries_eulerProduct_hasProd chi₂ 0 h1₂ hmul₂ hb₂ hs
  have hL₁ : HasProd (fun p : Nat.Primes => heckeFp chi₁ 0 p s) (heckeLSeries chi₁ 0 s) :=
    heckeLSeries_eulerProduct_hasProd chi₁ 0 h1₁ hmul₁ hb₁ hs
  have hd₂ : HasProd (fun p : Nat.Primes =>
      if p ∈ primeFactorFinset (4 * d₁ * d₂) then heckeGp chi₂ 0 p s else 1)
      (localGpProd d₁ d₂ chi₂ s) := by
    have hval : (∏ p ∈ primeFactorFinset (4 * d₁ * d₂),
        (if p ∈ primeFactorFinset (4 * d₁ * d₂) then heckeGp chi₂ 0 p s else 1))
        = ∏ p ∈ primeFactorFinset (4 * d₁ * d₂), heckeGp chi₂ 0 p s :=
      Finset.prod_congr rfl (fun p hp => if_pos hp)
    rw [localGpProd, ← hval]
    exact hasProd_prod_of_ne_finset_one (fun p hp => if_neg hp)
  have hd₁ : HasProd (fun p : Nat.Primes =>
      if p ∈ primeFactorFinset (4 * d₁ * d₂) then heckeGp chi₁ 0 p s else 1)
      (localGpProd d₁ d₂ chi₁ s) := by
    have hval : (∏ p ∈ primeFactorFinset (4 * d₁ * d₂),
        (if p ∈ primeFactorFinset (4 * d₁ * d₂) then heckeGp chi₁ 0 p s else 1))
        = ∏ p ∈ primeFactorFinset (4 * d₁ * d₂), heckeGp chi₁ 0 p s :=
      Finset.prod_congr rfl (fun p hp => if_pos hp)
    rw [localGpProd, ← hval]
    exact hasProd_prod_of_ne_finset_one (fun p hp => if_neg hp)
  have hkey : (fun p : Nat.Primes => heckeFp chi₂ 0 p s *
        (if p ∈ primeFactorFinset (4 * d₁ * d₂) then heckeGp chi₂ 0 p s else 1))
      = (fun p : Nat.Primes => heckeFp chi₁ 0 p s *
        (if p ∈ primeFactorFinset (4 * d₁ * d₂) then heckeGp chi₁ 0 p s else 1)) := by
    funext p
    by_cases hp : p ∈ primeFactorFinset (4 * d₁ * d₂)
    · rw [if_pos hp, if_pos hp, heckeFp_mul_heckeGp chi₂ 0 p s hmul₂ h1₂ hb₂ (by linarith),
        heckeFp_mul_heckeGp chi₁ 0 p s hmul₁ h1₁ hb₁ (by linarith)]
    · rw [if_neg hp, if_neg hp, mul_one, mul_one]
      exact (congrFun (heckeFp_eq_of_not_dvd h₁ h₂ hχ₁ hχ₂ hagree
        (fun hdvd => hp ((mem_primeFactorFinset hbad).mpr hdvd))) s).symm
  have h₂ := hL₂.mul hd₂
  have h₁' := hL₁.mul hd₁
  rw [hkey] at h₂
  have huniq : heckeLSeries chi₂ 0 s * localGpProd d₁ d₂ chi₂ s
      = heckeLSeries chi₁ 0 s * localGpProd d₁ d₂ chi₁ s := h₂.unique h₁'
  rw [huniq, mul_comm]

/-! ## 5. The half-plane `re s > 0` is preconnected -/

lemma convex_pos_re : Convex ℝ {s : ℂ | 0 < s.re} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by
    rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
  rw [hre]
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · have hb1 : b = 1 := by linarith
    rw [← ha0, zero_mul, zero_add, hb1, one_mul]
    exact hy
  · have h1 : 0 < a * x.re := mul_pos hapos hx
    have h2 : 0 ≤ b * y.re := mul_nonneg hb hy.le
    linarith

lemma isPreconnected_pos_re : IsPreconnected {s : ℂ | 0 < s.re} := convex_pos_re.isPreconnected

/-! ## 6. The test function whose zeros propagate -/

/-- `Λ₂·P₂·arch₁ - Λ₁·P₁·arch₂`, the cleared form of
`(Λ₂/Λ₁) - (arch₂/arch₁)·(P₂/P₁)`: it is holomorphic on `re s > 0` and vanishes on `re s > 1`
because the two Hecke `L`-series differ exactly by the product `P₂/P₁` of bad local factors. -/
def testFun (d₁ d₂ : ℕ) (chi₁ chi₂ : GaussianInt → ℂ) (Lam₁ Lam₂ : ℂ → ℂ) : ℂ → ℂ :=
  fun s => Lam₂ s * localGpProd d₁ d₂ chi₂ s * Work.FITop4.Bridge.heckeArch d₁ 0 s
    - Lam₁ s * localGpProd d₁ d₂ chi₁ s * Work.FITop4.Bridge.heckeArch d₂ 0 s

/-- The test function is holomorphic on the right half-plane. -/
lemma analyticOn_testFun {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    {chi₁ chi₂ : GaussianInt → ℂ} {Lam₁ Lam₂ : ℂ → ℂ}
    (hAn₁ : AnalyticOn ℂ Lam₁ Set.univ) (hAn₂ : AnalyticOn ℂ Lam₂ Set.univ) :
    AnalyticOn ℂ (testFun d₁ d₂ chi₁ chi₂ Lam₁ Lam₂) {s : ℂ | 0 < s.re} := by
  unfold testFun
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdLam₂ : DifferentiableOn ℂ Lam₂ {s : ℂ | 0 < s.re} :=
    hAn₂.differentiableOn.mono (Set.subset_univ _)
  have hdLam₁ : DifferentiableOn ℂ Lam₁ {s : ℂ | 0 < s.re} :=
    hAn₁.differentiableOn.mono (Set.subset_univ _)
  have hdP₂ : DifferentiableOn ℂ (localGpProd d₁ d₂ chi₂) {s : ℂ | 0 < s.re} :=
    (differentiable_localGpProd d₁ d₂ chi₂).differentiableOn
  have hdP₁ : DifferentiableOn ℂ (localGpProd d₁ d₂ chi₁) {s : ℂ | 0 < s.re} :=
    (differentiable_localGpProd d₁ d₂ chi₁).differentiableOn
  have hdArch₁ : DifferentiableOn ℂ (Work.FITop4.Bridge.heckeArch d₁ 0) {s : ℂ | 0 < s.re} :=
    fun s hs => (heckeArch_differentiableAt_of_pos h₁ 0 hs).differentiableWithinAt
  have hdArch₂ : DifferentiableOn ℂ (Work.FITop4.Bridge.heckeArch d₂ 0) {s : ℂ | 0 < s.re} :=
    fun s hs => (heckeArch_differentiableAt_of_pos h₂ 0 hs).differentiableWithinAt
  exact (((hdLam₂.mul hdP₂).mul hdArch₁).sub ((hdLam₁.mul hdP₁).mul hdArch₂)).analyticOn hU

/-- The test function vanishes on `re s > 1`. -/
lemma testFun_eq_zero_of_one_lt_re {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    {chi₁ chi₂ : GaussianInt → ℂ}
    (hχ₁ : IsCharMod4dStrict d₁ chi₁) (hχ₂ : IsCharMod4dStrict d₂ chi₂)
    (hagree : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      IsUnitMod4d d₁ z → IsUnitMod4d d₂ z → chi₁ z = chi₂ z)
    {Lam₁ Lam₂ : ℂ → ℂ}
    (hAgr₁ : ∀ s : ℂ, 1 < s.re →
      Lam₁ s = Work.FITop4.Bridge.heckeArch d₁ 0 s * heckeLSeries chi₁ 0 s)
    (hAgr₂ : ∀ s : ℂ, 1 < s.re →
      Lam₂ s = Work.FITop4.Bridge.heckeArch d₂ 0 s * heckeLSeries chi₂ 0 s)
    {s : ℂ} (hs : 1 < s.re) : testFun d₁ d₂ chi₁ chi₂ Lam₁ Lam₂ s = 0 := by
  have hkey := heckeLSeries_mul_localGpProd h₁ h₂ hχ₁ hχ₂ hagree hs
  have hmain : Work.FITop4.Bridge.heckeArch d₂ 0 s * heckeLSeries chi₂ 0 s
        * localGpProd d₁ d₂ chi₂ s * Work.FITop4.Bridge.heckeArch d₁ 0 s
      = Work.FITop4.Bridge.heckeArch d₁ 0 s * heckeLSeries chi₁ 0 s
        * localGpProd d₁ d₂ chi₁ s * Work.FITop4.Bridge.heckeArch d₂ 0 s := by
    calc Work.FITop4.Bridge.heckeArch d₂ 0 s * heckeLSeries chi₂ 0 s
          * localGpProd d₁ d₂ chi₂ s * Work.FITop4.Bridge.heckeArch d₁ 0 s
        = Work.FITop4.Bridge.heckeArch d₂ 0 s
            * (heckeLSeries chi₂ 0 s * localGpProd d₁ d₂ chi₂ s)
            * Work.FITop4.Bridge.heckeArch d₁ 0 s := by ring
      _ = Work.FITop4.Bridge.heckeArch d₂ 0 s
            * (localGpProd d₁ d₂ chi₁ s * heckeLSeries chi₁ 0 s)
            * Work.FITop4.Bridge.heckeArch d₁ 0 s := by rw [hkey]
      _ = Work.FITop4.Bridge.heckeArch d₁ 0 s * heckeLSeries chi₁ 0 s
            * localGpProd d₁ d₂ chi₁ s * Work.FITop4.Bridge.heckeArch d₂ 0 s := by ring
  unfold testFun
  rw [hAgr₂ s hs, hAgr₁ s hs, hmain, sub_self]

/-- The test function vanishes in a whole neighbourhood of `s = 2`. -/
lemma testFun_eventuallyEq_zero {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    {chi₁ chi₂ : GaussianInt → ℂ}
    (hχ₁ : IsCharMod4dStrict d₁ chi₁) (hχ₂ : IsCharMod4dStrict d₂ chi₂)
    (hagree : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      IsUnitMod4d d₁ z → IsUnitMod4d d₂ z → chi₁ z = chi₂ z)
    {Lam₁ Lam₂ : ℂ → ℂ}
    (hAgr₁ : ∀ s : ℂ, 1 < s.re →
      Lam₁ s = Work.FITop4.Bridge.heckeArch d₁ 0 s * heckeLSeries chi₁ 0 s)
    (hAgr₂ : ∀ s : ℂ, 1 < s.re →
      Lam₂ s = Work.FITop4.Bridge.heckeArch d₂ 0 s * heckeLSeries chi₂ 0 s) :
    testFun d₁ d₂ chi₁ chi₂ Lam₁ Lam₂ =ᶠ[nhds (2 : ℂ)] 0 := by
  filter_upwards [Metric.ball_mem_nhds (2 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hzball
  refine testFun_eq_zero_of_one_lt_re h₁ h₂ hχ₁ hχ₂ hagree hAgr₁ hAgr₂ ?_
  have h1 : ‖z - 2‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have h2 : |z.re - 2| ≤ ‖z - 2‖ := by simpa using Complex.abs_re_le_norm (z - 2)
  have h3 : |z.re - 2| < 1 := lt_of_le_of_lt h2 h1
  rw [abs_lt] at h3
  linarith [h3.1]

/-- **Two strict characters that agree on the primary units have the same real zeros in `(0,1)`.**
The local Euler factor of `L(·,χ)` at a rational prime `p` depends only on the values of `χ` on the
primary Gaussian integers of norm `p^k`; for `p ∤ d₁d₂` all of those are units modulo `4d₁` and
`4d₂`, so `hagree` makes the local factors equal.  At a prime `p | d₁` every primary element of
norm `p^k` (`k ≥ 1`) is a non-unit modulo `4d₁`, so `λ₁(p^k) = 0` and the corresponding local
factor is `1`.  Hence the two `L`-functions differ by the finite product of local factors over the
primes dividing `d₁d₂`, and each local factor (`1` at `p = 2`, `(1-cX)^{-2}` at a split prime,
`(1-X²)^{-1}` at an inert prime, `X = p^{-s}`, `c ∈ {±1}`) is holomorphic and non-vanishing on
`re s > 0`.  So the ratio `Lval d₂ 0 Lam₂ / Lval d₁ 0 Lam₁` is holomorphic and non-vanishing on
`re s > 0`, and the zeros of the two entire functions with `0 < re s` coincide; in particular a
real zero `β ∈ (0,1)` of the second is a real zero of the first. -/
theorem same_real_zeros_of_agree_on_primary_units
    {d₁ d₂ : ℕ} (h₁ : 1 ≤ d₁) (h₂ : 1 ≤ d₂)
    {chi₁ chi₂ : GaussianInt → ℂ}
    (hχ₁ : Work.FIArea5.S16Hecke.IsCharMod4dStrict d₁ chi₁)
    (hχ₂ : Work.FIArea5.S16Hecke.IsCharMod4dStrict d₂ chi₂)
    (hagree : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d₁ z → Work.FIArea5.S16Hecke.IsUnitMod4d d₂ z →
        chi₁ z = chi₂ z)
    {Lam₁ Lam₂ : ℂ → ℂ} (hAn₁ : AnalyticOn ℂ Lam₁ Set.univ)
    (hAgr₁ : ∀ s : ℂ, 1 < s.re →
      Lam₁ s = Work.FITop4.Bridge.heckeArch d₁ 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s)
    (hAn₂ : AnalyticOn ℂ Lam₂ Set.univ)
    (hAgr₂ : ∀ s : ℂ, 1 < s.re →
      Lam₂ s = Work.FITop4.Bridge.heckeArch d₂ 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hz : Work.FIArea6Hecke.Lval d₂ 0 Lam₂ (β : ℂ) = 0) :
    Work.FIArea6Hecke.Lval d₁ 0 Lam₁ (β : ℂ) = 0 := by
  classical
  obtain ⟨h1₁, hmul₁, hb₁, -, -⟩ := hχ₁.1
  have hβmem : 0 < ((β : ℂ)).re := by simpa using hβ0
  -- the test function vanishes at `β`
  have hmem2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by
    simp only [Set.mem_ofPred_eq]
    norm_num
  have hFβ : testFun d₁ d₂ chi₁ chi₂ Lam₁ Lam₂ (β : ℂ) = 0 :=
    (AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      ((isOpen_lt continuous_const Complex.continuous_re).analyticOn_iff_analyticOnNhd.mp
        (analyticOn_testFun h₁ h₂ hAn₁ hAn₂))
      isPreconnected_pos_re hmem2 (testFun_eventuallyEq_zero h₁ h₂ hχ₁ hχ₂ hagree hAgr₁ hAgr₂))
      (by simp only [Set.mem_ofPred_eq]; exact hβmem)
  unfold testFun at hFβ
  -- `Λ₂ β = 0`
  have hLam₂β : Lam₂ (β : ℂ) = 0 := by
    by_contra hne
    exact absurd hz ((Lval_ne_zero_iff h₂ 0 hβmem).mpr hne)
  rw [hLam₂β, zero_mul, zero_mul, zero_sub] at hFβ
  -- `Λ₁ β · P₁ β · arch₂ β = 0`
  have hne_arch : Work.FITop4.Bridge.heckeArch d₂ 0 (β : ℂ) ≠ 0 :=
    heckeArch_ne_zero_of_pos_re h₂ 0 hβmem
  have hne_P₁ : localGpProd d₁ d₂ chi₁ (β : ℂ) ≠ 0 :=
    localGpProd_ne_zero h1₁ hmul₁ hb₁ hβmem
  have hLam₁β : Lam₁ (β : ℂ) = 0 := by
    rcases mul_eq_zero.mp (neg_eq_zero.mp hFβ) with h | h
    · rcases mul_eq_zero.mp h with h1 | h2
      · exact h1
      · exact absurd h2 hne_P₁
    · exact absurd h hne_arch
  rw [Lval, hLam₁β, zero_div]

end

end Work.FIArea6Hecke.R
