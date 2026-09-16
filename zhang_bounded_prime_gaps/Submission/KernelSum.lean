import Mathlib
import Submission.KernelLimit
import Submission.KernelLimitFamily
import Submission.Commons.NumberTheory.Moebius.sum_divisors_moebius_lcm_cpow
import Submission.Commons.NumberTheory.Zeta.summable_lcm_inv_cpow
import Submission.Commons.NumberTheory.Moebius.moebius_abs_le_one
import Submission.KernelFun

open scoped BigOperators Topology
open Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# The divisor-sum kernel as an Euler product (Lemma 4.1, ℕ-level bridge)

Polymath8a's Lemma 4.1 begins by substituting the Fourier representation (37) of
the smooth cutoffs into the doubly-indexed divisor sum (36); after Fubini the
kernel of the resulting ξ-integral is the *doubly-indexed Möbius/lcm sum*

    K(ξ, ξ′) = Σ_{d,d′ ≥ 1, ([d,d′], WN) = 1} μ(d)μ(d′)/([d,d′])·d^{−a}·d′^{−b} ,
    a = (1+iξ)/log x ,  b = (1+iξ′)/log x ,

which the paper then rewrites as the Euler product `K = ∏_{p ∤ WN} K_p` with the
local factors `K_p` of (39) — exactly the `coordLocalK`/`locK` product whose
limit is analysed in `Submission.KernelLimit`, `KernelLimitK`,
`KernelLimitFamily`.

This module records the bridge between the two descriptions:

  * `kernelWeight`/`kernelWeightQ` — the summand (with the `([d,d′], q) = 1`
    restriction) and `kernelSum` — the doubly-indexed infinite sum;
  * `hasSum_of_tendsto_finset_mono` — a generic criterion: if `Σ_{x∈u n} f x`
    converges and `u n` eventually contains every index at which `f` is nonzero,
    then `f` has that sum;
  * the exhaustion of the coprime squarefree locus by the primorial chain
    `m n = ∏_{p ∈ Sfilter q n} p`.

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-! ## A generic HasSum criterion along an increasing chain -/

/-- **`HasSum` from convergence along a chain.**  If the partial sums of `f`
over a chain `u n` of finite sets converge to `a`, every index at which `f` does
not vanish is eventually covered by the chain (`hexh`), and `f` is absolutely
summable, then `f` has sum `a` in the unconditional sense. -/
theorem hasSum_of_tendsto_finset_mono {ι : Type*} {f : ι → ℂ} {u : ℕ → Finset ι}
    (hmono : Monotone u)
    (hexh : ∀ S : Finset ι, ∃ n, ∀ x ∈ S, x ∈ u n ∨ f x = 0)
    (habs : Summable fun x => ‖f x‖) {a : ℂ}
    (hlim : Tendsto (fun n => ∑ x ∈ u n, f x) atTop (𝓝 a)) : HasSum f a := by
  classical
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_atTop']
  intro U hU
  rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hε, hsub⟩
  rw [tendsto_atTop'] at hlim
  obtain ⟨n₂, hn₂⟩ := hlim (Metric.ball a (ε / 2)) (Metric.ball_mem_nhds a (by linarith))
  have hnorm : Tendsto (fun s : Finset ι => ∑ x ∈ s, ‖f x‖) atTop
      (𝓝 (∑' x, ‖f x‖)) := habs.hasSum
  rw [tendsto_atTop'] at hnorm
  obtain ⟨S₀, hS₀⟩ := hnorm (Metric.ball (∑' x, ‖f x‖) (ε / 2))
    (Metric.ball_mem_nhds _ (by linarith))
  obtain ⟨n₁, hn₁⟩ := hexh S₀
  refine ⟨u (max n₁ n₂), ?_⟩
  intro s hs
  have hn₂' : dist (∑ x ∈ u (max n₁ n₂), f x) a < ε / 2 := hn₂ _ (le_max_right _ _)
  have hS₀' : dist (∑ x ∈ S₀, ‖f x‖) (∑' x, ‖f x‖) < ε / 2 := hS₀ _ le_rfl
  -- the complement of `S₀` is small
  set g : ι → ℝ := ((↑S₀ : Set ι))ᶜ.indicator (fun x => ‖f x‖) with hg
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    by_cases hx : x ∈ (↑S₀ : Set ι)ᶜ
    · rw [hg, Set.indicator_of_mem hx]; exact norm_nonneg _
    · rw [hg, Set.indicator_of_notMem hx]
  have hgsum : Summable g :=
    Summable.of_nonneg_of_le hg0 (fun x => by
      by_cases hx : x ∈ (↑S₀ : Set ι)ᶜ
      · rw [hg, Set.indicator_of_mem hx]
      · rw [hg, Set.indicator_of_notMem hx]; exact norm_nonneg _) habs
  have hcompl : (∑' x, g x) = ∑' x : ↑((↑S₀ : Set ι))ᶜ, ‖f ↑x‖ := by
    rw [hg, ← tsum_subtype]
  have htsum_split := Summable.sum_add_tsum_compl (s := S₀) habs
  have hc : (∑' x : ↑((↑S₀ : Set ι))ᶜ, ‖f ↑x‖) < ε / 2 := by
    have h2 : |∑ x ∈ S₀, ‖f x‖ - ∑' x, ‖f x‖| < ε / 2 := by
      simpa [dist_eq_norm, Real.norm_eq_abs] using hS₀'
    have h3 : ∑' x, ‖f x‖ - ∑ x ∈ S₀, ‖f x‖ = ∑' x : ↑((↑S₀ : Set ι))ᶜ, ‖f ↑x‖ := by
      linarith
    rw [← h3]
    rw [abs_lt] at h2
    linarith [h2.2]
  -- the tail sum is bounded by the complement
  have htail : ∑ x ∈ s \ u (max n₁ n₂), ‖f x‖ < ε / 2 := by
    have h1 : ∑ x ∈ s \ u (max n₁ n₂), ‖f x‖ =
        ∑ x ∈ (s \ u (max n₁ n₂)).filter (fun x => x ∉ (↑S₀ : Set ι)), ‖f x‖ := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro x hx hxnot
      have hxS : x ∈ (↑S₀ : Set ι) := by
        by_contra hxS
        exact hxnot (Finset.mem_filter.mpr ⟨hx, hxS⟩)
      have hxu : x ∉ u (max n₁ n₂) := (Finset.mem_sdiff.mp hx).2
      rcases hn₁ x hxS with h | h
      · exact absurd (hmono (le_max_left n₁ n₂) h) hxu
      · simp [h]
    rw [h1]
    have h2 : ∑ x ∈ (s \ u (max n₁ n₂)).filter (fun x => x ∉ (↑S₀ : Set ι)), ‖f x‖ =
        ∑ x ∈ (s \ u (max n₁ n₂)).filter (fun x => x ∉ (↑S₀ : Set ι)), g x := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [hg, Set.indicator_of_mem (Finset.mem_filter.mp hx).2]
    rw [h2]
    refine lt_of_le_of_lt ?_ (by rw [← hcompl] at hc; exact hc)
    exact Summable.sum_le_tsum _ (fun i _ => hg0 i) hgsum
  -- assemble
  have hsplit : ∑ x ∈ s, f x - a = (∑ x ∈ s \ u (max n₁ n₂), f x) +
      (∑ x ∈ u (max n₁ n₂), f x - a) := by
    have h2 : ∑ x ∈ s, f x = ∑ x ∈ s \ u (max n₁ n₂), f x + ∑ x ∈ u (max n₁ n₂), f x :=
      (Finset.sum_sdiff hs).symm
    rw [h2]; ring
  have hdist : dist (∑ x ∈ s, f x) a ≤ (∑ x ∈ s \ u (max n₁ n₂), ‖f x‖) + ε / 2 := by
    rw [dist_eq_norm, hsplit]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖∑ x ∈ s \ u (max n₁ n₂), f x‖ ≤ ∑ x ∈ s \ u (max n₁ n₂), ‖f x‖ :=
      norm_sum_le _ _
    have h3 : ‖∑ x ∈ u (max n₁ n₂), f x - a‖ < ε / 2 := by
      rw [← dist_eq_norm]
      exact hn₂'
    linarith
  exact hsub (Metric.mem_ball.mpr (lt_of_le_of_lt hdist (by linarith)))

/-! ## The doubly-indexed kernel weight -/

/-- The summand of the P8 (38) kernel: `μ(d)μ(d′)·(lcm d d′)⁻¹·d^{−a}·d′^{−b}`. -/
noncomputable def kernelWeight (a b : ℂ) (x : ℕ × ℕ) : ℂ :=
  ((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) * ((ArithmeticFunction.moebius x.2 : ℤ) : ℂ) *
    (((Nat.lcm x.1 x.2 : ℕ) : ℂ))⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b)

/-- The same with the coprimality restriction `(lcm d d′, q) = 1` of (36). -/
noncomputable def kernelWeightQ (q : ℕ) (a b : ℂ) (x : ℕ × ℕ) : ℂ :=
  if (Nat.lcm x.1 x.2).Coprime q then kernelWeight a b x else 0

/-- The full doubly-indexed kernel sum. -/
noncomputable def kernelSum (q : ℕ) (a b : ℂ) : ℂ := ∑' x : ℕ × ℕ, kernelWeightQ q a b x

/-- The primorial `∏_{p < n, p ∤ q} p` — the modulus whose divisors carry the
kernel's Euler factorization. -/
noncomputable def primorial (q n : ℕ) : ℕ := ∏ p ∈ Sfilter q n, p

lemma primorial_ne_zero (q n : ℕ) : primorial q n ≠ 0 := by
  unfold primorial
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primesBelow
    (Finset.mem_of_mem_filter p hp)).ne_zero)

lemma one_le_primorial (q n : ℕ) : 1 ≤ primorial q n :=
  Nat.one_le_iff_ne_zero.mpr (primorial_ne_zero q n)

lemma primeFactors_primorial (q n : ℕ) : (primorial q n).primeFactors = Sfilter q n := by
  unfold primorial
  exact Nat.primeFactors_prod
    (fun p hp => Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_filter p hp))

/-! ## Vanishing of the kernel weight outside the squarefree/coprime locus -/

/-- The kernel weight vanishes unless both coordinates are nonzero, squarefree
and jointly coprime to `q`. -/
lemma kernelWeightQ_eq_zero_of_not {q : ℕ} {a b : ℂ} (ha : a.re ≠ 0) (hb : b.re ≠ 0) {x : ℕ × ℕ}
    (h : ¬ (x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
      (Nat.lcm x.1 x.2).Coprime q)) : kernelWeightQ q a b x = 0 := by
  by_cases hc : (Nat.lcm x.1 x.2).Coprime q
  · rw [kernelWeightQ, if_pos hc, kernelWeight]
    by_cases h1 : x.1 = 0
    · have hexp : (-a) ≠ 0 := fun hz => ha (by simpa using congrArg Complex.re hz)
      have h0 : (x.1 : ℂ) ^ (-a) = 0 := by
        rw [show (x.1 : ℂ) = 0 by simp [h1], Complex.zero_cpow hexp]
      rw [h0]; ring
    · by_cases h2 : x.2 = 0
      · have hexp : (-b) ≠ 0 := fun hz => hb (by simpa using congrArg Complex.re hz)
        have h0 : (x.2 : ℂ) ^ (-b) = 0 := by
          rw [show (x.2 : ℂ) = 0 by simp [h2], Complex.zero_cpow hexp]
        rw [h0]; ring
      · by_cases h3 : Squarefree x.1
        · by_cases h4 : Squarefree x.2
          · exact absurd ⟨h1, h2, h3, h4, hc⟩ h
          · have hμ : ((ArithmeticFunction.moebius x.2 : ℤ) : ℂ) = 0 := by
              have hz : ArithmeticFunction.moebius x.2 = 0 :=
                ArithmeticFunction.moebius_eq_zero_of_not_squarefree h4
              simp [hz]
            rw [hμ]; ring
        · have hμ : ((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) = 0 := by
            have hz : ArithmeticFunction.moebius x.1 = 0 :=
              ArithmeticFunction.moebius_eq_zero_of_not_squarefree h3
            simp [hz]
          rw [hμ]; ring
  · rw [kernelWeightQ, if_neg hc]

/-! ## Exhaustion of the coprime squarefree locus by the primorial chain -/

/-- Every squarefree index whose coordinates are coprime to `q` lies among the
divisors of a sufficiently large primorial. -/
lemma exists_mem_divisors_primorial {q : ℕ} (S : Finset (ℕ × ℕ))
    (hS : ∀ x ∈ S, x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
      (Nat.lcm x.1 x.2).Coprime q) :
    ∃ n, ∀ x ∈ S, x ∈ (Nat.divisors (primorial q n)) ×ˢ (Nat.divisors (primorial q n)) := by
  classical
  refine ⟨S.sup (fun x => max x.1 x.2) + 1, fun x hx => ?_⟩
  obtain ⟨hx1, hx2, hsq1, hsq2, hcop⟩ := hS x hx
  set N := S.sup (fun x => max x.1 x.2) with hN
  have hcopgcd : Nat.gcd (Nat.lcm x.1 x.2) q = 1 := hcop.gcd_eq_one
  have key : ∀ {d : ℕ}, d ≠ 0 → Squarefree d →
      (∀ p : ℕ, p.Prime → p ∣ d → p ∈ Sfilter q (N + 1)) → d ∣ primorial q (N + 1) := by
    intro d _ hsq hsub
    rw [← Nat.prod_primeFactors_of_squarefree hsq, primorial]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (fun p hp => hsub p
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  have key1 : ∀ p : ℕ, p.Prime → p ∣ x.1 → p ∈ Sfilter q (N + 1) := by
    intro p hp hpd
    have hple : p ≤ x.1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hx1) hpd
    have hbound : x.1 ≤ N := le_trans (le_max_left _ _) (Finset.le_sup (f := fun y : ℕ × ℕ => max y.1 y.2) hx)
    have hplcm : p ∣ Nat.lcm x.1 x.2 := hpd.trans (dvd_lcm_left x.1 x.2)
    have hpndvd : ¬ p ∣ q := by
      intro hpq
      have hpd1 : p ∣ 1 := by
        rw [← hcopgcd]
        exact Nat.dvd_gcd hplcm hpq
      have hle1 : p ≤ 1 := Nat.le_of_dvd one_pos hpd1
      have := hp.two_le
      omega
    rw [Sfilter, Finset.mem_filter, Nat.mem_primesBelow]
    exact ⟨⟨by omega, hp⟩, hpndvd⟩
  have key2 : ∀ p : ℕ, p.Prime → p ∣ x.2 → p ∈ Sfilter q (N + 1) := by
    intro p hp hpd
    have hple : p ≤ x.2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hx2) hpd
    have hbound : x.2 ≤ N := le_trans (le_max_right _ _) (Finset.le_sup (f := fun y : ℕ × ℕ => max y.1 y.2) hx)
    have hplcm : p ∣ Nat.lcm x.1 x.2 := hpd.trans (dvd_lcm_right x.1 x.2)
    have hpndvd : ¬ p ∣ q := by
      intro hpq
      have hpd1 : p ∣ 1 := by
        rw [← hcopgcd]
        exact Nat.dvd_gcd hplcm hpq
      have hle1 : p ≤ 1 := Nat.le_of_dvd one_pos hpd1
      have := hp.two_le
      omega
    rw [Sfilter, Finset.mem_filter, Nat.mem_primesBelow]
    exact ⟨⟨by omega, hp⟩, hpndvd⟩
  have hdvd1 : x.1 ∣ primorial q (N + 1) := key hx1 hsq1 key1
  have hdvd2 : x.2 ∣ primorial q (N + 1) := key hx2 hsq2 key2
  rw [Finset.mem_product]
  exact ⟨Nat.mem_divisors.mpr ⟨hdvd1, primorial_ne_zero q _⟩,
    Nat.mem_divisors.mpr ⟨hdvd2, primorial_ne_zero q _⟩⟩


/-! ## Absolute summability of the kernel weight -/

/-- The Möbius values are bounded by `1` in norm. -/
lemma norm_moebius_intCast_complex_le_one (n : ℕ) :
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  have hcast : ((ArithmeticFunction.moebius n : ℤ) : ℂ) =
      ((ArithmeticFunction.moebius n : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, show ‖((ArithmeticFunction.moebius n : ℝ) : ℂ)‖ =
    |(ArithmeticFunction.moebius n : ℝ)| from RCLike.norm_ofReal _]
  exact Commons.NumberTheory.Moebius.moebius_abs_le_one n

/-- The norm of the kernel weight is at most the μ-free lcm kernel. -/
lemma norm_kernelWeight_le (a b : ℂ) (x : ℕ × ℕ) :
    ‖kernelWeight a b x‖ ≤
      ‖(((Nat.lcm x.1 x.2 : ℕ)) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b)‖ := by
  have hfac : kernelWeight a b x =
      ((((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) *
        ((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)) *
        ((((Nat.lcm x.1 x.2 : ℕ)) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b))) := by
    rw [kernelWeight]; ring
  rw [hfac, norm_mul]
  have h1 := norm_moebius_intCast_complex_le_one x.1
  have h2 := norm_moebius_intCast_complex_le_one x.2
  calc ‖((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) *
        ((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)‖ *
        ‖(((Nat.lcm x.1 x.2 : ℕ)) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b)‖
      ≤ (1 * 1) * ‖(((Nat.lcm x.1 x.2 : ℕ)) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = ‖(((Nat.lcm x.1 x.2 : ℕ)) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b)‖ := by ring

/-- The kernel weight (with the coprimality restriction) is absolutely summable. -/
theorem summable_kernelWeightQ (q : ℕ) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Summable (fun x : ℕ × ℕ => ‖kernelWeightQ q a b x‖) := by
  have hbase := Commons.NumberTheory.Zeta.summable_lcm_inv_cpow ha hb
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hbase
  by_cases hc : (Nat.lcm x.1 x.2).Coprime q
  · rw [kernelWeightQ, if_pos hc]; exact norm_kernelWeight_le a b x
  · rw [kernelWeightQ, if_neg hc, norm_zero]; exact norm_nonneg _

/-! ## The primorial chain and the Euler factorization -/

lemma squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have ha : a.Prime := hs a (Finset.mem_insert_self a s)
      have hc : a.Coprime (∏ p ∈ s, p) := by
        rw [Nat.coprime_prod_right_iff]
        intro p hp
        refine (ha.coprime_iff_not_dvd).mpr fun hdvd => ?_
        have hp' : p.Prime := hs' p hp
        have hpa : p = a := (hp'.dvd_iff_eq ha.ne_one).mp hdvd
        exact has (hpa ▸ hp)
      rw [Finset.prod_insert has, Nat.squarefree_mul hc]
      exact ⟨ha.squarefree, ih hs'⟩

lemma squarefree_primorial (q n : ℕ) : Squarefree (primorial q n) :=
  squarefree_prod_primes _
    (fun p hp => Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_filter p hp))

lemma coprime_primorial (q n : ℕ) : (primorial q n).Coprime q := by
  rw [primorial, Nat.coprime_prod_left_iff]
  intro p hp
  have hpndvd : ¬ p ∣ q := (Finset.mem_filter.mp hp).2
  have hpp : p.Prime := Nat.prime_of_mem_primesBelow (Finset.mem_of_mem_filter p hp)
  exact (hpp.coprime_iff_not_dvd).mpr hpndvd

lemma coprime_lcm_divisors_primorial {q n d d' : ℕ}
    (hd : d ∈ (primorial q n).divisors) (hd' : d' ∈ (primorial q n).divisors) :
    (Nat.lcm d d').Coprime q := by
  have h1 : d ∣ primorial q n := (Nat.mem_divisors.mp hd).1
  have h2 : d' ∣ primorial q n := (Nat.mem_divisors.mp hd').1
  exact (coprime_primorial q n).coprime_dvd_left (Nat.lcm_dvd h1 h2)

/-- **The finite Euler factorization in the sieve's normalization.**  The
doubly-indexed kernel sum over the divisors of the primorial equals the finite
Euler product of the local factors `locK`. -/
lemma sum_prod_divisors_kernelWeightQ (q n : ℕ) (a b : ℂ) :
    (∑ x ∈ (Nat.divisors (primorial q n)) ×ˢ (Nat.divisors (primorial q n)),
        kernelWeightQ q a b x) = ∏ p ∈ Sfilter q n, locK p a b := by
  classical
  rw [Finset.sum_product]
  have h1 : ∀ d ∈ (primorial q n).divisors, ∀ d' ∈ (primorial q n).divisors,
      kernelWeightQ q a b (d, d') = kernelWeight a b (d, d') := by
    intro d hd d' hd'
    rw [kernelWeightQ, if_pos (coprime_lcm_divisors_primorial hd hd')]
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun d' hd' => h1 d hd d' hd'))]
  have h26 := Commons.NumberTheory.Moebius.sum_divisors_moebius_lcm_cpow (primorial q n)
    (squarefree_primorial q n) a b
  simp only [kernelWeight]
  rw [h26, primeFactors_primorial]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  unfold locK
  ring

/-! ## The bridge theorem -/

/-- **Lemma 4.1, ℕ-level bridge.**  The doubly-indexed Möbius/lcm kernel sum
equals the limit of the finite Euler products `∏_{p ∈ Sfilter q n} locK p a b`
(which exists by `exists_tendsto_locKprod`). -/
theorem hasSum_kernelWeightQ (q : ℕ) (hq : q ≠ 0) {a b : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) :
    ∃ L : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, locK p a b) atTop (𝓝 L) ∧
      HasSum (kernelWeightQ q a b) L := by
  classical
  obtain ⟨L, hL⟩ := exists_tendsto_locKprod q hq ha hb
  refine ⟨L, hL, ?_⟩
  refine hasSum_of_tendsto_finset_mono
    (u := fun n => (Nat.divisors (primorial q n)) ×ˢ (Nat.divisors (primorial q n)))
    ?_ ?_ (summable_kernelWeightQ q ha hb) ?_
  · refine monotone_nat_of_le_succ (fun n => ?_)
    have hdvd : primorial q n ∣ primorial q (n + 1) := by
      rw [primorial, primorial]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Sfilter_mono q (Nat.le_succ n))
    have hsub : (primorial q n).divisors ⊆ (primorial q (n + 1)).divisors :=
      Nat.divisors_subset_of_dvd (primorial_ne_zero q (n + 1)) hdvd
    exact Finset.product_subset_product hsub hsub
  · intro S
    obtain ⟨n, hn⟩ := exists_mem_divisors_primorial (S.filter (fun x =>
      x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
        (Nat.lcm x.1 x.2).Coprime q))
      (fun x hx => (Finset.mem_filter.mp hx).2)
    refine ⟨n, fun x hx => ?_⟩
    by_cases hgood : x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ Squarefree x.1 ∧ Squarefree x.2 ∧
        (Nat.lcm x.1 x.2).Coprime q
    · exact Or.inl (hn x (Finset.mem_filter.mpr ⟨hx, hgood⟩))
    · exact Or.inr (kernelWeightQ_eq_zero_of_not ha.ne' hb.ne' hgood)
  · refine hL.congr' (Eventually.of_forall (fun n => ?_))
    exact (sum_prod_divisors_kernelWeightQ q n a b).symm

/-- **The kernel sum is the kernel.** -/
theorem kernelSum_eq_kernelFun (q : ℕ) (hq : q ≠ 0) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    kernelSum q a b = kernelFun q a b := by
  obtain ⟨L, hL, hsum⟩ := hasSum_kernelWeightQ q hq ha hb
  rw [kernelSum, hsum.tsum_eq]
  exact (kernelFun_eq_of_tendsto hL).symm

end Commons.NumberTheory.MaynardSieve
