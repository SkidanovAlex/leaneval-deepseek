import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Framework
import Submission.Work.ChenPlan.LinearSieve.SelbergBound
import Submission.Work.ChenPlan.LinearSieve.basic
import Submission.Work.ChenPlan.LinearSieve.Selberg.sum_divisors_lt_eq_sum_powerset
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.vocab
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.interval_packing
import Submission.Work.ChenPlan.LinearSieve.Selberg.tail_mass_constraint_of_product_bound
import Submission.Work.ChenPlan.LinearSieve.Selberg.sum_levels_mul_hitIndicator_le_refSum
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_cdf
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.summable_cY_ae
import Submission.Work.LinearSieve.Selberg.selectionMass_eq_measure
import Submission.Work.ChenPlan.LinearSieve.Selberg.hit_all_prob

/-!
# The sharp Selberg `G`-bound (`gsum_bound_dense`)

The target is the sharp base case (`u ≤ 2`) of the Ankeny–Onishi `G`-bound:

`gSum A (√D) · Vf A Z ≥ log D / log Z / (2 e^γ) - η`   for `1 ≤ log D / log Z ≤ 2`.

The route developed here is the **probabilistic re-reading** of `gSum · Vf`: under `IsLinearNat`
every prime of `P = A.prodPrimes` is `< Z`, so with `h = A.selbergTerms`,

* `Vf A Z · h(d) = ν(d) · ∏_{p ∣ P, p ∤ d} (1 - ν p)`  (proved below, `Vf_mul_selbergTerms`),
* hence `Vf A Z · gSum A ξ` is the probability that the product of the "selected" primes
  (independent Bernoulli, probabilities `ν p`) is `< ξ = √D`,
* writing `θ p = log p / log Z` and `λ = log D / (2 log Z) ∈ [1/2,1]`, this is `P(Y < λ)` with
  `Y = Σ_p θ p · B_p`,
* `IsLinearNat A Z K` is exactly the statement that the "mass measure" `μ = Σ_p x_p δ_{θ p}` with
  `x_p = -log (1 - ν p)` is dominated by the harmonic measure in the tail sense,
  `μ([θ,1]) ≤ log (1/θ)`.

The final step is the comparison with the extremal ("continuum") configuration, for which the
classical computation gives `P(Y_* < λ) = λ e^{-γ}` for `λ ≤ 1`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ChenPlan.LinearSieve.Selberg

open Work.ChenPlan.LinearSieve

/-- **The local identity.**  If every prime of `P = A.prodPrimes` is below the sift limit `Z`, then
for every divisor `d` of `P` the product `Vf A Z · h(d)` factors as `ν(d)` times the product of
`1 - ν p` over the primes of `P` not dividing `d`.  This is the probability that the independent
Bernoulli selection with probabilities `ν p` picks out exactly the primes of `d`. -/
theorem Vf_mul_selbergTerms (A : BoundingSieve) {Z : ℕ}
    (hZ : ∀ p ∈ A.prodPrimes.primeFactors, p < Z) {d : ℕ} (hd : d ∣ A.prodPrimes) :
    Vf A Z * A.selbergTerms d
      = A.nu d * ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => ¬ p ∣ d), (1 - A.nu p) := by
  classical
  have hP0 : A.prodPrimes ≠ 0 := A.prodPrimes_ne_zero
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hP0 hd
  have hVf : Vf A Z = ∏ p ∈ A.prodPrimes.primeFactors, (1 - A.nu p) := by
    rw [Vf, Finset.filter_true_of_mem (fun p hp => hZ p hp)]
  rw [hVf, BoundingSieve.selbergTerms_apply]
  -- `d.primeFactors = P.primeFactors.filter (· ∣ d)`
  have hpf : d.primeFactors = A.prodPrimes.primeFactors.filter (fun p : ℕ => p ∣ d) := by
    ext p
    rw [Nat.mem_primeFactors, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hpd, -⟩
      exact ⟨Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hd, hP0⟩, hpd⟩
    · rintro ⟨hpP, hpd⟩
      obtain ⟨hp, -, -⟩ := Nat.mem_primeFactors.mp hpP
      exact ⟨hp, hpd, hd0⟩
  -- split `∏_{p ∣ P} (1 - ν p)` along the primes dividing `d`
  have hsplit : (∏ p ∈ A.prodPrimes.primeFactors, (1 - A.nu p))
      = (∏ p ∈ d.primeFactors, (1 - A.nu p))
        * ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => ¬ p ∣ d), (1 - A.nu p) := by
    rw [hpf, Finset.prod_filter_mul_prod_filter_not]
  have hprod : (∏ p ∈ d.primeFactors, (1 - A.nu p)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    have hpP : p ∣ A.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hd
    have := A.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) hpP
    linarith
  rw [hsplit, Finset.prod_inv_distrib]
  calc ((∏ p ∈ d.primeFactors, (1 - A.nu p)) * ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => ¬ p ∣ d), (1 - A.nu p))
        * (A.nu d * (∏ x ∈ d.primeFactors, (1 - A.nu x))⁻¹)
      = (A.nu d * ((∏ x ∈ d.primeFactors, (1 - A.nu x))⁻¹
            * (∏ x ∈ d.primeFactors, (1 - A.nu x))))
          * ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => ¬ p ∣ d), (1 - A.nu p) := by ring
    _ = A.nu d * ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => ¬ p ∣ d), (1 - A.nu p) := by
        rw [inv_mul_cancel₀ hprod]; ring


/-! ## The finite core of step 1: Poisson weights and the per-level coupling

The comparison route needs the per-level statement that the indicator `1_{N ≥ 1}` of a Poisson
variable `N` with mean `x` is Bernoulli with parameter `1 - e^{-x}`, together with the fact that
the *product* Poisson law pushes the indicator process forward to the product Bernoulli law.  The
per-level part is proved here; the product part is delegated
(`Selberg.poisson_product_coupling`). -/

/-- The exponential series, in the form used below. -/
theorem real_exp_eq_tsum_div (x : ℝ) : Real.exp x = ∑' n : ℕ, x ^ n / n.factorial := by
  rw [Real.exp_eq_exp_ℝ]
  exact congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) x

/-- The Poisson weight of `n` with mean `x`: `e^{-x} x^n / n!`. -/
noncomputable def poissonWeight (x : ℝ) (n : ℕ) : ℝ := Real.exp (-x) * x ^ n / n.factorial

theorem poissonWeight_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ poissonWeight x n := by
  rw [poissonWeight]; positivity

theorem poissonWeight_zero (x : ℝ) : poissonWeight x 0 = Real.exp (-x) := by
  simp [poissonWeight]

theorem summable_poissonWeight (x : ℝ) : Summable fun n : ℕ => poissonWeight x n := by
  have hsum' : Summable fun n : ℕ => x ^ n / n.factorial := Real.summable_pow_div_factorial x
  have h1 : ∀ n : ℕ, poissonWeight x n = Real.exp (-x) * (x ^ n / n.factorial) := by
    intro n; rw [poissonWeight]; ring
  simpa only [h1] using hsum'.mul_left (Real.exp (-x))

/-- The Poisson law has total mass one. -/
theorem tsum_poissonWeight (x : ℝ) : ∑' n : ℕ, poissonWeight x n = 1 := by
  have hsum : Summable fun n : ℕ => x ^ n / n.factorial := Real.summable_pow_div_factorial x
  have h1 : ∀ n : ℕ, poissonWeight x n = Real.exp (-x) * (x ^ n / n.factorial) := by
    intro n; rw [poissonWeight]; ring
  simp_rw [h1]
  rw [Summable.tsum_mul_left _ hsum, ← real_exp_eq_tsum_div x, ← Real.exp_add]
  simp

/-- **The per-level coupling.**  `P(N ≥ 1) = 1 - e^{-x}` for a Poisson variable with mean `x`:
the indicator of `{N ≥ 1}` is Bernoulli with parameter `1 - e^{-x}`, so `Bern(1-e^{-x})` is
stochastically dominated by `Poi(x)`. -/
theorem tsum_poissonWeight_succ (x : ℝ) :
    ∑' n : ℕ, poissonWeight x (n + 1) = 1 - Real.exp (-x) := by
  have h := (summable_poissonWeight x).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at h
  rw [poissonWeight_zero] at h
  have htot := tsum_poissonWeight x
  linarith


/-- **Multiplicativity on squarefree divisors.**  For a squarefree divisor `d` of `P` the sieve
density `ν(d)` is the product of the `ν p` over the prime factors of `d`. -/
lemma nu_eq_prod_primeFactors (A : BoundingSieve) {d : ℕ} (hd : d ∣ A.prodPrimes) :
    A.nu d = ∏ p ∈ d.primeFactors, A.nu p := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd A.prodPrimes_squarefree
  have hpair : (d.primeFactors : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  calc A.nu d = A.nu (∏ p ∈ d.primeFactors, p) := by rw [Nat.prod_primeFactors_of_squarefree hsq]
    _ = ∏ p ∈ d.primeFactors, A.nu p :=
        ArithmeticFunction.IsMultiplicative.map_prod id A.nu_mult d.primeFactors hpair

/-- **The summand of `Vf_mul_gSum` in powerset form.**  For `d ∣ P` the Bernoulli weight
`ν(d) · ∏_{p ∣ P, p ∤ d}(1 - ν p)` equals `(∏_{p ∣ d} ν p) · ∏_{p ∈ P \ d}(1 - ν p)`. -/
lemma summand_eq_powerset (A : BoundingSieve) {d : ℕ} (hd : d ∣ A.prodPrimes) :
    A.nu d * ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => ¬ p ∣ d), (1 - A.nu p)
      = (∏ p ∈ d.primeFactors, A.nu p)
          * ∏ p ∈ A.prodPrimes.primeFactors \ d.primeFactors, (1 - A.nu p) := by
  have hdne : d ≠ 0 := ne_zero_of_dvd_ne_zero A.prodPrimes_ne_zero hd
  have hflt : A.prodPrimes.primeFactors.filter (fun p : ℕ => ¬ p ∣ d)
      = A.prodPrimes.primeFactors \ d.primeFactors := by
    rw [Finset.sdiff_eq_filter]
    refine Finset.filter_congr ?_
    intro p hp
    constructor
    · intro hnpd hpd
      exact hnpd (Nat.dvd_of_mem_primeFactors hpd)
    · intro hnpd hpd
      exact hnpd (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpd, hdne⟩)
  rw [hflt, nu_eq_prod_primeFactors A hd]


/-- **The logarithmic form of the truncation.**  For `D > 0` and positive primes, the condition
`∏_{p ∈ S} p < √D` is exactly `∑_{p ∈ S} log p < log D / 2`.  This is the bridge to the
`θ p = log p / log Z`, `λ = log D / (2 log Z)` language in which `IsLinearNat` is phrased. -/
theorem prod_lt_sqrt_iff_sum_log_lt {D : ℝ} (hD : 0 < D) {S : Finset ℕ}
    (hS : ∀ p ∈ S, 0 < p) :
    ((∏ p ∈ S, (p : ℝ)) < Real.sqrt D) ↔ ((∑ p ∈ S, Real.log p) < Real.log D / 2) := by
  have hprod : 0 < ∏ p ∈ S, (p : ℝ) := Finset.prod_pos (fun p hp => Nat.cast_pos.mpr (hS p hp))
  rw [← Real.log_sqrt hD.le, ← Real.log_prod (fun p hp => ne_of_gt (Nat.cast_pos.mpr (hS p hp)))]
  exact (Real.log_lt_log_iff hprod (Real.sqrt_pos.mpr hD)).symm


/-! ## The axiom in logarithmic (tail-mass) form

`IsLinearNat A Z K` bounds the tail *product* `∏_{p ≥ w}(1 - ν p)^{-1}`.  Taking logarithms turns it
into a bound on the tail *mass* `Σ_{p ≥ w} -log (1 - ν p)`, which is the form used by the
extremal problem: with `θ = log w / log Z` it says
`Σ_{θ p ≥ θ} -log (1 - ν p) ≤ log (1/θ) + log (1 + K/(θ log Z))` up to the harmless slack. -/

/-- **The axiom in logarithmic form.** -/
theorem sum_negLog_one_sub_le (A : BoundingSieve) {Z : ℕ} {K : ℝ} (hK : 0 ≤ K) (hZ2 : 2 ≤ Z)
    (hlin : IsLinearNat A Z K) {w : ℝ} (hw : 2 ≤ w) (hwZ : w < (Z : ℝ)) :
    (∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)), -Real.log (1 - A.nu p))
      ≤ Real.log (Real.log (Z : ℝ) / Real.log w) + Real.log (1 + K / Real.log w) := by
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  have hprod := hlin.2 w hw hwZ
  have hlt : ∀ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)), A.nu p < 1 := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).1
    exact A.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp')
      (Nat.mem_primeFactors.mp hp').2.1
  have hlog : Real.log (∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)),
        (1 - A.nu p)⁻¹)
      = ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)), -Real.log (1 - A.nu p) := by
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [Real.log_inv]
    · intro p hp
      exact inv_ne_zero (by have := hlt p hp; linarith)
  have hpos : 0 < ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - A.nu p)⁻¹ :=
    Finset.prod_pos (fun p hp => inv_pos.mpr (by have := hlt p hp; linarith))
  have h4 : Real.log (∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ)),
        (1 - A.nu p)⁻¹)
      ≤ Real.log ((Real.log (Z : ℝ) / Real.log w) * (1 + K / Real.log w)) :=
    Real.log_le_log hpos hprod
  have hRpos : 0 < Real.log (Z : ℝ) / Real.log w := div_pos hlogZ hlogw
  have hRpos2 : 0 < 1 + K / Real.log w := by
    have : 0 ≤ K / Real.log w := div_nonneg hK hlogw.le
    linarith
  rw [Real.log_mul (ne_of_gt hRpos) (ne_of_gt hRpos2)] at h4
  linarith [hlog ▸ h4]



/-! ## Removing the slack: the shift of the levels

`IsLinearNat` bounds the tail *mass* only up to the slack `s(u) = log (1 + K/(u log Z))`.  Shifting
every level `t` to `t · exp (-(s t))` removes the slack exactly: the shifted levels satisfy the
strict constraint `Σ_{t' ≥ u} m ≤ log (1/u)`, and they are pointwise smaller than the original ones,
so any lower bound proved for the strict constraint transfers back. -/

/-- The slack function `s(u) = log (1 + K/(u L))` (`L = log Z`). -/
noncomputable def slack (K L u : ℝ) : ℝ := Real.log (1 + K / (u * L))

/-- The shifted level `t · exp (-(s t))`. -/
noncomputable def shiftLevel (K L t : ℝ) : ℝ := t * Real.exp (-(slack K L t))

theorem slack_nonneg {K L u : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (hu : 0 < u) : 0 ≤ slack K L u := by
  rw [slack]
  refine Real.log_nonneg ?_
  have : 0 ≤ K / (u * L) := div_nonneg hK (by positivity)
  linarith

theorem shiftLevel_pos {K L t : ℝ} (ht : 0 < t) : 0 < shiftLevel K L t := by
  rw [shiftLevel]; positivity

theorem shiftLevel_le {K L t : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (ht : 0 < t) :
    shiftLevel K L t ≤ t := by
  have hexp : Real.exp (-(slack K L t)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (slack_nonneg hK hL ht))
  calc shiftLevel K L t = t * Real.exp (-(slack K L t)) := rfl
    _ ≤ t * 1 := mul_le_mul_of_nonneg_left hexp ht.le
    _ = t := mul_one t

/-- **The shift, strictly.**  If a finite level/mass configuration satisfies the *slacky* tail
constraint `Σ_{t j ≥ u} m j ≤ log (1/u) + s u` for `u ∈ (0,1]`, then the shifted levels
`shiftLevel K L (t j)` satisfy the *strict* constraint `Σ ≤ log (1/u)`.

The proof picks, for each `u`, a level `t i` minimal among those whose shift reaches `u`; the whole
suffix above `u` is then contained in the suffix above `t i`, so the axiom at the *single* level
`t i` controls it, and `log (1/shiftLevel K L (t i)) = log (1/t i) + s (t i)`. -/
theorem shift_strict_constraint {ι : Type*} [DecidableEq ι] (S : Finset ι) (t m : ι → ℝ)
    (ht : ∀ j ∈ S, 0 < t j) (ht1 : ∀ j ∈ S, t j ≤ 1) (hm : ∀ j ∈ S, 0 ≤ m j)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 < L)
    (hcon : ∀ u : ℝ, 0 < u → u ≤ 1 →
      ∑ j ∈ S.filter (fun j => u ≤ t j), m j ≤ Real.log (1 / u) + slack K L u) :
    ∀ u : ℝ, 0 < u → u ≤ 1 →
      ∑ j ∈ S.filter (fun j => u ≤ shiftLevel K L (t j)), m j ≤ Real.log (1 / u) := by
  intro u hu0 hu1
  set T : Finset ι := S.filter (fun j => u ≤ shiftLevel K L (t j)) with hT
  rcases T.eq_empty_or_nonempty with hE | hne
  · rw [hE, Finset.sum_empty, one_div, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos hu0.le hu1
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image T t hne
    have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
    have hti : 0 < t i := ht i hiS
    have hti1 : t i ≤ 1 := ht1 i hiS
    have hge : u ≤ shiftLevel K L (t i) := (Finset.mem_filter.mp hi).2
    have hposi : 0 < shiftLevel K L (t i) := shiftLevel_pos hti
    have hsub : T ⊆ S.filter (fun j => t i ≤ t j) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, hmin j hj⟩
    have hkey : ∑ j ∈ T, m j ≤ Real.log (1 / t i) + slack K L (t i) :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hm j (Finset.mem_filter.mp hj).1))
        (hcon (t i) hti hti1)
    have hlogeq : Real.log (1 / shiftLevel K L (t i)) = Real.log (1 / t i) + slack K L (t i) := by
      rw [shiftLevel, one_div, one_div, Real.log_inv, Real.log_inv,
        Real.log_mul (ne_of_gt hti) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
      ring
    have hmono : Real.log (1 / shiftLevel K L (t i)) ≤ Real.log (1 / u) := by
      refine Real.log_le_log (div_pos one_pos hposi) ?_
      rw [one_div, one_div, inv_le_inv₀ hposi hu0]
      exact hge
    calc ∑ j ∈ T, m j ≤ Real.log (1 / t i) + slack K L (t i) := hkey
      _ = Real.log (1 / shiftLevel K L (t i)) := hlogeq.symm
      _ ≤ Real.log (1 / u) := hmono

/-- **The shift decreases the weighted sum pointwise.** -/
theorem sum_shiftLevel_mul_le {ι : Type*} (S : Finset ι) (t b : ι → ℝ) (ht : ∀ j ∈ S, 0 < t j)
    (hb : ∀ j ∈ S, 0 ≤ b j) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 < L) :
    (∑ j ∈ S, shiftLevel K L (t j) * b j) ≤ ∑ j ∈ S, t j * b j :=
  Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (shiftLevel_le hK hL (ht j hj)) (hb j hj))

/-- **The summed identity.**  With every prime of `P` below `Z`, the Selberg sum times `Vf` is the
sum, over the divisors of `P` below `ξ`, of the Bernoulli weights
`ν(d) · ∏_{p ∣ P, p ∤ d} (1 - ν p)`. -/
theorem Vf_mul_gSum (A : BoundingSieve) {Z : ℕ}
    (hZ : ∀ p ∈ A.prodPrimes.primeFactors, p < Z) (ξ : ℝ) :
    Vf A Z * gSum A ξ
      = ∑ d ∈ A.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < ξ),
          A.nu d * ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => ¬ p ∣ d), (1 - A.nu p) := by
  rw [gSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  exact Vf_mul_selbergTerms A hZ (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)

open Work.ChenPlan.LinearSieve.Selberg in
/-- **The selection-mass form of `Vf · gSum`.**  For `ξ ≤ Z` (so that, under `IsLinearNat`, the
level `ξ` is below the sift limit) the quantity `Vf A Z * gSum A ξ` is the probability that the
independent Bernoulli selection of the primes of `P = A.prodPrimes`, with probabilities `ν p`,
picks a set of primes whose product is `< ξ`:

`Vf A Z * gSum A ξ = Σ_{S ⊆ P.primeFactors, ∏_{p ∈ S} p < ξ} (∏_{p ∈ S} ν p) · ∏_{p ∈ P \ S}(1 - ν p)`.

This is the interface used by the extremal problem (`Selberg/Alt`). -/
theorem Vf_mul_gSum_powerset (A : BoundingSieve) {Z : ℕ}
    (hZ : ∀ p ∈ A.prodPrimes.primeFactors, p < Z) (ξ : ℝ) :
    Vf A Z * gSum A ξ
      = ∑ S ∈ A.prodPrimes.primeFactors.powerset.filter
            (fun S => ((∏ p ∈ S, p : ℕ) : ℝ) < ξ),
          (∏ p ∈ S, A.nu p) * ∏ p ∈ A.prodPrimes.primeFactors \ S, (1 - A.nu p) := by
  classical
  rw [Vf_mul_gSum A hZ ξ]
  have hstep : ∀ d ∈ A.prodPrimes.divisors.filter (fun d : ℕ => (d : ℝ) < ξ),
      A.nu d * ∏ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => ¬ p ∣ d), (1 - A.nu p)
        = (∏ p ∈ d.primeFactors, A.nu p)
            * ∏ p ∈ A.prodPrimes.primeFactors \ d.primeFactors, (1 - A.nu p) := fun d hd =>
    summand_eq_powerset A (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)
  rw [Finset.sum_congr rfl hstep]
  exact sum_divisors_lt_eq_sum_powerset A.prodPrimes A.prodPrimes_squarefree ξ
    (fun S => (∏ p ∈ S, A.nu p) * ∏ p ∈ A.prodPrimes.primeFactors \ S, (1 - A.nu p))


/-- **The packing, after the shift.**  For a finite level/mass configuration satisfying the *slacky*
tail constraint, the shifted levels admit pairwise disjoint intervals `(a j, b j]` of lengths the
masses, each contained in `(0, log (1/shiftLevel K L (t j))]`.  This is `interval_packing` fed with
`shift_strict_constraint`, i.e. with a constraint that has no slack left. -/
theorem exists_packing_shifted {n : ℕ} (t m : Fin n → ℝ) (ht : ∀ j, 0 < t j)
    (ht1 : ∀ j, t j ≤ 1) (hm : ∀ j, 0 < m j) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 < L)
    (hcon : ∀ u : ℝ, 0 < u → u ≤ 1 →
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => u ≤ t j), m j ≤ Real.log (1 / u) + slack K L u) :
    ∃ a b : Fin n → ℝ, (∀ j, 0 ≤ a j) ∧ (∀ j, b j - a j = m j)
      ∧ (∀ j, b j ≤ Real.log (1 / shiftLevel K L (t j)))
      ∧ Work.ChenPlan.LinearSieve.Selberg.Alt.PairwiseDisjointIoc a b := by
  have hstrict := shift_strict_constraint Finset.univ t m (fun j _ => ht j) (fun j _ => ht1 j)
    (fun j _ => le_of_lt (hm j)) hK hL hcon
  exact Work.ChenPlan.LinearSieve.Selberg.Alt.interval_packing (fun j => shiftLevel K L (t j)) m
    (fun j => shiftLevel_pos (ht j)) hm hstrict



/-! ## The assembly: the selection mass in the `θ`-language, and the reference comparison

With `θ = s/2 = log D/(2 log Z)` and `levelLog Z p = log p / log Z`, the selection-mass identity
reads

`Vf A Z * gSum A (√D) = Σ_{S : Σ_{p ∈ S} levelLog Z p < θ} (∏_{p ∈ S} ν p) · ∏_{p ∉ S}(1 - ν p)`,

i.e. it is the distribution function at `θ` of the sum `Σ_p levelLog Z p · B_p` of the independent
Bernoulli selection.  The last input — the extremal comparison with the reference variable
`refSum = Σ_{k ≥ 1} e^{-S_k}` of a unit-rate Poisson process — is stated as
`selectionMass_lower`; its proof is the interval coupling (see `Selberg/Alt`), using the two
delegated pieces `Alt.interval_events` and `Alt.refsum_cdf` together with
`sum_levels_mul_hitIndicator_le_refSum`. -/

/-- The level of a prime: `log p / log Z`. -/
noncomputable def levelLog (Z p : ℕ) : ℝ := Real.log (p : ℝ) / Real.log (Z : ℝ)

/-- **The selection mass in the `θ`-language.**  For `θ = log D / (2 log Z)` the quantity
`Vf A Z * gSum A (√D)` is the sum, over the subsets `S` of the primes of `P` whose levels add up
to less than `θ`, of the Bernoulli weights. -/
theorem Vf_mul_gSum_sqrt_eq_thetaSum (A : BoundingSieve) {Z : ℕ} {D θ : ℝ} (hD : 0 < D)
    (hθ : θ = Real.log D / (2 * Real.log (Z : ℝ))) (hZ1 : 1 < Z)
    (hZP : ∀ p ∈ A.prodPrimes.primeFactors, p < Z) :
    Vf A Z * gSum A (Real.sqrt D)
      = ∑ S ∈ A.prodPrimes.primeFactors.powerset.filter
          (fun S => (∑ p ∈ S, levelLog Z p) < θ),
        (∏ p ∈ S, A.nu p) * ∏ p ∈ A.prodPrimes.primeFactors \ S, (1 - A.nu p) := by
  classical
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast hZ1)
  rw [Vf_mul_gSum_powerset A hZP (Real.sqrt D)]
  refine Finset.sum_congr ?_ (fun S _ => rfl)
  refine Finset.filter_congr (fun S hS => ?_)
  have hprime : ∀ p ∈ S, 0 < p := by
    intro p hp
    have hp' : p ∈ A.prodPrimes.primeFactors := (Finset.mem_powerset.mp hS) hp
    exact (Nat.prime_of_mem_primeFactors hp').pos
  rw [Nat.cast_prod, prod_lt_sqrt_iff_sum_log_lt hD hprime, hθ]
  simp only [levelLog]
  have heq : Real.log D / (2 * Real.log (Z : ℝ)) = Real.log D / 2 / Real.log (Z : ℝ) := by ring
  rw [heq, ← Finset.sum_div, div_lt_div_iff_of_pos_right hlogZ]

/-- The mass attached to a prime: `m p = -log (1 - ν p)`, so that `e^{-m p} = 1 - ν p`. -/
noncomputable def atomMass (A : BoundingSieve) (p : ℕ) : ℝ := -Real.log (1 - A.nu p)

/-- The deadline of the room attached to `p`: `log (1/t p) + s(t p)` where `t p = log p / log Z`
is the level of `p` and `s(u) = log (1 + K/(u log Z))` is the slack of the axiom. -/
noncomputable def deadline (Z : ℕ) (K : ℝ) (p : ℕ) : ℝ :=
  Real.log (Real.log (Z : ℝ) / Real.log (p : ℝ)) + Real.log (1 + K / Real.log (p : ℝ))

theorem atomMass_pos (A : BoundingSieve) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) :
    0 < atomMass A p := by
  have hpr := Nat.prime_of_mem_primeFactors hp
  have h1 := A.nu_pos_of_prime p hpr (Nat.mem_primeFactors.mp hp).2.1
  have h2 := A.nu_lt_one_of_prime p hpr (Nat.mem_primeFactors.mp hp).2.1
  rw [atomMass, neg_pos]
  exact Real.log_neg (by linarith) (by linarith)

theorem exp_neg_atomMass (A : BoundingSieve) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) :
    Real.exp (-(atomMass A p)) = 1 - A.nu p := by
  have hpr := Nat.prime_of_mem_primeFactors hp
  have h2 := A.nu_lt_one_of_prime p hpr (Nat.mem_primeFactors.mp hp).2.1
  rw [atomMass, neg_neg]
  exact Real.exp_log (by linarith)

theorem one_sub_exp_neg_atomMass (A : BoundingSieve) {p : ℕ}
    (hp : p ∈ A.prodPrimes.primeFactors) : 1 - Real.exp (-(atomMass A p)) = A.nu p := by
  rw [exp_neg_atomMass A hp]; ring

/-- **The axiom in tail-mass form.**  For a prime `p` of the sieve the total mass of the primes
`≥ p` is at most the deadline `log (log Z / log p) + log (1 + K/log p)`. -/
theorem mass_tail_le_deadline (A : BoundingSieve) {Z : ℕ} {K : ℝ} (hK : 0 ≤ K) (hZ2 : 2 ≤ Z)
    (hlin : IsLinearNat A Z K) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) :
    (∑ q ∈ A.prodPrimes.primeFactors.filter (fun q : ℕ => p ≤ q), atomMass A q)
      ≤ deadline Z K p := by
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hpZ : (p : ℝ) < (Z : ℝ) := by exact_mod_cast hlin.1 p hp
  have h := sum_negLog_one_sub_le A hK hZ2 hlin (w := (p : ℝ)) (by exact_mod_cast hp2) hpZ
  have hfil : A.prodPrimes.primeFactors.filter (fun q : ℕ => (p : ℝ) ≤ (q : ℝ))
      = A.prodPrimes.primeFactors.filter (fun q : ℕ => p ≤ q) :=
    Finset.filter_congr (fun q _ => by rw [Nat.cast_le])
  rw [hfil] at h
  simpa only [atomMass, deadline] using h

/-- The left endpoint of the room of `p`: the rooms of the primes `> p` are placed first. -/
noncomputable def roomA (A : BoundingSieve) (p : ℕ) : ℝ :=
  ∑ q ∈ A.prodPrimes.primeFactors.filter (fun q : ℕ => p < q), atomMass A q

/-- The right endpoint of the room of `p`. -/
noncomputable def roomB (A : BoundingSieve) (p : ℕ) : ℝ := roomA A p + atomMass A p

theorem roomA_nonneg (A : BoundingSieve) (p : ℕ) : 0 ≤ roomA A p :=
  Finset.sum_nonneg (fun q hq => le_of_lt (atomMass_pos A (Finset.mem_filter.mp hq).1))

theorem roomB_sub_roomA (A : BoundingSieve) (p : ℕ) : roomB A p - roomA A p = atomMass A p := by
  rw [roomB]; ring

theorem roomB_eq_tail (A : BoundingSieve) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) :
    roomB A p = ∑ q ∈ A.prodPrimes.primeFactors.filter (fun q : ℕ => p ≤ q), atomMass A q := by
  have hset : A.prodPrimes.primeFactors.filter (fun q : ℕ => p ≤ q)
      = insert p (A.prodPrimes.primeFactors.filter (fun q : ℕ => p < q)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hq, hpq⟩
      rcases eq_or_lt_of_le hpq with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨hq, h⟩
    · rintro (rfl | ⟨hq, hpq⟩)
      · exact ⟨hp, le_rfl⟩
      · exact ⟨hq, le_of_lt hpq⟩
  have hnot : p ∉ A.prodPrimes.primeFactors.filter (fun q : ℕ => p < q) := by
    simp only [Finset.mem_filter, lt_self_iff_false, and_false, not_false_iff]
  rw [hset, Finset.sum_insert hnot, roomB, roomA, add_comm]

theorem roomB_le_deadline (A : BoundingSieve) {Z : ℕ} {K : ℝ} (hK : 0 ≤ K) (hZ2 : 2 ≤ Z)
    (hlin : IsLinearNat A Z K) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) :
    roomB A p ≤ deadline Z K p := by
  rw [roomB_eq_tail A hp]
  exact mass_tail_le_deadline A hK hZ2 hlin hp

theorem room_disjoint (A : BoundingSieve) {p q : ℕ}
    (hp : p ∈ A.prodPrimes.primeFactors) (hq : q ∈ A.prodPrimes.primeFactors) (h : p < q) :
    Disjoint (Set.Ioc (roomA A p) (roomB A p)) (Set.Ioc (roomA A q) (roomB A q)) := by
  have hle : roomB A q ≤ roomA A p := by
    rw [roomB_eq_tail A hq, roomA]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter] at hr ⊢
      exact ⟨hr.1, lt_of_lt_of_le h hr.2⟩
    · intro r hr _
      exact le_of_lt (atomMass_pos A (Finset.mem_filter.mp hr).1)
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  have h1 : x ≤ roomB A q := hx'.2
  have h2 : roomA A p < x := hx.1
  linarith

/-- **The rooms.**  The primes of the sieve admit pairwise disjoint intervals `(a p, b p]` of
length `atomMass A p`, inside `(0, deadline Z K p]`. -/
theorem exists_rooms (A : BoundingSieve) {Z : ℕ} {K : ℝ} (hK : 0 ≤ K) (hZ2 : 2 ≤ Z)
    (hlin : IsLinearNat A Z K) :
    ∃ a b : {p // p ∈ A.prodPrimes.primeFactors} → ℝ,
      (∀ p, 0 ≤ a p) ∧ (∀ p, b p - a p = atomMass A p)
        ∧ (∀ p, b p ≤ deadline Z K p)
        ∧ (∀ p q, p ≠ q → Disjoint (Set.Ioc (a p) (b p)) (Set.Ioc (a q) (b q))) := by
  refine ⟨fun p => roomA A p, fun p => roomB A p, fun p => roomA_nonneg A p, fun p => ?_, ?_, ?_⟩
  · exact roomB_sub_roomA A p
  · exact fun p => roomB_le_deadline A hK hZ2 hlin p.2
  · intro p q hpq
    rcases lt_or_gt_of_ne (fun h => hpq (Subtype.ext h)) with h | h
    · exact room_disjoint A p.2 q.2 h
    · exact (room_disjoint A q.2 p.2 h).symm

/-- **Bookkeeping.**  The parameter range `s = log D / log Z ≤ 2` forces `Z ≥ √D`, so that a lower
bound on `D` gives one on `Z` (used to absorb the `O(K/log Z)` errors). -/
theorem sqrt_le_of_log_div_le_two {D : ℝ} {Z : ℕ} (hD : 0 < D) (hZ1 : 1 < Z)
    (hs : Real.log D / Real.log (Z : ℝ) ≤ 2) : Real.sqrt D ≤ (Z : ℝ) := by
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast hZ1)
  have hD2 : D ≤ (Z : ℝ) ^ 2 := by
    have h : Real.log D ≤ 2 * Real.log (Z : ℝ) := (div_le_iff₀ hlogZ).mp hs
    have h2 : Real.log D ≤ Real.log ((Z : ℝ) ^ 2) := by
      rw [Real.log_pow]; push_cast; linarith
    exact (Real.log_le_log_iff hD (by positivity)).mp h2
  calc Real.sqrt D ≤ Real.sqrt ((Z : ℝ) ^ 2) := Real.sqrt_le_sqrt hD2
    _ = (Z : ℝ) := Real.sqrt_sq (by positivity)



/-! ## The heavy/light decomposition and the coupling -/

variable {A : BoundingSieve}





/-- The natural threshold of the heavy primes. -/
noncomputable def heavyN (K ε : ℝ) : ℕ := ⌈Real.exp (K / ε)⌉₊

/-- The mass of the *light* primes (those with `log p < K/ε`), at the level scale. -/
noncomputable def delta (A : BoundingSieve) (Z : ℕ) (K ε : ℝ) : ℝ :=
  ∑ p : {p // p ∈ A.prodPrimes.primeFactors},
    if Real.exp (K / ε) ≤ ((p : ℕ) : ℝ) then 0 else levelLog Z (p : ℕ)

theorem levelLog_pos (A : BoundingSieve) {Z : ℕ} (hZ2 : 2 ≤ Z)
    {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) : 0 < levelLog Z p := by
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp2)
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  rw [levelLog]
  exact div_pos hlogp hlogZ

theorem levelLog_nonneg (Z n : ℕ) : 0 ≤ levelLog Z n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [levelLog]
  · rw [levelLog]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (Real.log_natCast_nonneg Z)

/-- The light-prime error is at most `N log N / log Z` with `N = ⌈e^{K/ε}⌉₊`. -/
theorem delta_le (A : BoundingSieve) {Z : ℕ} {K ε : ℝ} (hK : 0 ≤ K) (hZ2 : 2 ≤ Z) (hε : 0 < ε) :
    delta A Z K ε ≤ (heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ) / Real.log Z := by
  classical
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  have hN1 : 1 ≤ heavyN K ε := by
    rw [heavyN]
    exact Nat.ceil_pos.mpr (lt_of_lt_of_le (by norm_num) (Real.one_le_exp (by positivity)))
  have hlogN : 0 ≤ Real.log (heavyN K ε : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  set L : Finset {p // p ∈ A.prodPrimes.primeFactors} :=
    Finset.univ.filter (fun p => ¬ (Real.exp (K / ε) ≤ ((p : ℕ) : ℝ))) with hL
  have hdelta : delta A Z K ε = ∑ p ∈ L, levelLog Z (p : ℕ) := by
    rw [delta, Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add]
    rw [hL]
  rw [hdelta]
  have hlt : ∀ p ∈ L, (p : ℕ) < heavyN K ε := by
    intro p hp
    rw [hL, Finset.mem_filter] at hp
    have h1 : ((p : ℕ) : ℝ) < Real.exp (K / ε) := not_le.mp hp.2
    have h2 : Real.exp (K / ε) ≤ ((heavyN K ε : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : ((p : ℕ) : ℝ) < ((heavyN K ε : ℕ) : ℝ) := lt_of_lt_of_le h1 h2
    exact_mod_cast h3
  have hinj : ∀ p ∈ L, ∀ q ∈ L, (p : ℕ) = (q : ℕ) → p = q := by
    intro p _ q _ hpq
    exact Subtype.ext hpq
  have himg : ∑ p ∈ L, levelLog Z (p : ℕ)
      = ∑ n ∈ L.image (fun p : {p // p ∈ A.prodPrimes.primeFactors} => (p : ℕ)), levelLog Z n :=
    (Finset.sum_image (f := fun n : ℕ => levelLog Z n)
      (g := fun p : {p // p ∈ A.prodPrimes.primeFactors} => (p : ℕ)) hinj).symm
  rw [himg]
  have hsub : L.image (fun p : {p // p ∈ A.prodPrimes.primeFactors} => (p : ℕ))
      ⊆ Finset.range (heavyN K ε) := by
    intro n hn
    rw [Finset.mem_range]
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact hlt p hp
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => ?_)) ?_
  · exact levelLog_nonneg Z n
  · calc ∑ n ∈ Finset.range (heavyN K ε), levelLog Z n
        ≤ ∑ _n ∈ Finset.range (heavyN K ε), Real.log (heavyN K ε : ℝ) / Real.log Z := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rcases Nat.eq_zero_or_pos n with hn0 | hnpos
          · rw [hn0]
            simp only [levelLog, Nat.cast_zero, Real.log_zero, zero_div]
            exact div_nonneg hlogN hlogZ.le
          · rw [levelLog, div_le_div_iff_of_pos_right hlogZ]
            exact Real.log_le_log (by exact_mod_cast hnpos)
              (by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hn)))
      _ = (heavyN K ε : ℝ) * (Real.log (heavyN K ε : ℝ) / Real.log Z) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ) / Real.log Z := by ring

theorem deadline_le_heavy (A : BoundingSieve) {Z : ℕ} {K ε : ℝ} (hK : 0 ≤ K) (hZ2 : 2 ≤ Z)
    (hε : 0 < ε) {p : ℕ} (hp : p ∈ A.prodPrimes.primeFactors) (hpp : Real.exp (K / ε) ≤ (p : ℝ)) :
    deadline Z K p ≤ Real.log (1 / levelLog Z p) + Real.log (1 + ε) := by
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp2)
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  have hlogpK : K / ε ≤ Real.log (p : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hpp
    rwa [Real.log_exp] at h
  have hKle : K ≤ ε * Real.log (p : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogpK hε.le
    rw [mul_div_cancel₀ K (ne_of_gt hε)] at h
    exact h
  have hratio : K / Real.log (p : ℝ) ≤ ε := (div_le_iff₀ hlogp).mpr hKle
  have hlog1 : Real.log (1 + K / Real.log (p : ℝ)) ≤ Real.log (1 + ε) :=
    Real.log_le_log (by have h : 0 ≤ K / Real.log (p : ℝ) := div_nonneg hK hlogp.le; linarith)
      (by linarith)
  have hinv : (1 : ℝ) / levelLog Z p = Real.log (Z : ℝ) / Real.log (p : ℝ) := by
    rw [levelLog, one_div, inv_div]
  rw [hinv, deadline]
  linarith

/-- **The pointwise coupling.**  If the intervals `(a i, b i]` are pairwise disjoint, `a i ≥ 0` and
`b i ≤ log (1/t i) + log (1+ε)` with `t i > 0`, then on the set where the reference series
converges the weighted hit sum is at most `(1+ε)` times the reference sum. -/
theorem hitSum_le_refSum {Ω : Type*} {ι : Type*} [Fintype ι] (E : ℕ → Ω → ℝ)
    (t a b : ι → ℝ) (ht : ∀ i, 0 < t i) (ha : ∀ i, 0 ≤ a i)
    {ε : ℝ} (hε : 0 ≤ ε) (hb : ∀ i, b i ≤ Real.log (1 / t i) + Real.log (1 + ε))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (ω : Ω)
    (hsum : Summable fun k : ℕ => Real.exp (-(Alt.partialSum (fun i => E i ω) (k + 1)))) :
    (∑ i, t i * (Alt.IntervalHit E (a i) (b i)).indicator (fun _ => (1 : ℝ)) ω)
      ≤ (1 + ε) * Alt.refSum (fun i => E i ω) := by
  classical
  set S : ℕ → ℝ := fun k => Alt.partialSum (fun i => E i ω) k with hS
  set f : ℕ → ℝ := fun k => Real.exp (- S (k + 1)) with hf
  have hfpos : ∀ k, 0 ≤ f k := fun k => le_of_lt (Real.exp_pos _)
  have hsumf : Summable f := by simpa only [hf, hS] using hsum
  have hmem : ∀ i, ω ∈ Alt.IntervalHit E (a i) (b i) ↔
      ∃ k, 1 ≤ k ∧ S k ∈ Set.Ioc (a i) (b i) := by
    intro i
    constructor
    · rintro ⟨k, hk⟩
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simp only [Alt.partialSum, Finset.sum_range_zero] at hk
        exact absurd hk.1 (not_lt.mpr (ha i))
      · exact ⟨k, hkpos, hk⟩
    · rintro ⟨k, _, hk⟩
      exact ⟨k, hk⟩
  let kk : ι → ℕ := fun i =>
    if h : ω ∈ Alt.IntervalHit E (a i) (b i) then Nat.find ((hmem i).mp h) else 0
  have hkk : ∀ i (h : ω ∈ Alt.IntervalHit E (a i) (b i)),
      1 ≤ kk i ∧ S (kk i) ∈ Set.Ioc (a i) (b i) := by
    intro i h
    have h' : kk i = Nat.find ((hmem i).mp h) := by simp only [kk, dif_pos h]
    rw [h']
    exact Nat.find_spec ((hmem i).mp h)
  set I : Finset ι := Finset.univ.filter (fun i => ω ∈ Alt.IntervalHit E (a i) (b i)) with hI
  have hkk_inj : Set.InjOn kk ↑I := by
    intro i hi i' hi' hEq
    by_contra hne
    have h1 := (hkk i (Finset.mem_filter.mp hi).2).2
    have h2 := (hkk i' (Finset.mem_filter.mp hi').2).2
    rw [hEq] at h1
    exact (Set.disjoint_left.mp (hdisj i i' hne)) h1 h2
  have hLHS : ∑ i : ι, t i * (Alt.IntervalHit E (a i) (b i)).indicator
        (fun _ => (1 : ℝ)) ω = ∑ i ∈ I, t i := by
    have h1 : ∀ i : ι, t i *
        (Alt.IntervalHit E (a i) (b i)).indicator (fun _ => (1 : ℝ)) ω
        = if ω ∈ Alt.IntervalHit E (a i) (b i) then t i else 0 := by
      intro i
      rw [Set.indicator_apply]
      by_cases h : ω ∈ Alt.IntervalHit E (a i) (b i) <;> simp [h]
    simp only [h1, hI]
    rw [Finset.sum_filter]
  have hexp : Real.exp (Real.log (1 + ε)) = 1 + ε := Real.exp_log (by linarith)
  have hbase : ∑ i ∈ I, t i ≤ ∑ i ∈ I, (1 + ε) * f (kk i - 1) := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨hk1, hk2⟩ := hkk i (Finset.mem_filter.mp hi).2
    have hkey : f (kk i - 1) = Real.exp (- S (kk i)) := by
      simp only [hf, Nat.sub_add_cancel hk1]
    rw [hkey]
    have hlog : Real.log (1 / t i) = - Real.log (t i) := by rw [one_div, Real.log_inv]
    have hb' : Real.log (t i) ≤ - S (kk i) + Real.log (1 + ε) := by
      have := hb i
      rw [hlog] at this
      linarith [hk2.2]
    have hexp2 : Real.exp (- S (kk i) + Real.log (1 + ε))
        = (1 + ε) * Real.exp (- S (kk i)) := by
      rw [Real.exp_add, hexp]; ring
    calc t i = Real.exp (Real.log (t i)) := (Real.exp_log (ht i)).symm
      _ ≤ Real.exp (- S (kk i) + Real.log (1 + ε)) := Real.exp_le_exp.mpr hb'
      _ = (1 + ε) * Real.exp (- S (kk i)) := hexp2
  have hinj_sub : Set.InjOn (fun i => kk i - 1) ↑I := by
    intro i hi i' hi' hEq
    change kk i - 1 = kk i' - 1 at hEq
    have h1 := (hkk i (Finset.mem_filter.mp hi).2).1
    have h2 := (hkk i' (Finset.mem_filter.mp hi').2).1
    have h3 : kk i = kk i' := by omega
    exact hkk_inj hi hi' h3
  have hsum_img : ∑ i ∈ I, f (kk i - 1) = ∑ k ∈ I.image (fun i => kk i - 1), f k :=
    (Finset.sum_image hinj_sub).symm
  have hstep : ∑ i ∈ I, (1 + ε) * f (kk i - 1)
      = (1 + ε) * ∑ k ∈ I.image (fun i => kk i - 1), f k := by
    conv_lhs => rw [← Finset.mul_sum]
    rw [hsum_img]
  have hfin : (∑ i, t i * (Alt.IntervalHit E (a i) (b i)).indicator (fun _ => (1 : ℝ)) ω)
      ≤ (1 + ε) * ∑ k ∈ I.image (fun i => kk i - 1), f k := by
    rw [hLHS]
    exact le_trans hbase (le_of_eq hstep)
  refine le_trans hfin ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  calc ∑ k ∈ I.image (fun i => kk i - 1), f k ≤ ∑' k, f k :=
        Summable.sum_le_tsum _ (fun k _ => hfpos k) hsumf
    _ = Alt.refSum (fun i => E i ω) := by simp only [hf, hS, Alt.refSum]

/-- **The pointwise coupling with the light-prime error.**  The weighted hit sum is at most
`(1+ε)` times the reference sum, plus the deterministic contribution `delta` of the light primes. -/
theorem hitSum_le_refSum_add_delta (A : BoundingSieve) {Z : ℕ} {K ε : ℝ} (hK : 0 ≤ K)
    (hZ2 : 2 ≤ Z) (hlin : IsLinearNat A Z K) (hε : 0 < ε) {Ω : Type*} (E : ℕ → Ω → ℝ) (ω : Ω)
    (hsum : Summable fun k : ℕ => Real.exp (-(Alt.partialSum (fun i => E i ω) (k + 1)))) :
    (∑ p : {p // p ∈ A.prodPrimes.primeFactors},
        levelLog Z p * (Alt.IntervalHit E (roomA A p) (roomB A p)).indicator
          (fun _ => (1 : ℝ)) ω)
      ≤ (1 + ε) * Alt.refSum (fun i => E i ω) + delta A Z K ε := by
  classical
  set hcond : {p // p ∈ A.prodPrimes.primeFactors} → Prop :=
    fun p => Real.exp (K / ε) ≤ ((p : ℕ) : ℝ) with hhcond
  set g : {p // p ∈ A.prodPrimes.primeFactors} → ℝ := fun p => levelLog Z p *
    (Alt.IntervalHit E (roomA A p) (roomB A p)).indicator (fun _ => (1 : ℝ)) ω with hg
  have hsplit : ∑ p, g p
      = ∑ p ∈ Finset.univ.filter hcond, g p
        + ∑ p ∈ Finset.univ.filter (fun p => ¬ hcond p), g p := by
    rw [Finset.sum_filter_add_sum_filter_not Finset.univ hcond g]
  rw [hsplit]
  have hheavy : ∑ p ∈ Finset.univ.filter hcond, g p
      ≤ (1 + ε) * Alt.refSum (fun i => E i ω) := by
    have hne : ∀ p q : {p // p ∈ A.prodPrimes.primeFactors}, p ≠ q →
        (p : ℕ) ≠ (q : ℕ) := fun p q h hpq => h (Subtype.ext hpq)
    have hcoup := hitSum_le_refSum (E := E)
      (t := fun p : ↥(Finset.univ.filter hcond) =>
        levelLog Z (((p : {p // p ∈ A.prodPrimes.primeFactors}) : ℕ)))
      (a := fun p : ↥(Finset.univ.filter hcond) =>
        roomA A (((p : {p // p ∈ A.prodPrimes.primeFactors}) : ℕ)))
      (b := fun p : ↥(Finset.univ.filter hcond) =>
        roomB A (((p : {p // p ∈ A.prodPrimes.primeFactors}) : ℕ)))
      (ht := fun p => levelLog_pos A hZ2 (p.1.2))
      (ha := fun p => roomA_nonneg A _)
      (hε := hε.le)
      (hb := fun p => le_trans (roomB_le_deadline A hK hZ2 hlin p.1.2)
        (deadline_le_heavy A hK hZ2 hε p.1.2 (Finset.mem_filter.mp p.2).2))
      (hdisj := fun p q hpq => by
        have hpq' : ((p.1 : {p // p ∈ A.prodPrimes.primeFactors}) : ℕ)
            ≠ ((q.1 : {p // p ∈ A.prodPrimes.primeFactors}) : ℕ) :=
          hne _ _ (fun h => hpq (Subtype.ext h))
        rcases lt_or_gt_of_ne hpq' with h | h
        · exact room_disjoint A p.1.2 q.1.2 h
        · exact (room_disjoint A q.1.2 p.1.2 h).symm)
      (ω := ω) (hsum := hsum)
    rw [Finset.sum_subtype (Finset.univ.filter hcond) (fun x => Iff.rfl) g]
    exact hcoup
  have hlight : ∑ p ∈ Finset.univ.filter (fun p => ¬ hcond p), g p ≤ delta A Z K ε := by
    have h1 : ∑ p ∈ Finset.univ.filter (fun p => ¬ hcond p), g p
        ≤ ∑ p ∈ Finset.univ.filter (fun p => ¬ hcond p), levelLog Z (p : ℕ) := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      have hlv : 0 ≤ levelLog Z (p : ℕ) := le_of_lt (levelLog_pos A hZ2 p.2)
      have hind : (Alt.IntervalHit E (roomA A p) (roomB A p)).indicator
          (fun _ => (1 : ℝ)) ω ≤ 1 := by
        rw [Set.indicator_apply]
        by_cases h : ω ∈ Alt.IntervalHit E (roomA A p) (roomB A p) <;> simp [h]
      simp only [hg]
      exact mul_le_of_le_one_right hlv hind
    refine le_trans h1 ?_
    rw [delta, Finset.sum_ite]
    simp only [Finset.sum_const_zero, zero_add, hhcond]
    exact le_rfl
  linarith








/-- The image of the subtype-finset of the primes of `S`. -/
lemma val_image_filter (S : Finset ℕ) (hS : S ⊆ A.prodPrimes.primeFactors) :
    (Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S)).image
      (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ)) = S := by
  ext p
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hp; exact ⟨⟨p, hS hp⟩, hp, rfl⟩

lemma sum_level_eq {Z : ℕ} (S : Finset ℕ) (hS : S ⊆ A.prodPrimes.primeFactors) :
    (∑ i ∈ Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S),
        levelLog Z (i : ℕ)) = ∑ p ∈ S, levelLog Z p := by
  have h := Finset.sum_image (f := fun p : ℕ => levelLog Z p)
    (g := fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ))
    (s := Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S))
    (fun x _ y _ h => Subtype.ext h)
  rw [val_image_filter (A := A) S hS] at h
  exact h.symm

lemma prod_nu_eq (S : Finset ℕ) (hS : S ⊆ A.prodPrimes.primeFactors) :
    (∏ i ∈ Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S),
        A.nu (i : ℕ))
      = ∏ p ∈ S, A.nu p := by
  have h := Finset.prod_image (f := fun p : ℕ => A.nu p)
    (g := fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ))
    (s := Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S))
    (fun x _ y _ (h : (x : ℕ) = (y : ℕ)) => Subtype.ext h)
  rw [val_image_filter (A := A) S hS] at h
  exact h.symm

lemma prod_exp_eq (S : Finset ℕ) (hS : S ⊆ A.prodPrimes.primeFactors) :
    (∏ i ∈ (Finset.univ : Finset {p // p ∈ A.prodPrimes.primeFactors}) \
        Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S),
        Real.exp (-(atomMass A (i : ℕ))))
      = ∏ p ∈ A.prodPrimes.primeFactors \ S, (1 - A.nu p) := by
  have hinj : Function.Injective (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ)) :=
    fun x y h => Subtype.ext h
  have huniv : (Finset.univ : Finset {p // p ∈ A.prodPrimes.primeFactors}).image
      (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ)) = A.prodPrimes.primeFactors := by
    rw [Finset.univ_eq_attach]
    exact Finset.attach_image_val
  have hsdiff : ((Finset.univ : Finset {p // p ∈ A.prodPrimes.primeFactors}) \
        Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S)).image
        (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ))
      = A.prodPrimes.primeFactors \ S := by
    rw [Finset.image_sdiff _ _ hinj, huniv, val_image_filter (A := A) S hS]
  rw [← hsdiff, Finset.prod_image]
  · refine Finset.prod_congr rfl (fun x hx => ?_)
    rw [exp_neg_atomMass A x.2]
  · intro x _ y _ h; exact Subtype.ext h


theorem measurableSet_intervalHit (E : ℕ → (ℕ → ℝ) → ℝ) (hE : ∀ i, Measurable (E i)) (a b : ℝ) :
    MeasurableSet (Alt.IntervalHit E a b) := by
  have h : Alt.IntervalHit E a b
      = ⋃ k : ℕ, (fun ω => Alt.partialSum (fun i => E i ω) k) ⁻¹' Set.Ioc a b := by
    ext ω; simp [Alt.IntervalHit]
  rw [h]
  exact MeasurableSet.iUnion fun k => measurableSet_Ioc.preimage (by
    exact Finset.measurable_sum _ (fun i _ => hE i))

lemma delta_nonneg (Z : ℕ) (K ε : ℝ) : 0 ≤ delta A Z K ε := by
  rw [delta]
  refine Finset.sum_nonneg (fun p _ => ?_)
  by_cases h : Real.exp (K / ε) ≤ ((p : ℕ) : ℝ) <;> simp [h, levelLog_nonneg]

lemma refSumLt_measurable (E : ℕ → (ℕ → ℝ) → ℝ) (hE : ∀ i, Measurable (E i)) (θ' : ℝ) :
    MeasurableSet (Alt.refSumLt E θ') := by
  have h1 : ∀ k, Measurable (fun x : ℕ → ℝ => Alt.partialSum (fun i => E i x) k) := fun k =>
    Finset.measurable_sum _ (fun i _ => hE i)
  have hmeas : Measurable (fun x : ℕ → ℝ => Alt.refSum (fun i => E i x)) :=
    Measurable.tsum (fun k => Real.measurable_exp.comp (h1 (k+1)).neg)
  exact measurableSet_lt hmeas measurable_const

lemma refSumLt_summand_measurable (E : ℕ → (ℕ → ℝ) → ℝ) (hE : ∀ i, Measurable (E i)) (θ : ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (t a b : ι → ℝ) :
    MeasurableSet {ω : ℕ → ℝ |
      (∑ i, t i * (Alt.IntervalHit E (a i) (b i)).indicator (fun _ => (1 : ℝ)) ω) < θ} := by
  refine measurableSet_lt ?_ measurable_const
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact measurable_const.mul
    (measurable_const.indicator (measurableSet_intervalHit E hE (a i) (b i)))


end Work.ChenPlan.LinearSieve.Selberg

namespace Work.ChenPlan.LinearSieve.Selberg

open Work.ChenPlan.LinearSieve.Selberg.Alt

variable {A : BoundingSieve}

/-! ## The canonical exponential space -/

open MeasureTheory

theorem coord_measurable (i : ℕ) : Measurable (fun x : ℕ → ℝ => x i) := measurable_pi_apply i

theorem coord_isStdExp (i : ℕ) : IsStdExp (fun x : ℕ → ℝ => x i) canonM := by
  intro c
  have hmap : canonM.map (fun x : ℕ → ℝ => x i) = expLaw := by
    rw [canonM]; exact Measure.infinitePi_map_eval (fun _ : ℕ => expLaw) i
  rw [show canonM {ω | (fun x : ℕ → ℝ => x i) ω ≤ c}
      = canonM ((fun x : ℕ → ℝ => x i) ⁻¹' Set.Iic c) from rfl]
  rw [← Measure.map_apply (measurable_pi_apply i) measurableSet_Iic, hmap]
  exact hasExpLaw_expLaw c

theorem coord_iIndep : ProbabilityTheory.iIndepFun (fun i (x : ℕ → ℝ) => x i) canonM := by
  rw [canonM]
  exact ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => expLaw)
    (X := fun i (x : ℝ) => x) (fun i => measurable_id)

theorem hae_summable :
    ∀ᵐ x ∂canonM, Summable fun k : ℕ => Real.exp (-(Alt.partialSum (fun i => x i) (k + 1))) := by
  filter_upwards [summable_cY_ae] with x hx
  have h2 : Summable fun k : ℕ => (fun j => Real.exp (-(cSum x j))) (k + 1) :=
    hx.comp_injective Nat.succ_injective
  simpa only [Alt.cSum_eq_partialSum] using h2

lemma filter_mem_image_val (T : Finset {p // p ∈ A.prodPrimes.primeFactors}) :
    Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} =>
      (x : ℕ) ∈ T.image (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ))) = T := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h : y = x := Subtype.ext hyx
    rwa [h] at hy
  · intro hx; exact ⟨x, hx, rfl⟩

open Finset MeasureTheory in
theorem gsum_bound_dense (K : ℝ) (hK : 0 ≤ K) :
    ∀ η : ℝ, 0 < η → ∃ D₀ : ℝ, ∀ (A : BoundingSieve) (Z : ℕ) (D : ℝ),
      2 ≤ Z → D₀ ≤ D → Work.ChenPlan.LinearSieve.IsLinearNat A Z K →
      1 ≤ Real.log D / Real.log Z → Real.log D / Real.log Z ≤ 2 →
      Real.log D / Real.log Z / (2 * Real.exp Real.eulerMascheroniConstant) - η
        ≤ Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) * Work.ChenPlan.LinearSieve.Vf A Z := by
  intro η hη
  set G : ℝ := Real.exp Real.eulerMascheroniConstant with hGdef
  have hGpos : 0 < G := by rw [hGdef]; exact Real.exp_pos _
  have hG1 : 1 ≤ G := by
    rw [hGdef]
    exact le_of_lt (Real.one_lt_exp_iff.mpr (by linarith [Real.one_half_lt_eulerMascheroniConstant]))
  have hG2 : G < 2 := by
    rw [hGdef]
    have h1 : Real.eulerMascheroniConstant < (2 : ℝ) / 3 := Real.eulerMascheroniConstant_lt_two_thirds
    have h2 : Real.exp Real.eulerMascheroniConstant ≤ Real.exp ((2 : ℝ) / 3) :=
      Real.exp_le_exp.mpr h1.le
    have h3 : Real.exp ((2 : ℝ) / 3) < 2 := by
      have h4 : Real.exp ((2 : ℝ) / 3) < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr (by linarith [Real.log_two_gt_d9])
      rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h4
    linarith
  set η₁ : ℝ := min η 1 with hη₁
  have hη₁pos : 0 < η₁ := lt_min hη one_pos
  have hη₁le : η₁ ≤ η := min_le_left _ _
  have hη₁1 : η₁ ≤ 1 := min_le_right _ _
  set ε : ℝ := η / (2 * G) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  refine ⟨Real.exp (8 * (heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ) / η₁ + 1), ?_⟩
  intro A Z D hZ2 hD hlin hs1 hs2
  have hZ1 : 1 < Z := by omega
  have hlogZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast hZ1)
  have hD₀pos : 0 < Real.exp (8 * (heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ) / η₁ + 1) :=
    Real.exp_pos _
  have hDpos : 0 < D := lt_of_lt_of_le hD₀pos hD
  have hsq : Real.sqrt D ≤ (Z : ℝ) := sqrt_le_of_log_div_le_two hDpos hZ1 hs2
  have hZP : ∀ p ∈ A.prodPrimes.primeFactors, p < Z := hlin.1
  -- the parameter `θ = log D / (2 log Z) ∈ (0,1]`
  have hlogDge : Real.log (Z : ℝ) ≤ Real.log D := (one_le_div hlogZ).mp hs1
  have hlogDpos : 0 < Real.log D := lt_of_lt_of_le hlogZ hlogDge
  set θ : ℝ := Real.log D / (2 * Real.log (Z : ℝ)) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one (by positivity : (0 : ℝ) < 2 * Real.log Z)]
    linarith [(div_le_iff₀ hlogZ).mp hs2]
  have hθhalf : 1 / 2 ≤ θ := by
    rw [hθdef, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log Z)]
    linarith
  -- the light-prime error
  have hdelta_le : delta A Z K ε ≤ η₁ / 4 := by
    refine le_trans (delta_le A hK hZ2 hεpos) ?_
    have h1 : 8 * ((heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ)) / η₁ + 1 ≤ Real.log D := by
      have h := Real.log_le_log hD₀pos hD
      rw [Real.log_exp] at h
      calc 8 * ((heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ)) / η₁ + 1
          = 8 * (heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ) / η₁ + 1 := by ring
        _ ≤ Real.log D := h
    have h2 : Real.log (Real.sqrt D) ≤ Real.log Z := Real.log_le_log (Real.sqrt_pos.mpr hDpos) hsq
    rw [Real.log_sqrt hDpos.le] at h2
    have h3 : 4 * ((heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ)) / η₁ ≤ Real.log Z := by
      rw [div_le_iff₀ hη₁pos]
      have h4 : 8 * ((heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ)) ≤ Real.log D * η₁ := by
        have h5 : 8 * ((heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ)) / η₁ ≤ Real.log D := by
          linarith
        exact (div_le_iff₀ hη₁pos).mp h5
      nlinarith [h4, h2, hlogZ, hη₁pos]
    have h4 : (heavyN K ε : ℝ) * Real.log (heavyN K ε : ℝ) ≤ (Real.log Z) * (η₁ / 4) := by
      have := (div_le_iff₀ hη₁pos).mp h3
      linarith
    rw [div_le_iff₀ hlogZ]
    linarith
  have hδlt : delta A Z K ε < θ := by
    linarith [hdelta_le, hθhalf, hη₁1]
  set θ' : ℝ := (θ - delta A Z K ε) / (1 + ε) with hθ'def
  have hθ'pos : 0 < θ' := by
    rw [hθ'def]; exact div_pos (by linarith) (by positivity)
  have hθ'1 : θ' ≤ 1 := by
    rw [hθ'def, div_le_one (by positivity : (0 : ℝ) < 1 + ε)]
    linarith [hθ1, delta_nonneg (A := A) Z K ε]
  -- the rooms
  let a : {p // p ∈ A.prodPrimes.primeFactors} → ℝ := fun p => roomA A p
  let b : {p // p ∈ A.prodPrimes.primeFactors} → ℝ := fun p => roomB A p
  have hbma : ∀ i : {p // p ∈ A.prodPrimes.primeFactors}, b i - a i = atomMass A (i : ℕ) :=
    fun i => roomB_sub_roomA A (i : ℕ)
  have ha : ∀ i, 0 ≤ a i := fun i => roomA_nonneg A (i : ℕ)
  have hab : ∀ i, a i ≤ b i := fun i => by
    have := atomMass_pos A i.2
    simp only [a, b, roomB]
    linarith
  have hdisj : ∀ i j : {p // p ∈ A.prodPrimes.primeFactors}, i ≠ j →
      Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne (fun h => hij (Subtype.ext h)) with h | h
    · exact room_disjoint A i.2 j.2 h
    · exact (room_disjoint A j.2 i.2 h).symm
  -- the up-set probabilities
  have hup : ∀ U : Finset {p // p ∈ A.prodPrimes.primeFactors},
      ENNReal.toReal (canonM (⋂ i ∈ U, Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i)))
        = ∏ i ∈ U, (1 - Real.exp (-(b i - a i))) := fun U =>
    hit_all_prob canonM (fun i (x : ℕ → ℝ) => x i)
      (fun i => (coord_measurable i).aemeasurable) (fun i => coord_isStdExp i) coord_iIndep
      a b ha hab hdisj U
  -- the CDF identity
  have hcdf := Work.LinearSieve.Selberg.selectionMass_eq_measure (μ := canonM)
    (H := fun i : {p // p ∈ A.prodPrimes.primeFactors} =>
      Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i))
    (fun i => measurableSet_intervalHit _ coord_measurable (a i) (b i))
    (fun i : {p // p ∈ A.prodPrimes.primeFactors} => Real.exp (-(b i - a i))) hup
    (fun i : {p // p ∈ A.prodPrimes.primeFactors} => levelLog Z (i : ℕ)) θ
  -- the identification with `Vf * gSum`
  have hkey : Work.ChenPlan.LinearSieve.Vf A Z * Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D)
      = ENNReal.toReal (canonM {ω | (∑ i : {p // p ∈ A.prodPrimes.primeFactors},
          levelLog Z (i : ℕ) * (Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i)).indicator
            (fun _ => (1 : ℝ)) ω) < θ}) := by
    rw [Vf_mul_gSum_sqrt_eq_thetaSum A hDpos rfl hZ1 hZP, hcdf]
    refine Finset.sum_bij (fun (S : Finset ℕ) (_ : S ∈ A.prodPrimes.primeFactors.powerset.filter
        (fun S => (∑ p ∈ S, levelLog Z p) < θ)) =>
        Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S))
      ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_filter] at hS ⊢
      refine ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
      rw [sum_level_eq (A := A) S (Finset.mem_powerset.mp hS.1)]
      exact hS.2
    · intro S hS S' hS' h
      have h1 : (Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} =>
          (x : ℕ) ∈ S)).image (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ)) = S :=
        val_image_filter (A := A) S (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
      have h2 : (Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} =>
          (x : ℕ) ∈ S')).image (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ)) = S' :=
        val_image_filter (A := A) S' (Finset.mem_powerset.mp (Finset.mem_filter.mp hS').1)
      rw [← h1, h, h2]
    · intro T hT
      rw [Finset.mem_filter] at hT
      refine ⟨T.image (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ)), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_powerset.mpr (Finset.image_subset_iff.mpr (fun x _ => x.2)), ?_⟩
        rw [← sum_level_eq (A := A) _ (Finset.image_subset_iff.mpr (fun x _ => x.2))]
        · rw [filter_mem_image_val (A := A) T]
          exact hT.2
      · exact filter_mem_image_val (A := A) T
    · intro S hS
      rw [Finset.mem_filter] at hS
      obtain ⟨hSpow, hSθ⟩ := hS
      have hsub : S ⊆ A.prodPrimes.primeFactors := Finset.mem_powerset.mp hSpow
      show (∏ p ∈ S, A.nu p) * ∏ p ∈ A.prodPrimes.primeFactors \ S, (1 - A.nu p)
        = (∏ i ∈ Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} =>
              (x : ℕ) ∈ S), (1 - Real.exp (-(b i - a i))))
          * ∏ i ∈ (Finset.univ : Finset {p // p ∈ A.prodPrimes.primeFactors}) \
              Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S),
              Real.exp (-(b i - a i))
      have h1 : (∏ i ∈ Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} =>
            (x : ℕ) ∈ S), (1 - Real.exp (-(b i - a i))))
          = ∏ p ∈ S, A.nu p := by
        rw [← prod_nu_eq (A := A) S hsub]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [hbma i, one_sub_exp_neg_atomMass A i.2]
      have h2 : (∏ i ∈ (Finset.univ : Finset {p // p ∈ A.prodPrimes.primeFactors}) \
            Finset.univ.filter (fun x : {p // p ∈ A.prodPrimes.primeFactors} => (x : ℕ) ∈ S),
            Real.exp (-(b i - a i)))
          = ∏ p ∈ A.prodPrimes.primeFactors \ S, (1 - A.nu p) := by
        simp only [hbma]
        exact prod_exp_eq (A := A) S hsub
      rw [h1, h2]
  -- the coupling and the reference CDF
  have hle : ENNReal.toReal (canonM (Alt.refSumLt (fun i (x : ℕ → ℝ) => x i) θ'))
      ≤ ENNReal.toReal (canonM {ω | (∑ i : {p // p ∈ A.prodPrimes.primeFactors},
          levelLog Z (i : ℕ) * (Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i)).indicator
            (fun _ => (1 : ℝ)) ω) < θ}) := by
    set t : Set (ℕ → ℝ) := {ω | (∑ i : {p // p ∈ A.prodPrimes.primeFactors},
        levelLog Z (i : ℕ) * (Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i)).indicator
          (fun _ => (1 : ℝ)) ω) < θ} with htdef
    set s : Set (ℕ → ℝ) := Alt.refSumLt (fun i (x : ℕ → ℝ) => x i) θ' with hsdef
    have ht : MeasurableSet t := by
      rw [htdef]
      exact refSumLt_summand_measurable _ coord_measurable θ _ a b
    have hae_sub : ∀ᵐ ω ∂canonM, ω ∈ s → ω ∈ t := by
      filter_upwards [hae_summable] with ω hsum hlt
      have hpt := hitSum_le_refSum_add_delta A hK hZ2 hlin hεpos
        (fun i (x : ℕ → ℝ) => x i) ω hsum
      have hlt' : Alt.refSum (fun i => ω i) < θ' := hlt
      have h3 : (1 + ε) * Alt.refSum (fun i => ω i) + delta A Z K ε < θ := by
        have h2 : (1 + ε) * ((θ - delta A Z K ε) / (1 + ε)) + delta A Z K ε = θ := by
          field_simp
          ring
        rw [hθ'def] at hlt'
        linarith [mul_lt_mul_of_pos_left hlt' (by linarith : (0 : ℝ) < 1 + ε)]
      exact lt_of_le_of_lt hpt h3
    have hnull : canonM (s \ t) = 0 := by
      refine measure_mono_null ?_ (by rw [← ae_iff]; exact hae_sub)
      intro ω hω
      simp only [Set.mem_diff, Set.mem_setOf_eq] at hω ⊢
      exact fun h => hω.2 (h hω.1)
    have hmono : canonM s ≤ canonM t := by
      have hsplit := MeasureTheory.measure_inter_add_diff (μ := canonM) s ht
      calc canonM s = canonM (s ∩ t) + canonM (s \ t) := hsplit.symm
        _ = canonM (s ∩ t) + 0 := by rw [hnull]
        _ = canonM (s ∩ t) := by rw [add_zero]
        _ ≤ canonM t := measure_mono (μ := canonM) Set.inter_subset_right
    exact ENNReal.toReal_mono (measure_ne_top canonM t) hmono
  have href : ENNReal.toReal (canonM (Alt.refSumLt (fun i (x : ℕ → ℝ) => x i) θ'))
      = θ' / G := by
    rw [refsum_cdf canonM (fun i (x : ℕ → ℝ) => x i)
      (fun i => (coord_measurable i).aemeasurable) (fun i => coord_isStdExp i) coord_iIndep
      hθ'pos hθ'1, hGdef]
  -- the arithmetic
  have harith : θ / G - η ≤ θ' / G := by
    have hGε : G * ε = η / 2 := by rw [hεdef]; field_simp
    have hnum : ε * θ + delta A Z K ε ≤ η * G * (1 + ε) := by
      have h1 : ε * θ ≤ ε := by nlinarith [hθ1, hεpos]
      have h2 : delta A Z K ε ≤ η / 4 := le_trans hdelta_le (by linarith)
      have h3 : η * G * (1 + ε) = η * G + η ^ 2 / 2 := by nlinarith [hGε]
      have h4 : η / 4 + ε ≤ η * G + η ^ 2 / 2 := by
        have hεb : ε ≤ η / 2 := by
          rw [hεdef, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * G)]
          nlinarith [hG1, hη]
        nlinarith [hεb, hG1, hη, sq_nonneg η]
      linarith
    rw [hθ'def]
    rw [show (θ - delta A Z K ε) / (1 + ε) / G
        = (θ - delta A Z K ε) / (G * (1 + ε)) from by field_simp]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < G * (1 + ε))]
    have hsub : (θ / G - η) * (G * (1 + ε)) = θ * (1 + ε) - η * G * (1 + ε) := by
      field_simp
    rw [hsub]
    nlinarith [hnum]
  have hθG : θ / G = Real.log D / Real.log Z / (2 * Real.exp Real.eulerMascheroniConstant) := by
    simp only [hθdef, hGdef]
    field_simp
  rw [← hθG]
  calc θ / G - η ≤ θ' / G := harith
    _ = ENNReal.toReal (canonM (Alt.refSumLt (fun i (x : ℕ → ℝ) => x i) θ')) := href.symm
    _ ≤ ENNReal.toReal (canonM {ω | (∑ i : {p // p ∈ A.prodPrimes.primeFactors},
          levelLog Z (i : ℕ) * (Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i)).indicator
            (fun _ => (1 : ℝ)) ω) < θ}) := hle
    _ = Work.ChenPlan.LinearSieve.Vf A Z * Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) :=
        hkey.symm
    _ = Work.ChenPlan.LinearSieve.gSum A (Real.sqrt D) * Work.ChenPlan.LinearSieve.Vf A Z := by ring

end Work.ChenPlan.LinearSieve.Selberg
