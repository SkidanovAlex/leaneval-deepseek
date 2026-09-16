import Mathlib
import Submission.KernelSum
import Submission.KernelFun
import Submission.KernelLimitK
import Submission.KernelLimitFamily
import Submission.CrudeKernelCoord
import Submission.Lemma41K
import Submission.Commons.NumberTheory.Moebius.sum_pairwise_divisors_moebius_lcm_cpow

open scoped BigOperators Topology
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# The pairwise (`k`-coordinate) kernel of Lemma 4.1

Polymath8a's Lemma 4.1 is applied in the sieve to the divisor sum (36), whose
index tuples are restricted by *two* conditions: coordinatewise coprimality
`([d_j,d'_j], WN) = 1` and — coming from the `S`-counting of §4.1 — the
*pairwise* coprimality of the lcm moduli `[d_i,d'_i] ⊥ [d_j,d'_j]` (`i ≠ j`).
The Euler product of the corresponding local factors
`K_p = 1 + Σ_j (−p^{−1−a_j} − p^{−1−b_j} + p^{−1−a_j−b_j})` is exactly
`coordLocalK p a b` (P8 (39)), whose P8 (41) pole asymptotic (uniformly for a
family of moduli) is `KernelLimitFamily.kernel_pole_asymptotic_family_eps`.

This module sets up the `k`-coordinate pairwise objects and proves that the
pairwise divisor sum (with the two coprimality constraints) is the Euler-product
kernel:

  * `kernelWeightK`, `PairwiseCoprimeK`, `pairKernelWeight`, `pairKernelSum`
    (the ℕ-level pairwise divisor sum) and `pairKernel` (the Euler-product limit);
  * `summable_pairKernelWeight` — absolute summability;
  * `exists_mem_piFinset_divisors_primorial` — the exhaustion of the nonzero
    locus by the primorial chains `∏_{p ∈ Sfilter q n} p`;
  * `exists_tendsto_coordKprod` — convergence of `∏_{p ∈ Sfilter q n} coordLocalK p a b`;
  * `pairKernelSum_eq_pairKernel` — the bridge `pairwise sum = Euler product`.

All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-! ## The `k`-coordinate pairwise weight -/

/-- The `k`-coordinate kernel weight: the product over the coordinates of the
one-coordinate Möbius/lcm weights `μ(d)μ(d′)/[d,d′]·d^{−a}·d′^{−b}`. -/
noncomputable def kernelWeightK {k : ℕ} (a b : Fin k → ℂ) (x : Fin k → ℕ × ℕ) : ℂ :=
  ∏ j : Fin k, kernelWeight (a j) (b j) (x j)

/-- Pairwise coprimality of the lcm moduli of a tuple. -/
abbrev PairwiseCoprimeK {k : ℕ} (x : Fin k → ℕ × ℕ) : Prop :=
  ∀ i j : Fin k, i ≠ j → ((x i).1.lcm (x i).2).Coprime ((x j).1.lcm (x j).2)

/-- The pairwise kernel weight: the `k`-coordinate weight, restricted to tuples
whose lcm moduli are pairwise coprime and each coprime to `q`. -/
noncomputable def pairKernelWeight (q : ℕ) {k : ℕ} (a b : Fin k → ℂ)
    (x : Fin k → ℕ × ℕ) : ℂ :=
  if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
    kernelWeightK a b x
  else 0

/-- The ℕ-level pairwise divisor sum (P8 (36) with the pairwise restriction). -/
noncomputable def pairKernelSum (q : ℕ) {k : ℕ} (a b : Fin k → ℂ) : ℂ :=
  ∑' x : Fin k → ℕ × ℕ, pairKernelWeight q a b x

/-- The pairwise Euler-product kernel `∏_{p ∤ q} K_p`, realized as the limit of
the finite products. -/
noncomputable def pairKernel (q : ℕ) {k : ℕ} (a b : Fin k → ℂ) : ℂ :=
  (atTop : Filter ℕ).limUnder fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalK p a b

/-! ## Vanishing outside the coprime squarefree locus -/

/-- One coordinate's kernel weight vanishes unless the pair is nonzero
squarefree. -/
lemma kernelWeight_eq_zero_of_not {a b : ℂ} (ha : a.re ≠ 0) (hb : b.re ≠ 0)
    {x : ℕ × ℕ} (h : ¬ (x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ Squarefree x.1 ∧ Squarefree x.2)) :
    kernelWeight a b x = 0 := by
  have h1 : kernelWeight a b x = kernelWeightQ 1 a b x := by
    rw [kernelWeightQ, if_pos (Nat.coprime_one_right _)]
  rw [h1]
  exact kernelWeightQ_eq_zero_of_not ha hb fun hc => h ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩

/-- The `k`-coordinate weight vanishes as soon as one coordinate is not a pair
of nonzero squarefree numbers. -/
lemma kernelWeightK_eq_zero_of_not {k : ℕ} {a b : Fin k → ℂ}
    (ha : ∀ j, (a j).re ≠ 0) (hb : ∀ j, (b j).re ≠ 0) {x : Fin k → ℕ × ℕ}
    (h : ¬ ∀ j : Fin k, ((x j).1 ≠ 0 ∧ (x j).2 ≠ 0 ∧ Squarefree (x j).1 ∧
      Squarefree (x j).2)) :
    kernelWeightK a b x = 0 := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ j)
    (kernelWeight_eq_zero_of_not (ha j) (hb j) fun hc => hj ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩)

/-- The pairwise kernel weight vanishes outside the pairwise-coprime squarefree
locus. -/
lemma pairKernelWeight_eq_zero_of_not {q k : ℕ} {a b : Fin k → ℂ}
    (ha : ∀ j, (a j).re ≠ 0) (hb : ∀ j, (b j).re ≠ 0) {x : Fin k → ℕ × ℕ}
    (h : ¬ ((∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x ∧
      ∀ j : Fin k, ((x j).1 ≠ 0 ∧ (x j).2 ≠ 0 ∧ Squarefree (x j).1 ∧
        Squarefree (x j).2))) :
    pairKernelWeight q a b x = 0 := by
  rw [pairKernelWeight]
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · rw [if_pos hg]
    exact kernelWeightK_eq_zero_of_not ha hb (fun hk => h ⟨hg.1, hg.2, hk⟩)
  · rw [if_neg hg]

/-- In particular the pairwise weight vanishes at a tuple with a zero entry. -/
lemma pairKernelWeight_eq_zero_of_zero {q k : ℕ} {a b : Fin k → ℂ}
    (ha : ∀ j, (a j).re ≠ 0) (hb : ∀ j, (b j).re ≠ 0) {x : Fin k → ℕ × ℕ}
    (h : ¬ ∀ j : Fin k, ((x j).1 ≠ 0 ∧ (x j).2 ≠ 0)) :
    pairKernelWeight q a b x = 0 := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp h
  rw [pairKernelWeight]
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · rw [if_pos hg]
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      (kernelWeight_eq_zero_of_not (ha j) (hb j) fun hc => hj ⟨hc.1, hc.2.1⟩)
  · rw [if_neg hg]

/-! ## Absolute summability -/

/-- The one-coordinate Möbius/lcm kernel weight is absolutely summable. -/
theorem summable_norm_kernelWeight {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Summable (fun x : ℕ × ℕ => ‖kernelWeight a b x‖) := by
  have hbase := Commons.NumberTheory.Zeta.summable_lcm_inv_cpow ha hb
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => norm_kernelWeight_le a b x) hbase

/-- **Absolute summability of the pairwise kernel weight.** -/
theorem summable_pairKernelWeight (q : ℕ) {k : ℕ} {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) :
    Summable (fun x : Fin k → ℕ × ℕ => ‖pairKernelWeight q a b x‖) := by
  have hsingle : ∀ j : Fin k, Summable fun x : ℕ × ℕ => ‖kernelWeight (a j) (b j) x‖ :=
    fun j => summable_norm_kernelWeight (ha j) (hb j)
  have hprod : Summable (fun x : Fin k → ℕ × ℕ =>
      ‖∏ j : Fin k, kernelWeight (a j) (b j) (x j)‖) :=
    summable_norm_prod_pi k (fun j (x : ℕ × ℕ) => kernelWeight (a j) (b j) x) hsingle
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hprod
  rw [pairKernelWeight, kernelWeightK]
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · rw [if_pos hg]
  · rw [if_neg hg]
    simpa using Finset.prod_nonneg (fun j (_ : j ∈ Finset.univ) => norm_nonneg (kernelWeight (a j) (b j) (x j)))

/-! ## Exhaustion of the nonzero locus by the primorial chains -/

/-- The primorial chain is increasing (divisibility form). -/
lemma primorial_dvd_primorial {q n n' : ℕ} (h : n ≤ n') : primorial q n ∣ primorial q n' := by
  rw [primorial, primorial]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Sfilter_mono q h)

/-- **Exhaustion.**  Every tuple all of whose coordinates are pairs of nonzero
squarefree numbers with lcm coprime to `q` lies among the tuples of divisors of
a sufficiently large primorial. -/
lemma exists_mem_piFinset_divisors_primorial {q k : ℕ} (S : Finset (Fin k → ℕ × ℕ))
    (hS : ∀ x ∈ S, ∀ j : Fin k, (x j).1 ≠ 0 ∧ (x j).2 ≠ 0 ∧ Squarefree (x j).1 ∧
      Squarefree (x j).2 ∧ ((x j).1.lcm (x j).2).Coprime q) :
    ∃ n : ℕ, ∀ x ∈ S, x ∈ Fintype.piFinset
      (fun _ : Fin k => Nat.divisors (primorial q n) ×ˢ Nat.divisors (primorial q n)) := by
  classical
  choose nf hnf using fun j : Fin k => exists_mem_divisors_primorial
    (S.image (fun x : Fin k → ℕ × ℕ => x j)) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨(hS x hx j).1, (hS x hx j).2.1, (hS x hx j).2.2.1, (hS x hx j).2.2.2.1,
        (hS x hx j).2.2.2.2⟩)
  refine ⟨Finset.univ.sup nf, fun x hx => ?_⟩
  rw [Fintype.mem_piFinset]
  intro j
  have hj : nf j ≤ Finset.univ.sup nf := Finset.le_sup (Finset.mem_univ j)
  have hdvd : primorial q (nf j) ∣ primorial q (Finset.univ.sup nf) :=
    primorial_dvd_primorial hj
  have hsub : Nat.divisors (primorial q (nf j)) ⊆ Nat.divisors (primorial q (Finset.univ.sup nf)) :=
    Nat.divisors_subset_of_dvd (primorial_ne_zero q _) hdvd
  have hmem := hnf j (x j) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [Finset.mem_product] at hmem ⊢
  exact ⟨hsub hmem.1, hsub hmem.2⟩

/-! ## Convergence of the `coordLocalK` Euler product -/

/-- **Convergence of the `k`-coordinate kernel product.**  For `q ≠ 0` and
weights `a_j, b_j` with positive real parts, the Euler product
`∏_{p ∤ q} K_p` of the local factors of P8 (39) converges. -/
theorem exists_tendsto_coordKprod (k : ℕ) (q : ℕ) (hq : q ≠ 0) {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) :
    ∃ L : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalK p a b) atTop (𝓝 L) := by
  classical
  obtain ⟨C, hC0, hCbound⟩ := exists_coordK_ratio_bound k
  set Zf : Fin k → ℂ := fun j => zetaWN q (1 + a j + b j) /
    (zetaWN q (1 + a j) * zetaWN q (1 + b j)) with hZf
  have hratio : ∃ M : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n,
      coordLocalK p a b / ∏ j : Fin k, locR p (a j) (b j)) atTop (𝓝 M) := by
    obtain ⟨M, hM⟩ := exists_tendsto_prod_one_add_filter q (C := C) hC0.le
      (fun p hp2 => by
        simpa using hCbound p hp2 a b (fun j => (ha j).le) (fun j => (hb j).le))
    exact ⟨M, hM.congr' (by
      filter_upwards with n
      refine Finset.prod_congr rfl (fun p _ => ?_)
      ring)⟩
  obtain ⟨M, hM⟩ := hratio
  have hRlim : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n,
      ∏ j : Fin k, locR p (a j) (b j)) atTop (𝓝 (∏ j : Fin k, Zf j)) := by
    have hcomm : (fun n : ℕ => ∏ p ∈ Sfilter q n, ∏ j : Fin k, locR p (a j) (b j)) =
        fun n : ℕ => ∏ j : Fin k, ∏ p ∈ Sfilter q n, locR p (a j) (b j) := by
      funext n
      exact Finset.prod_comm
    rw [hcomm]
    refine tendsto_finset_prod_of _ (fun j _ => ?_)
    have hR := eulerRatioZetaWN q hq (ha j) (hb j)
    have h1 : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, locR p (a j) (b j)) atTop
        (𝓝 (zetaWN q (1 + a j + b j) /
          (zetaWN q (1 + a j) * zetaWN q (1 + b j)))) := by
      refine hR.congr' ?_
      filter_upwards with n
      refine Finset.prod_congr rfl (fun p _ => ?_)
      rw [locR, div_eq_mul_inv]
    rw [hZf]
    exact h1
  refine ⟨(∏ j : Fin k, Zf j) * M, ?_⟩
  have hEq : (fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalK p a b) =
      fun n : ℕ => (∏ p ∈ Sfilter q n, ∏ j : Fin k, locR p (a j) (b j)) *
        (∏ p ∈ Sfilter q n, coordLocalK p a b / ∏ j : Fin k, locR p (a j) (b j)) := by
    funext n
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp2 : 2 ≤ p := two_le_of_mem_Sfilter hp
    have hRnz : (∏ j : Fin k, locR p (a j) (b j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => by
        intro hz
        have h := locR_norm_ge_sixth (a j) (b j) hp2 (ha j).le (hb j).le
        rw [hz] at h
        norm_num at h)
    field_simp [hRnz]
  rw [hEq]
  exact hRlim.mul hM

/-- The defining convergence of `pairKernel`. -/
theorem tendsto_pairKernel (q : ℕ) (hq : q ≠ 0) {k : ℕ} {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) :
    Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalK p a b) atTop (𝓝 (pairKernel q a b)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_coordKprod k q hq ha hb
  have h1 : pairKernel q a b = L := hL.limUnder_eq
  rw [h1]
  exact hL

/-- The pointwise value of `pairKernel` at any point where the Euler product
converges. -/
theorem pairKernel_eq_of_tendsto {q k : ℕ} {a b : Fin k → ℂ} {L : ℂ}
    (h : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalK p a b) atTop (𝓝 L)) :
    pairKernel q a b = L := h.limUnder_eq

/-- **Transfer of the crude bound to the pairwise kernel.** -/
theorem norm_pairKernel_le {q k : ℕ} (hq : q ≠ 0) {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) {C : ℝ}
    (hC : ∀ n : ℕ, ‖∏ p ∈ Sfilter q n, coordLocalK p a b‖ ≤ C) :
    ‖pairKernel q a b‖ ≤ C := by
  have hclosed : IsClosed {z : ℂ | ‖z‖ ≤ C} := isClosed_le continuous_norm continuous_const
  exact hclosed.mem_of_tendsto (tendsto_pairKernel q hq ha hb) (Eventually.of_forall hC)


/-! ## The finite Euler factorization and the bridge to the Euler product -/

/-- **Finite Euler factorization of the pairwise kernel weight.**  Over the
divisors of a primorial the pairwise-restricted weight factorizes into the Euler
product of the local factors `coordLocalK`. -/
theorem sum_pairKernelWeight_piFinset (q n : ℕ) {k : ℕ} (a b : Fin k → ℂ) :
    (∑ x ∈ Fintype.piFinset
        (fun _ : Fin k => (Nat.divisors (primorial q n)) ×ˢ (Nat.divisors (primorial q n))),
        pairKernelWeight q a b x) = ∏ p ∈ Sfilter q n, coordLocalK p a b := by
  classical
  set D := Nat.divisors (primorial q n) with hD
  have hguard : ∀ x ∈ Fintype.piFinset (fun _ : Fin k => D ×ˢ D),
      (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) := by
    intro x hx j
    rw [Fintype.mem_piFinset] at hx
    exact coprime_lcm_divisors_primorial (Finset.mem_product.mp (hx j)).1
      (Finset.mem_product.mp (hx j)).2
  have hstep : ∀ x ∈ Fintype.piFinset (fun _ : Fin k => D ×ˢ D),
      pairKernelWeight q a b x = if PairwiseCoprimeK x then kernelWeightK a b x else 0 := by
    intro x hx
    rw [pairKernelWeight]
    by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
    · rw [if_pos hg, if_pos hg.2]
    · rw [if_neg hg]
      rw [if_neg]
      exact fun h => hg ⟨hguard x hx, h⟩
  rw [Finset.sum_congr rfl hstep]
  rw [show (∑ x ∈ Fintype.piFinset (fun _ : Fin k => D ×ˢ D),
        (if PairwiseCoprimeK x then kernelWeightK a b x else 0)) =
      ∑ x ∈ (Fintype.piFinset (fun _ : Fin k => D ×ˢ D)).filter PairwiseCoprimeK,
        kernelWeightK a b x from (Finset.sum_filter _ _).symm]
  have hL40 := Commons.NumberTheory.Moebius.sum_pairwise_divisors_moebius_lcm_cpow
    (primorial q n) (squarefree_primorial q n) k a b
  have hfun : ∀ x ∈ (Fintype.piFinset (fun _ : Fin k => D ×ˢ D)).filter PairwiseCoprimeK,
      kernelWeightK a b x = ∏ j : Fin k,
        (((ArithmeticFunction.moebius (x j).1 : ℤ) : ℂ) *
          ((ArithmeticFunction.moebius (x j).2 : ℤ) : ℂ) *
          (((Nat.lcm (x j).1 (x j).2 : ℕ) : ℂ))⁻¹ * ((x j).1 : ℂ) ^ (-(a j)) *
          ((x j).2 : ℂ) ^ (-(b j))) := by
    intro x hx
    rw [kernelWeightK]
    exact Finset.prod_congr rfl (fun j _ => by rw [kernelWeight])
  rw [Finset.sum_congr rfl hfun, hL40, primeFactors_primorial]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [coordLocalK_eq p (Nat.prime_of_mem_primesBelow
    (Finset.mem_of_mem_filter p hp)).ne_zero a b]

/-- **The pairwise kernel weight is summable with the Euler-product limit.** -/
theorem hasSum_pairKernelWeight (q : ℕ) (hq : q ≠ 0) {k : ℕ} {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) :
    ∃ L : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalK p a b) atTop (𝓝 L) ∧
      HasSum (pairKernelWeight q a b) L := by
  classical
  obtain ⟨L, hL⟩ := exists_tendsto_coordKprod k q hq ha hb
  refine ⟨L, hL, ?_⟩
  refine hasSum_of_tendsto_finset_mono
    (u := fun n => Fintype.piFinset
      (fun _ : Fin k => (Nat.divisors (primorial q n)) ×ˢ
        (Nat.divisors (primorial q n))))
    ?_ ?_ (summable_pairKernelWeight q ha hb) ?_
  · refine monotone_nat_of_le_succ (fun n => ?_)
    have hdvd : primorial q n ∣ primorial q (n + 1) := primorial_dvd_primorial (Nat.le_succ n)
    have hsub : Nat.divisors (primorial q n) ⊆ Nat.divisors (primorial q (n + 1)) :=
      Nat.divisors_subset_of_dvd (primorial_ne_zero q (n + 1)) hdvd
    intro x hx
    rw [Fintype.mem_piFinset] at hx ⊢
    exact fun j => Finset.product_subset_product hsub hsub (hx j)
  · intro S
    obtain ⟨n, hn⟩ := exists_mem_piFinset_divisors_primorial
      (S.filter (fun x => ∀ j : Fin k, (x j).1 ≠ 0 ∧ (x j).2 ≠ 0 ∧ Squarefree (x j).1 ∧
        Squarefree (x j).2 ∧ ((x j).1.lcm (x j).2).Coprime q))
      (fun x hx => (Finset.mem_filter.mp hx).2)
    refine ⟨n, fun x hx => ?_⟩
    by_cases hgood : (∀ j : Fin k, (x j).1 ≠ 0 ∧ (x j).2 ≠ 0 ∧ Squarefree (x j).1 ∧
        Squarefree (x j).2 ∧ ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
    · exact Or.inl (hn x (Finset.mem_filter.mpr ⟨hx, hgood.1⟩))
    · refine Or.inr ?_
      refine pairKernelWeight_eq_zero_of_not (fun j => (ha j).ne') (fun j => (hb j).ne') ?_
      intro hc
      exact hgood ⟨fun j => ⟨(hc.2.2 j).1, (hc.2.2 j).2.1, (hc.2.2 j).2.2.1,
        (hc.2.2 j).2.2.2, hc.1 j⟩, hc.2.1⟩
  · refine hL.congr' (Eventually.of_forall (fun n => ?_))
    exact (sum_pairKernelWeight_piFinset q n a b).symm

/-- **The pairwise divisor sum is the pairwise kernel.** -/
theorem pairKernelSum_eq_pairKernel (q : ℕ) (hq : q ≠ 0) {k : ℕ} {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) :
    pairKernelSum q a b = pairKernel q a b := by
  obtain ⟨L, hL, hsum⟩ := hasSum_pairKernelWeight q hq ha hb
  rw [pairKernelSum, hsum.tsum_eq]
  exact (pairKernel_eq_of_tendsto hL).symm

end Commons.NumberTheory.MaynardSieve
