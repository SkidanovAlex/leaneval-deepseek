import Mathlib
import Submission.PairwiseKernel
import Submission.Commons.NumberTheory.Zeta.summable_totient_lcm_cpow
import Submission.Commons.NumberTheory.Moebius.sum_divisors_moebius_totient_lcm_cpow
import Submission.Commons.NumberTheory.Moebius.sum_pairwise_divisors_moebius_totient_lcm_cpow



open scoped BigOperators Topology
open Filter MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# The `φ`-denominator (`S₂`) kernel of Lemma 4.1

Polymath8a Lemma 4.1 ("The same claim holds if the denominators `[d_j,d'_j]` are
replaced by `φ([d_j,d'_j])`") is what the *prime* (θ-weighted) sums of Theorem
3.5 consume: the main term of `S₂ = Σ_{d,e} ∏ᵢ αᵢβᵢ · S̃` is governed by the
divisor sum

    `Σ_{d,e (pairwise good, coprime to q)} ∏_j μ(d_j)μ(d′_j)/φ([d_j,d′_j])
        · d_j^{−a_j} d′_j^{−b_j}`,

whose per-prime local factor is `1 + Σ_j (−x_j z − y_j z + x_j y_j z)` with
`z = 1/φ(p) = 1/(p−1)` (instead of `z = 1/p`):

    `K^φ_p = 1 + Σ_j (−p^{−a_j}/(p−1) − p^{−b_j}/(p−1) + p^{−a_j−b_j}/(p−1))`.

This module mirrors `Submission.PairwiseKernel` for that weight:
  * `coordLocalKPhi`, `kernelWeightPhi`, `kernelWeightKPhi`,
    `pairKernelWeightPhi`, `pairKernelSumPhi`, `pairKernelPhi`;
  * the finite Euler factorization (`sum_pairKernelWeightPhi_piFinset`) from the
    fleet lemma `sum_pairwise_divisors_moebius_totient_lcm_cpow`;
  * absolute summability (`summable_pairKernelWeightPhi`);
  * convergence of the Euler product (`exists_tendsto_coordKPhiProd`,
    `tendsto_pairKernelPhi`) by comparison with the plain `locR` reference;
  * the bridge `pairKernelSumPhi_eq_pairKernelPhi`.

The *comparison* `pairKernelPhi = pairKernel·(1+O(1/w))` on the sieve's modulus
families, and the resulting φ-Lemma 4.1, are in `Submission.PhiLemma41`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-! ## The `φ`-denominator local factor and weights -/

/-- The `φ`-denominator local Euler factor: `coordLocal` at the weights
`x_{jp} = p^{−a_j}`, `y_{jp} = p^{−b_j}` and the `1/φ(p)` denominator weight
`z = (p−1)^{−1}`. -/
noncomputable def coordLocalKPhi {k : ℕ} (p : ℕ) (a b : Fin k → ℂ) : ℂ :=
  coordLocal (R := ℂ) (ι := ℕ) (fun j _ => (p : ℂ) ^ (-(a j)))
    (fun j _ => (p : ℂ) ^ (-(b j))) (fun _ _ => (((p - 1 : ℕ) : ℂ))⁻¹) p

/-- The local factor in standard form:
`K^φ_p = 1 + Σ_j (−p^{−a_j}/(p−1) − p^{−b_j}/(p−1) + p^{−a_j−b_j}/(p−1))`. -/
lemma coordLocalKPhi_eq {k : ℕ} (p : ℕ) (hp : p ≠ 0) (a b : Fin k → ℂ) :
    coordLocalKPhi p a b =
      1 + ∑ j : Fin k, (-((p : ℂ) ^ (-(a j)) * (((p - 1 : ℕ) : ℂ))⁻¹) -
        ((p : ℂ) ^ (-(b j)) * (((p - 1 : ℕ) : ℂ))⁻¹) +
        ((p : ℂ) ^ (-(a j + b j)) * (((p - 1 : ℕ) : ℂ))⁻¹)) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  unfold coordLocalKPhi coordLocal
  dsimp only
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hab : (p : ℂ) ^ (-(a j)) * (p : ℂ) ^ (-(b j)) = (p : ℂ) ^ (-(a j + b j)) := by
    rw [← Complex.cpow_add _ _ hp0]
    congr 1; ring
  rw [hab]
  ring

/-- The one-coordinate `φ`-denominator kernel weight
`μ(d)μ(d′)·φ([d,d′])^{−1}·d^{−a}·d′^{−b}`. -/
noncomputable def kernelWeightPhi (a b : ℂ) (x : ℕ × ℕ) : ℂ :=
  ((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) * ((ArithmeticFunction.moebius x.2 : ℤ) : ℂ) *
    ((((Nat.lcm x.1 x.2).totient : ℕ) : ℂ))⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b)

/-- The `k`-coordinate `φ`-denominator kernel weight. -/
noncomputable def kernelWeightKPhi {k : ℕ} (a b : Fin k → ℂ) (x : Fin k → ℕ × ℕ) : ℂ :=
  ∏ j : Fin k, kernelWeightPhi (a j) (b j) (x j)

/-- The pairwise `φ`-denominator kernel weight (guarded by the coprimality
conditions of P8 (36)). -/
noncomputable def pairKernelWeightPhi (q : ℕ) {k : ℕ} (a b : Fin k → ℂ)
    (x : Fin k → ℕ × ℕ) : ℂ :=
  if (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x then
    kernelWeightKPhi a b x
  else 0

/-- The ℕ-level pairwise `φ`-denominator divisor sum. -/
noncomputable def pairKernelSumPhi (q : ℕ) {k : ℕ} (a b : Fin k → ℂ) : ℂ :=
  ∑' x : Fin k → ℕ × ℕ, pairKernelWeightPhi q a b x

/-- The `φ`-denominator Euler-product kernel `∏_{p ∤ q} K^φ_p`, realized as the
limit of the finite products. -/
noncomputable def pairKernelPhi (q : ℕ) {k : ℕ} (a b : Fin k → ℂ) : ℂ :=
  (atTop : Filter ℕ).limUnder fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalKPhi p a b

/-! ## Vanishing outside the coprime squarefree locus -/

/-- One coordinate's `φ`-weight vanishes unless the pair is nonzero and
squarefree. -/
lemma kernelWeightPhi_eq_zero_of_not {a b : ℂ} {x : ℕ × ℕ}
    (h : ¬ (x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ Squarefree x.1 ∧ Squarefree x.2)) :
    kernelWeightPhi a b x = 0 := by
  rw [kernelWeightPhi]
  by_cases h1 : x.1 = 0
  · have hμ : ((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) = 0 := by
      simp [h1]
    rw [hμ]; ring
  · by_cases h2 : x.2 = 0
    · have hμ : ((ArithmeticFunction.moebius x.2 : ℤ) : ℂ) = 0 := by
        simp [h2]
      rw [hμ]; ring
    · by_cases h3 : Squarefree x.1
      · by_cases h4 : Squarefree x.2
        · exact absurd ⟨h1, h2, h3, h4⟩ h
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

/-- The `k`-coordinate `φ`-weight vanishes as soon as one coordinate is not a
pair of nonzero squarefree numbers. -/
lemma kernelWeightKPhi_eq_zero_of_not {k : ℕ} {a b : Fin k → ℂ}
    {x : Fin k → ℕ × ℕ}
    (h : ¬ ∀ j : Fin k, ((x j).1 ≠ 0 ∧ (x j).2 ≠ 0 ∧ Squarefree (x j).1 ∧
      Squarefree (x j).2)) :
    kernelWeightKPhi a b x = 0 := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ j)
    (kernelWeightPhi_eq_zero_of_not fun hc => hj ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩)

/-- The pairwise `φ`-weight vanishes outside the pairwise-coprime squarefree
locus. -/
lemma pairKernelWeightPhi_eq_zero_of_not {q k : ℕ} {a b : Fin k → ℂ}
    {x : Fin k → ℕ × ℕ}
    (h : ¬ ((∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x ∧
      ∀ j : Fin k, ((x j).1 ≠ 0 ∧ (x j).2 ≠ 0 ∧ Squarefree (x j).1 ∧
        Squarefree (x j).2))) :
    pairKernelWeightPhi q a b x = 0 := by
  rw [pairKernelWeightPhi]
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · rw [if_pos hg]
    exact kernelWeightKPhi_eq_zero_of_not (fun hk => h ⟨hg.1, hg.2, hk⟩)
  · rw [if_neg hg]

/-! ## The finite Euler factorization -/

/-- **Finite Euler factorization of the `φ`-denominator pairwise weight.** -/
theorem sum_pairKernelWeightPhi_piFinset (q n : ℕ) {k : ℕ} (a b : Fin k → ℂ) :
    (∑ x ∈ Fintype.piFinset
        (fun _ : Fin k => (Nat.divisors (primorial q n)) ×ˢ (Nat.divisors (primorial q n))),
        pairKernelWeightPhi q a b x) = ∏ p ∈ Sfilter q n, coordLocalKPhi p a b := by
  classical
  set D := Nat.divisors (primorial q n) with hD
  have hguard : ∀ x ∈ Fintype.piFinset (fun _ : Fin k => D ×ˢ D),
      (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) := by
    intro x hx j
    rw [Fintype.mem_piFinset] at hx
    exact coprime_lcm_divisors_primorial (Finset.mem_product.mp (hx j)).1
      (Finset.mem_product.mp (hx j)).2
  have hstep : ∀ x ∈ Fintype.piFinset (fun _ : Fin k => D ×ˢ D),
      pairKernelWeightPhi q a b x = if PairwiseCoprimeK x then kernelWeightKPhi a b x else 0 := by
    intro x hx
    rw [pairKernelWeightPhi]
    by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
    · rw [if_pos hg, if_pos hg.2]
    · rw [if_neg hg]
      rw [if_neg]
      exact fun h => hg ⟨hguard x hx, h⟩
  rw [Finset.sum_congr rfl hstep]
  rw [show (∑ x ∈ Fintype.piFinset (fun _ : Fin k => D ×ˢ D),
        (if PairwiseCoprimeK x then kernelWeightKPhi a b x else 0)) =
      ∑ x ∈ (Fintype.piFinset (fun _ : Fin k => D ×ˢ D)).filter PairwiseCoprimeK,
        kernelWeightKPhi a b x from (Finset.sum_filter _ _).symm]
  have hL55 := Commons.NumberTheory.Moebius.sum_pairwise_divisors_moebius_totient_lcm_cpow
    (primorial q n) (squarefree_primorial q n) k a b
  have hfun : ∀ x ∈ (Fintype.piFinset (fun _ : Fin k => D ×ˢ D)).filter PairwiseCoprimeK,
      kernelWeightKPhi a b x = ∏ j : Fin k,
        (((ArithmeticFunction.moebius (x j).1 : ℤ) : ℂ) *
          ((ArithmeticFunction.moebius (x j).2 : ℤ) : ℂ) *
          (((Nat.lcm (x j).1 (x j).2).totient : ℂ))⁻¹ * ((x j).1 : ℂ) ^ (-(a j)) *
          ((x j).2 : ℂ) ^ (-(b j))) := by
    intro x hx
    rw [kernelWeightKPhi]
    exact Finset.prod_congr rfl (fun j _ => by rw [kernelWeightPhi])
  rw [Finset.sum_congr rfl hfun, hL55, primeFactors_primorial]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  rw [coordLocalKPhi_eq p (Nat.prime_of_mem_primesBelow
    (Finset.mem_of_mem_filter p hp)).ne_zero a b]


/-! ## Absolute summability -/

/-- The norm of the `φ`-weight is at most the μ-free totient kernel. -/
lemma norm_kernelWeightPhi_le (a b : ℂ) (x : ℕ × ℕ) :
    ‖kernelWeightPhi a b x‖ ≤
      ‖((((Nat.lcm x.1 x.2).totient : ℕ)) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b)‖ := by
  have hfac : kernelWeightPhi a b x =
      ((((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) *
        ((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)) *
        (((((Nat.lcm x.1 x.2).totient : ℕ)) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b))) := by
    rw [kernelWeightPhi]; ring
  rw [hfac, norm_mul]
  have h1 := norm_moebius_intCast_complex_le_one x.1
  have h2 := norm_moebius_intCast_complex_le_one x.2
  calc ‖((ArithmeticFunction.moebius x.1 : ℤ) : ℂ) *
        ((ArithmeticFunction.moebius x.2 : ℤ) : ℂ)‖ *
        ‖((((Nat.lcm x.1 x.2).totient : ℕ)) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b)‖
      ≤ (1 * 1) * ‖((((Nat.lcm x.1 x.2).totient : ℕ)) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) *
          (x.2 : ℂ) ^ (-b)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = ‖((((Nat.lcm x.1 x.2).totient : ℕ)) : ℂ)⁻¹ * (x.1 : ℂ) ^ (-a) * (x.2 : ℂ) ^ (-b)‖ := by
        ring

/-- The one-coordinate `φ`-weight is absolutely summable. -/
theorem summable_norm_kernelWeightPhi {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Summable (fun x : ℕ × ℕ => ‖kernelWeightPhi a b x‖) := by
  have hbase := Commons.NumberTheory.Zeta.summable_totient_lcm_cpow ha hb
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _)
    (fun x => norm_kernelWeightPhi_le a b x) hbase

/-- **Absolute summability of the pairwise `φ`-weight.** -/
theorem summable_pairKernelWeightPhi (q : ℕ) {k : ℕ} {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) :
    Summable (fun x : Fin k → ℕ × ℕ => ‖pairKernelWeightPhi q a b x‖) := by
  have hsingle : ∀ j : Fin k, Summable fun x : ℕ × ℕ => ‖kernelWeightPhi (a j) (b j) x‖ :=
    fun j => summable_norm_kernelWeightPhi (ha j) (hb j)
  have hprod : Summable (fun x : Fin k → ℕ × ℕ =>
      ‖∏ j : Fin k, kernelWeightPhi (a j) (b j) (x j)‖) :=
    summable_norm_prod_pi k (fun j (x : ℕ × ℕ) => kernelWeightPhi (a j) (b j) x) hsingle
  refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hprod
  rw [pairKernelWeightPhi, kernelWeightKPhi]
  by_cases hg : (∀ j : Fin k, ((x j).1.lcm (x j).2).Coprime q) ∧ PairwiseCoprimeK x
  · rw [if_pos hg]
  · rw [if_neg hg]
    simpa using Finset.prod_nonneg (fun j (_ : j ∈ Finset.univ) =>
      norm_nonneg (kernelWeightPhi (a j) (b j) (x j)))

/-! ## Convergence of the `φ`-denominator Euler product -/

/-- Lower bound for the product of `k` reference factors, `p ≥ 2`. -/
lemma prod_locR_norm_ge (k : ℕ) (p : ℕ) (hp2 : 2 ≤ p) (a b : Fin k → ℂ)
    (ha : ∀ j, 0 ≤ (a j).re) (hb : ∀ j, 0 ≤ (b j).re) :
    (1 / 6 : ℝ) ^ k ≤ ‖∏ j : Fin k, locR p (a j) (b j)‖ := by
  rw [norm_prod]
  calc (1 / 6 : ℝ) ^ k = ∏ _j : Fin k, (1 / 6 : ℝ) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ j : Fin k, ‖locR p (a j) (b j)‖ :=
        Finset.prod_le_prod₀ (fun j _ => by norm_num) (fun j _ => locR_norm_ge_sixth (a j) (b j) hp2 (ha j) (hb j))

/-- **Difference of the `φ`-local factor and the plain local factor**:
`K^φ_p − K_p = −(Σ_j (p^{−a_j} + p^{−b_j} − p^{−a_j−b_j}))/(p(p−1))`. -/
lemma coordLocalKPhi_sub_coordLocalK {k : ℕ} (p : ℕ) (hp2 : 2 ≤ p) (a b : Fin k → ℂ) :
    coordLocalKPhi p a b - coordLocalK p a b =
      -(∑ j : Fin k, ((p : ℂ) ^ (-(a j)) + (p : ℂ) ^ (-(b j)) -
          (p : ℂ) ^ (-(a j + b j)))) / ((p : ℂ) * ((p : ℂ) - 1)) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hcast : (((p - 1 : ℕ)) : ℂ) = (p : ℂ) - 1 := by
    have h1 : 1 ≤ p := by omega
    push_cast [Nat.cast_sub h1]
    ring
  rw [coordLocalKPhi_eq p (by omega : p ≠ 0) a b, coordLocalK_eq p (by omega : p ≠ 0) a b,
    hcast]
  simp only [add_sub_add_left_eq_sub]
  rw [← Finset.sum_sub_distrib, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h1 : (p : ℂ) ^ (-(a j)) * (p : ℂ) ^ (-1 : ℂ) = (p : ℂ) ^ (-(1 + a j)) := by
    rw [← Complex.cpow_add _ _ hp0]; congr 1; ring
  have h2 : (p : ℂ) ^ (-(b j)) * (p : ℂ) ^ (-1 : ℂ) = (p : ℂ) ^ (-(1 + b j)) := by
    rw [← Complex.cpow_add _ _ hp0]; congr 1; ring
  have h3 : (p : ℂ) ^ (-(a j)) * (p : ℂ) ^ (-(b j)) = (p : ℂ) ^ (-(a j + b j)) := by
    rw [← Complex.cpow_add _ _ hp0]; congr 1; ring
  have h4 : (p : ℂ) ^ (-(a j + b j)) * (p : ℂ) ^ (-1 : ℂ) =
      (p : ℂ) ^ (-(1 + a j + b j)) := by
    rw [← Complex.cpow_add _ _ hp0]; congr 1; ring
  rw [← h1, ← h2, ← h4, ← h3, Complex.cpow_neg_one]
  field_simp
  ring

/-- Norm bound for the difference of the local factors. -/
lemma norm_coordLocalKPhi_sub_coordLocalK_le {k : ℕ} (p : ℕ) (hp2 : 2 ≤ p)
    (a b : Fin k → ℂ) (ha : ∀ j, 0 ≤ (a j).re) (hb : ∀ j, 0 ≤ (b j).re) :
    ‖coordLocalKPhi p a b - coordLocalK p a b‖ ≤ 3 * k / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hnorm_cpow : ∀ j : Fin k, ‖(p : ℂ) ^ (-(a j))‖ ≤ 1 := by
    intro j
    have h := Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos (n := p) (by omega : 0 < p)
      (w := -(a j)) (z := (0 : ℂ)) (by simp; linarith [ha j])
    simpa using h
  have hnorm_cpow' : ∀ j : Fin k, ‖(p : ℂ) ^ (-(b j))‖ ≤ 1 := by
    intro j
    have h := Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos (n := p) (by omega : 0 < p)
      (w := -(b j)) (z := (0 : ℂ)) (by simp; linarith [hb j])
    simpa using h
  have hnorm_cpow'' : ∀ j : Fin k, ‖(p : ℂ) ^ (-(a j + b j))‖ ≤ 1 := by
    intro j
    have h := Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos (n := p) (by omega : 0 < p)
      (w := -(a j + b j)) (z := (0 : ℂ)) (by simp; linarith [ha j, hb j])
    simpa using h
  have hσ : ‖∑ j : Fin k, ((p : ℂ) ^ (-(a j)) + (p : ℂ) ^ (-(b j)) -
      (p : ℂ) ^ (-(a j + b j)))‖ ≤ 3 * k := by
    calc ‖∑ j : Fin k, ((p : ℂ) ^ (-(a j)) + (p : ℂ) ^ (-(b j)) - (p : ℂ) ^ (-(a j + b j)))‖
        ≤ ∑ j : Fin k, ‖(p : ℂ) ^ (-(a j)) + (p : ℂ) ^ (-(b j)) -
            (p : ℂ) ^ (-(a j + b j))‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin k, (3 : ℝ) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have h1 : ‖(p : ℂ) ^ (-(a j)) + (p : ℂ) ^ (-(b j))‖ ≤ 2 := by
            have := norm_add_le ((p : ℂ) ^ (-(a j))) ((p : ℂ) ^ (-(b j)))
            linarith [hnorm_cpow j, hnorm_cpow' j]
          have h2 := norm_sub_le ((p : ℂ) ^ (-(a j)) + (p : ℂ) ^ (-(b j)))
            ((p : ℂ) ^ (-(a j + b j)))
          linarith [hnorm_cpow'' j]
      _ = 3 * k := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hden : ‖(p : ℂ) * ((p : ℂ) - 1)‖ = (p : ℝ) * ((p : ℝ) - 1) := by
    have hcast : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by
      have h1 : 1 ≤ p := by omega
      push_cast [Nat.cast_sub h1]
      ring
    rw [← hcast, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  rw [coordLocalKPhi_sub_coordLocalK p hp2 a b, norm_div, norm_neg, hden]
  have hpos : 0 < (p : ℝ) * ((p : ℝ) - 1) := by
    have h2 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    positivity
  rw [div_le_div_iff₀ hpos hpos]
  calc ‖∑ j : Fin k, ((p : ℂ) ^ (-(a j)) + (p : ℂ) ^ (-(b j)) - (p : ℂ) ^ (-(a j + b j)))‖ *
        ((p : ℝ) * ((p : ℝ) - 1))
      ≤ (3 * (k : ℝ)) * ((p : ℝ) * ((p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_right hσ hpos.le
    _ = 3 * (k : ℝ) * ((p : ℝ) * ((p : ℝ) - 1)) := by ring
    _ ≤ 3 * (k : ℝ) * ((p : ℝ) * ((p : ℝ) - 1)) := le_rfl

/-- **Convergence of the `φ`-denominator kernel product.**  The `φ`-Euler
product is obtained from the plain one by the factor `∏(K^φ_p/K_p)`, whose local
factors differ by `O(p⁻²)`. -/
theorem exists_tendsto_coordKPhiProd (k : ℕ) (q : ℕ) (hq : q ≠ 0) {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) :
    ∃ L : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalKPhi p a b) atTop (𝓝 L) := by
  classical
  obtain ⟨C0, hC0pos, hC0⟩ := Commons.NumberTheory.Zeta.exists_norm_coordK_div_prod_locR_sub_one_le k
  set C : ℝ := 2 * C0 + 6 * (k : ℝ) * (6 : ℝ) ^ k + 1 with hCdef
  have hCnonneg : 0 ≤ C := by positivity
  have hz : ∀ p : ℕ, 2 ≤ p →
      ‖coordLocalKPhi p a b / (∏ j : Fin k, locR p (a j) (b j)) - 1‖ ≤ C / (p : ℝ) ^ 2 := by
    intro p hp2
    have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hpp1 : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    have hsq : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    -- the plain comparison
    have hplain := hC0 p hp2 a b (fun j => (ha j).le) (fun j => (hb j).le)
    have h1 : ‖coordLocalK p a b / (∏ j : Fin k, locR p (a j) (b j)) - 1‖ ≤ C0 / (p : ℝ) ^ 2 := by
      have hK : coordLocalK p a b = 1 + ∑ j : Fin k, (-((p : ℂ) ^ (-(1 + a j))) -
          ((p : ℂ) ^ (-(1 + b j))) + ((p : ℂ) ^ (-(1 + a j + b j)))) :=
        coordLocalK_eq p (by omega : p ≠ 0) a b
      rw [hK]
      exact hplain
    -- the difference of the local factors, divided by the reference product
    have hRge := prod_locR_norm_ge k p hp2 a b (fun j => (ha j).le) (fun j => (hb j).le)
    have hRpos : 0 < ‖∏ j : Fin k, locR p (a j) (b j)‖ := by
      have h6 : (0 : ℝ) < (1 / 6 : ℝ) ^ k := by positivity
      linarith
    have hRinv : ‖(∏ j : Fin k, locR p (a j) (b j))‖⁻¹ ≤ 6 ^ k := by
      have h6 : ((1 / 6 : ℝ) ^ k)⁻¹ = 6 ^ k := by rw [one_div, inv_pow, inv_inv]
      calc ‖(∏ j : Fin k, locR p (a j) (b j))‖⁻¹ ≤ (((1 / 6 : ℝ) ^ k))⁻¹ :=
            (inv_le_inv₀ hRpos (by positivity)).mpr hRge
        _ = 6 ^ k := h6
    have h2 : ‖coordLocalKPhi p a b / (∏ j : Fin k, locR p (a j) (b j)) -
        coordLocalK p a b / (∏ j : Fin k, locR p (a j) (b j))‖ ≤
        6 * (k : ℝ) * (6 : ℝ) ^ k / (p : ℝ) ^ 2 := by
      have heq : coordLocalKPhi p a b / (∏ j : Fin k, locR p (a j) (b j)) -
          coordLocalK p a b / (∏ j : Fin k, locR p (a j) (b j)) =
          (coordLocalKPhi p a b - coordLocalK p a b) /
            (∏ j : Fin k, locR p (a j) (b j)) := by ring
      rw [heq, norm_div]
      have hb1 := norm_coordLocalKPhi_sub_coordLocalK_le p hp2 a b
        (fun j => (ha j).le) (fun j => (hb j).le)
      have hstep1 : ‖coordLocalKPhi p a b - coordLocalK p a b‖ *
            ‖(∏ j : Fin k, locR p (a j) (b j))‖⁻¹ ≤
            (3 * (k : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) * 6 ^ k :=
        mul_le_mul hb1 hRinv (by positivity) (by positivity)
      have hbig := norm_coordLocalKPhi_sub_coordLocalK_le p hp2 a b
        (fun j => (ha j).le) (fun j => (hb j).le)
      have hstep2 : (3 * (k : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) * 6 ^ k ≤
          6 * (k : ℝ) * (6 : ℝ) ^ k / (p : ℝ) ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hpp1 hsq]
        calc 3 * (k : ℝ) * 6 ^ k * (p : ℝ) ^ 2
            ≤ 3 * (k : ℝ) * 6 ^ k * (2 * ((p : ℝ) * ((p : ℝ) - 1))) := by
              have h2 : (p : ℝ) ^ 2 ≤ 2 * ((p : ℝ) * ((p : ℝ) - 1)) := by nlinarith
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 6 * (k : ℝ) * (6 : ℝ) ^ k * ((p : ℝ) * ((p : ℝ) - 1)) := by ring
      exact hstep1.trans hstep2
    -- combine
    have hsum : ‖coordLocalKPhi p a b / (∏ j : Fin k, locR p (a j) (b j)) - 1‖ ≤
        (C0 + 6 * (k : ℝ) * (6 : ℝ) ^ k) / (p : ℝ) ^ 2 := by
      calc ‖coordLocalKPhi p a b / (∏ j : Fin k, locR p (a j) (b j)) - 1‖
          = ‖(coordLocalKPhi p a b / (∏ j : Fin k, locR p (a j) (b j)) -
              coordLocalK p a b / (∏ j : Fin k, locR p (a j) (b j))) +
              (coordLocalK p a b / (∏ j : Fin k, locR p (a j) (b j)) - 1)‖ := by
              congr 1; ring
        _ ≤ ‖coordLocalKPhi p a b / (∏ j : Fin k, locR p (a j) (b j)) -
              coordLocalK p a b / (∏ j : Fin k, locR p (a j) (b j))‖ +
              ‖coordLocalK p a b / (∏ j : Fin k, locR p (a j) (b j)) - 1‖ := norm_add_le _ _
        _ ≤ 6 * (k : ℝ) * (6 : ℝ) ^ k / (p : ℝ) ^ 2 + C0 / (p : ℝ) ^ 2 := add_le_add h2 h1
        _ = (C0 + 6 * (k : ℝ) * (6 : ℝ) ^ k) / (p : ℝ) ^ 2 := by ring
    have hle : C0 + 6 * (k : ℝ) * (6 : ℝ) ^ k ≤ C := by
      rw [hCdef]
      linarith [hC0pos.le]
    exact hsum.trans (div_le_div_of_nonneg_right hle hsq.le)
  -- the ratio product converges
  obtain ⟨M, hM⟩ := exists_tendsto_prod_one_add_filter q hCnonneg hz
  have hratio : ∃ M : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n,
      coordLocalKPhi p a b / ∏ j : Fin k, locR p (a j) (b j)) atTop (𝓝 M) := by
    refine ⟨M, hM.congr' (Eventually.of_forall (fun n => ?_))⟩
    refine Finset.prod_congr rfl (fun p _ => ?_)
    ring
  obtain ⟨M, hM⟩ := hratio
  set Zf : Fin k → ℂ := fun j => zetaWN q (1 + a j + b j) /
    (zetaWN q (1 + a j) * zetaWN q (1 + b j)) with hZf
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
  have hEq : (fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalKPhi p a b) =
      fun n : ℕ => (∏ p ∈ Sfilter q n, ∏ j : Fin k, locR p (a j) (b j)) *
        (∏ p ∈ Sfilter q n, coordLocalKPhi p a b / ∏ j : Fin k, locR p (a j) (b j)) := by
    funext n
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp2 : 2 ≤ p := two_le_of_mem_Sfilter hp
    have hRnz : (∏ j : Fin k, locR p (a j) (b j)) ≠ 0 := by
      intro hz0
      have h := prod_locR_norm_ge k p hp2 a b (fun j => (ha j).le) (fun j => (hb j).le)
      rw [hz0] at h
      simp only [norm_zero] at h
      have h6 : (0 : ℝ) < (6 : ℝ) ^ k := pow_pos (by norm_num) k
      have : (0 : ℝ) < (1 / 6 : ℝ) ^ k := by positivity
      linarith
    field_simp [hRnz]
  rw [hEq]
  exact hRlim.mul hM

/-- The defining convergence of `pairKernelPhi`. -/
theorem tendsto_pairKernelPhi (q : ℕ) (hq : q ≠ 0) {k : ℕ} {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) :
    Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalKPhi p a b) atTop
      (𝓝 (pairKernelPhi q a b)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_coordKPhiProd k q hq ha hb
  have h1 : pairKernelPhi q a b = L := hL.limUnder_eq
  rw [h1]
  exact hL

/-- The pointwise value of `pairKernelPhi` at any point where the Euler product
converges. -/
theorem pairKernelPhi_eq_of_tendsto {q k : ℕ} {a b : Fin k → ℂ} {L : ℂ}
    (h : Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalKPhi p a b) atTop (𝓝 L)) :
    pairKernelPhi q a b = L := h.limUnder_eq

/-- Transfer of a uniform bound to the `φ`-kernel. -/
theorem norm_pairKernelPhi_le {q k : ℕ} (hq : q ≠ 0) {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) {C : ℝ}
    (hC : ∀ n : ℕ, ‖∏ p ∈ Sfilter q n, coordLocalKPhi p a b‖ ≤ C) :
    ‖pairKernelPhi q a b‖ ≤ C := by
  have hclosed : IsClosed {z : ℂ | ‖z‖ ≤ C} := isClosed_le continuous_norm continuous_const
  exact hclosed.mem_of_tendsto (tendsto_pairKernelPhi q hq ha hb) (Eventually.of_forall hC)

/-! ## The bridge to the ℕ-level divisor sum -/

/-- **The pairwise `φ`-weight is summable with the Euler-product limit.** -/
theorem hasSum_pairKernelWeightPhi (q : ℕ) (hq : q ≠ 0) {k : ℕ} {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) :
    ∃ L : ℂ, Tendsto (fun n : ℕ => ∏ p ∈ Sfilter q n, coordLocalKPhi p a b) atTop (𝓝 L) ∧
      HasSum (pairKernelWeightPhi q a b) L := by
  classical
  obtain ⟨L, hL⟩ := exists_tendsto_coordKPhiProd k q hq ha hb
  refine ⟨L, hL, ?_⟩
  refine hasSum_of_tendsto_finset_mono
    (u := fun n => Fintype.piFinset
      (fun _ : Fin k => (Nat.divisors (primorial q n)) ×ˢ
        (Nat.divisors (primorial q n))))
    ?_ ?_ (summable_pairKernelWeightPhi q ha hb) ?_
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
      refine pairKernelWeightPhi_eq_zero_of_not ?_
      intro hc
      exact hgood ⟨fun j => ⟨(hc.2.2 j).1, (hc.2.2 j).2.1, (hc.2.2 j).2.2.1,
        (hc.2.2 j).2.2.2, hc.1 j⟩, hc.2.1⟩
  · refine hL.congr' (Eventually.of_forall (fun n => ?_))
    exact (sum_pairKernelWeightPhi_piFinset q n a b).symm

/-- **The pairwise `φ`-divisor sum is the `φ`-kernel.** -/
theorem pairKernelSumPhi_eq_pairKernelPhi (q : ℕ) (hq : q ≠ 0) {k : ℕ} {a b : Fin k → ℂ}
    (ha : ∀ j, 0 < (a j).re) (hb : ∀ j, 0 < (b j).re) :
    pairKernelSumPhi q a b = pairKernelPhi q a b := by
  obtain ⟨L, hL, hsum⟩ := hasSum_pairKernelWeightPhi q hq ha hb
  rw [pairKernelSumPhi, hsum.tsum_eq]
  exact (pairKernelPhi_eq_of_tendsto hL).symm

end Commons.NumberTheory.MaynardSieve
