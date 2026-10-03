import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Commons.Analysis.Walsh.exists_khintchine_le_of_two_le

namespace Commons.Analysis.Walsh

open Finset

/-!
# Rademacher–Hilbert even moment inequality

For a finite family of vectors `x i` in a complex Hilbert space, the `2m`-th moment of the
Rademacher sum `∑ i ε_i x i` is bounded by `(K m)^m (∑ i ‖x i‖^2)^m` uniformly in the number
of vectors.  The proof reduces the vector-valued even moment to the scalar Khintchine
inequality by expanding both moments over the Rademacher "even patterns"; each term of the
vector expansion is dominated termwise by the corresponding scalar term through
`|Re ⟨x i, x j⟩| ≤ ‖x i‖ ‖x j‖`.
-/

/-- The real Rademacher sign attached to the bit `e i`. -/
private def sg {n : ℕ} (e : Fin n → Bool) (i : Fin n) : ℝ := if e i then 1 else -1

private lemma sg_cast {n : ℕ} (e : Fin n → Bool) (i : Fin n) :
    ((sg e i : ℝ) : ℂ) = (if e i then (1 : ℂ) else -1) := by
  rw [sg]; by_cases h : e i <;> simp [h]

/-- `0 ≤ ∑_{b : Bool} (if b then 1 else -1)^c`; the sum equals `0` or `2`. -/
private lemma sum_bool_sgn_pow_nonneg (c : ℕ) :
    0 ≤ ∑ b : Bool, (if b then (1 : ℝ) else -1) ^ c := by
  have h : (∑ b : Bool, (if b then (1 : ℝ) else -1) ^ c) = 1 + (-1 : ℝ) ^ c := by
    rw [Fintype.sum_bool]; simp
  rw [h]
  rcases Nat.even_or_odd c with hc | hc
  · rw [hc.neg_one_pow]; norm_num
  · rw [hc.neg_one_pow]; norm_num

/-- The sum over all sign vectors of a product of Rademacher coordinates is nonnegative.
Indeed it equals `∏_j (1 + (-1)^{c_j})`, where `c_j` is the number of times `j` occurs. -/
private lemma sgn_prod_sum_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (k : ι → Fin n) :
    0 ≤ ∑ e : Fin n → Bool, ∏ a, sg e (k a) := by
  classical
  have hfib2 : ∀ e : Fin n → Bool,
      (∏ a, sg e (k a))
        = ∏ j : Fin n, (sg e j) ^ ((Finset.univ.filter (fun a : ι => k a = j)).card) := by
    intro e
    rw [← Finset.prod_fiberwise (s := (Finset.univ : Finset ι)) (g := k)
      (f := fun a => sg e (k a))]
    apply Finset.prod_congr rfl
    intro j _
    rw [show (∏ a ∈ (Finset.univ.filter (fun a : ι => k a = j)), sg e (k a))
        = ∏ a ∈ (Finset.univ.filter (fun a : ι => k a = j)), sg e j by
      apply Finset.prod_congr rfl; intro a ha
      rw [Finset.mem_filter] at ha; rw [ha.2]]
    rw [Finset.prod_const]
  simp_rw [hfib2]
  have hsum : (∑ e : Fin n → Bool,
        ∏ j : Fin n, (sg e j) ^ ((Finset.univ.filter (fun a : ι => k a = j)).card))
      = ∏ j : Fin n, ∑ b : Bool,
          (if b then (1 : ℝ) else -1) ^ ((Finset.univ.filter (fun a : ι => k a = j)).card) := by
    have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset Bool))
      (g := fun (j : Fin n) (b : Bool) => (if b then (1 : ℝ) else -1)
        ^ ((Finset.univ.filter (fun a : ι => k a = j)).card))
    rw [Fintype.piFinset_univ] at h
    simpa only [sg] using h
  rw [hsum]
  apply Finset.prod_nonneg
  intro j _
  exact sum_bool_sgn_pow_nonneg _

/-- **Expansion of an even moment in the Rademacher even patterns.** For any real coefficient
family `g`, the sum over the sign cube of the `m`-th power of `∑_a ε_{a.1} ε_{a.2} g a`
equals the sum over `m`-tuples of pairs of the product of the coefficients times the sign
average `∑_e ∏_l ε_{p_l.1} ε_{p_l.2}`. -/
private lemma moment_expansion (m n : ℕ) (g : Fin n × Fin n → ℝ) :
    (∑ e : Fin n → Bool, (∑ a : Fin n × Fin n, sg e a.1 * sg e a.2 * g a) ^ m)
      = ∑ p : Fin m → Fin n × Fin n,
          (∏ l : Fin m, g (p l))
            * (∑ e : Fin n → Bool, ∏ l : Fin m, sg e (p l).1 * sg e (p l).2) := by
  classical
  have h1 : ∀ e : Fin n → Bool,
      (∑ a : Fin n × Fin n, sg e a.1 * sg e a.2 * g a) ^ m
        = ∑ p : Fin m → Fin n × Fin n, ∏ l : Fin m, sg e (p l).1 * sg e (p l).2 * g (p l) := by
    intro e
    rw [Fintype.sum_pow]
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [show (∑ e : Fin n → Bool, ∏ l : Fin m, sg e (p l).1 * sg e (p l).2 * g (p l))
        = ∑ e : Fin n → Bool,
            (∏ l : Fin m, g (p l)) * (∏ l : Fin m, sg e (p l).1 * sg e (p l).2) by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.prod_mul_distrib, mul_comm]]
  rw [Finset.mul_sum]

/-- Squared norm expansion: `‖∑_i sg_i • x_i‖^2 = ∑_{i,j} sg_i sg_j Re ⟨x_i, x_j⟩`. -/
private lemma norm_sq_eq_sum (n : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : Fin n → Bool) (x : Fin n → H) :
    ‖∑ i : Fin n, (sg e i : ℂ) • x i‖ ^ 2
      = ∑ a : Fin n × Fin n, sg e a.1 * sg e a.2 * (inner ℂ (x a.1) (x a.2)).re := by
  have hexp : (inner ℂ (∑ i, ((sg e i : ℝ) : ℂ) • x i)
                (∑ i, ((sg e i : ℝ) : ℂ) • x i)).re
        = ∑ a : Fin n × Fin n, sg e a.1 * sg e a.2 * (inner ℂ (x a.1) (x a.2)).re := by
    rw [sum_inner]
    simp_rw [inner_sum]
    rw [Complex.re_sum]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [inner_smul_left, inner_smul_right]
    rw [Complex.conj_ofReal]
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  rw [show ‖∑ i : Fin n, (sg e i : ℂ) • x i‖ ^ 2
        = (inner ℂ (∑ i, ((sg e i : ℝ) : ℂ) • x i)
            (∑ i, ((sg e i : ℝ) : ℂ) • x i)).re from
      (by simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (∑ i, ((sg e i : ℝ) : ℂ) • x i)).symm)]
  rw [hexp]

/-- `|a|^(2m) = a^(2m)`. -/
private lemma abs_pow_even (a : ℝ) (m : ℕ) : |a| ^ (2 * m) = a ^ (2 * m) := by
  rw [pow_mul, sq_abs, ← pow_mul]

/-- **Vector-to-scalar Rademacher even-moment reduction.** The `2m`-th moment of a Rademacher
sum of vectors is bounded by the `2m`-th moment of the scalar Rademacher sum of the norms. -/
private lemma vector_le_scalar (m n : ℕ) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (x : Fin n → H) :
    (∑ e : Fin n → Bool, ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ (2 * m))
      ≤ ∑ e : Fin n → Bool, (∑ i : Fin n, (if e i then (1 : ℝ) else -1) * ‖x i‖) ^ (2 * m) := by
  classical
  let T : (Fin m → Fin n × Fin n) → ℝ :=
    fun p => ∑ e : Fin n → Bool, ∏ l : Fin m, sg e (p l).1 * sg e (p l).2
  have hT_nonneg : ∀ p, 0 ≤ T p := by
    intro p
    have heq : T p = ∑ e : Fin n → Bool, ∏ a : Fin m × Bool,
        sg e (if a.2 then (p a.1).1 else (p a.1).2) := by
      show (∑ e : Fin n → Bool, ∏ l : Fin m, sg e (p l).1 * sg e (p l).2) = _
      apply Finset.sum_congr rfl; intro e _
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl; intro l _
      rw [Fintype.prod_bool]
      simp
    rw [heq]
    exact sgn_prod_sum_nonneg n (fun a : Fin m × Bool => if a.2 then (p a.1).1 else (p a.1).2)
  have hvec : (∑ e : Fin n → Bool, ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ (2 * m))
      = ∑ p : Fin m → Fin n × Fin n,
          (∏ l : Fin m, (inner ℂ (x (p l).1) (x (p l).2)).re) * T p := by
    have h2 : ∀ e : Fin n → Bool,
        ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ (2 * m)
          = (∑ a : Fin n × Fin n,
              sg e a.1 * sg e a.2 * (inner ℂ (x a.1) (x a.2)).re) ^ m := by
      intro e
      rw [pow_mul]
      congr 1
      rw [show (∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i)
            = ∑ i : Fin n, (sg e i : ℂ) • x i by
        apply Finset.sum_congr rfl; intro i _; rw [sg_cast]]
      exact norm_sq_eq_sum n e x
    simp_rw [h2]
    exact moment_expansion m n (fun a => (inner ℂ (x a.1) (x a.2)).re)
  have hsc : (∑ e : Fin n → Bool, (∑ i : Fin n, (if e i then (1 : ℝ) else -1) * ‖x i‖) ^ (2 * m))
      = ∑ p : Fin m → Fin n × Fin n, (∏ l : Fin m, ‖x (p l).1‖ * ‖x (p l).2‖) * T p := by
    have h2 : ∀ e : Fin n → Bool,
        (∑ i : Fin n, (if e i then (1 : ℝ) else -1) * ‖x i‖) ^ (2 * m)
          = (∑ a : Fin n × Fin n, sg e a.1 * sg e a.2 * (‖x a.1‖ * ‖x a.2‖)) ^ m := by
      intro e
      rw [pow_mul]
      congr 1
      have h3 : (∑ i : Fin n, (if e i then (1 : ℝ) else -1) * ‖x i‖)
          = ∑ i : Fin n, sg e i * ‖x i‖ := by
        apply Finset.sum_congr rfl; intro i _; rw [sg]
      rw [h3]
      have hL : (∑ i : Fin n, sg e i * ‖x i‖) ^ 2
          = ∑ i : Fin n, ∑ j : Fin n, sg e i * sg e j * (‖x i‖ * ‖x j‖) := by
        rw [sq, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        ring
      rw [hL, Fintype.sum_prod_type]
    simp_rw [h2]
    exact moment_expansion m n (fun a => ‖x a.1‖ * ‖x a.2‖)
  rw [hvec, hsc]
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_right _ (hT_nonneg p)
  calc ∏ l : Fin m, (inner ℂ (x (p l).1) (x (p l).2)).re
      ≤ |∏ l : Fin m, (inner ℂ (x (p l).1) (x (p l).2)).re| := le_abs_self _
    _ = ∏ l : Fin m, |(inner ℂ (x (p l).1) (x (p l).2)).re| := by rw [Finset.abs_prod]
    _ ≤ ∏ l : Fin m, ‖x (p l).1‖ * ‖x (p l).2‖ :=
        Finset.prod_le_prod₀ (fun l _ => abs_nonneg _) (fun l _ =>
          le_trans (Complex.abs_re_le_norm _) (norm_inner_le_norm _ _))

theorem rademacher_hilbert_even_moment :
    ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ), 1 ≤ m → ∀ {H : Type*} [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] (n : ℕ) (x : Fin n → H),
      (∑ e : Fin n → Bool, ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ (2 * m))
        / (2 : ℝ) ^ n
      ≤ (K * m) ^ m * (∑ i : Fin n, ‖x i‖ ^ 2) ^ m := by
  classical
  obtain ⟨C, hCpos, hC⟩ := exists_khintchine_le_of_two_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro m hm H _ _ n x
  have hp : (2 : ℝ) ≤ (2 * m : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * m)
  have hred := vector_le_scalar m n x
  have hdiv : (∑ e : Fin n → Bool, ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ (2 * m))
        / (2 : ℝ) ^ n
      ≤ (∑ e : Fin n → Bool,
          (∑ i : Fin n, (if e i then (1 : ℝ) else -1) * ‖x i‖) ^ (2 * m)) / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_right hred (by positivity)
  have hLHS_eq : (∑ e : Fin n → Bool,
        |∑ i : Fin n, (if e i then (1 : ℝ) else -1) * ‖x i‖| ^ ((2 * m : ℝ)))
      = ∑ e : Fin n → Bool,
          (∑ i : Fin n, (if e i then (1 : ℝ) else -1) * ‖x i‖) ^ (2 * m) := by
    have hcast : (2 * m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
    apply Finset.sum_congr rfl; intro e _
    rw [hcast, Real.rpow_natCast]
    exact abs_pow_even _ m
  have hRHS_eq : (C * (2 * m : ℝ)) ^ ((2 * m : ℝ) / 2)
        * (∑ i : Fin n, ‖x i‖ ^ 2) ^ ((2 * m : ℝ) / 2)
      = ((2 * C) * m) ^ m * (∑ i : Fin n, ‖x i‖ ^ 2) ^ m := by
    rw [show (2 * m : ℝ) / 2 = (m : ℝ) by ring, Real.rpow_natCast, Real.rpow_natCast]
    congr 1
    ring
  have hsc' : (∑ e : Fin n → Bool,
        (∑ i : Fin n, (if e i then (1 : ℝ) else -1) * ‖x i‖) ^ (2 * m)) / (2 : ℝ) ^ n
      ≤ ((2 * C) * m) ^ m * (∑ i : Fin n, ‖x i‖ ^ 2) ^ m := by
    have h := hC n (2 * m : ℝ) hp (fun i : Fin n => ‖x i‖)
    rw [hLHS_eq, hRHS_eq] at h
    exact h
  exact hdiv.trans hsc'

end Commons.Analysis.Walsh