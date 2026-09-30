import Mathlib.NumberTheory.LSeries.DirichletContinuation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Dirichlet series of `ζ(s) L(s,χ) L(s,ψ) L(s,χψ)` for quadratic `χ`, `ψ`

Let `χ` and `ψ` be quadratic Dirichlet characters modulo `N` (that is, `χ * χ = 1` and
`ψ * ψ = 1`, so that all their values lie in `{0, 1, -1}`).  Then the product

  `ζ(s) L(s,χ) L(s,ψ) L(s,χψ)`

is the Dirichlet series `∑ r n / n^s` of a sequence `r : ℕ → ℝ` of **nonnegative** real
numbers with `r 1 = 1` and whose abscissa of absolute convergence is `< 2`.

The coefficient sequence is the Dirichlet convolution of the coefficient functions
`1`, `χ`, `ψ`, `χψ`; the crucial point is the local computation
`r p^k = ∑_{i+j+l+m=k} χ(p)^j ψ(p)^l (χψ)(p)^m ≥ 0`
for every prime power `p^k` (the local Euler factor is either `(1-X)^{-4}` or `(1-X²)^{-2}`,
both of which have nonnegative coefficients), combined with multiplicativity.

## Tags

Dirichlet character, Dirichlet L-series, quadratic character, Landau positivity
-/

open scoped LSeries.notation
open scoped ComplexOrder
open Complex

set_option linter.unusedSectionVars false

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

variable {N : ℕ} [NeZero N]

/-! ## Dirichlet convolution of arithmetic functions at prime powers -/

lemma mul_apply_eq_sum_divisors (f g : ArithmeticFunction ℂ) (n : ℕ) :
    (f * g) n = ∑ d ∈ n.divisors, f d * g (n / d) := by
  rw [ArithmeticFunction.mul_apply]
  exact Nat.sum_divisorsAntidiagonal (fun a b => f a * g b)

/-- Dirichlet convolution of arithmetic functions, evaluated at a prime power. -/
lemma mul_apply_prime_pow (f g : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [mul_apply_eq_sum_divisors, Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos]

/-- Values of the (coerced) zeta arithmetic function. -/
lemma zetaC_apply_ne (x : ℕ) (hx : x ≠ 0) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) x = 1 := by
  rw [ArithmeticFunction.natCoe_apply]
  exact_mod_cast ArithmeticFunction.zeta_apply_ne hx

/-! ## The arithmetic function of a Dirichlet character -/

/-- The arithmetic function `n ↦ χ n` attached to a Dirichlet character `χ`. -/
def chiAF (χ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n : ℕ => χ (n : ZMod N)

lemma chiAF_apply_of_ne (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : n ≠ 0) :
    chiAF χ n = χ (n : ZMod N) := by
  simp [chiAF, toArithmeticFunction, hn]

lemma chiAF_prime_pow (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    chiAF χ (p ^ k) = (χ (p : ZMod N)) ^ k := by
  rw [chiAF_apply_of_ne _ (pow_ne_zero k hp.ne_zero), Nat.cast_pow, map_pow]

/-! ## The arithmetic function `ζ * χ * ψ * χψ` -/

/-- The arithmetic function whose Dirichlet series is `ζ(s)L(s,χ)L(s,ψ)L(s,χψ)`. -/
def tripleAF (χ ψ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * chiAF χ * chiAF ψ * chiAF (χ * ψ)

lemma isMultiplicative_tripleAF (χ ψ : DirichletCharacter ℂ N) :
    (tripleAF χ ψ).IsMultiplicative := by
  have hz : (ArithmeticFunction.zeta : ArithmeticFunction ℂ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  exact ((hz.mul (DirichletCharacter.isMultiplicative_toArithmeticFunction χ)).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ)).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction (χ * ψ))

/-! ## The local Euler factors, in two convenient groupings -/

/-- For a geometric-looking alternating sum: for `m ≤ j` one has
`(-b)^m * b^(j-m) = (-1)^m * b^j`, so the sum factors. -/
lemma sum_symm (b : ℂ) (j : ℕ) :
    (∑ m ∈ Finset.range (j + 1), (-1 * b) ^ m * b ^ (j - m))
      = (∑ m ∈ Finset.range (j + 1), (-1 : ℂ) ^ m) * b ^ j := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_pow, mul_assoc, ← pow_add,
    Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]

/-- The local Euler factor written using the grouping `(χ * ζ) * (χψ * ψ)`: the inner
sums are of the "ascending" shape `∑ a^l`. -/
lemma tripleAF_prime_pow_order1 (χ ψ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime)
    (k : ℕ) :
    tripleAF χ ψ (p ^ k) =
      ∑ i ∈ Finset.range (k + 1),
        (∑ l ∈ Finset.range (i + 1), (χ (p : ZMod N)) ^ l) *
          (∑ m ∈ Finset.range (k - i + 1),
            ((χ * ψ) (p : ZMod N)) ^ m * (ψ (p : ZMod N)) ^ (k - i - m)) := by
  have h : tripleAF χ ψ = (chiAF χ * (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) *
      (chiAF (χ * ψ) * chiAF ψ) := by
    simp only [tripleAF]
    ring
  rw [h, mul_apply_prime_pow _ _ hp k]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_apply_prime_pow _ _ hp i, mul_apply_prime_pow _ _ hp (k - i)]
  congr 1
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [chiAF_prime_pow χ hp l, zetaC_apply_ne _ (pow_ne_zero _ hp.ne_zero), mul_one]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [chiAF_prime_pow (χ * ψ) hp m, chiAF_prime_pow ψ hp (k - i - m)]

/-- The local Euler factor written using the grouping `(ψ * ζ) * (χψ * χ)`. -/
lemma tripleAF_prime_pow_order2 (χ ψ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime)
    (k : ℕ) :
    tripleAF χ ψ (p ^ k) =
      ∑ i ∈ Finset.range (k + 1),
        (∑ l ∈ Finset.range (i + 1), (ψ (p : ZMod N)) ^ l) *
          (∑ m ∈ Finset.range (k - i + 1),
            ((χ * ψ) (p : ZMod N)) ^ m * (χ (p : ZMod N)) ^ (k - i - m)) := by
  have h : tripleAF χ ψ = (chiAF ψ * (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) *
      (chiAF (χ * ψ) * chiAF χ) := by
    simp only [tripleAF]
    ring
  rw [h, mul_apply_prime_pow _ _ hp k]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_apply_prime_pow _ _ hp i, mul_apply_prime_pow _ _ hp (k - i)]
  congr 1
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [chiAF_prime_pow ψ hp l, zetaC_apply_ne _ (pow_ne_zero _ hp.ne_zero), mul_one]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [chiAF_prime_pow (χ * ψ) hp m, chiAF_prime_pow χ hp (k - i - m)]

/-! ## Positivity of the local Euler factors -/

lemma pow_mem_of_mem (b : ℂ) (hb : b = 0 ∨ b = 1 ∨ b = -1) (t : ℕ) :
    b ^ t = 0 ∨ b ^ t = 1 ∨ b ^ t = -1 := by
  rcases hb with rfl | rfl | rfl
  · by_cases ht : t = 0
    · exact Or.inr (Or.inl (by simp [ht]))
    · exact Or.inl (zero_pow ht)
  · exact Or.inr (Or.inl (one_pow t))
  · rcases Nat.even_or_odd t with h | h
    · exact Or.inr (Or.inl h.neg_one_pow)
    · exact Or.inr (Or.inr h.neg_one_pow)

lemma sq_nonneg_of_mem (b : ℂ) (hb : b = 0 ∨ b = 1 ∨ b = -1) : 0 ≤ b * b := by
  rcases hb with rfl | rfl | rfl <;> norm_num

lemma pow_even_nonneg (b : ℂ) (hb : b = 0 ∨ b = 1 ∨ b = -1) {j : ℕ} (hj : Even j) :
    0 ≤ b ^ j := by
  obtain ⟨t, rfl⟩ := hj
  rw [pow_add]
  exact sq_nonneg_of_mem (b ^ t) (pow_mem_of_mem b hb t)

/-- The local Euler factor at a prime power is nonnegative. -/
lemma tripleAF_prime_pow_nonneg (χ ψ : DirichletCharacter ℂ N)
    (hχ : χ * χ = 1) (hψ : ψ * ψ = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ tripleAF χ ψ (p ^ k) := by
  have hχ2 : χ ^ 2 = 1 := by rwa [pow_two]
  have hψ2 : ψ ^ 2 = 1 := by rwa [pow_two]
  have hqa := MulChar.isQuadratic_iff_sq_eq_one.mpr hχ2
  have hqb := MulChar.isQuadratic_iff_sq_eq_one.mpr hψ2
  by_cases ha : χ (p : ZMod N) = -1
  · -- first case: `χ p = -1`
    rw [tripleAF_prime_pow_order1 χ ψ hp k, MulChar.mul_apply χ ψ (p : ZMod N), ha]
    refine Finset.sum_nonneg fun i hi => mul_nonneg ?_ ?_
    · rw [neg_one_geom_sum]
      split <;> norm_num
    · rw [sum_symm, neg_one_geom_sum]
      split_ifs with hj
      · norm_num
      · have hj' : Even (k - i) := by
          rcases Nat.even_or_odd (k - i) with h | h
          · exact h
          · exact absurd h.add_one hj
        have hb : ψ (p : ZMod N) = 0 ∨ ψ (p : ZMod N) = 1 ∨ ψ (p : ZMod N) = -1 := by
          rcases hqb (p : ZMod N) with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        have := pow_even_nonneg (ψ (p : ZMod N)) hb hj'
        simpa using this
  · by_cases hb : ψ (p : ZMod N) = -1
    · -- second case: `ψ p = -1` (and `χ p ≠ -1`)
      rw [tripleAF_prime_pow_order2 χ ψ hp k, MulChar.mul_apply χ ψ (p : ZMod N), hb,
        mul_comm (χ (p : ZMod N)) (-1)]
      have ha01 : χ (p : ZMod N) = 0 ∨ χ (p : ZMod N) = 1 := by
        rcases hqa (p : ZMod N) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h ha
      have ha0 : (0 : ℂ) ≤ χ (p : ZMod N) := by
        rcases ha01 with h | h <;> simp [h]
      refine Finset.sum_nonneg fun i hi => mul_nonneg ?_ ?_
      · rw [neg_one_geom_sum]
        split <;> norm_num
      · rw [sum_symm, neg_one_geom_sum]
        split_ifs with hj
        · norm_num
        · have hpow : (0 : ℂ) ≤ (χ (p : ZMod N)) ^ (k - i) := pow_nonneg ha0 _
          calc (0 : ℂ) ≤ (χ (p : ZMod N)) ^ (k - i) := hpow
            _ = 1 * (χ (p : ZMod N)) ^ (k - i) := (one_mul _).symm
    · -- third case: `χ p ≠ -1` and `ψ p ≠ -1`, so both values are `0` or `1`
      rw [tripleAF_prime_pow_order1 χ ψ hp k, MulChar.mul_apply χ ψ (p : ZMod N)]
      have ha01 : χ (p : ZMod N) = 0 ∨ χ (p : ZMod N) = 1 := by
        rcases hqa (p : ZMod N) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h ha
      have hb01 : ψ (p : ZMod N) = 0 ∨ ψ (p : ZMod N) = 1 := by
        rcases hqb (p : ZMod N) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hb
      have ha0 : (0 : ℂ) ≤ χ (p : ZMod N) := by
        rcases ha01 with h | h <;> simp [h]
      have hb0 : (0 : ℂ) ≤ ψ (p : ZMod N) := by
        rcases hb01 with h | h <;> simp [h]
      have hab0 : (0 : ℂ) ≤ χ (p : ZMod N) * ψ (p : ZMod N) := mul_nonneg ha0 hb0
      refine Finset.sum_nonneg fun i hi => mul_nonneg ?_ ?_
      · exact Finset.sum_nonneg fun l hl => pow_nonneg ha0 l
      · exact Finset.sum_nonneg fun m hm =>
          mul_nonneg (pow_nonneg hab0 m) (pow_nonneg hb0 (k - i - m))

/-! ## Nonnegativity of the coefficient sequence -/

lemma tripleAF_nonneg (χ ψ : DirichletCharacter ℂ N)
    (hχ : χ * χ = 1) (hψ : ψ * ψ = 1) (n : ℕ) : 0 ≤ tripleAF χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [(isMultiplicative_tripleAF χ ψ).multiplicative_factorization _ hn]
    change 0 ≤ ∏ x ∈ n.factorization.support, tripleAF χ ψ (x ^ n.factorization x)
    rw [Nat.support_factorization]
    exact Finset.prod_nonneg fun p hp =>
      tripleAF_prime_pow_nonneg χ ψ hχ hψ (Nat.prime_of_mem_primeFactors hp) _

/-! ## L-series of the auxiliary arithmetic functions -/

lemma LSeriesSummable_chiAF (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => chiAF χ n) s :=
  (LSeriesSummable_congr s fun hn => chiAF_apply_of_ne χ hn).mpr
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs)

lemma LSeriesSummable_zetaC {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s :=
  ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs

lemma LSeries_chiAF (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => chiAF χ n) s = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact LSeries_congr (fun hn => chiAF_apply_of_ne χ hn) s

lemma LSeries_zetaC {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s = riemannZeta s :=
  ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs

lemma abscissaOfAbsConv_chiAF (χ : DirichletCharacter ℂ N) :
    LSeries.abscissaOfAbsConv (fun n => chiAF χ n) = 1 :=
  (LSeries.abscissaOfAbsConv_congr fun hn => chiAF_apply_of_ne χ hn).trans
    (DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne N) χ)

lemma abscissaOfAbsConv_zetaC :
    LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) = 1 :=
  (LSeries.abscissaOfAbsConv_congr fun {n} hn => zetaC_apply_ne n hn).trans
    LSeries.abscissaOfAbsConv_one

lemma abscissaOfAbsConv_mul_le (f g : ArithmeticFunction ℂ) :
    LSeries.abscissaOfAbsConv (fun n => (f * g) n) ≤
      max (LSeries.abscissaOfAbsConv (fun n => f n))
        (LSeries.abscissaOfAbsConv (fun n => g n)) := by
  show LSeries.abscissaOfAbsConv (⇑(f * g)) ≤ _
  rw [← ArithmeticFunction.coe_mul]
  exact LSeries.abscissaOfAbsConv_convolution_le _ _

/-! ## The coefficient sequence `r` -/

/-- The coefficient sequence `r` of `ζ(s)L(s,χ)L(s,ψ)L(s,χψ)`, as a real sequence. -/
def quadTripleSeq (χ ψ : DirichletCharacter ℂ N) : ℕ → ℝ :=
  fun n => (tripleAF χ ψ n).re

lemma quadTripleSeq_nonneg (χ ψ : DirichletCharacter ℂ N) (hχ : χ * χ = 1) (hψ : ψ * ψ = 1)
    (n : ℕ) : 0 ≤ quadTripleSeq χ ψ n :=
  (Complex.nonneg_iff.mp (tripleAF_nonneg χ ψ hχ hψ n)).1

lemma quadTripleSeq_one (χ ψ : DirichletCharacter ℂ N) : quadTripleSeq χ ψ 1 = 1 := by
  simp [quadTripleSeq, (isMultiplicative_tripleAF χ ψ).map_one]

lemma ofReal_quadTripleSeq (χ ψ : DirichletCharacter ℂ N) (hχ : χ * χ = 1) (hψ : ψ * ψ = 1)
    (n : ℕ) : ((quadTripleSeq χ ψ n : ℝ) : ℂ) = tripleAF χ ψ n := by
  have him : (tripleAF χ ψ n).im = 0 :=
    (Complex.nonneg_iff.mp (tripleAF_nonneg χ ψ hχ hψ n)).2.symm
  apply Complex.ext <;> simp [quadTripleSeq, him]

/-- The L-series of the coefficient sequence is `ζ(s)L(s,χ)L(s,ψ)L(s,χψ)`. -/
theorem LSeries_quadTripleSeq (χ ψ : DirichletCharacter ℂ N) (hχ : χ * χ = 1)
    (hψ : ψ * ψ = 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (quadTripleSeq χ ψ n : ℂ)) s =
      riemannZeta s * (DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction ψ s *
        DirichletCharacter.LFunction (χ * ψ) s) := by
  have hfac : tripleAF χ ψ =
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        (chiAF χ * (chiAF ψ * chiAF (χ * ψ))) := by
    simp only [tripleAF]
    ring
  have hfac_f : (fun n => tripleAF χ ψ n) =
      (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        (chiAF χ * (chiAF ψ * chiAF (χ * ψ)))) n) := by
    rw [hfac]
  have hfun : (fun n => (quadTripleSeq χ ψ n : ℂ)) = fun n => tripleAF χ ψ n := by
    funext n
    exact ofReal_quadTripleSeq χ ψ hχ hψ n
  have hZ := LSeriesSummable_zetaC hs
  have hX := LSeriesSummable_chiAF χ hs
  have hY := LSeriesSummable_chiAF ψ hs
  have hW := LSeriesSummable_chiAF (χ * ψ) hs
  have hYW : LSeriesSummable (fun n => (chiAF ψ * chiAF (χ * ψ)) n) s :=
    ArithmeticFunction.LSeriesSummable_mul hY hW
  have hXYW : LSeriesSummable
      (fun n => (chiAF χ * (chiAF ψ * chiAF (χ * ψ))) n) s :=
    ArithmeticFunction.LSeriesSummable_mul hX hYW
  rw [hfun, hfac_f]
  rw [ArithmeticFunction.LSeries_mul' hZ hXYW,
    ArithmeticFunction.LSeries_mul' hX hYW,
    ArithmeticFunction.LSeries_mul' hY hW,
    LSeries_zetaC hs, LSeries_chiAF χ hs, LSeries_chiAF ψ hs, LSeries_chiAF (χ * ψ) hs]
  ring

/-- The abscissa of absolute convergence of the coefficient sequence is `< 2`. -/
theorem abscissaOfAbsConv_quadTripleSeq (χ ψ : DirichletCharacter ℂ N) (hχ : χ * χ = 1)
    (hψ : ψ * ψ = 1) :
    LSeries.abscissaOfAbsConv (fun n => (quadTripleSeq χ ψ n : ℂ)) < 2 := by
  have hfun : (fun n => (quadTripleSeq χ ψ n : ℂ)) = fun n => tripleAF χ ψ n := by
    funext n
    exact ofReal_quadTripleSeq χ ψ hχ hψ n
  rw [hfun]
  have hZ : LSeries.abscissaOfAbsConv
      (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) ≤ 1 :=
    (abscissaOfAbsConv_zetaC).le
  have hX : LSeries.abscissaOfAbsConv (fun n => chiAF χ n) ≤ 1 :=
    (abscissaOfAbsConv_chiAF χ).le
  have hY : LSeries.abscissaOfAbsConv (fun n => chiAF ψ n) ≤ 1 :=
    (abscissaOfAbsConv_chiAF ψ).le
  have hW : LSeries.abscissaOfAbsConv (fun n => chiAF (χ * ψ) n) ≤ 1 :=
    (abscissaOfAbsConv_chiAF (χ * ψ)).le
  have hle1 : ∀ (f g : ArithmeticFunction ℂ),
      LSeries.abscissaOfAbsConv (fun n => f n) ≤ 1 →
      LSeries.abscissaOfAbsConv (fun n => g n) ≤ 1 →
      LSeries.abscissaOfAbsConv (fun n => (f * g) n) ≤ 1 := by
    intro f g hf hg
    refine (abscissaOfAbsConv_mul_le f g).trans ?_
    rw [max_le_iff]
    exact ⟨hf, hg⟩
  have hstep : LSeries.abscissaOfAbsConv (fun n => tripleAF χ ψ n) ≤ 1 := by
    have h1 : LSeries.abscissaOfAbsConv
        (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * chiAF χ * chiAF ψ) n) ≤ 1 :=
      hle1 ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * chiAF χ) (chiAF ψ)
        (hle1 (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (chiAF χ) hZ hX) hY
    exact hle1 _ _ h1 hW
  refine hstep.trans_lt ?_
  norm_num

/-! ## The main theorem -/

theorem LFunction_quadratic_triple_LSeries_coeffs
    {N : ℕ} [NeZero N] (χ ψ : DirichletCharacter ℂ N)
    (hχ : χ * χ = 1) (hψ : ψ * ψ = 1) :
    ∃ r : ℕ → ℝ, (∀ n : ℕ, 0 ≤ r n) ∧ r 1 = 1 ∧
      LSeries.abscissaOfAbsConv (fun n : ℕ => (r n : ℂ)) < 2 ∧
      ∀ s : ℂ, 1 < s.re →
        riemannZeta s * (DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction ψ s *
          DirichletCharacter.LFunction (χ * ψ) s) = LSeries (fun n : ℕ => (r n : ℂ)) s := by
  refine ⟨quadTripleSeq χ ψ, fun n => quadTripleSeq_nonneg χ ψ hχ hψ n,
    quadTripleSeq_one χ ψ, abscissaOfAbsConv_quadTripleSeq χ ψ hχ hψ, fun s hs => ?_⟩
  exact (LSeries_quadTripleSeq χ ψ hχ hψ hs).symm

end

end Commons.NumberTheory.DirichletCharacter