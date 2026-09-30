import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_quadratic_triple_LSeries_coeffs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Dirichlet series of `ζ(s) L(s,χ) L(s,ψ) L(s,χ'ψ')` for quadratic `χ`, `ψ`
of possibly different levels

Let `χ` be a quadratic Dirichlet character modulo `N` and `ψ` a quadratic Dirichlet
character modulo `M` (so that `χ * χ = 1` and `ψ * ψ = 1`, hence all their values lie in
`{0, 1, -1}`).  Let `χ'` and `ψ'` be the level-`N*M` lifts of `χ` and `ψ` (i.e.
`χ.changeLevel (Nat.dvd_mul_right N M)` and `ψ.changeLevel (Nat.dvd_mul_left M N)`).
Then the product

  `ζ(s) L(s,χ) L(s,ψ) L(s,χ'ψ')`

is the Dirichlet series `∑ r n / n^s` of a sequence `r : ℕ → ℝ` of **nonnegative** real
numbers with `r 1 = 1` and whose abscissa of absolute convergence is `< 2`.

The coefficient sequence is the Dirichlet convolution of the coefficient functions
`1`, `χ`, `ψ`, `χ'ψ'`.  At a prime `p` the relevant values are `a = χ p ∈ {0,±1}`,
`b = ψ p ∈ {0,±1}` and `c = (χ'ψ') p`; one has `c = a * b` (the interesting case being
`p ∤ NM`, where all three values are determined by the units map), so that the local Euler
factor is either `(1-X)⁻⁴` or `(1-X²)⁻²`, both of which have nonnegative coefficients.

## Tags

Dirichlet character, Dirichlet L-series, quadratic character, Landau positivity
-/

open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

open Complex

/-! ## Changing levels -/

/-- `changeLevel` does not change the value at a prime that does not divide the new level. -/
lemma changeLevel_apply_of_prime_not_dvd {n m : ℕ} (hm : n ∣ m) (χ : DirichletCharacter ℂ n)
    {p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (χ.changeLevel hm) (p : ZMod m) = χ (p : ZMod n) := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_prime_iff_not_dvd (n := m) hp).mpr hpm
  have h1 : (χ.changeLevel hm) (p : ZMod m) = (χ.changeLevel hm) (u : ZMod m) := by
    rw [hu]
  rw [h1, DirichletCharacter.changeLevel_eq_cast_of_dvd χ hm u]
  congr 1
  rw [hu]
  exact ZMod.cast_natCast hm p

/-- At a prime, the product of the two level-lifted characters takes the value `χ p * ψ p`. -/
lemma levelLift_mul_apply_prime {N M : ℕ} (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p : ℕ} (hp : p.Prime) :
    ((χ.changeLevel (Nat.dvd_mul_right N M)) * (ψ.changeLevel (Nat.dvd_mul_left M N)))
        (p : ZMod (N * M)) = χ (p : ZMod N) * ψ (p : ZMod M) := by
  rw [MulChar.mul_apply]
  by_cases hN : p ∣ N
  · have hNM : p ∣ N * M := dvd_trans hN (Nat.dvd_mul_right N M)
    have h1 : ¬ IsUnit (p : ZMod (N * M)) := fun h ↦
      (ZMod.isUnit_prime_iff_not_dvd (n := N * M) hp).mp h hNM
    have h2 : ¬ IsUnit (p : ZMod N) := fun h ↦
      (ZMod.isUnit_prime_iff_not_dvd (n := N) hp).mp h hN
    rw [MulChar.map_nonunit _ h1, MulChar.map_nonunit _ h2]
    ring
  · by_cases hM : p ∣ M
    · have hNM : p ∣ N * M := dvd_trans hM (Nat.dvd_mul_left M N)
      have h1 : ¬ IsUnit (p : ZMod (N * M)) := fun h ↦
        (ZMod.isUnit_prime_iff_not_dvd (n := N * M) hp).mp h hNM
      have h2 : ¬ IsUnit (p : ZMod M) := fun h ↦
        (ZMod.isUnit_prime_iff_not_dvd (n := M) hp).mp h hM
      rw [MulChar.map_nonunit _ h1, MulChar.map_nonunit _ h2]
      ring
    · have hNM : ¬ p ∣ N * M := fun h ↦ (hp.dvd_mul.mp h).elim hN hM
      rw [changeLevel_apply_of_prime_not_dvd (Nat.dvd_mul_right N M) χ hp hNM,
        changeLevel_apply_of_prime_not_dvd (Nat.dvd_mul_left M N) ψ hp hNM]

variable {N M : ℕ} [NeZero N] [NeZero M]

/-! ## The arithmetic function `ζ * χ * ψ * χ'ψ'` -/

/-- The arithmetic function whose Dirichlet series is `ζ(s)L(s,χ)L(s,ψ)L(s,χ'ψ')`. -/
def mixedTripleAF (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    ArithmeticFunction ℂ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * chiAF χ * chiAF ψ *
    chiAF ((χ.changeLevel (Nat.dvd_mul_right N M)) * (ψ.changeLevel (Nat.dvd_mul_left M N)))

lemma isMultiplicative_mixedTripleAF (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    (mixedTripleAF χ ψ).IsMultiplicative := by
  have hz : (ArithmeticFunction.zeta : ArithmeticFunction ℂ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  exact ((hz.mul (DirichletCharacter.isMultiplicative_toArithmeticFunction χ)).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ)).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction _)

/-! ## Local Euler factors -/

/-- Local Euler factor, grouped as `(χ * ζ) * (χ'ψ' * ψ)`. -/
lemma mixedTripleAF_prime_pow_order1 (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mixedTripleAF χ ψ (p ^ k) =
      ∑ i ∈ Finset.range (k + 1),
        (∑ l ∈ Finset.range (i + 1), (χ (p : ZMod N)) ^ l) *
          (∑ m ∈ Finset.range (k - i + 1),
            (χ (p : ZMod N) * ψ (p : ZMod M)) ^ m * (ψ (p : ZMod M)) ^ (k - i - m)) := by
  have h : mixedTripleAF χ ψ =
      (chiAF χ * (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) *
        (chiAF ((χ.changeLevel (Nat.dvd_mul_right N M)) *
          (ψ.changeLevel (Nat.dvd_mul_left M N))) * chiAF ψ) := by
    simp only [mixedTripleAF]
    ring
  rw [h, mul_apply_prime_pow _ _ hp k]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_apply_prime_pow _ _ hp i, mul_apply_prime_pow _ _ hp (k - i)]
  congr 1
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [chiAF_prime_pow χ hp l, zetaC_apply_ne _ (pow_ne_zero _ hp.ne_zero), mul_one]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [chiAF_prime_pow _ hp m, chiAF_prime_pow ψ hp (k - i - m),
      levelLift_mul_apply_prime χ ψ hp]

/-- Local Euler factor, grouped as `(ψ * ζ) * (χ'ψ' * χ)`. -/
lemma mixedTripleAF_prime_pow_order2 (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    mixedTripleAF χ ψ (p ^ k) =
      ∑ i ∈ Finset.range (k + 1),
        (∑ l ∈ Finset.range (i + 1), (ψ (p : ZMod M)) ^ l) *
          (∑ m ∈ Finset.range (k - i + 1),
            (χ (p : ZMod N) * ψ (p : ZMod M)) ^ m * (χ (p : ZMod N)) ^ (k - i - m)) := by
  have h : mixedTripleAF χ ψ =
      (chiAF ψ * (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) *
        (chiAF ((χ.changeLevel (Nat.dvd_mul_right N M)) *
          (ψ.changeLevel (Nat.dvd_mul_left M N))) * chiAF χ) := by
    simp only [mixedTripleAF]
    ring
  rw [h, mul_apply_prime_pow _ _ hp k]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_apply_prime_pow _ _ hp i, mul_apply_prime_pow _ _ hp (k - i)]
  congr 1
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [chiAF_prime_pow ψ hp l, zetaC_apply_ne _ (pow_ne_zero _ hp.ne_zero), mul_one]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [chiAF_prime_pow _ hp m, chiAF_prime_pow χ hp (k - i - m),
      levelLift_mul_apply_prime χ ψ hp]

/-! ## Positivity of the local Euler factors -/

lemma mixedTripleAF_prime_pow_nonneg (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ * χ = 1) (hψ : ψ * ψ = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ mixedTripleAF χ ψ (p ^ k) := by
  have hχ2 : χ ^ 2 = 1 := by rwa [pow_two]
  have hψ2 : ψ ^ 2 = 1 := by rwa [pow_two]
  have hqa := MulChar.isQuadratic_iff_sq_eq_one.mpr hχ2
  have hqb := MulChar.isQuadratic_iff_sq_eq_one.mpr hψ2
  by_cases ha : χ (p : ZMod N) = -1
  · -- `χ p = -1`
    rw [mixedTripleAF_prime_pow_order1 χ ψ hp k, ha]
    refine Finset.sum_nonneg fun i hi => mul_nonneg ?_ ?_
    · rw [neg_one_geom_sum]
      split <;> norm_num
    · rw [sum_symm (ψ (p : ZMod M)) (k - i), neg_one_geom_sum]
      split_ifs with hj
      · norm_num
      · have hj' : Even (k - i) := by
          rcases Nat.even_or_odd (k - i) with h | h
          · exact h
          · exact absurd h.add_one hj
        have hb : ψ (p : ZMod M) = 0 ∨ ψ (p : ZMod M) = 1 ∨ ψ (p : ZMod M) = -1 := by
          rcases hqb (p : ZMod M) with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        have := pow_even_nonneg (ψ (p : ZMod M)) hb hj'
        simpa using this
  · by_cases hb : ψ (p : ZMod M) = -1
    · -- `ψ p = -1` (and `χ p ≠ -1`)
      rw [mixedTripleAF_prime_pow_order2 χ ψ hp k, hb, mul_comm (χ (p : ZMod N)) (-1)]
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
    · -- `χ p ≠ -1` and `ψ p ≠ -1`, so both values are `0` or `1`
      rw [mixedTripleAF_prime_pow_order1 χ ψ hp k]
      have ha01 : χ (p : ZMod N) = 0 ∨ χ (p : ZMod N) = 1 := by
        rcases hqa (p : ZMod N) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h ha
      have hb01 : ψ (p : ZMod M) = 0 ∨ ψ (p : ZMod M) = 1 := by
        rcases hqb (p : ZMod M) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hb
      have ha0 : (0 : ℂ) ≤ χ (p : ZMod N) := by
        rcases ha01 with h | h <;> simp [h]
      have hb0 : (0 : ℂ) ≤ ψ (p : ZMod M) := by
        rcases hb01 with h | h <;> simp [h]
      have hab0 : (0 : ℂ) ≤ χ (p : ZMod N) * ψ (p : ZMod M) := mul_nonneg ha0 hb0
      refine Finset.sum_nonneg fun i hi => mul_nonneg ?_ ?_
      · exact Finset.sum_nonneg fun l hl => pow_nonneg ha0 l
      · exact Finset.sum_nonneg fun m hm =>
          mul_nonneg (pow_nonneg hab0 m) (pow_nonneg hb0 (k - i - m))

/-! ## Nonnegativity of the coefficient sequence -/

lemma mixedTripleAF_nonneg (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ * χ = 1) (hψ : ψ * ψ = 1) (n : ℕ) : 0 ≤ mixedTripleAF χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [(isMultiplicative_mixedTripleAF χ ψ).multiplicative_factorization _ hn]
    change 0 ≤ ∏ x ∈ n.factorization.support, mixedTripleAF χ ψ (x ^ n.factorization x)
    rw [Nat.support_factorization]
    exact Finset.prod_nonneg fun p hp =>
      mixedTripleAF_prime_pow_nonneg χ ψ hχ hψ (Nat.prime_of_mem_primeFactors hp) _

/-! ## The coefficient sequence `r` -/

/-- The coefficient sequence `r` of `ζ(s)L(s,χ)L(s,ψ)L(s,χ'ψ')`, as a real sequence. -/
def mixedTripleSeq (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) : ℕ → ℝ :=
  fun n => (mixedTripleAF χ ψ n).re

lemma mixedTripleSeq_nonneg (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ * χ = 1) (hψ : ψ * ψ = 1) (n : ℕ) : 0 ≤ mixedTripleSeq χ ψ n :=
  (Complex.nonneg_iff.mp (mixedTripleAF_nonneg χ ψ hχ hψ n)).1

lemma mixedTripleSeq_one (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M) :
    mixedTripleSeq χ ψ 1 = 1 := by
  simp [mixedTripleSeq, (isMultiplicative_mixedTripleAF χ ψ).map_one]

lemma ofReal_mixedTripleSeq (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ * χ = 1) (hψ : ψ * ψ = 1) (n : ℕ) :
    ((mixedTripleSeq χ ψ n : ℝ) : ℂ) = mixedTripleAF χ ψ n := by
  have him : (mixedTripleAF χ ψ n).im = 0 :=
    (Complex.nonneg_iff.mp (mixedTripleAF_nonneg χ ψ hχ hψ n)).2.symm
  apply Complex.ext <;> simp [mixedTripleSeq, him]

/-! ## The L-series of the coefficient sequence -/

lemma LSeriesSummable_chiAF_mixed (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => chiAF χ n) s :=
  (LSeriesSummable_congr s fun hn => chiAF_apply_of_ne χ hn).mpr
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs)

theorem LSeries_mixedTripleSeq (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ * χ = 1) (hψ : ψ * ψ = 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (mixedTripleSeq χ ψ n : ℂ)) s =
      riemannZeta s * (DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction ψ s *
        DirichletCharacter.LFunction ((χ.changeLevel (Nat.dvd_mul_right N M)) *
          (ψ.changeLevel (Nat.dvd_mul_left M N))) s) := by
  have hfac : mixedTripleAF χ ψ =
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        (chiAF χ * (chiAF ψ *
          chiAF ((χ.changeLevel (Nat.dvd_mul_right N M)) *
            (ψ.changeLevel (Nat.dvd_mul_left M N))))) := by
    simp only [mixedTripleAF]
    ring
  have hfac_f : (fun n => mixedTripleAF χ ψ n) =
      (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        (chiAF χ * (chiAF ψ *
          chiAF ((χ.changeLevel (Nat.dvd_mul_right N M)) *
            (ψ.changeLevel (Nat.dvd_mul_left M N)))))) n) := by
    rw [hfac]
  have hfun : (fun n => (mixedTripleSeq χ ψ n : ℂ)) = fun n => mixedTripleAF χ ψ n := by
    funext n
    exact ofReal_mixedTripleSeq χ ψ hχ hψ n
  have hZ := LSeriesSummable_zetaC hs
  have hX := LSeriesSummable_chiAF_mixed χ hs
  have hY := LSeriesSummable_chiAF_mixed ψ hs
  have hW := LSeriesSummable_chiAF_mixed
    ((χ.changeLevel (Nat.dvd_mul_right N M)) * (ψ.changeLevel (Nat.dvd_mul_left M N))) hs
  have hYW : LSeriesSummable (fun n => (chiAF ψ *
      chiAF ((χ.changeLevel (Nat.dvd_mul_right N M)) *
        (ψ.changeLevel (Nat.dvd_mul_left M N)))) n) s :=
    ArithmeticFunction.LSeriesSummable_mul hY hW
  have hXYW : LSeriesSummable
      (fun n => (chiAF χ * (chiAF ψ *
        chiAF ((χ.changeLevel (Nat.dvd_mul_right N M)) *
          (ψ.changeLevel (Nat.dvd_mul_left M N))))) n) s :=
    ArithmeticFunction.LSeriesSummable_mul hX hYW
  rw [hfun, hfac_f]
  rw [ArithmeticFunction.LSeries_mul' hZ hXYW,
    ArithmeticFunction.LSeries_mul' hX hYW,
    ArithmeticFunction.LSeries_mul' hY hW,
    LSeries_zetaC hs, LSeries_chiAF χ hs, LSeries_chiAF ψ hs, LSeries_chiAF _ hs]
  ring

/-- The abscissa of absolute convergence of the coefficient sequence is `< 2`. -/
theorem abscissaOfAbsConv_mixedTripleSeq (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ * χ = 1) (hψ : ψ * ψ = 1) :
    LSeries.abscissaOfAbsConv (fun n => (mixedTripleSeq χ ψ n : ℂ)) < 2 := by
  have hfun : (fun n => (mixedTripleSeq χ ψ n : ℂ)) = fun n => mixedTripleAF χ ψ n := by
    funext n
    exact ofReal_mixedTripleSeq χ ψ hχ hψ n
  rw [hfun]
  have hZ : LSeries.abscissaOfAbsConv
      (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n) ≤ 1 :=
    (abscissaOfAbsConv_zetaC).le
  have hX : LSeries.abscissaOfAbsConv (fun n => chiAF χ n) ≤ 1 :=
    (abscissaOfAbsConv_chiAF χ).le
  have hY : LSeries.abscissaOfAbsConv (fun n => chiAF ψ n) ≤ 1 :=
    (abscissaOfAbsConv_chiAF ψ).le
  have hW : LSeries.abscissaOfAbsConv
      (fun n => chiAF ((χ.changeLevel (Nat.dvd_mul_right N M)) *
        (ψ.changeLevel (Nat.dvd_mul_left M N))) n) ≤ 1 :=
    (abscissaOfAbsConv_chiAF _).le
  have hle1 : ∀ (f g : ArithmeticFunction ℂ),
      LSeries.abscissaOfAbsConv (fun n => f n) ≤ 1 →
      LSeries.abscissaOfAbsConv (fun n => g n) ≤ 1 →
      LSeries.abscissaOfAbsConv (fun n => (f * g) n) ≤ 1 := by
    intro f g hf hg
    refine (abscissaOfAbsConv_mul_le f g).trans ?_
    rw [max_le_iff]
    exact ⟨hf, hg⟩
  have hstep : LSeries.abscissaOfAbsConv (fun n => mixedTripleAF χ ψ n) ≤ 1 := by
    have h1 : LSeries.abscissaOfAbsConv
        (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * chiAF χ * chiAF ψ) n) ≤ 1 :=
      hle1 ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * chiAF χ) (chiAF ψ)
        (hle1 (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (chiAF χ) hZ hX) hY
    exact hle1 _ _ h1 hW
  refine hstep.trans_lt ?_
  norm_num

/-! ## The main theorem -/

theorem LFunction_quadratic_triple_LSeries_coeffs_mixed
    {N M : ℕ} [NeZero N] [NeZero M] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ * χ = 1) (hψ : ψ * ψ = 1) :
    ∃ r : ℕ → ℝ, (∀ n : ℕ, 0 ≤ r n) ∧ r 1 = 1 ∧
      LSeries.abscissaOfAbsConv (fun n : ℕ => (r n : ℂ)) < 2 ∧
      ∀ s : ℂ, 1 < s.re →
        riemannZeta s * (DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction ψ s *
          DirichletCharacter.LFunction ((χ.changeLevel (Nat.dvd_mul_right N M)) *
            (ψ.changeLevel (Nat.dvd_mul_left M N))) s) = LSeries (fun n : ℕ => (r n : ℂ)) s := by
  refine ⟨mixedTripleSeq χ ψ, fun n => mixedTripleSeq_nonneg χ ψ hχ hψ n,
    mixedTripleSeq_one χ ψ, abscissaOfAbsConv_mixedTripleSeq χ ψ hχ hψ, fun s hs => ?_⟩
  exact (LSeries_mixedTripleSeq χ ψ hχ hψ hs).symm

end

end Commons.NumberTheory.DirichletCharacter
