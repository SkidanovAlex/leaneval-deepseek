import Mathlib
import Submission.Work.C17.lc_defs
import Submission.Work.C17I.sympSym_deriv_coeff_bound
import Submission.Work.C17I.pureB_coeff_bound

set_option linter.unusedSimpArgs false

namespace Work.C17I

open PowerSeries

noncomputable section

/-! ### Toolbox -/

/-- `PC` is `logP` evaluated at the odd integers `a = 2m+1`, `b = 2n+1`. -/
private lemma PC_eq_aOf (m n : ℕ) (ra rb rab r0 : ℤ) :
    Submission.CDTPlan.PC m n ra rb rab r0
      = Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 := by
  simp only [Submission.CDTPlan.PC, Work.C17.aOf]

/-- A rate-`R` bound with `R ≤ 5` gives the `(1/5)^k`-rate bound with the same constant. -/
private lemma bound_of_rate {C R : ℝ} (hC : 0 ≤ C) (hR0 : 0 ≤ R) (hR5 : R ≤ 5)
    (k : ℕ) {a : ℝ} (ha : a ≤ C * R ^ k) : a * (1 / 5 : ℝ) ^ k ≤ C := by
  have h5 : (0 : ℝ) ≤ (1 / 5 : ℝ) ^ k := pow_nonneg (by norm_num) k
  have hsplit : R ^ k * (1 / 5 : ℝ) ^ k = (R / 5) ^ k := by
    rw [← mul_pow]; ring_nf
  have hle : (R / 5) ^ k ≤ 1 := pow_le_one₀ (div_nonneg hR0 (by norm_num)) (by linarith)
  calc a * (1 / 5 : ℝ) ^ k ≤ (C * R ^ k) * (1 / 5 : ℝ) ^ k := mul_le_mul_of_nonneg_right ha h5
    _ = C * (R ^ k * (1 / 5 : ℝ) ^ k) := by ring
    _ = C * (R / 5) ^ k := by rw [hsplit]
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hle hC
    _ = C := by ring

/-- `‖(k : ℚ) : ℂ‖` is `≥ 1` for a positive natural number `k`. -/
private lemma norm_nat_cast_ge_one {k : ℕ} (hk : 0 < k) : (1 : ℝ) ≤ ‖((k : ℚ) : ℂ)‖ := by
  rw [Work.CPull.norm_rat_cast_complex]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k : ℚ) : ℝ))]
  have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  simpa using h1

/-- Coefficients of `intY`, in `ℂ`. -/
private lemma coeff_intY_cast (w : PowerSeries ℚ) (k : ℕ) :
    ((PowerSeries.coeff k (Submission.CDTPlan.intY w) : ℚ) : ℂ)
      = if k = 0 then 0
        else ((PowerSeries.coeff (k - 1) w : ℚ) : ℂ) / ((k : ℚ) : ℂ) := by
  rw [Submission.CDTPlan.intY, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · push_cast; ring

/-- Coefficients of `tq`. -/
private lemma coeff_tq_cast (j : ℕ) (w : PowerSeries ℚ) (k : ℕ) :
    ((PowerSeries.coeff k (Submission.CDTPlan.tq j w) : ℚ) : ℂ)
      = ((PowerSeries.coeff (k + j) w : ℚ) : ℂ) := by
  rw [Submission.CDTPlan.tq, PowerSeries.coeff_mk]

/-- Coefficients of `X * w`. -/
private lemma coeff_X_mul (w : PowerSeries ℚ) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.X * w)
      = if k = 0 then 0 else PowerSeries.coeff (k - 1) w := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
    simp [PowerSeries.constantCoeff_X]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
    rw [if_neg (Nat.succ_ne_zero n), PowerSeries.coeff_succ_X_mul, Nat.succ_sub_one]

/-- `intY` of a series whose coefficients satisfy a rate-`4` bound satisfies the
`(1/5)^k`-rate bound with the same constant. -/
private lemma intY_rate_bound {w : PowerSeries ℚ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hw : ∀ n : ℕ, ‖((PowerSeries.coeff n w : ℚ) : ℂ)‖ ≤ C₀ * 4 ^ n) (k : ℕ) :
    ‖((PowerSeries.coeff k (Submission.CDTPlan.intY w) : ℚ) : ℂ)‖ * (1 / 5 : ℝ) ^ k ≤ C₀ := by
  rw [coeff_intY_cast]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [if_pos rfl]
    simpa using hC₀
  · rw [if_neg (Nat.pos_iff_ne_zero.mp hk), norm_div]
    have hk1 : (1 : ℝ) ≤ ‖((k : ℚ) : ℂ)‖ := norm_nat_cast_ge_one hk
    have hkpos : (0 : ℝ) < ‖((k : ℚ) : ℂ)‖ := by linarith
    have hdiv : ‖((PowerSeries.coeff (k - 1) w : ℚ) : ℂ)‖ / ‖((k : ℚ) : ℂ)‖
        ≤ ‖((PowerSeries.coeff (k - 1) w : ℚ) : ℂ)‖ := by
      rw [div_le_iff₀ hkpos]
      nlinarith [norm_nonneg ((PowerSeries.coeff (k - 1) w : ℚ) : ℂ)]
    have hstep : ‖((PowerSeries.coeff (k - 1) w : ℚ) : ℂ)‖ / ‖((k : ℚ) : ℂ)‖
          * (1 / 5 : ℝ) ^ k
        ≤ ‖((PowerSeries.coeff (k - 1) w : ℚ) : ℂ)‖ * (1 / 5 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hdiv (pow_nonneg (by norm_num) k)
    have hbase : ‖((PowerSeries.coeff (k - 1) w : ℚ) : ℂ)‖ ≤ C₀ * 4 ^ k :=
      le_trans (hw (k - 1)) (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega)) hC₀)
    exact le_trans hstep (bound_of_rate hC₀ (by norm_num) (by norm_num) k hbase)

/-- `X * w` inherits a rate-`4` bound. -/
private lemma X_mul_rate {w : PowerSeries ℚ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hw : ∀ n : ℕ, ‖((PowerSeries.coeff n w : ℚ) : ℂ)‖ ≤ C₀ * 4 ^ n) :
    ∀ n : ℕ, ‖((PowerSeries.coeff n (PowerSeries.X * w) : ℚ) : ℂ)‖ ≤ C₀ * 4 ^ n := by
  intro n
  rw [coeff_X_mul]
  split_ifs with hn
  · subst hn
    simpa using mul_nonneg hC₀ (by positivity : (0 : ℝ) ≤ 4 ^ 0)
  · calc ‖((PowerSeries.coeff (n - 1) w : ℚ) : ℂ)‖ ≤ C₀ * 4 ^ (n - 1) := hw (n - 1)
      _ ≤ C₀ * 4 ^ n := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega)) hC₀

/-- `tq j w` inherits a rate-`4` bound, with an extra factor `4 ^ j`. -/
private lemma tq_rate {w : PowerSeries ℚ} {C₀ : ℝ} (_hC₀ : 0 ≤ C₀)
    (hw : ∀ n : ℕ, ‖((PowerSeries.coeff n w : ℚ) : ℂ)‖ ≤ C₀ * 4 ^ n) (j : ℕ) :
    ∀ n : ℕ, ‖((PowerSeries.coeff n (Submission.CDTPlan.tq j w) : ℚ) : ℂ)‖
      ≤ (C₀ * 4 ^ j) * 4 ^ n := by
  intro n
  rw [coeff_tq_cast]
  calc ‖((PowerSeries.coeff (n + j) w : ℚ) : ℂ)‖ ≤ C₀ * 4 ^ (n + j) := hw (n + j)
    _ = (C₀ * 4 ^ j) * 4 ^ n := by rw [pow_add]; ring

/-- The pure series `B₁,…,B₇` satisfy the `(1/5)^k`-rate bound. -/
private lemma pureB_rate_bound (i : Fin 7) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDTPlan.pureB i) : ℚ) : ℂ)‖ * (1 / 5 : ℝ) ^ k ≤ C' := by
  obtain ⟨D, hD, hDb⟩ := Work.C17I.pureB_coeff_bound i
  exact ⟨D, hD, fun k => bound_of_rate (le_of_lt hD) (by norm_num) (by norm_num) k (hDb k)⟩

/-! ## The seventeen coefficient bounds -/

/-- Coefficient bounds at rate `1/5` for the seventeen series of Theorem C (`Submission.CDTPlan.seventeen`).

`seventeen m n ra rb rab r0 : Fin 17 → ℚ⟦y⟧` is `B₁,…,B₅, G, G', G'', G''', B₆, B₇, ∫yG, ∫G,
∫(G-jet₁)/y, …, ∫(G-jet₄)/y⁴` with `G = Sym⁺(logP a b ra rb rab r0)`, `a = aOf m`, `b = aOf n`
(see `Submission.CDTPlan.InterfacesC`: `PC`, `GC`, `dY`, `intY`, `tq`).

Ingredients, all previously proved and all in this workspace:
* `Work.C17I.pureB_coeff_bound (i : Fin 7)` : `∃ C, 0 < C ∧ ∀ n, ‖coeff_n (pureB i)‖ ≤ C * 2^n`,
  and `2^n (1/5)^n = (2/5)^n ≤ 1`, so the same constant works for entries `0..4, 9, 10`;
* `Work.C17I.sympSym_deriv_coeff_bound` with `C₀ = C`, `ρ₀ = 6/5 ≤ 5/4`: for each `k ≤ 3`,
  `∃ C, 0 < C ∧ ∀ n, ‖coeff_n (((PowerSeries.derivative (R := ℚ))^[k]) (sympSym P))‖ ≤ C * 4^n`, and
  `4^n (1/5)^n = (4/5)^n ≤ 1`, so the same constant works for entries `5..8`
  (note `seventeen … 5 = GC = sympSym (PC …)`, `PC m n … = logP (2m+1) (2n+1) … = logP (aOf m) (aOf n) …`,
  and entries `6,7,8` are the `dY`-iterates `((PowerSeries.derivative (R := ℚ))^[k]) G`, `k = 1,2,3`);
* the six integral entries: `intY`/`tq` are `PowerSeries.mk`-defined, giving
  `coeff_k (intY w) = if k = 0 then 0 else coeff_{k-1} w / k` and `coeff_k (tq j w) = coeff_{k+j} w`;
  from a bound `‖coeff_n w‖ ≤ C₀ 4^n` this yields `‖coeff_k (intY w)‖ ≤ C₀ 4^k`,
  `‖coeff_k (intY (X*w))‖ ≤ C₀ 4^k` and `‖coeff_k (intY (tq j w))‖ ≤ 64 C₀ 4^k` for `j ≤ 4`
  (entries `11..16`). -/
theorem seventeen_coeff_bounds (m n : ℕ) (ra rb rab r0 : ℤ) {C : ℝ} (hC : 0 < C)
    (hP : ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) : ℚ) : ℂ)‖
        ≤ C * (6 / 5 : ℝ) ^ k) :
    ∀ i : Fin 17, ∃ C' : ℝ, 0 < C' ∧ ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDTPlan.seventeen m n ra rb rab r0 i) : ℚ) : ℂ)‖
        * (1 / 5 : ℝ) ^ k ≤ C' := by
  -- the hypothesis, transported to `PC`
  have hPC : ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDTPlan.PC m n ra rb rab r0) : ℚ) : ℂ)‖
        ≤ C * (6 / 5 : ℝ) ^ k := by
    intro k
    rw [PC_eq_aOf]
    exact hP k
  -- the derivative bounds for `G`
  have hsymp : ∀ j : ℕ, j ≤ 3 → ∃ D : ℝ, 0 < D ∧ ∀ t : ℕ,
      ‖((PowerSeries.coeff t (((PowerSeries.derivative (R := ℚ))^[j])
        (Submission.CDT.sympSym (Submission.CDTPlan.PC m n ra rb rab r0))) : ℚ) : ℂ)‖ ≤ D * 4 ^ t :=
    fun j hj => Work.C17I.sympSym_deriv_coeff_bound (P := Submission.CDTPlan.PC m n ra rb rab r0)
      hC (by norm_num) (by norm_num) hPC j hj
  obtain ⟨D₀, hD₀, hD₀b⟩ := hsymp 0 (by norm_num)
  have hG : ∀ t : ℕ,
      ‖((PowerSeries.coeff t (Submission.CDTPlan.GC m n ra rb rab r0) : ℚ) : ℂ)‖ ≤ D₀ * 4 ^ t := by
    intro t
    simpa [Submission.CDTPlan.GC] using hD₀b t
  obtain ⟨D₁, hD₁, hD₁b⟩ := hsymp 1 (by norm_num)
  have hG1 : ∀ t : ℕ, ‖((PowerSeries.coeff t
      (Submission.CDTPlan.dY (Submission.CDTPlan.GC m n ra rb rab r0)) : ℚ) : ℂ)‖
        ≤ D₁ * 4 ^ t := by
    intro t
    simpa [Submission.CDTPlan.GC, Submission.CDTPlan.dY] using hD₁b t
  obtain ⟨D₂, hD₂, hD₂b⟩ := hsymp 2 (by norm_num)
  have hG2 : ∀ t : ℕ, ‖((PowerSeries.coeff t
      (Submission.CDTPlan.dY (Submission.CDTPlan.dY (Submission.CDTPlan.GC m n ra rb rab r0))) : ℚ) : ℂ)‖
        ≤ D₂ * 4 ^ t := by
    intro t
    simpa [Submission.CDTPlan.GC, Submission.CDTPlan.dY] using hD₂b t
  obtain ⟨D₃, hD₃, hD₃b⟩ := hsymp 3 (by norm_num)
  have hG3 : ∀ t : ℕ, ‖((PowerSeries.coeff t
      (Submission.CDTPlan.dY (Submission.CDTPlan.dY (Submission.CDTPlan.dY
        (Submission.CDTPlan.GC m n ra rb rab r0)))) : ℚ) : ℂ)‖
        ≤ D₃ * 4 ^ t := by
    intro t
    simpa [Submission.CDTPlan.GC, Submission.CDTPlan.dY] using hD₃b t
  intro i
  fin_cases i <;>
    simp only [Submission.CDTPlan.seventeen, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact pureB_rate_bound 0
  · exact pureB_rate_bound 1
  · exact pureB_rate_bound 2
  · exact pureB_rate_bound 3
  · exact pureB_rate_bound 4
  · exact ⟨D₀, hD₀, fun k => bound_of_rate (le_of_lt hD₀) (by norm_num) (by norm_num) k (hG k)⟩
  · exact ⟨D₁, hD₁, fun k => bound_of_rate (le_of_lt hD₁) (by norm_num) (by norm_num) k (hG1 k)⟩
  · exact ⟨D₂, hD₂, fun k => bound_of_rate (le_of_lt hD₂) (by norm_num) (by norm_num) k (hG2 k)⟩
  · exact ⟨D₃, hD₃, fun k => bound_of_rate (le_of_lt hD₃) (by norm_num) (by norm_num) k (hG3 k)⟩
  · exact pureB_rate_bound 5
  · exact pureB_rate_bound 6
  · refine ⟨D₀, hD₀, fun k => intY_rate_bound (le_of_lt hD₀) (X_mul_rate (le_of_lt hD₀) hG) k⟩
  · exact ⟨D₀, hD₀, fun k => intY_rate_bound (le_of_lt hD₀) hG k⟩
  · exact ⟨D₀ * 4 ^ 1, by positivity,
      fun k => intY_rate_bound (by positivity) (tq_rate (le_of_lt hD₀) hG 1) k⟩
  · exact ⟨D₀ * 4 ^ 2, by positivity,
      fun k => intY_rate_bound (by positivity) (tq_rate (le_of_lt hD₀) hG 2) k⟩
  · exact ⟨D₀ * 4 ^ 3, by positivity,
      fun k => intY_rate_bound (by positivity) (tq_rate (le_of_lt hD₀) hG 3) k⟩
  · exact ⟨D₀ * 4 ^ 4, by positivity,
      fun k => intY_rate_bound (by positivity) (tq_rate (le_of_lt hD₀) hG 4) k⟩

end

end Work.C17I
