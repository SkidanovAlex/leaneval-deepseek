import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17I.seventeen_coeff_bounds
import Submission.Work.C17I.sympSym_deriv_coeff_bound
import Submission.Work.C17I.pureB_coeff_bound

set_option linter.unusedSimpArgs false

namespace Work.C17I

open PowerSeries

noncomputable section

/-! ### Toolbox

The sibling theorem `Work.C17I.seventeen_coeff_bounds` proves the *rate* `1/5` version of these
bounds, i.e. `‖[yᵏ]fᵢ‖ ≤ C' · 5ᵏ`.  The present statement asks for a strictly *sharper* radius:
`∃ R > 1/5` with `‖[yᵏ]fᵢ‖ Rᵏ ≤ C'`, i.e. a growth rate `< 5`.  This does **not** follow from the
rate-`1/5` statement (which is compatible with coefficients `5ᵏ`), so the proof below re-runs the
analysis of `seventeen_coeff_bounds` but keeps the *actual* rate `4` produced by the ingredients
(`pureB_coeff_bound` gives rate `2`, `sympSym_deriv_coeff_bound` and the formal integrations give
rate `4`), and then converts rate `4` into radius `R = 1/4 > 1/5`. -/

/-- `PC` is `logP` evaluated at the odd integers `a = 2m+1`, `b = 2n+1`. -/
private lemma PC_eq_aOf (m n : ℕ) (ra rb rab r0 : ℤ) :
    Submission.CDTPlan.PC m n ra rb rab r0
      = Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 := by
  simp only [Submission.CDTPlan.PC, Work.C17.aOf]

/-- A coefficient bound of rate `4` yields the sharp radius bound with `R = 1/4 > 1/5`. -/
private lemma sharp_of_rate4 {w : PowerSeries ℚ} {D : ℝ} (hD : 0 < D)
    (h : ∀ k : ℕ, ‖((PowerSeries.coeff k w : ℚ) : ℂ)‖ ≤ D * 4 ^ k) :
    ∃ C' R : ℝ, 0 < C' ∧ (1 : ℝ) / 5 < R ∧ R ≤ 1 ∧ ∀ k : ℕ,
      ‖((PowerSeries.coeff k w : ℚ) : ℂ)‖ * R ^ k ≤ C' := by
  refine ⟨D, 1 / 4, hD, by norm_num, by norm_num, fun k => ?_⟩
  calc ‖((PowerSeries.coeff k w : ℚ) : ℂ)‖ * (1 / 4 : ℝ) ^ k
      ≤ (D * 4 ^ k) * (1 / 4 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (h k) (by positivity)
    _ = D := by rw [mul_assoc, ← mul_pow]; norm_num

/-- Existential wrapper around `sharp_of_rate4`. -/
private lemma sharp_of_rate4' {w : PowerSeries ℚ}
    (h : ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ, ‖((PowerSeries.coeff k w : ℚ) : ℂ)‖ ≤ D * 4 ^ k) :
    ∃ C' R : ℝ, 0 < C' ∧ (1 : ℝ) / 5 < R ∧ R ≤ 1 ∧ ∀ k : ℕ,
      ‖((PowerSeries.coeff k w : ℚ) : ℂ)‖ * R ^ k ≤ C' := by
  obtain ⟨D, hD, hb⟩ := h
  exact sharp_of_rate4 hD hb

/-- The seven pure series have rate-`2` coefficients, hence rate `4`. -/
private lemma pureB_rate4 (i : Fin 7) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      ‖((PowerSeries.coeff n (Submission.CDTPlan.pureB i) : ℚ) : ℂ)‖ ≤ D * 4 ^ n := by
  obtain ⟨C, hC, hb⟩ := Work.C17I.pureB_coeff_bound i
  refine ⟨C, hC, fun n => le_trans (hb n) ?_⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 4) n) (le_of_lt hC)

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

/-- `‖(k : ℚ) : ℂ‖ ≥ 1` for a positive natural number `k`. -/
private lemma norm_nat_cast_ge_one {k : ℕ} (hk : 0 < k) : (1 : ℝ) ≤ ‖((k : ℚ) : ℂ)‖ := by
  rw [Work.CPull.norm_rat_cast_complex]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k : ℚ) : ℝ))]
  have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  simpa using h1

/-- `X * w` inherits a rate-`4` bound. -/
private lemma X_mul_rate {w : PowerSeries ℚ} {D : ℝ} (hD : 0 < D)
    (hw : ∀ n : ℕ, ‖((PowerSeries.coeff n w : ℚ) : ℂ)‖ ≤ D * 4 ^ n) :
    ∀ n : ℕ, ‖((PowerSeries.coeff n (PowerSeries.X * w) : ℚ) : ℂ)‖ ≤ D * 4 ^ n := by
  intro n
  rw [coeff_X_mul]
  split_ifs with hn
  · subst hn
    simpa using mul_nonneg (le_of_lt hD) (by positivity : (0 : ℝ) ≤ 4 ^ 0)
  · calc ‖((PowerSeries.coeff (n - 1) w : ℚ) : ℂ)‖ ≤ D * 4 ^ (n - 1) := hw (n - 1)
      _ ≤ D * 4 ^ n := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega)) (le_of_lt hD)

/-- `tq j w` inherits a rate-`4` bound, with an extra factor `4 ^ j`. -/
private lemma tq_rate {w : PowerSeries ℚ} {D : ℝ} (hD : 0 < D)
    (hw : ∀ n : ℕ, ‖((PowerSeries.coeff n w : ℚ) : ℂ)‖ ≤ D * 4 ^ n) (j : ℕ) :
    ∀ n : ℕ, ‖((PowerSeries.coeff n (Submission.CDTPlan.tq j w) : ℚ) : ℂ)‖
      ≤ (D * 4 ^ j) * 4 ^ n := by
  intro n
  rw [coeff_tq_cast]
  calc ‖((PowerSeries.coeff (n + j) w : ℚ) : ℂ)‖ ≤ D * 4 ^ (n + j) := hw (n + j)
    _ = (D * 4 ^ j) * 4 ^ n := by rw [pow_add]; ring

/-- `intY` of a series satisfying a rate-`4` bound satisfies the same rate-`4` bound. -/
private lemma intY_rate {w : PowerSeries ℚ} {D : ℝ} (hD : 0 < D)
    (hw : ∀ n : ℕ, ‖((PowerSeries.coeff n w : ℚ) : ℂ)‖ ≤ D * 4 ^ n) (k : ℕ) :
    ‖((PowerSeries.coeff k (Submission.CDTPlan.intY w) : ℚ) : ℂ)‖ ≤ D * 4 ^ k := by
  rw [coeff_intY_cast]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [if_pos rfl]
    simpa using mul_nonneg (le_of_lt hD) (by positivity : (0 : ℝ) ≤ 4 ^ 0)
  · rw [if_neg (Nat.pos_iff_ne_zero.mp hk), norm_div]
    have hk1 : (1 : ℝ) ≤ ‖((k : ℚ) : ℂ)‖ := norm_nat_cast_ge_one hk
    have hkpos : (0 : ℝ) < ‖((k : ℚ) : ℂ)‖ := by linarith
    have hdiv : ‖((PowerSeries.coeff (k - 1) w : ℚ) : ℂ)‖ / ‖((k : ℚ) : ℂ)‖
        ≤ ‖((PowerSeries.coeff (k - 1) w : ℚ) : ℂ)‖ := by
      rw [div_le_iff₀ hkpos]
      nlinarith [norm_nonneg ((PowerSeries.coeff (k - 1) w : ℚ) : ℂ)]
    refine le_trans hdiv (le_trans (hw (k - 1)) (mul_le_mul_of_nonneg_left ?_ (le_of_lt hD)))
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega)

/-! ## The seventeen coefficient bounds at a sharp radius -/

theorem seventeen_coeff_bounds_sharp (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) (ra rb rab r0 : ℤ) {C : ℝ} (hC : 0 < C)
    (hP : ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) : ℚ) : ℂ)‖
        ≤ C * (6 / 5 : ℝ) ^ k) :
    ∀ i : Fin 17, ∃ C' R : ℝ, 0 < C' ∧ (1 : ℝ) / 5 < R ∧ R ≤ 1 ∧ ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDTPlan.seventeen m n ra rb rab r0 i) : ℚ) : ℂ)‖ * R ^ k ≤ C' := by
  -- the hypothesis, transported to `PC`
  have hPC : ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDTPlan.PC m n ra rb rab r0) : ℚ) : ℂ)‖
        ≤ C * (6 / 5 : ℝ) ^ k := by
    intro k
    rw [PC_eq_aOf]
    exact hP k
  -- the rate-4 bounds for `G` and its three `y`-derivatives
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
  · exact sharp_of_rate4' (pureB_rate4 0)
  · exact sharp_of_rate4' (pureB_rate4 1)
  · exact sharp_of_rate4' (pureB_rate4 2)
  · exact sharp_of_rate4' (pureB_rate4 3)
  · exact sharp_of_rate4' (pureB_rate4 4)
  · exact sharp_of_rate4' ⟨D₀, hD₀, hG⟩
  · exact sharp_of_rate4' ⟨D₁, hD₁, hG1⟩
  · exact sharp_of_rate4' ⟨D₂, hD₂, hG2⟩
  · exact sharp_of_rate4' ⟨D₃, hD₃, hG3⟩
  · exact sharp_of_rate4' (pureB_rate4 5)
  · exact sharp_of_rate4' (pureB_rate4 6)
  · exact sharp_of_rate4' ⟨D₀, hD₀, fun k => intY_rate hD₀ (X_mul_rate hD₀ hG) k⟩
  · exact sharp_of_rate4' ⟨D₀, hD₀, fun k => intY_rate hD₀ hG k⟩
  · exact sharp_of_rate4' ⟨D₀ * 4 ^ 1, by positivity,
      fun k => intY_rate (by positivity) (tq_rate hD₀ hG 1) k⟩
  · exact sharp_of_rate4' ⟨D₀ * 4 ^ 2, by positivity,
      fun k => intY_rate (by positivity) (tq_rate hD₀ hG 2) k⟩
  · exact sharp_of_rate4' ⟨D₀ * 4 ^ 3, by positivity,
      fun k => intY_rate (by positivity) (tq_rate hD₀ hG 3) k⟩
  · exact sharp_of_rate4' ⟨D₀ * 4 ^ 4, by positivity,
      fun k => intY_rate (by positivity) (tq_rate hD₀ hG 4) k⟩

end

end Work.C17I
