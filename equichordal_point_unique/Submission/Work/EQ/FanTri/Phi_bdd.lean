import Mathlib
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.walk_bounds
import Submission.Work.EQ.FanSep.centre_numbers

namespace Work.EQ.FanTri

/-- The distance from the state-`j` centre to `O₁ = -a/2` grows at least linearly:
`j + (1-a)/2 ≤ stQ a j`.  (For even `j` this is an equality, for odd `j` it is strict.) -/
lemma stQ_ge_lin {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℕ) :
    (j : ℝ) + (1 - a) / 2 ≤ stQ a j := by
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k = 2 * k from by omega, wb_stQ_two_mul ha1 k]
    push_cast
    linarith
  · subst hk
    rw [wb_stQ_two_mul_add_one ha0 k]
    push_cast
    linarith

/-- Each upward step weight is bounded by `eqLam a * (1 + 1/(j + (1-a)/2))`. -/
lemma upW_le_lin {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℕ) :
    upW a j ≤ eqLam a * (1 + 1 / ((j : ℝ) + (1 - a) / 2)) := by
  have hm0 : 0 < (1 - a) / 2 := by linarith
  have hj : 0 < (j : ℝ) + (1 - a) / 2 := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hq := stQ_ge_lin ha0 ha1 j
  have hL : 0 ≤ eqLam a := le_of_lt (eqLam_pos' ha0 ha1)
  rw [upW]
  apply mul_le_mul_of_nonneg_left _ hL
  have hle : 1 / stQ a j ≤ 1 / ((j : ℝ) + (1 - a) / 2) :=
    one_div_le_one_div_of_le hj hq
  linarith

/-- **The potential is dominated by a geometric times linear factor.**
`Phi a n = ∏_{j<n} upW a j ≤ eqLam a ^ n * ((n + (1-a)/2)/((1-a)/2))`: the factors
`1 + 1/stQ a j ≤ 1 + 1/(j + (1-a)/2)` telescope. -/
lemma Phi_le_geom {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    Phi a n ≤ eqLam a ^ n * (((n : ℝ) + (1 - a) / 2) / ((1 - a) / 2)) := by
  have hm0 : 0 < (1 - a) / 2 := by linarith
  have hmne : (1 - a) / 2 ≠ 0 := ne_of_gt hm0
  have hLp : 0 < eqLam a := eqLam_pos' ha0 ha1
  induction n with
  | zero =>
    rw [wb_Phi_zero, pow_zero, one_mul]
    simp only [Nat.cast_zero, zero_add]
    exact le_of_eq (div_self hmne).symm
  | succ n ih =>
    rw [wb_Phi_succ]
    have hup := upW_le_lin ha0 ha1 n
    have hupnn : 0 ≤ upW a n := le_of_lt (wb_upW_pos ha0 ha1 n)
    have hRnn : 0 ≤ eqLam a ^ n * (((n : ℝ) + (1 - a) / 2) / ((1 - a) / 2)) :=
      mul_nonneg (pow_nonneg (le_of_lt hLp) n)
        (div_nonneg (by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
          (le_of_lt hm0))
    have h1 := mul_le_mul ih hup hupnn hRnn
    refine le_trans h1 ?_
    have hnc : (n : ℝ) + (1 - a) / 2 ≠ 0 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      positivity
    have h2 : (((n : ℝ) + (1 - a) / 2) / ((1 - a) / 2)) *
          (1 + 1 / ((n : ℝ) + (1 - a) / 2))
        = ((n : ℝ) + 1 + (1 - a) / 2) / ((1 - a) / 2) := by
      rw [div_mul_eq_mul_div, mul_add, mul_one, mul_one_div, div_self hnc]
      ring_nf
    refine le_of_eq ?_
    rw [pow_succ]
    push_cast
    rw [← h2]
    ring

/-- For `0 < L < 1` and every `n`, `n * L^n ≤ L/(1-L)` (Bernoulli's inequality). -/
lemma n_mul_pow_le {L : ℝ} (hL0 : 0 < L) (hL1 : L < 1) (n : ℕ) :
    (n : ℝ) * L ^ n ≤ L / (1 - L) := by
  have h1L : 0 < 1 - L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL0
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, zero_mul]
    exact div_nonneg (le_of_lt hL0) (le_of_lt h1L)
  · have hc : -2 ≤ 1 / L - 1 := by
      have : 0 < 1 / L := by positivity
      linarith
    have hbern := one_add_mul_le_pow (a := 1 / L - 1) hc n
    have hone : (1 : ℝ) + (1 / L - 1) = 1 / L := by ring
    rw [hone] at hbern
    have hpow : L ^ n * (1 / L) ^ n = 1 := by
      rw [← mul_pow, mul_one_div, div_self hLne, one_pow]
    have hmult := mul_le_mul_of_nonneg_left hbern (le_of_lt (pow_pos hL0 n))
    rw [hpow] at hmult
    have hkey : (n : ℝ) * (1 - L) * L ^ n ≤ L := by
      have heq : L ^ n * (1 + (n : ℝ) * (1 / L - 1)) =
          L ^ n + (n : ℝ) * (1 / L - 1) * L ^ n := by ring
      have h1 : (n : ℝ) * (1 / L - 1) * L ^ n ≤ 1 := by
        have hnn : 0 ≤ L ^ n := le_of_lt (pow_pos hL0 n)
        nlinarith [hmult, heq, hnn]
      have heq2 : (n : ℝ) * (1 / L - 1) * L ^ n = (n : ℝ) * (1 - L) * L ^ n / L := by
        field_simp
      rw [heq2, div_le_iff₀ hL0] at h1
      simpa using h1
    rw [le_div_iff₀ h1L]
    have : (n : ℝ) * L ^ n * (1 - L) = (n : ℝ) * (1 - L) * L ^ n := by ring
    rw [this]
    exact hkey

/-- **The geometric-times-linear sequence is uniformly bounded.**
For `0 < a < 1` and every `n`, with `L = eqLam a` and `m = (1-a)/2`,
`L^n * ((n+m)/m) ≤ 1/a + 1`. -/
lemma geom_seq_bdd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    eqLam a ^ n * (((n : ℝ) + (1 - a) / 2) / ((1 - a) / 2)) ≤ 1 / a + 1 := by
  have hL0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hL1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hm0 : 0 < (1 - a) / 2 := by linarith
  have hmne : (1 - a) / 2 ≠ 0 := ne_of_gt hm0
  have hnm : (n : ℝ) * eqLam a ^ n ≤ eqLam a / (1 - eqLam a) := n_mul_pow_le hL0 hL1 n
  have hpow1 : eqLam a ^ n ≤ 1 := pow_le_one₀ (le_of_lt hL0) (le_of_lt hL1)
  have hdiv : (n : ℝ) * eqLam a ^ n / ((1 - a) / 2) ≤
      (eqLam a / (1 - eqLam a)) / ((1 - a) / 2) :=
    div_le_div_of_nonneg_right hnm (le_of_lt hm0)
  have hfinal : (eqLam a / (1 - eqLam a)) / ((1 - a) / 2) = 1 / a := by
    rw [eqLam_div_one_sub ha0 ha1]
    have ha : (a : ℝ) ≠ 0 := ne_of_gt ha0
    have h1a : (1 : ℝ) - a ≠ 0 := by linarith
    field_simp
  have hstep : eqLam a ^ n * (((n : ℝ) + (1 - a) / 2) / ((1 - a) / 2)) =
      (n : ℝ) * eqLam a ^ n / ((1 - a) / 2) + eqLam a ^ n := by
    rw [add_div, div_self hmne]
    ring
  rw [hstep]
  calc
    (n : ℝ) * eqLam a ^ n / ((1 - a) / 2) + eqLam a ^ n
        ≤ (eqLam a / (1 - eqLam a)) / ((1 - a) / 2) + 1 := add_le_add hdiv hpow1
    _ = 1 / a + 1 := by rw [hfinal]

/-- **The potential `Phi` is bounded.**  `Phi a n = ∏_{j<n} upW a j` with
`upW a j = eqLam a * (1 + 1 / stQ a j)`, `stQ a j = |stCtr j + a/2|`: since `stQ a j ≥ (1-a)/2`
and `stQ` grows linearly in `j`, the product grows at most like `n` while `eqLam a ^ n` decays
geometrically, so `Phi a` is bounded. -/
theorem Phi_bdd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, Work.EQ.Phi a n ≤ C := by
  refine ⟨1 / a + 1, ?_, ?_⟩
  · have : 0 < 1 / a := one_div_pos.mpr ha0
    linarith
  · intro n
    exact le_trans (Phi_le_geom ha0 ha1 n) (geom_seq_bdd ha0 ha1 n)

end Work.EQ.FanTri
