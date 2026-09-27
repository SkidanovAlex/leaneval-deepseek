import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.eq_endgame_defs

/-!
# The endgame contradiction, top level

`Work.EQ.eq_endgame_top`.  Let `λ = eqLam a = (1-a)/(1+a)` for `0 < a < 1`, let `D` be a
polynomial over `ℂ` of degree at least `3`, and suppose the polynomial identity

`(D(u/λ) - D(u)/λ)² (λD(u) - D(λu))² = a² (c²u² + D(u)²) (λD(u/λ) - D(λu)/λ)²`

holds for all `u : ℂ` (this is Rychlik's cleared germ identity after the reduction of the
rational germ `h = cX/D`).  Then `False`.

The proof is a leading-coefficient comparison.  With `n = D.natDegree`, `d = D.leadingCoeff`
and `L = (eqLam a : ℂ)`, the four polynomials `eP, eQ, eR, eE` of `eq_endgame_defs` all have
`natDegree` `n, n, n, 2n` and leading coefficients

`d(L⁻¹ⁿ - L⁻¹)`, `d(L - Lⁿ)`, `d(L L⁻¹ⁿ - L⁻¹ Lⁿ)`, `d²`.

Comparing the coefficient of `X^{4n}` gives

`(L⁻¹ⁿ - L⁻¹)² (L - Lⁿ)² = a² (L L⁻¹ⁿ - L⁻¹ Lⁿ)²`,

which, with `t = Lⁿ⁻¹`, is equivalent to `(1-t)² = a²(1+t)²`, hence to `Lⁿ⁻¹ = λ`; but
`a(1+λ) = 1-λ` forces `λⁿ⁻² = 1`, impossible for `0 < λ < 1` and `n ≥ 3`.
-/

namespace Work.EQ

open Polynomial

/-- For `0 < λ < 1` (here `λ = eqLam a`) no positive power equals `1`. -/
private lemma lamC_pow_ne_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {m : ℕ} (hm : 1 ≤ m) :
    (eqLam a : ℂ) ^ m ≠ 1 := by
  intro hc
  have hcast : ((eqLam a ^ m : ℝ) : ℂ) = (1:ℂ) := by rw [Complex.ofReal_pow]; exact hc
  have hr : eqLam a ^ m = 1 := Complex.ofReal_injective hcast
  have hlt : eqLam a ^ m < 1 :=
    pow_lt_one₀ (le_of_lt (endgame_lam_pos ha0 ha1)) (endgame_lam_lt_one ha0 ha1) (by omega)
  linarith

private lemma lamC_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : (eqLam a : ℂ) ≠ 0 := by
  rw [Complex.ofReal_ne_zero]; exact ne_of_gt (endgame_lam_pos ha0 ha1)

private lemma eP_ne {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℕ} (hn : 2 ≤ n) :
    ((eqLam a : ℂ)⁻¹ ^ n - (eqLam a : ℂ)⁻¹) ≠ 0 := by
  intro h
  have hL0 := lamC_ne_zero ha0 ha1
  have key : ((eqLam a : ℂ)) ^ n * ((eqLam a : ℂ)⁻¹ ^ n - (eqLam a : ℂ)⁻¹) = 0 := by
    rw [h, mul_zero]
  rw [mul_sub, ← mul_pow, mul_inv_cancel₀ hL0, one_pow] at key
  have key2 : (eqLam a : ℂ) ^ n * (eqLam a : ℂ)⁻¹ = 1 := (sub_eq_zero.mp key).symm
  have key3 : (eqLam a : ℂ) ^ (n - 1) = 1 := by
    rw [show n = (n - 1) + 1 by omega, pow_succ] at key2
    rw [mul_assoc, mul_inv_cancel₀ hL0, mul_one] at key2
    exact key2
  exact lamC_pow_ne_one ha0 ha1 (by omega) key3

private lemma eQ_ne {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℕ} (hn : 2 ≤ n) :
    ((eqLam a : ℂ) - (eqLam a : ℂ) ^ n) ≠ 0 := by
  intro h
  have hL0 := lamC_ne_zero ha0 ha1
  have h1 : (eqLam a : ℂ) = (eqLam a : ℂ) ^ n := sub_eq_zero.mp h
  have h2 : (eqLam a : ℂ) ^ (n - 1) = 1 := by
    rw [show n = (n - 1) + 1 by omega, pow_succ] at h1
    have : (1:ℂ) * (eqLam a : ℂ) = (eqLam a : ℂ) ^ (n - 1) * (eqLam a : ℂ) := by
      rw [one_mul]; exact h1
    exact (mul_right_cancel₀ hL0 this).symm
  exact lamC_pow_ne_one ha0 ha1 (by omega) h2

private lemma eR_ne {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℕ} (hn : 2 ≤ n) :
    ((eqLam a : ℂ) * (eqLam a : ℂ)⁻¹ ^ n - (eqLam a : ℂ)⁻¹ * (eqLam a : ℂ) ^ n) ≠ 0 := by
  intro h
  set L : ℂ := (eqLam a : ℂ) with hLdef
  have hL0 : L ≠ 0 := lamC_ne_zero ha0 ha1
  have hn1 : n = (n - 1) + 1 := by omega
  have h1 : L * L⁻¹ ^ n = L⁻¹ ^ (n - 1) := by
    have hpow : L⁻¹ ^ n = L⁻¹ * L⁻¹ ^ (n - 1) := by
      conv_lhs => rw [hn1]
      rw [pow_succ']
    rw [hpow, ← mul_assoc, mul_inv_cancel₀ hL0, one_mul]
  have h2 : L⁻¹ * L ^ n = L ^ (n - 1) := by
    have hpow : L ^ n = L * L ^ (n - 1) := by
      conv_lhs => rw [hn1]
      rw [pow_succ']
    rw [hpow, ← mul_assoc, inv_mul_cancel₀ hL0, one_mul]
  have h3 : L⁻¹ ^ (n - 1) = L ^ (n - 1) := by
    rw [← h1, ← h2]; exact sub_eq_zero.mp h
  have h4 : L⁻¹ ^ (n - 1) * L ^ (n - 1) = L ^ (n - 1) * L ^ (n - 1) := by rw [h3]
  rw [← mul_pow, inv_mul_cancel₀ hL0, one_pow] at h4
  rw [← pow_add, show (n - 1) + (n - 1) = 2 * n - 2 by omega] at h4
  exact (lamC_pow_ne_one ha0 ha1 (m := 2*n-2) (by omega)) h4.symm

private lemma natDegree_eP {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : Polynomial ℂ}
    (hn : 3 ≤ D.natDegree) : (eP (eqLam a : ℂ) D).natDegree = D.natDegree := by
  have hD : D ≠ 0 := by intro h; rw [h] at hn; simp at hn
  have hle : (eP (eqLam a : ℂ) D).natDegree ≤ D.natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_eP, Polynomial.coeff_eq_zero_of_natDegree_lt hN, zero_mul]
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle ?_
  rw [coeff_eP]
  exact mul_ne_zero (by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hD)
    (eP_ne ha0 ha1 (by omega))

private lemma natDegree_eQ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : Polynomial ℂ}
    (hn : 3 ≤ D.natDegree) : (eQ (eqLam a : ℂ) D).natDegree = D.natDegree := by
  have hD : D ≠ 0 := by intro h; rw [h] at hn; simp at hn
  have hle : (eQ (eqLam a : ℂ) D).natDegree ≤ D.natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_eQ, Polynomial.coeff_eq_zero_of_natDegree_lt hN, zero_mul]
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle ?_
  rw [coeff_eQ]
  exact mul_ne_zero (by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hD)
    (eQ_ne ha0 ha1 (by omega))

private lemma natDegree_eR {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : Polynomial ℂ}
    (hn : 3 ≤ D.natDegree) : (eR (eqLam a : ℂ) D).natDegree = D.natDegree := by
  have hD : D ≠ 0 := by intro h; rw [h] at hn; simp at hn
  have hle : (eR (eqLam a : ℂ) D).natDegree ≤ D.natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_eR, Polynomial.coeff_eq_zero_of_natDegree_lt hN, zero_mul]
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle ?_
  rw [coeff_eR]
  exact mul_ne_zero (by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hD)
    (eR_ne ha0 ha1 (by omega))

private lemma leadingCoeff_eP {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : Polynomial ℂ}
    (hn : 3 ≤ D.natDegree) :
    (eP (eqLam a : ℂ) D).leadingCoeff
      = D.leadingCoeff * ((eqLam a : ℂ)⁻¹ ^ D.natDegree - (eqLam a : ℂ)⁻¹) := by
  rw [← Polynomial.coeff_natDegree, natDegree_eP ha0 ha1 hn, coeff_eP, Polynomial.coeff_natDegree]

private lemma leadingCoeff_eQ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : Polynomial ℂ}
    (hn : 3 ≤ D.natDegree) :
    (eQ (eqLam a : ℂ) D).leadingCoeff
      = D.leadingCoeff * ((eqLam a : ℂ) - (eqLam a : ℂ) ^ D.natDegree) := by
  rw [← Polynomial.coeff_natDegree, natDegree_eQ ha0 ha1 hn, coeff_eQ, Polynomial.coeff_natDegree]

private lemma leadingCoeff_eR {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {D : Polynomial ℂ}
    (hn : 3 ≤ D.natDegree) :
    (eR (eqLam a : ℂ) D).leadingCoeff
      = D.leadingCoeff * ((eqLam a : ℂ) * (eqLam a : ℂ)⁻¹ ^ D.natDegree
          - (eqLam a : ℂ)⁻¹ * (eqLam a : ℂ) ^ D.natDegree) := by
  rw [← Polynomial.coeff_natDegree, natDegree_eR ha0 ha1 hn, coeff_eR, Polynomial.coeff_natDegree]

private lemma natDegree_eE {c : ℂ} {D : Polynomial ℂ} (hn : 3 ≤ D.natDegree) :
    (eE c D).natDegree = 2 * D.natDegree := by
  have hbound : (Polynomial.C (c^2) * Polynomial.X^2 : Polynomial ℂ).natDegree ≤ 2 := by
    calc _ ≤ (Polynomial.C (c^2) : Polynomial ℂ).natDegree + (Polynomial.X^2).natDegree :=
          Polynomial.natDegree_mul_le
      _ = 0 + 2 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
      _ = 2 := by norm_num
  have hlt : (Polynomial.C (c^2) * Polynomial.X^2 : Polynomial ℂ).natDegree < (D^2).natDegree := by
    rw [Polynomial.natDegree_pow]; omega
  rw [eE, Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt, Polynomial.natDegree_pow]

private lemma leadingCoeff_eE {c : ℂ} {D : Polynomial ℂ} (hn : 3 ≤ D.natDegree) :
    (eE c D).leadingCoeff = D.leadingCoeff ^ 2 := by
  rw [← Polynomial.coeff_natDegree, natDegree_eE (c := c) hn]
  rw [eE, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
  rw [mul_zero, zero_add]
  have hh : (D^2).coeff (2 * D.natDegree) = (D^2).leadingCoeff := by
    rw [← Polynomial.natDegree_pow]; exact Polynomial.coeff_natDegree
  rw [hh, Polynomial.leadingCoeff_pow]

/-- Leading-coefficient comparison of the endgame polynomial identity: the numeric relation
forced on `L = eqLam a`. -/
private lemma endgame_lead_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {c : ℂ} {D : Polynomial ℂ}
    (hn : 3 ≤ D.natDegree)
    (hpoly : eP (eqLam a : ℂ) D ^ 2 * eQ (eqLam a : ℂ) D ^ 2
        = Polynomial.C ((a:ℂ)^2) * eE c D * eR (eqLam a : ℂ) D ^ 2) :
    ((eqLam a : ℂ)⁻¹ ^ D.natDegree - (eqLam a : ℂ)⁻¹) ^ 2 *
        ((eqLam a : ℂ) - (eqLam a : ℂ) ^ D.natDegree) ^ 2
      = (a : ℂ) ^ 2 *
        ((eqLam a : ℂ) * (eqLam a : ℂ)⁻¹ ^ D.natDegree -
          (eqLam a : ℂ)⁻¹ * (eqLam a : ℂ) ^ D.natDegree) ^ 2 := by
  have hD : D ≠ 0 := by intro h; rw [h] at hn; simp at hn
  have hd : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD
  have key := congrArg Polynomial.leadingCoeff hpoly
  simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_C] at key
  rw [leadingCoeff_eP ha0 ha1 hn, leadingCoeff_eQ ha0 ha1 hn,
      leadingCoeff_eE (c := c) hn, leadingCoeff_eR ha0 ha1 hn] at key
  have hd4 : D.leadingCoeff ^ 4 ≠ 0 := pow_ne_zero 4 hd
  exact mul_left_cancel₀ hd4 (by linear_combination key)

/-- Field algebra: `(L⁻¹(t⁻¹-1))² (L(1-t))² = a²(t⁻¹-t)²` forces `(1-t)² = a²(1+t)²`. -/
private lemma alg_core {L a t : ℂ} (hL : L ≠ 0) (ht : t ≠ 0) (h1t : 1 - t ≠ 0)
    (h : (L⁻¹ * (t⁻¹ - 1))^2 * (L * (1 - t))^2 = a^2 * (t⁻¹ - t)^2) :
    (1 - t)^2 = a^2 * (1+t)^2 := by
  have h1 := h
  field_simp at h1
  ring_nf at h1
  have hfac : (1 - t) ^ 2 * ((1 - t) ^ 2 - a ^ 2 * (1 + t) ^ 2) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.mp hfac with h2 | h2
  · exact absurd h2 (pow_ne_zero 2 h1t)
  · exact sub_eq_zero.mp h2

/-- The numeric relation of `endgame_lead_eq` is impossible for `n ≥ 3`. -/
private lemma endgame_alg_false {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℕ} (hn : 3 ≤ n)
    (h : ((eqLam a : ℂ)⁻¹ ^ n - (eqLam a : ℂ)⁻¹) ^ 2 *
          ((eqLam a : ℂ) - (eqLam a : ℂ) ^ n) ^ 2
        = (a : ℂ) ^ 2 *
          ((eqLam a : ℂ) * (eqLam a : ℂ)⁻¹ ^ n -
            (eqLam a : ℂ)⁻¹ * (eqLam a : ℂ) ^ n) ^ 2) : False := by
  set L : ℂ := (eqLam a : ℂ) with hLdef
  set t : ℂ := L ^ (n-1) with htdef
  have hL0 : L ≠ 0 := lamC_ne_zero ha0 ha1
  have hn1 : n = (n-1) + 1 := by omega
  have hA : L⁻¹ ^ n - L⁻¹ = L⁻¹ * (t⁻¹ - 1) := by
    have e : L⁻¹ ^ n = L⁻¹ * t⁻¹ := by
      rw [hn1, pow_succ', inv_pow, ← htdef]
    rw [e]; ring
  have hB : L - L ^ n = L * (1 - t) := by
    have e : L ^ n = L * t := by
      rw [hn1, pow_succ', ← htdef]
    rw [e]; ring
  have hC : L * L⁻¹ ^ n - L⁻¹ * L ^ n = t⁻¹ - t := by
    have e1 : L * L⁻¹ ^ n = t⁻¹ := by
      rw [hn1, pow_succ', ← mul_assoc, mul_inv_cancel₀ hL0, one_mul, inv_pow, ← htdef]
    have e2 : L⁻¹ * L ^ n = t := by
      rw [hn1, pow_succ', ← mul_assoc, inv_mul_cancel₀ hL0, one_mul, ← htdef]
    rw [e1, e2]
  have ht0 : t ≠ 0 := by rw [htdef]; exact pow_ne_zero _ hL0
  have h1t : 1 - t ≠ 0 := by
    rw [sub_ne_zero, htdef]
    intro hc
    exact (lamC_pow_ne_one ha0 ha1 (m := n-1) (by omega)) hc.symm
  have h' : (L⁻¹ * (t⁻¹ - 1))^2 * (L * (1 - t))^2 = (a:ℂ)^2 * (t⁻¹ - t)^2 := by
    rw [hA, hB, hC] at h
    exact h
  have hmain : (1 - t)^2 = (a:ℂ)^2 * (1+t)^2 := alg_core hL0 ht0 h1t h'
  have hfac : (1 - t - (a:ℂ)*(1+t)) * (1 - t + (a:ℂ)*(1+t)) = 0 := by
    have hsq : (1-t)^2 - ((a:ℂ)*(1+t))^2 = 0 := by rw [hmain]; ring
    linear_combination hsq
  have hrel : (a:ℂ)*(1+L) = 1 - L := by
    have := endgame_lam_rel ha0
    rwa [← hLdef] at this
  rcases mul_eq_zero.mp hfac with hcase | hcase
  · have h1 : 1 - t = (a:ℂ)*(1+t) := by linear_combination hcase
    have key : (1 + (a:ℂ)) * (L - t) = 0 := by
      linear_combination h1 + hrel
    have h1a : (1 + (a:ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.ofReal_ne_zero]; linarith
    have hLt : L = t := by
      rcases mul_eq_zero.mp key with hh | hh
      · exact absurd hh h1a
      · exact sub_eq_zero.mp hh
    have hLpow : L ^ (n-1) = L := by rw [← htdef]; exact hLt.symm
    have : L ^ (n-2) = 1 := by
      have hn2 : n - 1 = (n-2) + 1 := by omega
      rw [hn2, pow_succ'] at hLpow
      have hh : (1:ℂ) * L = L^(n-2) * L := by rw [one_mul, mul_comm]; exact hLpow.symm
      exact (mul_right_cancel₀ hL0 hh).symm
    exact (lamC_pow_ne_one ha0 ha1 (m := n-2) (by omega)) this
  · have h1 : 1 - t = -((a:ℂ)*(1+t)) := by linear_combination hcase
    have key : (1-t)*(1+L) + (1-L)*(1+t) = 0 := by
      linear_combination (1+L)*h1 - (1+t)*hrel
    have key2 : t*L = 1 := by
      have : 2 - 2*(t*L) = 0 := by linear_combination key
      linear_combination (-1/2 : ℂ) * this
    have hLn : L ^ n = 1 := by
      have e : L ^ n = L * t := by rw [hn1, pow_succ', ← htdef]
      rw [e, mul_comm L t, key2]
    exact (lamC_pow_ne_one ha0 ha1 (m := n) (by omega)) hLn

theorem eq_endgame_top {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {c : ℂ} {D : Polynomial ℂ}
    (hEND : ∀ u : ℂ,
      (Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) D - Polynomial.eval u D / (Work.EQ.eqLam a : ℂ)) ^ 2 *
        ((Work.EQ.eqLam a : ℂ) * Polynomial.eval u D - Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) D) ^ 2
      = ((a : ℂ)) ^ 2 * (c ^ 2 * u ^ 2 + Polynomial.eval u D ^ 2) *
        ((Work.EQ.eqLam a : ℂ) * Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) D -
          Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) D / (Work.EQ.eqLam a : ℂ)) ^ 2)
    (hn : 3 ≤ D.natDegree) : False :=
  endgame_alg_false ha0 ha1 hn (endgame_lead_eq ha0 ha1 hn (endgame_poly_identity hEND))

end Work.EQ
