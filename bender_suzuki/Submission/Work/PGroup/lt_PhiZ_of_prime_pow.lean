import Mathlib
import Submission.Work.PGroup.Cyc2Defs
import Submission.Work.PGroup.expand_cyclotomic_eq_prod
import Submission.Work.PGroup.PhiZ_eval_lower
import Submission.Work.PGroup.PhiZ_eval_upper
import Submission.Work.PGroup.pow_arith

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `q < Φ_{D q^j}(2)` for `q` an odd prime and `D = ord_q(2)`

Let `q` be an odd prime and `D = orderOf (2 : ZMod q)`, i.e. the multiplicative order of `2`
modulo `q`.  For every `j ≥ 1` with `D * q^j ≠ 6` we show

  `q < Φ_{D q^j}(2)`   (`PhiZ (D * q^j)`).

## The argument

Write `n = D q^j`, `Ψ_D(M) = Φ_D(M) = (cyclotomic D ℤ).eval M`.

* From `Work.PGroup.expand_cyclotomic_eq_prod` together with `Polynomial.expand_eval`, the
  evaluation at `2` of the expand identity gives the exact product formula
  `Ψ_D(2^{q^j}) = ∏_{i ≤ j} PhiZ (D q^i)`, hence the *ratio identity*
  `PhiZ (D q^j) * Ψ_D(2^{q^{j-1}}) = Ψ_D(2^{q^j})`.
* Bounds on `Ψ_D` (delegated):
  `2^{(q^j-1)·φ(D)} < Ψ_D(2^{q^j})` (`PhiZ_eval_lower`) and
  `Ψ_D(2^{q^{j-1}}) < 2^{D q^{j-1}}` (`PhiZ_eval_upper`).
* Hence `q · Ψ_D(2^{q^{j-1}}) < Ψ_D(2^{q^j})` as soon as
  `q · 2^{D q^{j-1}} < 2^{(q^j-1)·φ(D)}` (`pow_arith`), and positivity of `Ψ_D(2^{q^{j-1}})`
  lets us cancel it to get `q < PhiZ (D q^j)`.

The hypothesis `D * q^j ≠ 6` is exactly the single case (`q = 3`, `D = 2`, `j = 1`) in which
`pow_arith` fails and in which in fact `Φ_6(2) = 3 = q`.
-/

namespace Work.PGroup

/-- The product formula for the cyclotomic value, obtained by evaluating the expand identity
`expand ℤ (q^j) (cyclotomic D ℤ) = ∏_{i ≤ j} cyclotomic (D q^i) ℤ` at `2`. -/
lemma eval_cyclotomic_prod {q D j : ℕ} (hq : q.Prime) (hDq : ¬ q ∣ D) :
    (Polynomial.cyclotomic D ℤ).eval ((2 : ℤ) ^ (q ^ j))
      = ∏ i ∈ Finset.range (j + 1), PhiZ (D * q ^ i) := by
  have h := expand_cyclotomic_eq_prod (q := q) (D := D) (j := j) hq hDq
  have h2 := congrArg (Polynomial.eval (2 : ℤ)) h
  rw [Polynomial.expand_eval] at h2
  simp only [Polynomial.eval_prod, PhiZ] at h2 ⊢
  exact h2

/-- The ratio identity `PhiZ (D q^j) · Ψ_D(2^{q^{j-1}}) = Ψ_D(2^{q^j})`. -/
lemma PhiZ_mul_eval_eq {q D j : ℕ} (hq : q.Prime) (hDq : ¬ q ∣ D) (hj : 1 ≤ j) :
    PhiZ (D * q ^ j) * (Polynomial.cyclotomic D ℤ).eval ((2 : ℤ) ^ (q ^ (j - 1)))
      = (Polynomial.cyclotomic D ℤ).eval ((2 : ℤ) ^ (q ^ j)) := by
  rw [eval_cyclotomic_prod hq hDq (j := j), eval_cyclotomic_prod hq hDq (j := j - 1)]
  have hjj : j - 1 + 1 = j := Nat.succ_pred_eq_of_pos hj
  rw [hjj, Finset.prod_range_succ, mul_comm]

theorem lt_PhiZ_of_prime_pow {q D j : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hD : D = orderOf (2 : ZMod q)) (hj : 1 ≤ j) (hne : D * q ^ j ≠ 6) :
    (q : ℤ) < PhiZ (D * q ^ j) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  -- ## Facts about `D`
  have h2nz : (2 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod q) = 0 := h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hdvd0 : orderOf (2 : ZMod q) ∣ q - 1 :=
    orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one h2nz)
  have hDdvd : D ∣ q - 1 := by rw [hD]; exact hdvd0
  have hDle : D ≤ q - 1 := Nat.le_of_dvd (by omega) hDdvd
  have hDge2 : 2 ≤ D := by
    rw [hD]
    have hpos : 0 < q - 1 := by omega
    have hle : orderOf (2 : ZMod q) ≤ q - 1 := Nat.le_of_dvd hpos hdvd0
    rcases Nat.eq_zero_or_pos (orderOf (2 : ZMod q)) with h0 | h0
    · rw [h0] at hdvd0; simp at hdvd0; omega
    · have hne1 : orderOf (2 : ZMod q) ≠ 1 := by
        intro h1
        have h2eq1 : (2 : ZMod q) = 1 := orderOf_eq_one_iff.mp h1
        have hone : ((1 : ℕ) : ZMod q) = 0 := by
          have h21 : (2 : ZMod q) - 1 = 0 := by rw [h2eq1]; ring
          have hcast : (2 : ZMod q) - 1 = ((1 : ℕ) : ZMod q) := by norm_num
          rw [hcast] at h21; exact h21
        exact hq.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 q).mp hone)
      omega
  have hDq : ¬ q ∣ D := by
    intro hqd
    have h1 : q ∣ q - 1 := dvd_trans hqd hDdvd
    have h2 : q ∣ 1 := by
      have := Nat.dvd_sub (dvd_refl q) h1
      convert this using 1
      omega
    exact hq.not_dvd_one h2
  have hD2q3 : D = 2 → q = 3 := by
    intro hD2
    rw [hD] at hD2
    have hp : (2 : ZMod q) ^ orderOf (2 : ZMod q) = 1 := pow_orderOf_eq_one _
    rw [hD2] at hp
    have hp4 : ((4 : ℕ) : ZMod q) = 1 := by
      have : (2 : ZMod q) ^ 2 = ((4 : ℕ) : ZMod q) := by norm_num
      rw [← this]; exact hp
    have h3 : ((3 : ℕ) : ZMod q) = 0 := by
      have h := congrArg (fun x : ZMod q => x - 1) hp4
      simp only [sub_self] at h
      convert h using 1
      norm_num
    have hd : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp h3
    have h3p : Nat.Prime 3 := by norm_num
    have := (Nat.Prime.dvd_iff_eq h3p hq.ne_one).mp hd
    omega
  -- ## The exceptional case is exactly `j = 1 ∧ D = 2`
  have hcase : j = 1 → 3 ≤ D := by
    intro hj1
    by_contra hlt
    have hD2 : D = 2 := by omega
    have hq3' : q = 3 := hD2q3 hD2
    have : D * q ^ j = 6 := by rw [hD2, hq3', hj1]; norm_num
    exact hne this
  -- ## Assembly
  have harith : q * 2 ^ (D * q ^ (j - 1)) < 2 ^ ((q ^ j - 1) * D.totient) :=
    pow_arith hq3 hDge2 hDle hj hcase
  have hkj : 1 ≤ q ^ j := Nat.one_le_pow j q (by omega)
  have hAgt : (2 : ℤ) ^ ((q ^ j - 1) * D.totient)
      < (Polynomial.cyclotomic D ℤ).eval ((2 : ℤ) ^ (q ^ j)) :=
    PhiZ_eval_lower hDge2 hkj
  have hM2 : 2 ≤ 2 ^ (q ^ (j - 1)) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (q ^ (j - 1)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow _ _ (by omega))
  have hBlt : (Polynomial.cyclotomic D ℤ).eval ((2 : ℤ) ^ (q ^ (j - 1)))
      < (2 : ℤ) ^ (D * q ^ (j - 1)) := by
    have h := PhiZ_eval_upper (D := D) (M := 2 ^ (q ^ (j - 1))) (by omega) hM2
    have hM : ((2 ^ (q ^ (j - 1)) : ℕ) : ℤ) = (2 : ℤ) ^ (q ^ (j - 1)) := by
      push_cast; ring
    rw [hM] at h
    rw [← pow_mul, mul_comm] at h
    exact h
  have hBpos : 0 < (Polynomial.cyclotomic D ℤ).eval ((2 : ℤ) ^ (q ^ (j - 1))) :=
    Polynomial.cyclotomic_pos' D (by
      have : (1 : ℤ) < (2 : ℤ) := by norm_num
      exact lt_of_lt_of_le this (by exact_mod_cast hM2))
  have hratio := PhiZ_mul_eval_eq hq hDq hj
  have hqposZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq.pos
  have hkey : (q : ℤ) * (Polynomial.cyclotomic D ℤ).eval ((2 : ℤ) ^ (q ^ (j - 1)))
      < (Polynomial.cyclotomic D ℤ).eval ((2 : ℤ) ^ (q ^ j)) := by
    have h1 : (q : ℤ) * (Polynomial.cyclotomic D ℤ).eval ((2 : ℤ) ^ (q ^ (j - 1)))
        < (q : ℤ) * (2 : ℤ) ^ (D * q ^ (j - 1)) :=
      mul_lt_mul_of_pos_left hBlt hqposZ
    have h2 : (q : ℤ) * (2 : ℤ) ^ (D * q ^ (j - 1))
        ≤ (2 : ℤ) ^ ((q ^ j - 1) * D.totient) := by
      have h2n : ((q * 2 ^ (D * q ^ (j - 1)) : ℕ) : ℤ)
          ≤ ((2 ^ ((q ^ j - 1) * D.totient) : ℕ) : ℤ) := Nat.cast_le.mpr (le_of_lt harith)
      simpa using h2n
    exact lt_trans (lt_of_lt_of_le h1 h2) hAgt
  have hthis := hkey
  rw [← hratio] at hthis
  exact lt_of_mul_lt_mul_right hthis (le_of_lt hBpos)

end Work.PGroup
