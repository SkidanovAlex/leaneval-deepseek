import Mathlib
import Submission.Commons.NumberTheory.Robin.sigma_ratio_prime_power_prod
import Submission.Commons.NumberTheory.Robin.ca_robin_cover
import Submission.Commons.NumberTheory.Robin.robin_of_good_family

/-!
# Robin's inequality from the covering by colossally abundant members (clean port)

This is a self-contained ("clean") port of `Submission.Commons.NumberTheory.Robin.robin_of_ca_cover`
which does **not** import `caBen_le_caExp` (whose public copies of `caMu_pos`, `caMu_nonneg`,
`caBen_pos`, `caMarg_ge_one_iff` clash with the standalone commons modules).  Every helper is
re-derived privately here:

* `SEC 0`  : the per-prime (Alaoglu–Erdős) marginal analysis (`caMu`, `caExp`, `caBen`, `caMarg`,
             threshold law, per-prime optimality `caBen_le_caExp`);
* `Port1`  : the colossally-abundant core (`Nε`, `Nminus`, right/left local constancy, covering);
* `Port2`  : global maximality of `N⁻(ε)` (`ca_minus_maximality_log`);
* `Port3`  : co-optimality `ben_ε(N⁻(ε)) = ben_ε(N_ε)` (`ca_minus_ben_eq`).

The published theorem assembles these through `robin_of_good_family`.
-/

open scoped BigOperators

namespace Commons.NumberTheory.Robin

noncomputable section

/-! ## SEC 0 — per-prime marginal analysis (private port of `caBen_le_caExp.lean`) -/



private def caMu (p : ℕ) (ε : ℝ) : ℝ :=
  Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)

/-- The exponent of the prime `p` in the CA number `N_ε`: `⌊μ(p,ε)⌋₊`. -/
private def caExp (p : ℕ) (ε : ℝ) : ℕ := ⌊caMu p ε⌋₊

/-- `(p:ℝ)^{1+ε} − p > 0` for `p ≥ 2`, `ε > 0`. -/
private lemma rpow_sub_one_pos {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    0 < ((p : ℝ) ^ (1 + ε)) - (p : ℝ) := by
  have hp0r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpε : 1 < (p : ℝ) ^ ε := by
    rw [Real.one_lt_rpow_iff (le_of_lt hp0r)]
    exact Or.inl ⟨by exact_mod_cast (by omega : 1 < p), hε⟩
  have hp1ε : (p : ℝ) ^ (1 + ε) = (p : ℝ) * (p : ℝ) ^ ε := by
    rw [Real.rpow_add hp0r, Real.rpow_one]
  rw [hp1ε]
  have hmul : (p : ℝ) < (p : ℝ) * (p : ℝ) ^ ε := by
    calc
      (p : ℝ) = (p : ℝ) * 1 := by ring
      _ < (p : ℝ) * (p : ℝ) ^ ε := mul_lt_mul_of_pos_left hpε hp0r
  linarith

/-- For `p ≥ 2`, `ε > 0` the quotient `(p^{1+ε}−1)/(p^{1+ε}−p)` exceeds 1, so `μ(p,ε) > 0`. -/
private lemma caMu_pos {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) : 0 < caMu p ε := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hdenpos : 0 < ((p : ℝ) ^ (1 + ε)) - (p : ℝ) := rpow_sub_one_pos hp hε
  have hnumpos : 0 < ((p : ℝ) ^ (1 + ε)) - 1 := by
    have h1l : (1 : ℝ) < 1 + ε := by linarith
    have h : 1 < (p : ℝ) ^ (1 + ε) := by
      rw [Real.one_lt_rpow_iff (le_of_lt hp0r)]
      exact Or.inl ⟨hp1r, (by linarith : 0 < 1 + ε)⟩
    linarith
  have hquotgt1 : 1 < (((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) := by
    rw [one_lt_div hdenpos]
    linarith
  have hlog : 0 < Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) :=
    Real.log_pos hquotgt1
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  exact div_pos hlog hlogp

/-- `A(p,ε) = (p^{1+ε}−1)/(p^{1+ε}−p) = 1 + (p−1)/(p^{1+ε}−p)` for `p ≥ 2`, `ε > 0`. -/
private lemma caQuot_eq_one_add {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) =
      1 + ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) := by
  have hd : ((p : ℝ) ^ (1 + ε)) - (p : ℝ) ≠ 0 := ne_of_gt (rpow_sub_one_pos hp hε)
  field_simp [hd]
  ring

/-- `μ(p,ε) = log(1 + (p−1)/(p^{1+ε}−p))/log p` (equivalent form of (4.11)). -/
private lemma caMu_eq_one_add {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    caMu p ε = Real.log (1 + ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ)))
        / Real.log (p : ℝ) := by
  unfold caMu
  rw [caQuot_eq_one_add hp hε]

/-- algebraic identity: `(p^{k+1}−1)/(p^k−1) = p + (p−1)/(p^k−1)` for `p ≥ 2`, `k ≥ 1`. -/
private lemma rpow_succ_sub_one_div {p : ℕ} {k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) =
      (p : ℝ) + ((p : ℝ) - 1) / (((p : ℝ) ^ k) - 1) := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hpkne : (p : ℝ) ^ k - 1 ≠ 0 := by
    have : 0 < (p : ℝ) ^ k - 1 := by
      have hpk : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
      linarith
    linarith
  rw [pow_succ, mul_comm]
  field_simp [hpkne]
  ring

/-- `p ≥ 2`, `ε > 0`, `k ≥ 1`: `μ(p,ε) ≥ k` iff `p^{1+ε} ≤ (p^{k+1}−1)/(p^k−1)`.
Forward: the power inequality ⇒ `μ ≥ k`. -/
private lemma caMu_ge_of_rpow_le {p : ℕ} {ε : ℝ} {k : ℕ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k)
    (h : (p : ℝ) ^ (1 + ε) ≤ (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1)) :
    k ≤ caMu p ε := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  have hd : 0 < ((p : ℝ) ^ (1 + ε)) - (p : ℝ) := rpow_sub_one_pos hp hε
  have hpk1pos : 0 < (p : ℝ) ^ k - 1 := by
    have hpk : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
    linarith
  have hpkpos : 0 < (p : ℝ) ^ k := by positivity
  have hd_le : ((p : ℝ) ^ (1 + ε)) - (p : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) ^ k - 1) := by
    have hle : (p : ℝ) ^ (1 + ε) ≤ (p : ℝ) + ((p : ℝ) - 1) / ((p : ℝ) ^ k - 1) := by
      calc
        (p : ℝ) ^ (1 + ε) ≤ (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := h
        _ = (p : ℝ) + ((p : ℝ) - 1) / ((p : ℝ) ^ k - 1) := rpow_succ_sub_one_div hp hk
    linarith
  let X : ℝ := 1 + ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))
  have hX : 0 < X := by
    have hnum : 0 < ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) :=
      div_pos (by have : (1 : ℝ) < (p : ℝ) := hp1r; linarith) hd
    dsimp [X]
    linarith
  have hXge : (p : ℝ) ^ k ≤ X := by
    have hmul : (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) * (((p : ℝ) ^ k) - 1) ≤ (p : ℝ) - 1 := by
      have hd' := (le_div_iff₀ hpk1pos).mp hd_le   -- d*(p^k−1) ≤ p−1
      nlinarith
    have hdiv : ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) ≥ (p : ℝ) ^ k - 1 := by
      rw [ge_iff_le]
      rw [le_div_iff₀ hd]
      nlinarith [hmul]
    dsimp [X]
    linarith
  have hXeq : caMu p ε = Real.log X / Real.log (p : ℝ) := by
    simpa [X, caMu_eq_one_add hp hε]
  have hlogge : Real.log ((p : ℝ) ^ k) ≤ Real.log X := Real.log_le_log hpkpos hXge
  have hlogpk : Real.log ((p : ℝ) ^ k) = (k : ℝ) * Real.log (p : ℝ) := by
    rw [← Real.rpow_natCast (p : ℝ) k]
    exact Real.log_rpow hp0r (k : ℝ)
  have hkl : (k : ℝ) * Real.log (p : ℝ) ≤ Real.log X := by
    rw [← hlogpk]
    exact hlogge
  have hdiv : (k : ℝ) ≤ Real.log X / Real.log (p : ℝ) := (le_div_iff₀ hlogp).mpr hkl
  simpa [hXeq] using hdiv

/-- `p ≥ 2`, `ε > 0`, `k ≥ 1`: if `μ(p,ε) ≥ k` then `p^{1+ε} ≤ (p^{k+1}−1)/(p^k−1)`. -/
private lemma caMu_ge_imp_rpow_le {p : ℕ} {ε : ℝ} {k : ℕ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k)
    (h : k ≤ caMu p ε) :
    (p : ℝ) ^ (1 + ε) ≤ (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  have hd : 0 < ((p : ℝ) ^ (1 + ε)) - (p : ℝ) := rpow_sub_one_pos hp hε
  have hpk1pos : 0 < (p : ℝ) ^ k - 1 := by
    have hpk : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
    linarith
  have hpkpos : 0 < (p : ℝ) ^ k := by positivity
  let X : ℝ := 1 + ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))
  have hXeq : caMu p ε = Real.log X / Real.log (p : ℝ) := by
    simpa [X, caMu_eq_one_add hp hε]
  have hlogpk : Real.log ((p : ℝ) ^ k) = (k : ℝ) * Real.log (p : ℝ) := by
    rw [← Real.rpow_natCast (p : ℝ) k]
    exact Real.log_rpow hp0r (k : ℝ)
  have hkl : (k : ℝ) * Real.log (p : ℝ) ≤ Real.log X := by
    have hkmu' : (k : ℝ) ≤ Real.log X / Real.log (p : ℝ) := by simpa [hXeq] using h
    exact (le_div_iff₀ hlogp).mp hkmu'
  have hlogge : Real.log ((p : ℝ) ^ k) ≤ Real.log X := by
    rw [hlogpk]
    exact hkl
  have hX : 0 < X := by
    have hnum : 0 < ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) :=
      div_pos (by have : (1 : ℝ) < (p : ℝ) := hp1r; linarith) hd
    dsimp [X]
    linarith
  have hXge : (p : ℝ) ^ k ≤ X := by
    have hexp := (Real.exp_le_exp).mpr hlogge
    rw [Real.exp_log hpkpos, Real.exp_log hX] at hexp
    exact hexp
  have hge : ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) ≥ (p : ℝ) ^ k - 1 := by
    dsimp [X] at hXge
    linarith
  have hd_le : ((p : ℝ) ^ (1 + ε)) - (p : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) ^ k - 1) := by
    have hd2 : (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) * (((p : ℝ) ^ k) - 1) ≤ (p : ℝ) - 1 := by
      have hd3 : ((p : ℝ) ^ k) - 1 ≤ ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) := hge
      have hd4 := (le_div_iff₀ hd).mp hd3   -- (p^k −1) * d ≤ p − 1
      nlinarith
    exact (le_div_iff₀ hpk1pos).mpr hd2
  calc
    (p : ℝ) ^ (1 + ε) = (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) + (p : ℝ) := by ring
    _ ≤ ((p : ℝ) - 1) / ((p : ℝ) ^ k - 1) + (p : ℝ) := by nlinarith [hd_le]
    _ = (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by
      rw [rpow_succ_sub_one_div hp hk]
      ring

/-- `p ≥ 2`, `ε > 0`, `k ≥ 1`: `μ(p,ε) ≥ k ⟺ p^{1+ε} ≤ (p^{k+1}−1)/(p^k−1)`. -/
private lemma caMu_ge_iff_rpow_le {p : ℕ} {ε : ℝ} {k : ℕ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k) :
    k ≤ caMu p ε ↔ (p : ℝ) ^ (1 + ε) ≤ (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by
  constructor
  · intro h
    exact caMu_ge_imp_rpow_le hp hε hk h
  · intro h
    exact caMu_ge_of_rpow_le hp hε hk h

/-- `caMu p ε ≥ 0` for `p ≥ 2`, `ε > 0`. -/
private lemma caMu_nonneg {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) : 0 ≤ caMu p ε :=
  le_of_lt (caMu_pos hp hε)

/-- `p ≥ 2`, `ε > 0`, `k ≥ 1`: exponent of `p` in `N_ε` is `≥ k` iff `μ(p,ε) ≥ k`. -/
private lemma caExp_ge_iff_mu {p : ℕ} {ε : ℝ} {k : ℕ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k) :
    k ≤ caExp p ε ↔ (k : ℝ) ≤ caMu p ε := by
  unfold caExp
  constructor
  · intro h
    -- k ≤ ⌊µ⌋₊  ⟹  k ≤ µ
    have hle : (⌊caMu p ε⌋₊ : ℝ) ≤ caMu p ε := Nat.floor_le (caMu_nonneg hp hε)
    exact le_trans (by exact_mod_cast h : (k : ℝ) ≤ (⌊caMu p ε⌋₊ : ℝ)) hle
  · intro h
    exact Nat.le_floor h

/-- Contribution of the prime power `p^b` to `ben_ε`: `σ(p^b)/p^{b(1+ε)}`. -/
private def caBen (p : ℕ) (ε : ℝ) (b : ℕ) : ℝ :=
  ((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ) / ((p : ℝ) ^ ((b : ℝ) * (1 + ε)))

/-- Marginal ratio of `ben_ε` when the exponent of `p` goes from `j` to `j+1`:
`(p^{j+2}−1)/(p^{j+1}−1) / p^{1+ε}`. -/
private def caMarg (p : ℕ) (ε : ℝ) (j : ℕ) : ℝ :=
  (((p : ℝ) ^ (j + 2 : ℕ) - 1) / ((p : ℝ) ^ (j + 1 : ℕ) - 1)) / ((p : ℝ) ^ (1 + ε))

/-- `caBen p ε b > 0` for `p ≥ 1`, any `ε`, `b`. -/
private lemma caBen_pos {p : ℕ} {ε : ℝ} {b : ℕ} (hp : 0 < p) : 0 < caBen p ε b := by
  unfold caBen
  have hσ : 0 < ArithmeticFunction.sigma 1 (p ^ b) :=
    (ArithmeticFunction.sigma_pos_iff).2 (pow_pos hp b)
  have hσr : (0 : ℝ) < ((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ) := by exact_mod_cast hσ
  have hpow : (0 : ℝ) < (p : ℝ) ^ ((b : ℝ) * (1 + ε)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp : (0 : ℝ) < (p : ℝ)) ((b : ℝ) * (1 + ε))
  exact div_pos hσr hpow

/-- `caMarg p ε j > 0` for `p ≥ 2`, `ε > 0`. -/
private lemma caMarg_pos {p : ℕ} {ε : ℝ} {j : ℕ} (hp : 2 ≤ p) (hε : 0 < ε) : 0 < caMarg p ε j := by
  unfold caMarg
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hA : 0 < (p : ℝ) ^ (j + 2 : ℕ) - 1 := by
    have h1 : 1 < (p : ℝ) ^ (j + 2 : ℕ) := one_lt_pow₀ hp1r (by omega : j + 2 ≠ 0)
    linarith
  have hB : 0 < (p : ℝ) ^ (j + 1 : ℕ) - 1 := by
    have h1 : 1 < (p : ℝ) ^ (j + 1 : ℕ) := one_lt_pow₀ hp1r (by omega : j + 1 ≠ 0)
    linarith
  exact div_pos (div_pos hA hB) (Real.rpow_pos_of_pos hp0 (1 + ε))

/-- closed form of `caBen` for a prime `p`:
`caBen p ε b = (p^{b+1}−1) / ((p−1) · p^{b(1+ε)})`. -/
private lemma caBen_eq_closed {p : ℕ} {ε : ℝ} {b : ℕ} (hp : Nat.Prime p) :
    caBen p ε b = (((p : ℝ) ^ (b + 1 : ℕ)) - 1) /
        (((p : ℝ) - 1) * ((p : ℝ) ^ ((b : ℝ) * (1 + ε)))) := by
  unfold caBen
  have hσdiv : ((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ) / ((p : ℝ) ^ b) =
      (((p : ℝ) ^ (b + 1 : ℕ)) - 1) / (((p : ℝ) ^ b) * ((p : ℝ) - 1)) := by
    simpa using (Commons.NumberTheory.Robin.sigma_one_ratio_prime_pow (p := p) (k := b) hp)
  have hp0n : p ≠ 0 := Nat.Prime.ne_zero hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp0n
  have hpb : (p : ℝ) ^ b ≠ 0 := pow_ne_zero _ hp0
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.Prime.ne_one hp) : (p : ℝ) ≠ 1)
  have hσ : ((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ) =
      ((p : ℝ) ^ b) * ((((p : ℝ) ^ (b + 1 : ℕ)) - 1) / (((p : ℝ) ^ b) * ((p : ℝ) - 1))) := by
    have h1 : ((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ) / ((p : ℝ) ^ b) *
        ((p : ℝ) ^ b) = ((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ) := by
      field_simp [hpb]
    rw [hσdiv] at h1
    calc
      ((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ)
          = ((((p : ℝ) ^ (b + 1 : ℕ)) - 1) / (((p : ℝ) ^ b) * ((p : ℝ) - 1))) * ((p : ℝ) ^ b) := by
              exact h1.symm
      _ = ((p : ℝ) ^ b) * ((((p : ℝ) ^ (b + 1 : ℕ)) - 1) / (((p : ℝ) ^ b) * ((p : ℝ) - 1))) := by ring
  rw [hσ]
  field_simp [hp0, hp1, hpb]

/-- `caBen p ε 0 = 1`. -/
private lemma caBen_zero (p : ℕ) (ε : ℝ) : caBen p ε 0 = 1 := by
  unfold caBen
  simp

/-- marginal step identity: `caBen (j+1) = caBen j · caMarg j` (prime `p`). -/
private lemma caBen_step {p : ℕ} {ε : ℝ} {j : ℕ} (hp : Nat.Prime p) :
    caBen p ε (j + 1) = caBen p ε j * caMarg p ε j := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.Prime.ne_one hp) : (p : ℝ) ≠ 1)
  have hB : (p : ℝ) ^ (j + 1 : ℕ) - 1 ≠ 0 := by
    have h1 : 1 < (p : ℝ) ^ (j + 1 : ℕ) := one_lt_pow₀ hp1r (by omega : j + 1 ≠ 0)
    linarith
  have hrpow : (p : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (1 + ε)) =
      (p : ℝ) ^ ((j : ℝ) * (1 + ε)) * (p : ℝ) ^ (1 + ε) := by
    have hexp : ((j + 1 : ℕ) : ℝ) * (1 + ε) = (j : ℝ) * (1 + ε) + (1 + ε) := by
      norm_num
      ring
    rw [hexp, Real.rpow_add hp0]
  calc
    caBen p ε (j + 1) = (((p : ℝ) ^ (j + 2 : ℕ)) - 1) /
        (((p : ℝ) - 1) * ((p : ℝ) ^ (((j + 1 : ℕ) : ℝ) * (1 + ε)))) := by
          rw [caBen_eq_closed hp]
    _ = (((p : ℝ) ^ (j + 2 : ℕ)) - 1) /
        (((p : ℝ) - 1) * (((p : ℝ) ^ ((j : ℝ) * (1 + ε))) * ((p : ℝ) ^ (1 + ε)))) := by
          rw [hrpow]
    _ = caBen p ε j * caMarg p ε j := by
      rw [caBen_eq_closed hp]
      unfold caMarg
      have hrj : (p : ℝ) ^ ((j : ℝ) * (1 + ε)) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hp0 ((j : ℝ) * (1 + ε)))
      have hr1 : (p : ℝ) ^ (1 + ε) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hp0 (1 + ε))
      field_simp [hp1, hB, hrj, hr1]

/-- threshold law: `1 ≤ caMarg p ε j ⟺ j+1 ≤ caExp p ε` (p prime, ε > 0). -/
private lemma caMarg_ge_one_iff {p : ℕ} {ε : ℝ} {j : ℕ} (hp : Nat.Prime p) (hε : 0 < ε) :
    (1 : ℝ) ≤ caMarg p ε j ↔ j + 1 ≤ caExp p ε := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hB : 0 < (p : ℝ) ^ (j + 1 : ℕ) - 1 := by
    have h1 : 1 < (p : ℝ) ^ (j + 1 : ℕ) := one_lt_pow₀ hp1r (by omega : j + 1 ≠ 0)
    linarith
  have hP : 0 < (p : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos hp0 (1 + ε)
  unfold caMarg
  have hL : ((1 : ℝ) ≤ ((((p : ℝ) ^ (j + 2 : ℕ) - 1) / ((p : ℝ) ^ (j + 1 : ℕ) - 1)) / ((p : ℝ) ^ (1 + ε))))
      ↔ (p : ℝ) ^ (1 + ε) ≤ (((p : ℝ) ^ (j + 2 : ℕ) - 1) / ((p : ℝ) ^ (j + 1 : ℕ) - 1)) := by
    constructor
    · intro h1
      have h2 : (1 : ℝ) * ((p : ℝ) ^ (1 + ε)) ≤
          (((p : ℝ) ^ (j + 2 : ℕ) - 1) / ((p : ℝ) ^ (j + 1 : ℕ) - 1)) :=
        (le_div_iff₀ hP).mp h1
      simpa using h2
    · intro h2
      exact (le_div_iff₀ hP).mpr (by simpa using h2)
  rw [hL]
  have hk1 : 1 ≤ j + 1 := by omega
  have hR : (p : ℝ) ^ (1 + ε) ≤ (((p : ℝ) ^ (j + 2 : ℕ) - 1) / ((p : ℝ) ^ (j + 1 : ℕ) - 1))
      ↔ ((j + 1 : ℕ) : ℝ) ≤ caMu p ε := by
    have h := (caMu_ge_iff_rpow_le (p := p) (ε := ε) (k := j + 1) hp2 hε hk1).symm
    simpa [Nat.cast_add] using h
  rw [hR]
  exact (caExp_ge_iff_mu (p := p) (ε := ε) (k := j + 1) hp2 hε hk1).symm

/-- if `c + 1 ≤ caExp p ε` then increasing the exponent from `c` to `c+1` raises `caBen`. -/
private lemma caBen_le_succ {p : ℕ} {ε : ℝ} (hp : Nat.Prime p) (hε : 0 < ε) {c : ℕ}
    (hc : c + 1 ≤ caExp p ε) : caBen p ε c ≤ caBen p ε (c + 1) := by
  have hge : (1 : ℝ) ≤ caMarg p ε c := (caMarg_ge_one_iff hp hε).mpr hc
  rw [caBen_step hp]
  calc
    caBen p ε c = caBen p ε c * 1 := by ring
    _ ≤ caBen p ε c * caMarg p ε c :=
      mul_le_mul_of_nonneg_left hge (le_of_lt (caBen_pos (p := p) (ε := ε) (b := c) (Nat.Prime.pos hp)))

/-- `caBen` increases while the exponent stays below `caExp p ε`:
`b ≤ c ≤ caExp p ε` implies `caBen b ≤ caBen c`. -/
private lemma caBen_mono_left {p : ℕ} {ε : ℝ} (hp : Nat.Prime p) (hε : 0 < ε) {b c : ℕ}
    (hbc : b ≤ c) (hc : c ≤ caExp p ε) : caBen p ε b ≤ caBen p ε c := by
  let P : ℕ → Prop := fun c => ∀ b : ℕ, b ≤ c → c ≤ caExp p ε → caBen p ε b ≤ caBen p ε c
  have hP : ∀ c : ℕ, P c := by
    intro c
    induction c with
    | zero =>
        intro b hbc hc
        have hb0 : b = 0 := by omega
        subst b
        exact le_rfl
    | succ c ih =>
        intro b hbc hc
        by_cases hbc' : b ≤ c
        · have h1 : caBen p ε b ≤ caBen p ε c := ih b hbc' (by omega)
          exact le_trans h1 (caBen_le_succ hp hε hc)
        · have hb : b = c + 1 := by omega
          subst b
          exact le_rfl
  exact hP c b hbc hc

/-- `caBen` decreases once the exponent passes `caExp p ε`:
`j ≥ caExp p ε` implies `caBen (j+1) ≤ caBen j`. -/
private lemma caBen_anti_succ {p : ℕ} {ε : ℝ} (hp : Nat.Prime p) (hε : 0 < ε) {j : ℕ}
    (hj : caExp p ε ≤ j) : caBen p ε (j + 1) ≤ caBen p ε j := by
  have hnot : ¬ (j + 1 ≤ caExp p ε) := by omega
  have hle : caMarg p ε j ≤ 1 := by
    have hmarg : ¬ (1 : ℝ) ≤ caMarg p ε j := fun h => hnot ((caMarg_ge_one_iff hp hε).mp h)
    exact le_of_lt (lt_of_not_ge hmarg)
  rw [caBen_step hp]
  have hpos : 0 ≤ caBen p ε j := le_of_lt (caBen_pos (p := p) (ε := ε) (b := j) (Nat.Prime.pos hp))
  calc
    caBen p ε j * caMarg p ε j ≤ caBen p ε j * 1 := mul_le_mul_of_nonneg_left hle hpos
    _ = caBen p ε j := by ring

/-- per-prime optimality: `caBen p ε b ≤ caBen p ε (caExp p ε)` for every `b`. -/
private theorem caBen_le_caExp_aux {p : ℕ} {ε : ℝ} {b : ℕ} (hp : Nat.Prime p) (hε : 0 < ε) :
    caBen p ε b ≤ caBen p ε (caExp p ε) := by
  by_cases hba : b ≤ caExp p ε
  · exact caBen_mono_left hp hε hba le_rfl
  · have ha : caExp p ε ≤ b := by omega
    have hdown : ∀ t : ℕ, caBen p ε (caExp p ε + t) ≤ caBen p ε (caExp p ε) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
          have hanti : caBen p ε (caExp p ε + t + 1) ≤ caBen p ε (caExp p ε + t) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (caBen_anti_succ (p := p) (ε := ε) (j := caExp p ε + t) hp hε (by omega))
          exact le_trans hanti ih
    have hb' : b = caExp p ε + (b - caExp p ε) := by omega
    rw [hb']
    exact hdown (b - caExp p ε)
/-- Per-prime optimality in the unfolded form requested by the project: for a prime `p`,
`ε > 0` and every exponent `b`, the contribution `σ(p^b)/p^{b(1+ε)}` is at most the
contribution at the CA exponent `⌊μ(p,ε)⌋₊`. -/
private lemma caBen_le_caExp {p : ℕ} {ε : ℝ} {b : ℕ} (hp : Nat.Prime p) (hε : 0 < ε) :
    ((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ) / ((p : ℝ) ^ ((b : ℝ) * (1 + ε))) ≤
    ((ArithmeticFunction.sigma 1 (p ^ Nat.floor (Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ))) : ℕ) : ℝ)
      / ((p : ℝ) ^ ((Nat.floor (Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)) : ℝ) * (1 + ε))) := by
  change caBen p ε b ≤ caBen p ε (caExp p ε)
  exact caBen_le_caExp_aux hp hε

/-! ## Port2 — global maximality of `N⁻(ε)` (private port of `ca_minus_maximality_log.lean`) -/

namespace Port2



/-! ## Definitions: the CA product `N_ε`, its predecessor `N⁻(ε)`, and helper lemmas -/

/-- the finite support bound of the CA product: `⌈exp(2/ε)⌉ + 2`. -/
private def caBound (ε : ℝ) : ℕ := Nat.ceil (Real.exp (2 / ε)) + 2

/-- the range of primes over which the CA product is taken. -/
private def caPrimes (ε : ℝ) : Finset ℕ := (Finset.range (caBound ε)).filter Nat.Prime

/-- exponent of `p` in the previous CA member `N⁻(ε)`: `caExp p ε − 1` at jump primes
(where `μ(p,ε) = ⌊μ(p,ε)⌋₊ ≥ 1` is an integer), else `caExp p ε`. -/
private def caMinusExp (p : ℕ) (ε : ℝ) : ℕ :=
  if caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε then caExp p ε - 1 else caExp p ε

/-- the CA number `N_ε = ∏_{p ∈ caPrimes ε} p ^ caExp p ε`. -/
private def caN (ε : ℝ) : ℕ := Finset.prod (caPrimes ε) (fun p => p ^ caExp p ε)

/-- the previous CA member `N⁻(ε) = ∏_{p ∈ caPrimes ε} p ^ caMinusExp p ε`. -/
private def Nminus (ε : ℝ) : ℕ := Finset.prod (caPrimes ε) (fun p => p ^ caMinusExp p ε)

/-- logarithm of `caBen`: `log(caBen p ε b) = log σ(p^b) − b(1+ε)·log p`. -/
private lemma caBen_log {p : ℕ} {ε : ℝ} {b : ℕ} (hp : 2 ≤ p) :
    Real.log (caBen p ε b) =
      Real.log (((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ)) -
        (b : ℝ) * (1 + ε) * Real.log (p : ℝ) := by
  unfold caBen
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hσ' : 0 < ArithmeticFunction.sigma 1 (p ^ b) :=
    (ArithmeticFunction.sigma_pos_iff).2 (pow_pos (by omega : 0 < p) b)
  have hσr : (0 : ℝ) < ((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ) := by exact_mod_cast hσ'
  have hrpow : (0 : ℝ) < (p : ℝ) ^ ((b : ℝ) * (1 + ε)) :=
    Real.rpow_pos_of_pos hp0 ((b : ℝ) * (1 + ε))
  rw [Real.log_div hσr.ne' hrpow.ne']
  rw [Real.log_rpow hp0]

/-- multiplicativity of `σ 1` over a product of prime powers with distinct primes. -/
private lemma sigma_prod_prime_pows {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p) (a : ℕ → ℕ) :
    ArithmeticFunction.sigma 1 (Finset.prod s (fun p => p ^ a p)) =
      Finset.prod s (fun p => ArithmeticFunction.sigma 1 (p ^ a p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hpnot ih =>
      have hp' : Nat.Prime p := hprime p (by simp)
      have hcop : (p ^ a p).Coprime (Finset.prod s (fun q => q ^ a q)) := by
        apply Nat.Coprime.prod_right
        intro q hq
        have hq' : Nat.Prime q := hprime q (Finset.mem_insert_of_mem hq)
        have hpq_ne : q ≠ p := by
          intro hpq
          exact hpnot (by simpa [hpq] using hq)
        have hpq : p.Coprime q := (Nat.coprime_primes hp' hq').mpr (Ne.symm hpq_ne)
        have h1 : p.Coprime (q ^ a q) := Nat.Coprime.pow_right (a q) hpq
        exact Nat.Coprime.pow_left (a p) h1
      have hσ := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
      have ih' := ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
      rw [Finset.prod_insert hpnot, hσ, ih', Finset.prod_insert hpnot]

/-- log factorisation of `σ` of a product of prime powers. -/
private lemma log_sigma_prod_pows_of_prime {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    (a : ℕ → ℕ) :
    Real.log (((ArithmeticFunction.sigma 1 (Finset.prod s (fun p => p ^ a p)) : ℕ) : ℝ)) =
      Finset.sum s (fun p =>
        Real.log (((ArithmeticFunction.sigma 1 (p ^ a p) : ℕ) : ℝ))) := by
  have hfac : ArithmeticFunction.sigma 1 (Finset.prod s (fun p => p ^ a p)) =
      Finset.prod s (fun p => ArithmeticFunction.sigma 1 (p ^ a p)) :=
    sigma_prod_prime_pows (s := s) hprime (fun p => a p)
  rw [hfac]
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  intro p hp
  have hp' : Nat.Prime p := hprime p hp
  have hσ : 0 < ArithmeticFunction.sigma 1 (p ^ a p) :=
    (ArithmeticFunction.sigma_pos_iff).2 (pow_pos (Nat.Prime.pos hp') (a p))
  exact_mod_cast (ne_of_gt hσ)

/-- log of a product of prime powers. -/
private lemma log_prod_pows_of_prime {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p) (a : ℕ → ℕ) :
    Real.log ((Finset.prod s (fun p => p ^ a p) : ℕ) : ℝ) =
      Finset.sum s (fun p => (a p : ℝ) * Real.log (p : ℝ)) := by
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow]
    rw [Real.log_pow]
  · intro p hp
    have hp' : Nat.Prime p := hprime p hp
    have hpow : 0 < p ^ a p := pow_pos (Nat.Prime.pos hp') (a p)
    exact_mod_cast (ne_of_gt hpow)

/-- log-benefit factorisation of a product of prime powers over a set of primes. -/
private lemma log_ben_prod_pows {ε : ℝ} {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    (a : ℕ → ℕ) :
    Real.log (((ArithmeticFunction.sigma 1 (Finset.prod s (fun p => p ^ a p)) : ℕ) : ℝ)) -
        (1 + ε) * Real.log ((Finset.prod s (fun p => p ^ a p) : ℕ) : ℝ) =
      Finset.sum s (fun p => Real.log (caBen p ε (a p))) := by
  have h1 := log_sigma_prod_pows_of_prime (s := s) hprime a
  have h2 := log_prod_pows_of_prime (s := s) hprime a
  rw [h1, h2]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp' : Nat.Prime p := hprime p hp
  have hcb := caBen_log (p := p) (ε := ε) (b := a p) hp'.two_le
  rw [hcb]
  ring

/-- log-benefit factorisation of `N⁻(ε)`. -/
private lemma log_ben_Nminus_eq_sum {ε : ℝ} :
    Real.log (((ArithmeticFunction.sigma 1 (Nminus ε) : ℕ) : ℝ)) -
        (1 + ε) * Real.log ((Nminus ε : ℕ) : ℝ) =
      Finset.sum (caPrimes ε) (fun p => Real.log (caBen p ε (caMinusExp p ε))) := by
  simpa [Nminus] using log_ben_prod_pows (ε := ε) (s := caPrimes ε)
    (fun p hp => (Finset.mem_filter.mp hp).2) (fun p => caMinusExp p ε)

/-- log-benefit factorisation of `N_ε`. -/
private lemma log_ben_caN_eq_sum {ε : ℝ} :
    Real.log (((ArithmeticFunction.sigma 1 (caN ε) : ℕ) : ℝ)) -
        (1 + ε) * Real.log ((caN ε : ℕ) : ℝ) =
      Finset.sum (caPrimes ε) (fun p => Real.log (caBen p ε (caExp p ε))) := by
  simpa [caN] using log_ben_prod_pows (ε := ε) (s := caPrimes ε)
    (fun p hp => (Finset.mem_filter.mp hp).2) (fun p => caExp p ε)

/-- from `μ(p,ε) = k` deduce the rpow equation `p^{1+ε} = (p^{k+1}−1)/(p^k−1)`
(prime `p`, `ε > 0`, `k ≥ 1`). -/
private lemma caMu_eq_imp_rpow_eq {p : ℕ} {ε : ℝ} {k : ℕ} (hp : Nat.Prime p) (hε : 0 < ε)
    (hk : 1 ≤ k) (hmu : caMu p ε = (k : ℝ)) :
    (p : ℝ) ^ (1 + ε) = (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos hp)
  have hlogp : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1r)
  have h1pe : 0 < 1 + ε := by linarith
  have hYgt1 : 1 < (p : ℝ) ^ (1 + ε) := by
    rw [Real.one_lt_rpow_iff (le_of_lt hp0)]
    exact Or.inl ⟨hp1r, h1pe⟩
  have hYp : 0 < (p : ℝ) ^ (1 + ε) - (p : ℝ) := by
    have hpe : 1 < (p : ℝ) ^ ε := by
      rw [Real.one_lt_rpow_iff (le_of_lt hp0)]
      exact Or.inl ⟨hp1r, hε⟩
    have hp1e : (p : ℝ) * (p : ℝ) ^ ε = (p : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hp0, Real.rpow_one]
    rw [← hp1e]
    exact sub_pos.mpr (by
      have hm := mul_lt_mul_of_pos_left hpe hp0
      simpa using hm)
  let Y : ℝ := (p : ℝ) ^ (1 + ε)
  let X : ℝ := (Y - 1) / (Y - (p : ℝ))
  have hXpos : 0 < X := by
    dsimp [X]
    exact div_pos (by linarith) hYp
  have hlogX : Real.log X = (k : ℝ) * Real.log (p : ℝ) := by
    have hmu' : Real.log X / Real.log (p : ℝ) = (k : ℝ) := by
      dsimp [X, Y]
      unfold caMu at hmu
      simpa using hmu
    calc
      Real.log X = Real.log X / Real.log (p : ℝ) * Real.log (p : ℝ) := by field_simp [hlogp]
      _ = (k : ℝ) * Real.log (p : ℝ) := by rw [hmu']
  have hXeq : X = (p : ℝ) ^ (k : ℕ) := by
    have he := congrArg Real.exp hlogX
    have hL : Real.exp (Real.log X) = X := Real.exp_log hXpos
    have hR : Real.exp ((k : ℝ) * Real.log (p : ℝ)) = (p : ℝ) ^ (k : ℕ) := by
      rw [Real.exp_nat_mul]
      rw [Real.exp_log hp0]
    simpa [hL, hR] using he
  have hpk1 : (p : ℝ) ^ k - 1 ≠ 0 := by
    have h : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
    linarith
  have hpowsucc : (p : ℝ) ^ (k : ℕ) * (p : ℝ) = (p : ℝ) ^ (k + 1 : ℕ) := by
    rw [pow_succ']
    ring
  have hmul : Y - 1 = (p : ℝ) ^ (k : ℕ) * (Y - (p : ℝ)) := by
    have hYp' : Y - (p : ℝ) ≠ 0 := ne_of_gt hYp
    calc
      Y - 1 = ((Y - 1) / (Y - (p : ℝ))) * (Y - (p : ℝ)) := by field_simp [hYp']
      _ = (p : ℝ) ^ (k : ℕ) * (Y - (p : ℝ)) := by
        dsimp [X] at hXeq
        rw [hXeq]
  let Z : ℝ := (p : ℝ) ^ (k : ℕ) * Y
  have hmul' : Y - 1 = Z - (p : ℝ) ^ (k + 1 : ℕ) := by
    calc
      Y - 1 = (p : ℝ) ^ (k : ℕ) * (Y - (p : ℝ)) := hmul
      _ = Z - (p : ℝ) ^ (k + 1 : ℕ) := by
        dsimp [Z]
        rw [← hpowsucc]
        ring
  have hZ : Z - Y = (p : ℝ) ^ (k + 1 : ℕ) - 1 := by
    linarith
  have hY : Y = (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by
    have hZ' : Y * ((p : ℝ) ^ (k : ℕ) - 1) = (p : ℝ) ^ (k + 1 : ℕ) - 1 := by
      calc
        Y * ((p : ℝ) ^ (k : ℕ) - 1) = Z - Y := by dsimp [Z]; ring
        _ = (p : ℝ) ^ (k + 1 : ℕ) - 1 := hZ
    calc
      Y = (Y * ((p : ℝ) ^ (k : ℕ) - 1)) / (((p : ℝ) ^ k) - 1) := by field_simp [hpk1]
      _ = (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by rw [hZ']
  simpa [Y] using hY

/-- generalized per-prime co-optimality: at a parameter `ε` with `μ(p,ε) = b ≥ 1` an integer,
the two neighbouring exponents `b−1` and `b` give the same `ben_ε` factor. -/
private lemma caBen_eq_pred_of_mu_int {p : ℕ} {ε : ℝ} {b : ℕ} (hp : Nat.Prime p) (hε : 0 < ε)
    (hb : 1 ≤ b) (hmu : caMu p ε = (b : ℝ)) :
    caBen p ε (b - 1) = caBen p ε b := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos hp)
  have hr : (p : ℝ) ^ (1 + ε) = (((p : ℝ) ^ (b + 1 : ℕ)) - 1) / (((p : ℝ) ^ b) - 1) :=
    caMu_eq_imp_rpow_eq hp hε hb hmu
  have hpk1 : (p : ℝ) ^ b - 1 ≠ 0 := by
    have h : 1 < (p : ℝ) ^ b := one_lt_pow₀ hp1r (by omega : b ≠ 0)
    linarith
  have hpkp1 : (p : ℝ) ^ (b + 1 : ℕ) - 1 ≠ 0 := by
    have h : 1 < (p : ℝ) ^ (b + 1 : ℕ) := one_lt_pow₀ hp1r (by omega : b + 1 ≠ 0)
    linarith
  have hp1ne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hRpos : (0 : ℝ) < (p : ℝ) ^ (((b - 1 : ℕ) : ℝ) * (1 + ε)) :=
    Real.rpow_pos_of_pos hp0 (((b - 1 : ℕ) : ℝ) * (1 + ε))
  have hRp1 : (0 : ℝ) < (p : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos hp0 (1 + ε)
  have hexp : ((b - 1 : ℕ) : ℝ) * (1 + ε) + (1 + ε) = (b : ℝ) * (1 + ε) := by
    have hbn : (b : ℕ) = (b - 1) + 1 := (Nat.sub_add_cancel hb).symm
    have hbr : (b : ℝ) = ((b - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast hbn
    nlinarith
  rw [caBen_eq_closed (p := p) (ε := ε) (b := b - 1) hp]
  rw [caBen_eq_closed (p := p) (ε := ε) (b := b) hp]
  have hkadd : (b - 1 + 1 : ℕ) = b := by omega
  rw [hkadd]
  have hRb : (p : ℝ) ^ ((b : ℝ) * (1 + ε)) =
      (p : ℝ) ^ (((b - 1 : ℕ) : ℝ) * (1 + ε)) * (p : ℝ) ^ (1 + ε) := by
    rw [← hexp, Real.rpow_add hp0]
  calc
    (((p : ℝ) ^ b) - 1) / (((p : ℝ) - 1) * ((p : ℝ) ^ (((b - 1 : ℕ) : ℝ) * (1 + ε))))
        = (((p : ℝ) ^ (b + 1 : ℕ)) - 1) / (((p : ℝ) - 1) * ((p : ℝ) ^ ((b : ℝ) * (1 + ε)))) := by
          rw [hRb, hr]
          field_simp [hp1ne, hpk1, hpkp1, hRpos.ne', hRp1.ne']

/-- `caMinusExp p ε ≤ caExp p ε`. -/
private lemma caMinusExp_le (p : ℕ) (ε : ℝ) : caMinusExp p ε ≤ caExp p ε := by
  unfold caMinusExp
  by_cases h : caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε
  · rw [if_pos h]
    omega
  · rw [if_neg h]

/-- `caMinusExp = caExp` away from jump primes. -/
private lemma caMinusExp_eq_caExp {p : ℕ} {ε : ℝ}
    (h : ¬(caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε)) : caMinusExp p ε = caExp p ε := by
  unfold caMinusExp
  rw [if_neg h]

/-- `caMinusExp = caExp − 1` at jump primes. -/
private lemma caMinusExp_eq_pred {p : ℕ} {ε : ℝ}
    (h : caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε) : caMinusExp p ε = caExp p ε - 1 := by
  unfold caMinusExp
  rw [if_pos h]

/-- per-prime benefit equality at every prime: the previous exponent gives the same
`ben_ε`-factor as the optimal one. -/
private lemma caBen_eq_of_caMinusExp {p : ℕ} {ε : ℝ} (hp : Nat.Prime p) (hε : 0 < ε) :
    caBen p ε (caMinusExp p ε) = caBen p ε (caExp p ε) := by
  by_cases h : caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε
  · have hmin := caMinusExp_eq_pred (p := p) (ε := ε) h
    rw [hmin]
    exact caBen_eq_pred_of_mu_int (p := p) (ε := ε) (b := caExp p ε) hp hε h.2 h.1
  · rw [caMinusExp_eq_caExp (p := p) (ε := ε) h]

/-- TRANSITION (T3, product level): `N⁻(ε)` and `N_ε` give the same `ben_ε` value. -/
private theorem ca_minus_ben_eq_core {ε : ℝ} (hε : 0 < ε) :
    Real.log (((ArithmeticFunction.sigma 1 (Nminus ε) : ℕ) : ℝ)) -
        (1 + ε) * Real.log ((Nminus ε : ℕ) : ℝ) =
      Real.log (((ArithmeticFunction.sigma 1 (caN ε) : ℕ) : ℝ)) -
        (1 + ε) * Real.log ((caN ε : ℕ) : ℝ) := by
  rw [log_ben_Nminus_eq_sum (ε := ε), log_ben_caN_eq_sum (ε := ε)]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
  exact congrArg Real.log (caBen_eq_of_caMinusExp (p := p) (ε := ε) hp' hε)


/-! ## Global Alaoglu–Erdős maximality of `N_ε` -/

/-- `log(σ 1 m)` splits over the prime factors of `m`. -/
private lemma log_sigma_eq_sum_log_primeFactors {m : ℕ} (hm : m ≠ 0) :
    Real.log (((ArithmeticFunction.sigma 1 m : ℕ) : ℝ)) =
      Finset.sum m.primeFactors (fun p =>
        Real.log (((ArithmeticFunction.sigma 1 (p ^ m.factorization p) : ℕ) : ℝ))) := by
  have hfac : ArithmeticFunction.sigma 1 m =
      Finset.prod m.primeFactors (fun p => ArithmeticFunction.sigma 1 (p ^ m.factorization p)) := by
    exact (ArithmeticFunction.isMultiplicative_sigma (k := 1)).multiplicative_factorization
      (ArithmeticFunction.sigma 1) hm
  have hfacℝ : ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) =
      Finset.prod m.primeFactors
        (fun p => ((ArithmeticFunction.sigma 1 (p ^ m.factorization p) : ℕ) : ℝ)) := by
    rw [hfac]
    simp [Nat.cast_prod]
  rw [hfacℝ]
  rw [Real.log_prod]
  intro p hp
  have hσ : 0 < ArithmeticFunction.sigma 1 (p ^ m.factorization p) :=
    (ArithmeticFunction.sigma_pos_iff).2
      (pow_pos (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)) _)
  exact_mod_cast (ne_of_gt hσ)

/-- `log m` splits over the prime factors of `m`. -/
private lemma log_nat_eq_sum_primeFactors {m : ℕ} (hm : m ≠ 0) :
    Real.log (m : ℝ) =
      Finset.sum m.primeFactors (fun p => (m.factorization p : ℝ) * Real.log (p : ℝ)) := by
  have hprod : (m : ℝ) = Finset.prod m.primeFactors (fun p => (p : ℝ) ^ m.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hm]
    rw [Nat.cast_prod]
    simp [Nat.cast_pow]
  rw [hprod]
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Real.log_pow]
  · intro p hp
    exact ne_of_gt (pow_pos (by
      exact_mod_cast (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp)) : (0 : ℝ) < (p : ℝ)) _)

/-- logarithm of the per-prime benefit factor of `m`:
`log σ(m) − (1+ε)·log m = Σ_{p | m} log(caBen p ε (v_p(m)))`. -/
private lemma log_ben_eq_sum_log_caBen {m : ℕ} {ε : ℝ} (hm : m ≠ 0) :
    Real.log (((ArithmeticFunction.sigma 1 m : ℕ) : ℝ)) - (1 + ε) * Real.log (m : ℝ) =
      Finset.sum m.primeFactors (fun p => Real.log (caBen p ε (m.factorization p))) := by
  have h1 := log_sigma_eq_sum_log_primeFactors (m := m) hm
  have h2 := log_nat_eq_sum_primeFactors (m := m) hm
  rw [h1, h2]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hcb := caBen_log (p := p) (ε := ε) (b := m.factorization p) hp'.two_le
  rw [hcb]
  ring

/-- per-prime optimality in the `caBen` normal form. -/
private lemma caBen_le_caExp_local {p : ℕ} {ε : ℝ} {b : ℕ} (hp : Nat.Prime p) (hε : 0 < ε) :
    caBen p ε b ≤ caBen p ε (caExp p ε) := by
  have h := caBen_le_caExp (p := p) (ε := ε) (b := b) hp hε
  simpa [caBen, caExp, caMu] using h

/-- a range-prime benefit factor is `≥ 1`: `1 ≤ caBen p ε (caExp p ε)`. -/
private lemma one_le_caBen_caExp {p : ℕ} {ε : ℝ} (hp : Nat.Prime p) (hε : 0 < ε) :
    (1 : ℝ) ≤ caBen p ε (caExp p ε) := by
  have h := caBen_le_caExp_local (p := p) (ε := ε) (b := 0) hp hε
  simpa [caBen_zero] using h

/-- the logarithmic per-prime benefit is monotone in the exponent towards `caExp`. -/
private lemma log_caBen_le_caExp {p : ℕ} {ε : ℝ} {b : ℕ} (hp : Nat.Prime p) (hε : 0 < ε) :
    Real.log (caBen p ε b) ≤ Real.log (caBen p ε (caExp p ε)) :=
  Real.log_le_log (caBen_pos (p := p) (ε := ε) (b := b) (Nat.Prime.pos hp))
    (caBen_le_caExp_local hp hε)

/-- GLOBAL ALAOGLU–ERDŐS MAXIMALITY (log form): for every `ε > 0`, `N_ε` maximizes
`ben_ε(m) = log σ(m) − (1+ε)·log m` over all `m ≥ 1`. -/
private theorem ca_global_maximality_log_aux {ε : ℝ} (hε : 0 < ε) (m : ℕ) (hm : m ≠ 0) :
    Real.log (((ArithmeticFunction.sigma 1 m : ℕ) : ℝ)) - (1 + ε) * Real.log (m : ℝ) ≤
    Real.log (((ArithmeticFunction.sigma 1 (caN ε) : ℕ) : ℝ)) -
      (1 + ε) * Real.log ((caN ε : ℕ) : ℝ) := by
  rw [log_ben_eq_sum_log_caBen (m := m) hm]
  rw [log_ben_caN_eq_sum (ε := ε)]
  have h1 : Finset.sum m.primeFactors (fun p => Real.log (caBen p ε (m.factorization p))) ≤
      Finset.sum m.primeFactors (fun p => Real.log (caBen p ε (caExp p ε))) :=
    Finset.sum_le_sum (fun p hp =>
      log_caBen_le_caExp (Nat.prime_of_mem_primeFactors hp) hε)
  have f_nonneg : ∀ p, Nat.Prime p → (0 : ℝ) ≤ Real.log (caBen p ε (caExp p ε)) :=
    fun p hp => Real.log_nonneg (one_le_caBen_caExp hp hε)
  have f_zero_outside : ∀ p, p ∈ m.primeFactors → p ∉ caPrimes ε →
      Real.log (caBen p ε (caExp p ε)) = 0 := by
    intro p hp hnotR
    have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hge : caBound ε ≤ p := by
      by_contra hlt
      have hlt' : p < caBound ε := Nat.lt_of_not_ge hlt
      exact hnotR (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt', hp'⟩)
    have hz : caExp p ε = 0 := by
      simpa [caExp, caMu] using
        caExp_eq_zero_of_ge_bound p ε hp'.two_le hε (by simpa [caBound] using hge)
    rw [hz]
    simp [caBen_zero]
  have h2 : Finset.sum m.primeFactors (fun p => Real.log (caBen p ε (caExp p ε))) ≤
      Finset.sum (caPrimes ε) (fun p => Real.log (caBen p ε (caExp p ε))) := by
    calc
      Finset.sum m.primeFactors (fun p => Real.log (caBen p ε (caExp p ε)))
          = Finset.sum m.primeFactors
              (fun p => if p ∈ caPrimes ε then Real.log (caBen p ε (caExp p ε)) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            by_cases hR : p ∈ caPrimes ε
            · simp [hR]
            · simp [hR, f_zero_outside p hp hR]
      _ = Finset.sum (m.primeFactors.filter (fun p => p ∈ caPrimes ε))
              (fun p => Real.log (caBen p ε (caExp p ε))) := by
            rw [Finset.sum_filter]
      _ ≤ Finset.sum (caPrimes ε) (fun p => Real.log (caBen p ε (caExp p ε))) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro p hp
              exact (Finset.mem_filter.mp hp).2
            · intro p hp _
              exact f_nonneg p (Finset.mem_filter.mp hp).2
  exact le_trans h1 h2

/-- The previous CA member `N⁻(ε)`, unfolded to the explicit range product appearing in the
statement of `ca_minus_maximality_log` (definitional identity). -/
private lemma Nminus_eq_inline (ε : ℝ) :
    Nminus ε = ((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ (if Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ) = (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ : ℝ) ∧ 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ then ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ - 1 else ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)))) := rfl

private theorem ca_minus_maximality_log {ε : ℝ} (hε : 0 < ε) (m : ℕ) (hm : m ≠ 0) :
    Real.log ((ArithmeticFunction.sigma 1 (m) : ℕ) : ℝ) - (1 + ε) * Real.log (m : ℝ) ≤
    Real.log ((ArithmeticFunction.sigma 1 ((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ (if Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ) = (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ : ℝ) ∧ 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ then ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ - 1 else ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)))) : ℕ) : ℝ) - (1 + ε) * Real.log ((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ (if Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ) = (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ : ℝ) ∧ 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ then ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ - 1 else ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊))) : ℝ) := by
  have key : Real.log (((ArithmeticFunction.sigma 1 m : ℕ) : ℝ)) - (1 + ε) * Real.log (m : ℝ) ≤
      Real.log (((ArithmeticFunction.sigma 1 (Nminus ε) : ℕ) : ℝ)) -
        (1 + ε) * Real.log ((Nminus ε : ℕ) : ℝ) :=
    le_trans (ca_global_maximality_log_aux hε m hm)
      (le_of_eq (ca_minus_ben_eq_core hε).symm)
  simp only [← Nat.cast_prod, ← Nat.cast_pow]
  rw [← Nminus_eq_inline (ε := ε)]
  exact key

end Port2

/-! ## Port3 — co-optimality of `N⁻(ε)` (private port of `ca_minus_ben_eq.lean`) -/

namespace Port3


/-- the finite support bound of the CA product: `⌈exp(2/ε)⌉ + 2`. -/
private def caBound (ε : ℝ) : ℕ := Nat.ceil (Real.exp (2 / ε)) + 2

/-- the range of primes over which the CA product is taken. -/
private def caPrimes (ε : ℝ) : Finset ℕ := (Finset.range (caBound ε)).filter Nat.Prime

/-- the exponent of `p` in the previous CA member `N⁻(ε)`: `caExp p ε − 1` at jump primes
(where `μ(p,ε) = ⌊μ(p,ε)⌋₊ ≥ 1` is an integer), else `caExp p ε`. -/
private def caMinusExp (p : ℕ) (ε : ℝ) : ℕ :=
  if caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε then caExp p ε - 1 else caExp p ε

/-- the CA number `N_ε`. -/
private def Nε (ε : ℝ) : ℕ :=
  Finset.prod (caPrimes ε) (fun p => p ^ caExp p ε)

/-- the previous CA member `N⁻(ε)`. -/
private def Nminus (ε : ℝ) : ℕ :=
  Finset.prod (caPrimes ε) (fun p => p ^ caMinusExp p ε)

/-- logarithm of `caBen`: `log(caBen p ε b) = log σ(p^b) − b(1+ε)·log p`. -/
private lemma caBen_log {p : ℕ} {ε : ℝ} {b : ℕ} (hp : 2 ≤ p) :
    Real.log (caBen p ε b) =
      Real.log (((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ)) -
        (b : ℝ) * (1 + ε) * Real.log (p : ℝ) := by
  unfold caBen
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hσ' : 0 < ArithmeticFunction.sigma 1 (p ^ b) :=
    (ArithmeticFunction.sigma_pos_iff).2 (pow_pos (by omega : 0 < p) b)
  have hσr : (0 : ℝ) < ((ArithmeticFunction.sigma 1 (p ^ b) : ℕ) : ℝ) := by exact_mod_cast hσ'
  have hrpow : (0 : ℝ) < (p : ℝ) ^ ((b : ℝ) * (1 + ε)) :=
    Real.rpow_pos_of_pos hp0 ((b : ℝ) * (1 + ε))
  rw [Real.log_div hσr.ne' hrpow.ne']
  rw [Real.log_rpow hp0]

/-- multiplicativity of `σ 1` over a product of prime powers with distinct primes. -/
private lemma sigma_prod_prime_pows {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p) (a : ℕ → ℕ) :
    ArithmeticFunction.sigma 1 (Finset.prod s (fun p => p ^ a p)) =
      Finset.prod s (fun p => ArithmeticFunction.sigma 1 (p ^ a p)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hpnot ih =>
      have hp' : Nat.Prime p := hprime p (by simp)
      have hcop : (p ^ a p).Coprime (Finset.prod s (fun q => q ^ a q)) := by
        apply Nat.Coprime.prod_right
        intro q hq
        have hq' : Nat.Prime q := hprime q (Finset.mem_insert_of_mem hq)
        have hpq_ne : q ≠ p := by
          intro hpq
          exact hpnot (by simpa [hpq] using hq)
        have hpq : p.Coprime q := (Nat.coprime_primes hp' hq').mpr (Ne.symm hpq_ne)
        have h1 : p.Coprime (q ^ a q) := Nat.Coprime.pow_right (a q) hpq
        exact Nat.Coprime.pow_left (a p) h1
      have hσ := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
      have ih' := ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
      rw [Finset.prod_insert hpnot, hσ, ih', Finset.prod_insert hpnot]

/-- log factorisation of `σ` of a prime-power range product. -/
private lemma log_sigma_prod_pows_of_prime {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    (a : ℕ → ℕ) :
    Real.log (((ArithmeticFunction.sigma 1 (Finset.prod s (fun p => p ^ a p)) : ℕ) : ℝ)) =
      Finset.sum s (fun p =>
        Real.log (((ArithmeticFunction.sigma 1 (p ^ a p) : ℕ) : ℝ))) := by
  have hfac : ArithmeticFunction.sigma 1 (Finset.prod s (fun p => p ^ a p)) =
      Finset.prod s (fun p => ArithmeticFunction.sigma 1 (p ^ a p)) :=
    sigma_prod_prime_pows (s := s) hprime (fun p => a p)
  rw [hfac]
  rw [Nat.cast_prod]
  rw [Real.log_prod]
  intro p hp
  have hp' : Nat.Prime p := hprime p hp
  have hσ : 0 < ArithmeticFunction.sigma 1 (p ^ a p) :=
    (ArithmeticFunction.sigma_pos_iff).2 (pow_pos (Nat.Prime.pos hp') (a p))
  exact_mod_cast (ne_of_gt hσ)

/-- log of a real prime-power range product (the `ℝ`-valued product used in the target). -/
private lemma log_prod_rpow_of_prime {s : Finset ℕ} (hprime : ∀ p ∈ s, Nat.Prime p)
    (a : ℕ → ℕ) :
    Real.log (Finset.prod s (fun p => (p : ℝ) ^ a p)) =
      Finset.sum s (fun p => (a p : ℝ) * Real.log (p : ℝ)) := by
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Real.log_pow]
  · intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos (hprime p hp))
    exact ne_of_gt (pow_pos hp0 (a p))

/-- log-benefit factorisation of an arbitrary prime-power range product (log-argument taken
in the `ℝ`-valued product form appearing in the goal). -/
private lemma log_ben_range_prodR {ε : ℝ} (a : ℕ → ℕ) :
    Real.log (((ArithmeticFunction.sigma 1
        (Finset.prod (caPrimes ε) (fun p => p ^ a p)) : ℕ) : ℝ)) -
      (1 + ε) * Real.log (Finset.prod (caPrimes ε) (fun p => (p : ℝ) ^ a p)) =
      Finset.sum (caPrimes ε) (fun p => Real.log (caBen p ε (a p))) := by
  have hprime : ∀ p ∈ caPrimes ε, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  have h1 := log_sigma_prod_pows_of_prime (s := caPrimes ε) hprime a
  have h2 := log_prod_rpow_of_prime (s := caPrimes ε) hprime a
  rw [h1, h2]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp' : Nat.Prime p := hprime p hp
  have hcb := caBen_log (p := p) (ε := ε) (b := a p) hp'.two_le
  rw [hcb]
  ring

/-- from `μ(p,ε) = k` deduce the rpow equation `p^{1+ε} = (p^{k+1}−1)/(p^k−1)`
(prime `p`, `ε > 0`, `k ≥ 1`). -/
private lemma caMu_eq_imp_rpow_eq {p : ℕ} {ε : ℝ} {k : ℕ} (hp : Nat.Prime p) (hε : 0 < ε)
    (hk : 1 ≤ k) (hmu : caMu p ε = (k : ℝ)) :
    (p : ℝ) ^ (1 + ε) = (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos hp)
  have hlogp : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1r)
  have h1pe : 0 < 1 + ε := by linarith
  have hYgt1 : 1 < (p : ℝ) ^ (1 + ε) := by
    rw [Real.one_lt_rpow_iff (le_of_lt hp0)]
    exact Or.inl ⟨hp1r, h1pe⟩
  have hYp : 0 < (p : ℝ) ^ (1 + ε) - (p : ℝ) := by
    have hpe : 1 < (p : ℝ) ^ ε := by
      rw [Real.one_lt_rpow_iff (le_of_lt hp0)]
      exact Or.inl ⟨hp1r, hε⟩
    have hp1e : (p : ℝ) * (p : ℝ) ^ ε = (p : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hp0, Real.rpow_one]
    rw [← hp1e]
    exact sub_pos.mpr (by
      have hm := mul_lt_mul_of_pos_left hpe hp0
      simpa using hm)
  let Y : ℝ := (p : ℝ) ^ (1 + ε)
  let X : ℝ := (Y - 1) / (Y - (p : ℝ))
  have hXpos : 0 < X := by
    dsimp [X]
    exact div_pos (by linarith) hYp
  have hlogX : Real.log X = (k : ℝ) * Real.log (p : ℝ) := by
    have hmu' : Real.log X / Real.log (p : ℝ) = (k : ℝ) := by
      dsimp [X, Y]
      unfold caMu at hmu
      simpa using hmu
    calc
      Real.log X = Real.log X / Real.log (p : ℝ) * Real.log (p : ℝ) := by field_simp [hlogp]
      _ = (k : ℝ) * Real.log (p : ℝ) := by rw [hmu']
  have hXeq : X = (p : ℝ) ^ (k : ℕ) := by
    have he := congrArg Real.exp hlogX
    have hL : Real.exp (Real.log X) = X := Real.exp_log hXpos
    have hR : Real.exp ((k : ℝ) * Real.log (p : ℝ)) = (p : ℝ) ^ (k : ℕ) := by
      rw [Real.exp_nat_mul]
      rw [Real.exp_log hp0]
    simpa [hL, hR] using he
  have hpk1 : (p : ℝ) ^ k - 1 ≠ 0 := by
    have h : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
    linarith
  have hpowsucc : (p : ℝ) ^ (k : ℕ) * (p : ℝ) = (p : ℝ) ^ (k + 1 : ℕ) := by
    rw [pow_succ']
    ring
  have hmul : Y - 1 = (p : ℝ) ^ (k : ℕ) * (Y - (p : ℝ)) := by
    have hYp' : Y - (p : ℝ) ≠ 0 := ne_of_gt hYp
    calc
      Y - 1 = ((Y - 1) / (Y - (p : ℝ))) * (Y - (p : ℝ)) := by field_simp [hYp']
      _ = (p : ℝ) ^ (k : ℕ) * (Y - (p : ℝ)) := by
        dsimp [X] at hXeq
        rw [hXeq]
  let Z : ℝ := (p : ℝ) ^ (k : ℕ) * Y
  have hmul' : Y - 1 = Z - (p : ℝ) ^ (k + 1 : ℕ) := by
    calc
      Y - 1 = (p : ℝ) ^ (k : ℕ) * (Y - (p : ℝ)) := hmul
      _ = Z - (p : ℝ) ^ (k + 1 : ℕ) := by
        dsimp [Z]
        rw [← hpowsucc]
        ring
  have hZ : Z - Y = (p : ℝ) ^ (k + 1 : ℕ) - 1 := by
    linarith
  have hY : Y = (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by
    have hZ' : Y * ((p : ℝ) ^ (k : ℕ) - 1) = (p : ℝ) ^ (k + 1 : ℕ) - 1 := by
      calc
        Y * ((p : ℝ) ^ (k : ℕ) - 1) = Z - Y := by dsimp [Z]; ring
        _ = (p : ℝ) ^ (k + 1 : ℕ) - 1 := hZ
    calc
      Y = (Y * ((p : ℝ) ^ (k : ℕ) - 1)) / (((p : ℝ) ^ k) - 1) := by field_simp [hpk1]
      _ = (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by rw [hZ']
  simpa [Y] using hY

/-- generalized per-prime co-optimality: at a parameter `ε` with `μ(p,ε) = b ≥ 1` an integer,
the two neighbouring exponents `b−1` and `b` give the same `ben_ε` factor. -/
private lemma caBen_eq_pred_of_mu_int {p : ℕ} {ε : ℝ} {b : ℕ} (hp : Nat.Prime p) (hε : 0 < ε)
    (hb : 1 ≤ b) (hmu : caMu p ε = (b : ℝ)) :
    caBen p ε (b - 1) = caBen p ε b := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos hp)
  have hr : (p : ℝ) ^ (1 + ε) = (((p : ℝ) ^ (b + 1 : ℕ)) - 1) / (((p : ℝ) ^ b) - 1) :=
    caMu_eq_imp_rpow_eq hp hε hb hmu
  have hpk1 : (p : ℝ) ^ b - 1 ≠ 0 := by
    have h : 1 < (p : ℝ) ^ b := one_lt_pow₀ hp1r (by omega : b ≠ 0)
    linarith
  have hpkp1 : (p : ℝ) ^ (b + 1 : ℕ) - 1 ≠ 0 := by
    have h : 1 < (p : ℝ) ^ (b + 1 : ℕ) := one_lt_pow₀ hp1r (by omega : b + 1 ≠ 0)
    linarith
  have hp1ne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hRpos : (0 : ℝ) < (p : ℝ) ^ (((b - 1 : ℕ) : ℝ) * (1 + ε)) :=
    Real.rpow_pos_of_pos hp0 (((b - 1 : ℕ) : ℝ) * (1 + ε))
  have hRp1 : (0 : ℝ) < (p : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos hp0 (1 + ε)
  have hexp : ((b - 1 : ℕ) : ℝ) * (1 + ε) + (1 + ε) = (b : ℝ) * (1 + ε) := by
    have hbn : (b : ℕ) = (b - 1) + 1 := (Nat.sub_add_cancel hb).symm
    have hbr : (b : ℝ) = ((b - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast hbn
    nlinarith
  rw [caBen_eq_closed (p := p) (ε := ε) (b := b - 1) hp]
  rw [caBen_eq_closed (p := p) (ε := ε) (b := b) hp]
  have hkadd : (b - 1 + 1 : ℕ) = b := by omega
  rw [hkadd]
  have hRb : (p : ℝ) ^ ((b : ℝ) * (1 + ε)) =
      (p : ℝ) ^ (((b - 1 : ℕ) : ℝ) * (1 + ε)) * (p : ℝ) ^ (1 + ε) := by
    rw [← hexp, Real.rpow_add hp0]
  calc
    (((p : ℝ) ^ b) - 1) / (((p : ℝ) - 1) * ((p : ℝ) ^ (((b - 1 : ℕ) : ℝ) * (1 + ε))))
        = (((p : ℝ) ^ (b + 1 : ℕ)) - 1) / (((p : ℝ) - 1) * ((p : ℝ) ^ ((b : ℝ) * (1 + ε)))) := by
          rw [hRb, hr]
          field_simp [hp1ne, hpk1, hpkp1, hRpos.ne', hRp1.ne']

/-- `caMinusExp p ε ≤ caExp p ε`. -/
private lemma caMinusExp_le (p : ℕ) (ε : ℝ) : caMinusExp p ε ≤ caExp p ε := by
  unfold caMinusExp
  by_cases h : caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε
  · rw [if_pos h]
    omega
  · rw [if_neg h]

/-- `caMinusExp = caExp` away from jump primes. -/
private lemma caMinusExp_eq_caExp {p : ℕ} {ε : ℝ}
    (h : ¬(caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε)) : caMinusExp p ε = caExp p ε := by
  unfold caMinusExp
  rw [if_neg h]

/-- `caMinusExp = caExp − 1` at jump primes. -/
private lemma caMinusExp_eq_pred {p : ℕ} {ε : ℝ}
    (h : caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε) : caMinusExp p ε = caExp p ε - 1 := by
  unfold caMinusExp
  rw [if_pos h]

/-- per-prime benefit equality at every prime: the previous exponent gives the same
`ben_ε`-factor as the optimal one. -/
private lemma caBen_eq_of_caMinusExp {p : ℕ} {ε : ℝ} (hp : Nat.Prime p) (hε : 0 < ε) :
    caBen p ε (caMinusExp p ε) = caBen p ε (caExp p ε) := by
  by_cases h : caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε
  · have hmin := caMinusExp_eq_pred (p := p) (ε := ε) h
    rw [hmin]
    exact caBen_eq_pred_of_mu_int (p := p) (ε := ε) (b := caExp p ε) hp hε h.2 h.1
  · rw [caMinusExp_eq_caExp (p := p) (ε := ε) h]

/-- TRANSITION (T3, product level): `N⁻(ε)` and `N_ε` give the same `ben_ε` value.
The `log`-arguments are written in the `ℝ`-valued product form of the goal, so that the
statement is syntactically the goal statement with `Nminus ε`, `Nε ε` abbreviated. -/
private theorem ca_minus_ben_eq_coreR {ε : ℝ} (hε : 0 < ε) :
    Real.log (((ArithmeticFunction.sigma 1 (Nminus ε) : ℕ) : ℝ)) -
        (1 + ε) * Real.log (Finset.prod (caPrimes ε) (fun p => (p : ℝ) ^ caMinusExp p ε)) =
      Real.log (((ArithmeticFunction.sigma 1 (Nε ε) : ℕ) : ℝ)) -
        (1 + ε) * Real.log (Finset.prod (caPrimes ε) (fun p => (p : ℝ) ^ caExp p ε)) := by
  have key : Finset.sum (caPrimes ε) (fun p => Real.log (caBen p ε (caMinusExp p ε))) =
      Finset.sum (caPrimes ε) (fun p => Real.log (caBen p ε (caExp p ε))) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
    exact congrArg Real.log (caBen_eq_of_caMinusExp (p := p) (ε := ε) hp' hε)
  calc
    Real.log (((ArithmeticFunction.sigma 1 (Nminus ε) : ℕ) : ℝ)) -
        (1 + ε) * Real.log (Finset.prod (caPrimes ε) (fun p => (p : ℝ) ^ caMinusExp p ε))
        = Finset.sum (caPrimes ε) (fun p => Real.log (caBen p ε (caMinusExp p ε))) := by
          unfold Nminus
          exact log_ben_range_prodR (ε := ε) (fun p => caMinusExp p ε)
    _ = Finset.sum (caPrimes ε) (fun p => Real.log (caBen p ε (caExp p ε))) := key
    _ = Real.log (((ArithmeticFunction.sigma 1 (Nε ε) : ℕ) : ℝ)) -
        (1 + ε) * Real.log (Finset.prod (caPrimes ε) (fun p => (p : ℝ) ^ caExp p ε)) := by
          unfold Nε
          exact (log_ben_range_prodR (ε := ε) (fun p => caExp p ε)).symm

private theorem ca_minus_ben_eq {ε : ℝ} (hε : 0 < ε) :
    Real.log ((ArithmeticFunction.sigma 1 ((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ (if Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ) = (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ : ℝ) ∧ 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ then ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ - 1 else ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)))) : ℕ) : ℝ) - (1 + ε) * Real.log ((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ (if Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ) = (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ : ℝ) ∧ 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ then ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ - 1 else ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊))) : ℝ) =
    Real.log ((ArithmeticFunction.sigma 1 ((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊))) : ℕ) : ℝ) - (1 + ε) * Real.log ((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) : ℝ) := by
  have h := ca_minus_ben_eq_coreR hε
  unfold Nε Nminus caPrimes caBound caMinusExp caExp caMu at h
  exact h

end Port3

/-! ## Port1 — colossally abundant core (private port of `robin_of_ca_cover.lean`'s mirror) -/

namespace Port1


/-- `F(p,k) = log((p^{k+1}−1)/(p^{k+1}−p))/log p` for `k ≥ 1` (Nicolas (4.5)). -/
private def caF (p : ℕ) (k : ℕ) : ℝ :=
  Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) / Real.log (p : ℝ)

/-- A finite bound for the support of `p ↦ caExp p ε`: primes with `caExp p ε ≠ 0` satisfy
`p < caEpsBound ε` (see `caExp_eq_zero_of_lt`); for `ε > 1` no prime contributes. -/
private def caEpsBound (ε : ℝ) : ℕ := if 0 < ε then Nat.ceil (Real.exp (2 / ε)) + 2 else 3

/-- The CA number `N_ε = ∏_{p < caEpsBound ε, p prime} p^{caExp p ε}` (Nicolas (4.11)). -/
private def Nε (ε : ℝ) : ℕ :=
  Finset.prod ((Finset.range (caEpsBound ε)).filter Nat.Prime) (fun p => p ^ caExp p ε)

/-- `p ≥ 2`, `ε > 0`: `caExp p ε = 0 ⟺ μ(p,ε) < 1`. -/
private lemma caExp_eq_zero_iff_mu_lt_one {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    caExp p ε = 0 ↔ caMu p ε < 1 := by
  have hiff : (1 : ℕ) ≤ caExp p ε ↔ ((1 : ℝ) ≤ caMu p ε) := by
    simpa using (caExp_ge_iff_mu (p := p) (ε := ε) (k := 1) hp hε (by norm_num))
  constructor
  · intro h
    by_contra hnot
    have hge : (1 : ℝ) ≤ caMu p ε := le_of_not_gt hnot
    have h1 : 1 ≤ caExp p ε := hiff.mpr hge
    omega
  · intro hlt
    by_contra hne
    have hpos : 1 ≤ caExp p ε := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
    have hge : (1 : ℝ) ≤ caMu p ε := hiff.mp hpos
    linarith


/-- `p ≥ 2`, `ε > 0`, `k ≥ 1`: `μ(p,ε) ≥ k ⟺ ε ≤ F(p,k)` (threshold lemma, commons L263). -/
private lemma caMu_ge_iff_caF_local {p : ℕ} {ε : ℝ} {k : ℕ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k) :
    k ≤ caMu p ε ↔ ε ≤ caF p k := by
  unfold caMu caF
  exact Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε k hp hε hk

/-- `p ≥ 2`, `ε > 0`, `k ≥ 1`: `caExp p ε ≥ k ⟺ ε ≤ F(p,k)` (the (4.12)-style law). -/
private lemma caExp_ge_iff_caF {p : ℕ} {ε : ℝ} {k : ℕ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k) :
    k ≤ caExp p ε ↔ ε ≤ caF p k := by
  rw [caExp_ge_iff_mu hp hε hk]
  exact caMu_ge_iff_caF_local hp hε hk

/-- `p ≥ 2`, `ε > 0`: the exponent of `p` in `N_ε` vanishes iff `ε > F(p,1)`. -/
private lemma caExp_eq_zero_iff_caF1_lt {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    caExp p ε = 0 ↔ caF p 1 < ε := by
  have hiff : (1 : ℕ) ≤ caExp p ε ↔ ε ≤ caF p 1 :=
    caExp_ge_iff_caF hp hε (by norm_num : 1 ≤ 1)
  constructor
  · intro h
    by_contra hnot
    have hle : ε ≤ caF p 1 := le_of_not_gt hnot
    have h1 : 1 ≤ caExp p ε := hiff.mpr hle
    omega
  · intro hlt
    by_contra hne
    have hpos : 1 ≤ caExp p ε := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
    have hle : ε ≤ caF p 1 := hiff.mp hpos
    linarith

/-- `p ≥ 2`, `ε > 0`: `ε > F(p,1)` forces the `p`-exponent in `N_ε` to be 0. -/
private lemma caExp_eq_zero_of_caF1_lt {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (h : caF p 1 < ε) : caExp p ε = 0 := (caExp_eq_zero_iff_caF1_lt hp hε).mpr h


private lemma Nε_pos (ε : ℝ) : 1 ≤ Nε ε := by
  unfold Nε
  exact Finset.one_le_prod' (by
    intro p hp
    have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have h2 : 2 ≤ p := hp'.two_le
    exact Nat.one_le_pow (caExp p ε) p (by omega))

private lemma Nε_eq_one_of_one_le {ε : ℝ} (hε1 : 1 ≤ ε) : Nε ε = 1 := by
  unfold Nε
  apply Finset.prod_eq_one
  intro p hp
  have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hpp : 2 ≤ p := hp'.two_le
  have hε : 0 < ε := lt_of_lt_of_le zero_lt_one hε1
  have hzero : caExp p ε = 0 := caExp_eq_zero_of_caF1_lt hpp hε
    (lt_of_lt_of_le (caF1_lt_one hpp) hε1)
  rw [hzero, pow_zero]

/-- exponent monotonicity (commons L265): `ε ≤ ε'` ⇒ `caExp p ε' ≤ caExp p ε`. -/
private lemma caExp_mono_of_le_local {p : ℕ} {ε ε' : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) (hε' : 0 < ε')
    (hle : ε ≤ ε') : caExp p ε' ≤ caExp p ε := by
  unfold caExp
  exact Commons.NumberTheory.Robin.caExp_mono_of_le p ε ε' hp hε hε' hle

/-- `caEpsBound` is anti-monotone in `ε`: `ε ≤ ε'` ⇒ `caEpsBound ε' ≤ caEpsBound ε`. -/
private lemma caEpsBound_mono {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') (hle : ε ≤ ε') :
    caEpsBound ε' ≤ caEpsBound ε := by
  unfold caEpsBound
  rw [if_pos hε, if_pos hε']
  have h2 : 2 / ε' ≤ 2 / ε := by
    rw [div_le_div_iff₀ hε' hε]
    nlinarith
  have hexp : Real.exp (2 / ε') ≤ Real.exp (2 / ε) := (Real.exp_le_exp).mpr h2
  have hceil : Nat.ceil (Real.exp (2 / ε')) ≤ Nat.ceil (Real.exp (2 / ε)) :=
    Nat.ceil_mono hexp
  exact Nat.add_le_add_right hceil 2


/-- support lemma (commons L264): primes `p ≥ caEpsBound ε` do not divide `N_ε`. -/
private lemma caExp_eq_zero_of_ge_bound_local {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (h : caEpsBound ε ≤ p) : caExp p ε = 0 := by
  unfold caExp
  unfold caEpsBound at h
  rw [if_pos hε] at h
  exact Commons.NumberTheory.Robin.caExp_eq_zero_of_ge_bound p ε hp hε h

/-- value-independence of the `N_ε` product: any range containing the support works. -/
private lemma Nε_eq_prod_range {ε : ℝ} {N : ℕ} (hε : 0 < ε) (hN : caEpsBound ε ≤ N) :
    Nε ε = Finset.prod ((Finset.range N).filter Nat.Prime) (fun p => p ^ caExp p ε) := by
  unfold Nε
  have hsub : (Finset.range (caEpsBound ε)).filter Nat.Prime ⊆
      (Finset.range N).filter Nat.Prime := by
    intro p hp
    rcases (Finset.mem_filter.mp hp) with ⟨hpB, hpp⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hpB) hN), hpp⟩
  exact Finset.prod_subset hsub (by
    intro p hpN hpR
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hpN).2
    have hp2 : 2 ≤ p := hpp.two_le
    have hpBnot : p ∉ Finset.range (caEpsBound ε) := by
      intro hc
      exact hpR (Finset.mem_filter.mpr ⟨hc, hpp⟩)
    have hpge : caEpsBound ε ≤ p := by
      by_contra hlt
      exact hpBnot (Finset.mem_range.mpr (Nat.lt_of_not_ge hlt))
    have hzero : caExp p ε = 0 := caExp_eq_zero_of_ge_bound_local hp2 hε hpge
    rw [hzero, pow_zero])


/-- (4.13): `ε ≤ ε'` (both positive) implies `N_{ε'} ∣ N_ε`. -/
private lemma Nε_dvd_of_le {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') (hle : ε ≤ ε') :
    Nε ε' ∣ Nε ε := by
  let R : Finset ℕ := (Finset.range (caEpsBound ε)).filter Nat.Prime
  have hB : caEpsBound ε' ≤ caEpsBound ε := caEpsBound_mono hε hε' hle
  have hN' : Nε ε' = Finset.prod R (fun p => p ^ caExp p ε') := by
    rw [Nε_eq_prod_range hε' hB]
  have hN : Nε ε = Finset.prod R (fun p => p ^ caExp p ε) := by
    rfl
  -- per-prime exponent inequality inside R
  have hmono : ∀ p ∈ R, caExp p ε' ≤ caExp p ε := by
    intro p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    exact caExp_mono_of_le_local hpp.two_le hε hε' hle
  let Q : ℕ := Finset.prod R (fun p => p ^ (caExp p ε - caExp p ε'))
  have hprod : Finset.prod R (fun p => p ^ caExp p ε) =
      (Finset.prod R (fun p => p ^ caExp p ε')) * Q := by
    dsimp [Q]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hle' : caExp p ε' ≤ caExp p ε := hmono p hp
    calc
      p ^ caExp p ε = p ^ (caExp p ε' + (caExp p ε - caExp p ε')) := by
        rw [Nat.add_sub_cancel' hle']
      _ = p ^ caExp p ε' * p ^ (caExp p ε - caExp p ε') := by rw [pow_add]
  refine ⟨Q, ?_⟩
  calc
    Nε ε = Finset.prod R (fun p => p ^ caExp p ε) := hN
    _ = (Finset.prod R (fun p => p ^ caExp p ε')) * Q := hprod
    _ = Nε ε' * Q := by rw [← hN']

/-- `F(p,k) > 0` for `p ≥ 2`, `k ≥ 1`. -/
private lemma caF_pos {p : ℕ} {k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) : 0 < caF p k := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  unfold caF
  have hpk1 : 1 < (p : ℝ) ^ (k + 1 : ℕ) := one_lt_pow₀ hp1r (by omega : k + 1 ≠ 0)
  have hpk : 1 < (p : ℝ) ^ k := by
    have hle : (p : ℝ) ^ 1 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ (le_of_lt hp1r) (by omega : 1 ≤ k)
    exact lt_of_lt_of_le (by simpa using hp1r) hle
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpm : (p : ℝ) < (p : ℝ) * (p : ℝ) ^ k := by
    simpa using (mul_lt_mul_of_pos_left hpk hp0)
  have hden : 0 < (p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ) := by
    have hpm' : (p : ℝ) * (p : ℝ) ^ k = (p : ℝ) ^ (k + 1 : ℕ) := by
      rw [pow_succ']
    linarith
  have hnum : 0 < (p : ℝ) ^ (k + 1 : ℕ) - 1 := by linarith
  have hquot : 1 < ((p : ℝ) ^ (k + 1 : ℕ) - 1) / ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ)) := by
    rw [one_lt_div hden]
    linarith
  exact div_pos (Real.log_pos hquot) hlogp

private lemma caMu_eq_of_caF {p : ℕ} {k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k) :
    caMu p (caF p k) = (k : ℝ) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos hp)
  have hlogp : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1r)
  let Q : ℝ := (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))
  have hQpos : 0 < Q := by
    dsimp [Q]
    have hnum : 0 < (p : ℝ) ^ (k + 1 : ℕ) - 1 := by
      have h1 : 1 < (p : ℝ) ^ (k + 1 : ℕ) := one_lt_pow₀ hp1r (by omega : k + 1 ≠ 0)
      linarith
    have hden : 0 < (p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ) := by
      have hpk : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
      rw [pow_succ']
      nlinarith [mul_lt_mul_of_pos_left hpk hp0]
    exact div_pos hnum hden
  have hQne : Q ≠ 0 := ne_of_gt hQpos
  have hcaF : caF p k = Real.log Q / Real.log (p : ℝ) := by
    dsimp [caF, Q]
  -- p^{1+caF p k} = p·Q
  have hpow1 : (p : ℝ) ^ (1 + caF p k) = (p : ℝ) * Q := by
    rw [hcaF]
    have hdef := Real.rpow_def_of_pos hp0 (1 + Real.log Q / Real.log (p : ℝ))
    rw [hdef]
    have hring : Real.log (p : ℝ) * (1 + Real.log Q / Real.log (p : ℝ)) =
        Real.log (p : ℝ) + Real.log Q := by
      field_simp [hlogp]
    rw [hring]
    rw [Real.exp_add]
    congr 1
    · exact Real.exp_log hp0
    · exact Real.exp_log hQpos
  -- (p^{1+ε}−1)/(p^{1+ε}−p) = p^k
  have hquot : (((p : ℝ) ^ (1 + caF p k)) - 1) / (((p : ℝ) ^ (1 + caF p k)) - (p : ℝ)) =
      (p : ℝ) ^ k := by
    rw [hpow1]
    have hD : 0 < ((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ) := by
      have hpk : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
      rw [pow_succ']
      nlinarith [mul_lt_mul_of_pos_left hpk hp0]
    have hDne : ((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ) ≠ 0 := ne_of_gt hD
    have hp0ne : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have hp1ne : (p : ℝ) - 1 ≠ 0 := by linarith
    dsimp [Q]
    have hmain : (((p : ℝ) * ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)))) - 1) /
        (((p : ℝ) * ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)))) - (p : ℝ)) =
        ((p : ℝ) ^ (k + 1 : ℕ)) / (p : ℝ) := by
      field_simp [hDne, hp0ne, hp1ne]
      ring
    calc
      (((p : ℝ) * ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)))) - 1) /
          (((p : ℝ) * ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)))) - (p : ℝ))
          = ((p : ℝ) ^ (k + 1 : ℕ)) / (p : ℝ) := hmain
      _ = (p : ℝ) ^ k := by
        have hpp : (p : ℝ) ^ (k + 1 : ℕ) = (p : ℝ) * (p : ℝ) ^ k := by rw [pow_succ']
        rw [hpp]
        field_simp [hp0ne]
  -- take logarithms
  have hlogquot : Real.log ((((p : ℝ) ^ (1 + caF p k)) - 1) / (((p : ℝ) ^ (1 + caF p k)) - (p : ℝ))) =
      (k : ℝ) * Real.log (p : ℝ) := by
    rw [hquot]
    rw [Real.log_pow]
  calc
    caMu p (caF p k) = Real.log ((((p : ℝ) ^ (1 + caF p k)) - 1) / (((p : ℝ) ^ (1 + caF p k)) - (p : ℝ))) / Real.log (p : ℝ) := by
      unfold caMu
      rfl
    _ = ((k : ℝ) * Real.log (p : ℝ)) / Real.log (p : ℝ) := by rw [hlogquot]
    _ = (k : ℝ) := by field_simp [hlogp]


private lemma caMu_eq_imp_rpow_eq {p : ℕ} {ε : ℝ} {k : ℕ} (hp : Nat.Prime p) (hε : 0 < ε) (hk : 1 ≤ k)
    (hmu : caMu p ε = (k : ℝ)) :
    (p : ℝ) ^ (1 + ε) = (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos hp)
  have hlogp : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1r)
  have h1pe : 0 < 1 + ε := by linarith
  have hYgt1 : 1 < (p : ℝ) ^ (1 + ε) := by
    rw [Real.one_lt_rpow_iff (le_of_lt hp0)]
    exact Or.inl ⟨hp1r, h1pe⟩
  have hYp : 0 < (p : ℝ) ^ (1 + ε) - (p : ℝ) := by
    -- p^{1+ε} = p·p^ε > p (since p^ε > 1)
    have hpe : 1 < (p : ℝ) ^ ε := by
      rw [Real.one_lt_rpow_iff (le_of_lt hp0)]
      exact Or.inl ⟨hp1r, hε⟩
    have hp1e : (p : ℝ) * (p : ℝ) ^ ε = (p : ℝ) ^ (1 + ε) := by
      rw [Real.rpow_add hp0, Real.rpow_one]
    rw [← hp1e]
    exact sub_pos.mpr (by
      have hm := mul_lt_mul_of_pos_left hpe hp0
      simpa using hm)
  let Y : ℝ := (p : ℝ) ^ (1 + ε)
  let X : ℝ := (Y - 1) / (Y - (p : ℝ))
  have hXpos : 0 < X := by
    dsimp [X]
    exact div_pos (by linarith) hYp
  have hlogX : Real.log X = (k : ℝ) * Real.log (p : ℝ) := by
    -- hmu: caMu p ε = k; unfold caMu and X
    have hmu' : Real.log X / Real.log (p : ℝ) = (k : ℝ) := by
      dsimp [X, Y]
      unfold caMu at hmu
      simpa using hmu
    calc
      Real.log X = Real.log X / Real.log (p : ℝ) * Real.log (p : ℝ) := by field_simp [hlogp]
      _ = (k : ℝ) * Real.log (p : ℝ) := by rw [hmu']
  have hXeq : X = (p : ℝ) ^ (k : ℕ) := by
    have he := congrArg Real.exp hlogX
    have hL : Real.exp (Real.log X) = X := Real.exp_log hXpos
    have hR : Real.exp ((k : ℝ) * Real.log (p : ℝ)) = (p : ℝ) ^ (k : ℕ) := by
      rw [Real.exp_nat_mul]
      rw [Real.exp_log hp0]
    simpa [hL, hR] using he
  -- X = (Y−1)/(Y−p) = p^k ⟹ Y·(p^k − 1) = p^{k+1} − 1
  have hpk1 : (p : ℝ) ^ k - 1 ≠ 0 := by
    have h : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
    linarith
  have hpowsucc : (p : ℝ) ^ (k : ℕ) * (p : ℝ) = (p : ℝ) ^ (k + 1 : ℕ) := by
    rw [pow_succ']
    ring
  have hmul : Y - 1 = (p : ℝ) ^ (k : ℕ) * (Y - (p : ℝ)) := by
    have hYp' : Y - (p : ℝ) ≠ 0 := ne_of_gt hYp
    calc
      Y - 1 = ((Y - 1) / (Y - (p : ℝ))) * (Y - (p : ℝ)) := by field_simp [hYp']
      _ = (p : ℝ) ^ (k : ℕ) * (Y - (p : ℝ)) := by
        dsimp [X] at hXeq
        rw [hXeq]
  let Z : ℝ := (p : ℝ) ^ (k : ℕ) * Y
  have hmul' : Y - 1 = Z - (p : ℝ) ^ (k + 1 : ℕ) := by
    calc
      Y - 1 = (p : ℝ) ^ (k : ℕ) * (Y - (p : ℝ)) := hmul
      _ = Z - (p : ℝ) ^ (k + 1 : ℕ) := by
        dsimp [Z]
        -- p^k·(Y − p) = p^k·Y − p^{k+1}
        rw [← hpowsucc]
        ring
  have hZ : Z - Y = (p : ℝ) ^ (k + 1 : ℕ) - 1 := by
    linarith  -- linear in Y, Z, p^{k+1}
  have hY : Y = (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by
    have hZ' : Y * ((p : ℝ) ^ (k : ℕ) - 1) = (p : ℝ) ^ (k + 1 : ℕ) - 1 := by
      calc
        Y * ((p : ℝ) ^ (k : ℕ) - 1) = Z - Y := by dsimp [Z]; ring
        _ = (p : ℝ) ^ (k + 1 : ℕ) - 1 := hZ
    -- from hZ': Y·(p^k−1) = p^{k+1}−1 divide by (p^k−1)
    calc
      Y = (Y * ((p : ℝ) ^ (k : ℕ) - 1)) / (((p : ℝ) ^ k) - 1) := by field_simp [hpk1]
      _ = (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by rw [hZ']
  simpa [Y] using hY

private lemma caExp_eq_of_caF {p : ℕ} {k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k) :
    caExp p (caF p k) = k := by
  unfold caExp
  rw [caMu_eq_of_caF hp hk]
  exact Nat.floor_natCast k


private def caMinusExp (p : ℕ) (ε : ℝ) : ℕ :=
  if caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε then caExp p ε - 1 else caExp p ε

private def Nminus (ε : ℝ) : ℕ :=
  Finset.prod ((Finset.range (caEpsBound ε)).filter Nat.Prime) (fun p => p ^ caMinusExp p ε)

private lemma caMinusExp_le (p : ℕ) (ε : ℝ) : caMinusExp p ε ≤ caExp p ε := by
  unfold caMinusExp
  by_cases h : caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε
  · rw [if_pos h]
    omega
  · rw [if_neg h]

private lemma caMinusExp_eq_caExp {p : ℕ} {ε : ℝ}
    (h : ¬(caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε)) : caMinusExp p ε = caExp p ε := by
  unfold caMinusExp
  rw [if_neg h]

private lemma caMinusExp_eq_pred {p : ℕ} {ε : ℝ}
    (h : caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε) : caMinusExp p ε = caExp p ε - 1 := by
  unfold caMinusExp
  rw [if_pos h]

private lemma one_le_Nminus (ε : ℝ) : 1 ≤ Nminus ε := by
  unfold Nminus
  have h : (1 : ℕ) ≤ Finset.prod ((Finset.range (caEpsBound ε)).filter Nat.Prime)
      (fun p => p ^ caMinusExp p ε) := by
    apply Finset.one_le_prod₀
    intro p hp
    have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
    exact one_le_pow₀ (Nat.Prime.one_le hp')
  simpa using h

private lemma pow_caExp_eq_pow_caMinusExp_mul {p : ℕ} {ε : ℝ} :
    p ^ caExp p ε =
      p ^ caMinusExp p ε * if caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε then p else 1 := by
  by_cases hj : caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε
  · have hmin := caMinusExp_eq_pred (p := p) (ε := ε) hj
    rw [hmin]
    rw [if_pos hj]
    have hEq : p ^ caExp p ε = p ^ (caExp p ε - 1) * p := by
      have hss : caExp p ε = (caExp p ε - 1) + 1 := by omega
      rw [hss, pow_add]
      simp
    rw [hEq]
  · have hmin := caMinusExp_eq_caExp (p := p) (ε := ε) hj
    rw [hmin]
    rw [if_neg hj]
    simp

private lemma Nε_eq_Nminus_mul_jump (ε : ℝ) :
    Nε ε = Nminus ε * Finset.prod ((Finset.range (caEpsBound ε)).filter Nat.Prime)
      (fun p => if caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε then p else 1) := by
  let R : Finset ℕ := (Finset.range (caEpsBound ε)).filter Nat.Prime
  unfold Nε Nminus
  calc
    Finset.prod R (fun p => p ^ caExp p ε)
        = Finset.prod R (fun p => p ^ caMinusExp p ε *
            (if caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε then p else 1)) := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          exact pow_caExp_eq_pow_caMinusExp_mul (p := p) (ε := ε)
    _ = Finset.prod R (fun p => p ^ caMinusExp p ε) *
        Finset.prod R (fun p => if caMu p ε = (caExp p ε : ℝ) ∧ 1 ≤ caExp p ε then p else 1) := by
          rw [Finset.prod_mul_distrib]

private lemma Nminus_dvd_Nε (ε : ℝ) : Nminus ε ∣ Nε ε := by
  rw [Nε_eq_Nminus_mul_jump ε]
  exact dvd_mul_right (Nminus ε) _

private lemma caF_strict_anti_k {p : ℕ} {k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    caF p (k + 1) < caF p k := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  let x1 : ℝ := (p : ℝ) ^ (k + 1 : ℕ)
  let x2 : ℝ := (p : ℝ) ^ (k + 2 : ℕ)
  have hx1gtp : (p : ℝ) < x1 := by
    dsimp [x1]
    have h1 : (1 : ℕ) < k + 1 := by omega
    have h := pow_lt_pow_right₀ hp1r h1
    simpa using h
  have hx2gtx1 : x1 < x2 := by
    dsimp [x1, x2]
    have h1 : (k + 1 : ℕ) < k + 2 := by omega
    exact pow_lt_pow_right₀ hp1r h1
  have hx1gt1 : (1 : ℝ) < x1 := lt_trans hp1r hx1gtp
  have hx2gt1 : (1 : ℝ) < x2 := lt_trans hx1gt1 hx2gtx1
  have hxp : (0 : ℝ) < x1 - (p : ℝ) := sub_pos.mpr hx1gtp
  have hxp2 : (0 : ℝ) < x2 - (p : ℝ) := sub_pos.mpr (lt_trans hx1gtp hx2gtx1)
  have hg : (x2 - 1) / (x2 - (p : ℝ)) < (x1 - 1) / (x1 - (p : ℝ)) := by
    have hmain : (x2 - 1) * (x1 - (p : ℝ)) < (x1 - 1) * (x2 - (p : ℝ)) := by
      have hc : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      nlinarith
    rw [div_lt_div_iff₀ hxp2 hxp]
    exact hmain
  have hlg : Real.log ((x2 - 1) / (x2 - (p : ℝ))) < Real.log ((x1 - 1) / (x1 - (p : ℝ))) := by
    have hpos1 : 0 < (x1 - 1) / (x1 - (p : ℝ)) := div_pos (sub_pos.mpr hx1gt1) hxp
    have hpos2 : 0 < (x2 - 1) / (x2 - (p : ℝ)) := div_pos (sub_pos.mpr hx2gt1) hxp2
    exact Real.log_lt_log hpos2 hg
  unfold caF
  rw [div_lt_div_iff₀ hlogp hlogp]
  calc
    Real.log (((p : ℝ) ^ (k + 1 + 1 : ℕ) - 1) / (((p : ℝ) ^ (k + 1 + 1 : ℕ)) - (p : ℝ))) * Real.log (p : ℝ)
        = Real.log (((p : ℝ) ^ (k + 2 : ℕ) - 1) / (((p : ℝ) ^ (k + 2 : ℕ)) - (p : ℝ))) * Real.log (p : ℝ) := by
          have hkk : (k + 1 + 1 : ℕ) = k + 2 := by omega
          rw [hkk]
    _ < Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) * Real.log (p : ℝ) := by
          dsimp [x1, x2] at hlg
          exact mul_lt_mul_of_pos_right hlg hlogp

private lemma caMu_eq_iff_caF_eq {p : ℕ} {ε : ℝ} {k : ℕ} (hp : Nat.Prime p) (hε : 0 < ε) (hk : 1 ≤ k) :
    caMu p ε = (k : ℝ) ↔ ε = caF p k := by
  constructor
  · intro hmu
    have hp2 : 2 ≤ p := hp.two_le
    have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos hp)
    have hlogp : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1r)
    have hrpow := caMu_eq_imp_rpow_eq hp hε hk hmu
    -- log of p^{1+ε} = log((p^{k+1}−1)/(p^k−1))
    have hpk1gt1 : (1 : ℝ) < (p : ℝ) ^ (k + 1 : ℕ) := one_lt_pow₀ hp1r (by omega : k + 1 ≠ 0)
    have hpk_gt1 : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
    have hpk1m : 0 < (p : ℝ) ^ (k + 1 : ℕ) - 1 := by linarith
    have hpkm : 0 < (p : ℝ) ^ k - 1 := by linarith
    have hpos : 0 < (p : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos hp0 (1 + ε)
    have hlogr : Real.log ((p : ℝ) ^ (1 + ε)) = Real.log ((p : ℝ) ^ (k + 1 : ℕ) - 1) - Real.log ((p : ℝ) ^ k - 1) := by
      have hq : (p : ℝ) ^ (1 + ε) = ((p : ℝ) ^ (k + 1 : ℕ) - 1) / ((p : ℝ) ^ k - 1) := hrpow
      have hq' : Real.log ((p : ℝ) ^ (1 + ε)) = Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / ((p : ℝ) ^ k - 1)) := by
        rw [hq]
      rw [hq']
      rw [Real.log_div hpk1m.ne' hpkm.ne']
    have hlog1 : (1 + ε) * Real.log (p : ℝ) =
        Real.log ((p : ℝ) ^ (k + 1 : ℕ) - 1) - Real.log ((p : ℝ) ^ k - 1) := by
      calc
        (1 + ε) * Real.log (p : ℝ) = Real.log ((p : ℝ) ^ (1 + ε)) := by
          rw [Real.log_rpow hp0]
        _ = Real.log ((p : ℝ) ^ (k + 1 : ℕ) - 1) - Real.log ((p : ℝ) ^ k - 1) := hlogr
    -- ε·log p = log((p^{k+1}−1)/(p^{k+1}−p))
    have hp0ne : (p : ℝ) ≠ 0 := ne_of_gt hp0
    have hpk1p : 0 < (p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ) := by
      have hpk : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
      have hm : (p : ℝ) * (p : ℝ) ^ k = (p : ℝ) ^ (k + 1 : ℕ) := by rw [pow_succ']
      have hpkmul : (p : ℝ) < (p : ℝ) * (p : ℝ) ^ k := by
        simpa using (mul_lt_mul_of_pos_left hpk hp0)
      rw [hm] at hpkmul
      exact sub_pos.mpr hpkmul
    have hlog2 : ε * Real.log (p : ℝ) =
        Real.log ((p : ℝ) ^ (k + 1 : ℕ) - 1) - Real.log ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ)) := by
      have hsplit : Real.log ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ)) =
          Real.log (p : ℝ) + Real.log ((p : ℝ) ^ k - 1) := by
        have hfac : (p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ) = (p : ℝ) * ((p : ℝ) ^ k - 1) := by
          rw [pow_succ']
          ring
        rw [hfac]
        rw [Real.log_mul hp0ne hpkm.ne']
      calc
        ε * Real.log (p : ℝ) = (1 + ε) * Real.log (p : ℝ) - Real.log (p : ℝ) := by ring
        _ = (Real.log ((p : ℝ) ^ (k + 1 : ℕ) - 1) - Real.log ((p : ℝ) ^ k - 1)) - Real.log (p : ℝ) := by rw [hlog1]
        _ = Real.log ((p : ℝ) ^ (k + 1 : ℕ) - 1) - (Real.log (p : ℝ) + Real.log ((p : ℝ) ^ k - 1)) := by ring
        _ = Real.log ((p : ℝ) ^ (k + 1 : ℕ) - 1) - Real.log ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ)) := by rw [hsplit]
    -- ε = log((p^{k+1}−1)/(p^{k+1}−p))/log p = caF p k
    unfold caF
    calc
      ε = (ε * Real.log (p : ℝ)) / Real.log (p : ℝ) := by field_simp [hlogp]
      _ = (Real.log ((p : ℝ) ^ (k + 1 : ℕ) - 1) - Real.log ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ))) / Real.log (p : ℝ) := by rw [hlog2]
      _ = Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ))) / Real.log (p : ℝ) := by
        rw [Real.log_div hpk1m.ne' hpk1p.ne']
  · intro h
    rw [h]
    exact caMu_eq_of_caF hp hk

/-! ## F-value membership and monotonicity -/

/-- `V` is a value taken by the CA family: `∃ ε > 0, N_ε = V`. -/
private def caFval (V : ℕ) : Prop := ∃ ε : ℝ, 0 < ε ∧ Nε ε = V

/-- `55440` is an F-value. -/
private theorem caFval_55440 : caFval 55440 := by
  rcases Commons.NumberTheory.Robin.ca_55440_in_family with ⟨ε, hε, h⟩
  exact ⟨ε, hε, by simpa [Nε, caEpsBound, caExp, caMu] using h⟩

/-- the family `N_ε` is unbounded. -/
private theorem caFval_unbounded (B : ℕ) : ∃ V : ℕ, caFval V ∧ B ≤ V := by
  rcases Commons.NumberTheory.Robin.ca_Neps_unbounded B with ⟨ε, hε, h⟩
  refine ⟨Nε ε, ⟨ε, hε, rfl⟩, ?_⟩
  simpa [Nε, caEpsBound, caExp, caMu] using h

/-- monotone values: `ε ≤ ε' ⟹ N_{ε'} ≤ N_ε` (from divisibility (4.13), both positive). -/
private lemma Nε_mono_value {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') (hle : ε ≤ ε') :
    Nε ε' ≤ Nε ε := by
  have hdvd : Nε ε' ∣ Nε ε := Nε_dvd_of_le hε hε' hle
  exact Nat.le_of_dvd (Nε_pos ε) hdvd

/-- strict order-reversal of the value function: smaller value ⟹ larger parameter. -/
private lemma Nε_strict_order {ε₁ ε₂ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) :
    Nε ε₁ < Nε ε₂ → ε₂ < ε₁ := by
  intro hlt
  by_contra hnot
  have hle : ε₁ ≤ ε₂ := le_of_not_gt hnot
  have hmono : Nε ε₂ ≤ Nε ε₁ := Nε_mono_value h₁ h₂ hle
  omega


/-- upper side, exponent bounded by its `ε₀`-value (any `ε' > ε₀`). -/
private lemma caExp_le_of_ge {p : ℕ} {ε₀ ε' : ℝ} (hp : 2 ≤ p) (hε₀ : 0 < ε₀) (hgt : ε₀ < ε') :
    caExp p ε' ≤ caExp p ε₀ := by
  have hε'pos : 0 < ε' := lt_trans hε₀ hgt
  exact caExp_mono_of_le_local hp hε₀ hε'pos (le_of_lt hgt)

/-- lower side, exponent bounded below by its `ε₀`-value (any `ε < ε₀`, positive). -/
private lemma caExp_ge_of_le {p : ℕ} {ε₀ ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) (hεlt : ε < ε₀) :
    caExp p ε₀ ≤ caExp p ε := by
  have hε₀ : 0 < ε₀ := lt_trans hε hεlt
  exact caExp_mono_of_le_local hp hε hε₀ (le_of_lt hεlt)

/-! ## Per-prime exponent windows

Throughout: `p` is a prime, `ε₀ > 0`, and `a = caExp p ε₀`.  These lemmas pin down the
exponent of `p` on one-sided windows to the right of `ε₀` (value `caMinusExp p ε₀`) and to
the left of `ε₀` (value `caExp p ε₀`).
-/

/-- right, exponent 0 at `ε₀`: stays 0 to the right (support shrinks). -/
private lemma caExp_eq_zero_of_right {p : ℕ} {ε₀ ε' : ℝ} (hp : 2 ≤ p) (hε₀ : 0 < ε₀)
    (hgt : ε₀ < ε') (hz : caExp p ε₀ = 0) : caExp p ε' = 0 := by
  have hle := caExp_le_of_ge (p := p) (ε₀ := ε₀) (ε' := ε') hp hε₀ hgt
  omega

/-- right, non-jump, exponent `a ≥ 1` preserved up to `ε' ≤ F(p,a)`. -/
private lemma caExp_eq_of_right_nonjump {p : ℕ} {ε₀ ε' : ℝ} (hp : 2 ≤ p) (hε₀ : 0 < ε₀)
    (hε' : 0 < ε') (hgt : ε₀ < ε') (hU : ε' ≤ caF p (caExp p ε₀))
    (hnj : ¬(caMu p ε₀ = (caExp p ε₀ : ℝ) ∧ 1 ≤ caExp p ε₀)) (hk : 1 ≤ caExp p ε₀) :
    caExp p ε' = caExp p ε₀ := by
  apply le_antisymm
  · exact caExp_le_of_ge (p := p) (ε₀ := ε₀) (ε' := ε') hp hε₀ hgt
  · have hiff := (caExp_ge_iff_caF (p := p) (ε := ε') (k := caExp p ε₀) hp hε' hk)
    exact hiff.mpr hU

/-- right, jump with `μ(p,ε₀) = a = 1`: exponent drops to 0 immediately. -/
private lemma caExp_eq_zero_of_right_jump_one {p : ℕ} {ε₀ ε' : ℝ} (hp : Nat.Prime p) (hε₀ : 0 < ε₀)
    (hgt : ε₀ < ε') (hjump : caMu p ε₀ = (1 : ℝ)) : caExp p ε' = 0 := by
  have hε' : 0 < ε' := lt_trans hε₀ hgt
  have hj' : caMu p ε₀ = ((1 : ℕ) : ℝ) := by simpa using hjump
  have hε0 : ε₀ = caF p 1 :=
    (caMu_eq_iff_caF_eq (p := p) (ε := ε₀) (k := 1) hp hε₀ (by norm_num)).mp hj'
  have hlt : caF p 1 < ε' := by
    rw [← hε0]
    exact hgt
  have hiff := (caExp_eq_zero_iff_caF1_lt (p := p) (ε := ε') hp.two_le hε')
  exact hiff.mpr hlt

/-- right, jump with `μ(p,ε₀) = a ≥ 2`: exponent drops to `a−1` up to `ε' ≤ F(p,a−1)`. -/
private lemma caExp_eq_pred_of_right_jump {p : ℕ} {ε₀ ε' : ℝ} (hp : Nat.Prime p) (hε₀ : 0 < ε₀)
    (hε' : 0 < ε') (hgt : ε₀ < ε') (hU : ε' ≤ caF p (caExp p ε₀ - 1))
    (hjump : caMu p ε₀ = (caExp p ε₀ : ℝ)) (ha2 : 2 ≤ caExp p ε₀) :
    caExp p ε' = caExp p ε₀ - 1 := by
  apply le_antisymm
  · have hk : 1 ≤ caExp p ε₀ := by omega
    have hε0eq : ε₀ = caF p (caExp p ε₀) :=
      (caMu_eq_iff_caF_eq (p := p) (ε := ε₀) (k := caExp p ε₀) hp hε₀ hk).mp hjump
    have h1 : caExp p ε' ≤ caExp p ε₀ := caExp_le_of_ge (p := p) (ε₀ := ε₀) (ε' := ε') hp.two_le hε₀ hgt
    have hnota : ¬(caExp p ε₀ ≤ caExp p ε') := by
      intro hage
      have hiff := (caExp_ge_iff_caF (p := p) (ε := ε') (k := caExp p ε₀) hp.two_le hε' hk)
      have hle' : ε' ≤ caF p (caExp p ε₀) := hiff.mp hage
      rw [← hε0eq] at hle'
      exact (not_lt_of_ge hle') hgt
    have hlt' : caExp p ε' < caExp p ε₀ := lt_of_le_not_ge h1 hnota
    omega
  · have hk' : 1 ≤ caExp p ε₀ - 1 := by omega
    have hiff := (caExp_ge_iff_caF (p := p) (ε := ε') (k := caExp p ε₀ - 1) hp.two_le hε' hk')
    exact hiff.mpr hU

/-- left, exponent 0 at `ε₀`: stays 0 to the left down to `ε > F(p,1)`. -/
private lemma caExp_eq_zero_of_left {p : ℕ} {ε₀ ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (hL : caF p 1 < ε) : caExp p ε = 0 := by
  have hiff := (caExp_eq_zero_iff_caF1_lt (p := p) (ε := ε) hp hε)
  exact hiff.mpr hL

/-- left, exponent preserved down to `ε > F(p,a+1)` (with `ε < ε₀`). -/
private lemma caExp_eq_of_left {p : ℕ} {ε₀ ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) (hlt : ε < ε₀)
    (hL : caF p (caExp p ε₀ + 1) < ε) : caExp p ε = caExp p ε₀ := by
  apply le_antisymm
  · by_contra hnot
    have hlt' : caExp p ε₀ < caExp p ε := lt_of_not_ge hnot
    have hage : caExp p ε₀ + 1 ≤ caExp p ε := by omega
    have hiff := (caExp_ge_iff_caF (p := p) (ε := ε) (k := caExp p ε₀ + 1) hp hε (by omega))
    have hle' : ε ≤ caF p (caExp p ε₀ + 1) := hiff.mp hage
    exact (not_lt_of_ge hle') hL
  · exact caExp_ge_of_le (p := p) (ε₀ := ε₀) (ε := ε) hp hε hlt

/-- `F(p,a+1) < ε₀` always (so the left window is nonempty). -/
private lemma caF_succ_lt {p : ℕ} {ε₀ : ℝ} (hp : 2 ≤ p) (hε₀ : 0 < ε₀) :
    caF p (caExp p ε₀ + 1) < ε₀ := by
  have hk' : 1 ≤ caExp p ε₀ + 1 := by omega
  have hnot : ¬(caExp p ε₀ + 1 ≤ caExp p ε₀) := by omega
  have hiff := (caExp_ge_iff_caF (p := p) (ε := ε₀) (k := caExp p ε₀ + 1) hp hε₀ hk')
  have hnot' : ¬(ε₀ ≤ caF p (caExp p ε₀ + 1)) := by
    intro hle
    exact hnot (hiff.mpr hle)
  exact lt_of_not_ge hnot'

/-- jump ⟹ parameter equals the jump value. -/
private lemma caEq_of_jump {p : ℕ} {ε₀ : ℝ} (hp : Nat.Prime p) (hε₀ : 0 < ε₀)
    (hjump : caMu p ε₀ = (caExp p ε₀ : ℝ)) (hk : 1 ≤ caExp p ε₀) :
    ε₀ = caF p (caExp p ε₀) :=
  (caMu_eq_iff_caF_eq (p := p) (ε := ε₀) (k := caExp p ε₀) hp hε₀ hk).mp hjump

/-- the jump-value upper bound exceeds `ε₀` when the exponent is `≥ 2`. -/
private lemma caF_pred_gt_of_jump {p : ℕ} {ε₀ : ℝ} (hp : Nat.Prime p) (hε₀ : 0 < ε₀)
    (hjump : caMu p ε₀ = (caExp p ε₀ : ℝ)) (ha2 : 2 ≤ caExp p ε₀) :
    ε₀ < caF p (caExp p ε₀ - 1) := by
  have hk : 1 ≤ caExp p ε₀ := by omega
  have hε0eq : ε₀ = caF p (caExp p ε₀) := caEq_of_jump hp hε₀ hjump hk
  have hk' : 1 ≤ caExp p ε₀ - 1 := by omega
  have hanti := caF_strict_anti_k (p := p) (k := caExp p ε₀ - 1) hp.two_le hk'
  have hrew : caF p (caExp p ε₀ - 1 + 1) = caF p (caExp p ε₀) := by
    congr 1
    omega
  calc
    ε₀ = caF p (caExp p ε₀) := hε0eq
    _ = caF p (caExp p ε₀ - 1 + 1) := hrew.symm
    _ < caF p (caExp p ε₀ - 1) := hanti

/-- non-jump with exponent `a ≥ 1`: `ε₀ < F(p,a)`. -/
private lemma caF_gt_of_nonjump {p : ℕ} {ε₀ : ℝ} (hp : Nat.Prime p) (hε₀ : 0 < ε₀)
    (hnj : ¬(caMu p ε₀ = (caExp p ε₀ : ℝ) ∧ 1 ≤ caExp p ε₀)) (hk : 1 ≤ caExp p ε₀) :
    ε₀ < caF p (caExp p ε₀) := by
  have hle : ε₀ ≤ caF p (caExp p ε₀) := by
    have hiff := (caExp_ge_iff_caF (p := p) (ε := ε₀) (k := caExp p ε₀) hp.two_le hε₀ hk)
    exact hiff.mp (le_rfl : caExp p ε₀ ≤ caExp p ε₀)
  have hne : ε₀ ≠ caF p (caExp p ε₀) := by
    intro heq
    have hj : caMu p ε₀ = (caExp p ε₀ : ℝ) :=
      (caMu_eq_iff_caF_eq (p := p) (ε := ε₀) (k := caExp p ε₀) hp hε₀ hk).mpr heq
    exact hnj ⟨hj, hk⟩
  exact lt_of_le_of_ne hle hne

/-! ## Local constancy of the value function -/

/-- `N_ε` is constant on a left-neighbourhood of every `ε₀ > 0`. -/
private theorem Nε_left_local_const {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε₀ - δ < ε → ε < ε₀ → Nε ε = Nε ε₀ := by
  let B : ℕ := caEpsBound (ε₀ / 2)
  let T : Finset ℕ := (Finset.range B).filter Nat.Prime
  let S : Finset ℝ := T.image (fun p => caF p (caExp p ε₀ + 1))
  have hε02 : 0 < ε₀ / 2 := by positivity
  have h2B : (2 : ℕ) < B := by
    have hcex : (1 : ℕ) ≤ Nat.ceil (Real.exp (2 / (ε₀ / 2))) := by
      have hle : Real.exp (0 : ℝ) ≤ Real.exp (2 / (ε₀ / 2)) :=
        (Real.exp_le_exp).mpr (le_of_lt (by positivity : (0 : ℝ) < 2 / (ε₀ / 2)))
      have h1 : (1 : ℝ) ≤ Real.exp (2 / (ε₀ / 2)) := by simpa using hle
      simpa using (Nat.ceil_mono h1 : Nat.ceil (1 : ℝ) ≤ Nat.ceil (Real.exp (2 / (ε₀ / 2))))
    dsimp [B]
    unfold caEpsBound
    rw [if_pos hε02]
    omega
  have h2mem : (2 : ℕ) ∈ T := by
    dsimp [T, B]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2B, by norm_num⟩
  have hTne : T.Nonempty := ⟨2, h2mem⟩
  have hSne : S.Nonempty := by
    refine ⟨caF 2 (caExp 2 ε₀ + 1), ?_⟩
    rw [Finset.mem_image]
    exact ⟨2, h2mem, rfl⟩
  let L : ℝ := S.max' hSne
  have hLmem : L ∈ S := Finset.max'_mem S hSne
  have hAllLt : ∀ v ∈ S, v < ε₀ := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨p, hpT, rfl⟩
    have hp : Nat.Prime p := (Finset.mem_filter.mp hpT).2
    exact caF_succ_lt (p := p) (ε₀ := ε₀) hp.two_le hε₀
  have hLlt : L < ε₀ := hAllLt L hLmem
  have hLpos : 0 < L := by
    -- L ∈ S and every element of S is positive (a caF value with index ≥ 1)
    rcases Finset.mem_image.mp hLmem with ⟨p, hpT, heq⟩
    rw [← heq]
    have hp : Nat.Prime p := (Finset.mem_filter.mp hpT).2
    exact caF_pos hp.two_le (by omega : 1 ≤ caExp p ε₀ + 1)
  let δ : ℝ := min (ε₀ / 2) (ε₀ - L)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min_iff.mpr ⟨hε02, sub_pos.mpr hLlt⟩
  refine ⟨δ, hδ, ?_⟩
  intro ε hlo hhi
  have hεpos : 0 < ε := by
    have hδε : ε₀ / 2 < ε := by
      have h1 : ε₀ / 2 ≤ ε₀ - δ := by
        dsimp [δ]
        have hml : min (ε₀ / 2) (ε₀ - L) ≤ ε₀ / 2 := min_le_left (ε₀ / 2) (ε₀ - L)
        linarith
      exact lt_of_le_of_lt h1 hlo
    exact lt_trans hε02 hδε
  have hεL : L < ε := by
    have h1 : L ≤ ε₀ - δ := by
      dsimp [δ]
      have hml : min (ε₀ / 2) (ε₀ - L) ≤ ε₀ - L := min_le_right (ε₀ / 2) (ε₀ - L)
      linarith
    exact lt_of_le_of_lt h1 hlo
  have hε02le : ε₀ / 2 ≤ ε := le_of_lt (by
    have hδε : ε₀ / 2 < ε := by
      have h1 : ε₀ / 2 ≤ ε₀ - δ := by
        dsimp [δ]
        have hml : min (ε₀ / 2) (ε₀ - L) ≤ ε₀ / 2 := min_le_left (ε₀ / 2) (ε₀ - L)
        linarith
      exact lt_of_le_of_lt h1 hlo
    exact hδε)
  have hexp : ∀ p : ℕ, p ∈ T → caExp p ε = caExp p ε₀ := by
    intro p hpT
    have hp : Nat.Prime p := (Finset.mem_filter.mp hpT).2
    have hLp : caF p (caExp p ε₀ + 1) ≤ L := by
      have hmem : caF p (caExp p ε₀ + 1) ∈ S := by
        rw [Finset.mem_image]
        exact ⟨p, hpT, rfl⟩
      exact Finset.le_max' S (caF p (caExp p ε₀ + 1)) hmem
    have hLplt : caF p (caExp p ε₀ + 1) < ε := lt_of_le_of_lt hLp hεL
    exact caExp_eq_of_left (p := p) (ε₀ := ε₀) (ε := ε) hp.two_le hεpos hhi hLplt
  have hBe : caEpsBound ε ≤ B := by
    dsimp [B]
    exact caEpsBound_mono hε02 hεpos hε02le
  have hB0 : caEpsBound ε₀ ≤ B := by
    dsimp [B]
    exact caEpsBound_mono hε02 hε₀ (by linarith : ε₀ / 2 ≤ ε₀)
  have h1 := Nε_eq_prod_range (ε := ε) (N := B) hεpos hBe
  have h2 := Nε_eq_prod_range (ε := ε₀) (N := B) hε₀ hB0
  rw [h1, h2]
  refine Finset.prod_congr rfl ?_
  intro p hp
  have hpT : p ∈ T := by simpa [T, B] using hp
  exact congrArg (fun e : ℕ => p ^ e) (hexp p hpT)

/-- the exponent of `p` in `Nminus ε₀` is zero whenever `caExp p ε₀ = 0`. -/
private lemma caMinusExp_eq_zero_of_caExp_zero {p : ℕ} {ε₀ : ℝ} (hz : caExp p ε₀ = 0) :
    caMinusExp p ε₀ = 0 := by
  have hle := caMinusExp_le p ε₀
  omega

/-- upper window bound of a constraint prime: the largest `ε'` to which the
right-side exponent identity is guaranteed. -/
private def caRightUB (p : ℕ) (ε₀ : ℝ) : ℝ :=
  if caMu p ε₀ = (caExp p ε₀ : ℝ) then
    if 2 ≤ caExp p ε₀ then caF p (caExp p ε₀ - 1) else ε₀ + 1
  else caF p (caExp p ε₀)

/-- `N_ε` is constant on a right-neighbourhood of every `ε₀ > 0`, with value `Nminus ε₀`. -/
private theorem Nε_right_local_const {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε' : ℝ, ε₀ < ε' → ε' < ε₀ + δ → Nε ε' = Nminus ε₀ := by
  let R0 : Finset ℕ := (Finset.range (caEpsBound ε₀)).filter Nat.Prime
  let T : Finset ℕ := R0.filter (fun p => 1 ≤ caExp p ε₀)
  let S : Finset ℝ := T.image (fun p => caRightUB p ε₀)
  by_cases hT : T.Nonempty
  · -- nonempty constraints: δ := min ε₀ (min S − ε₀)
    have hSne : S.Nonempty := by
      rcases hT with ⟨p0, hp0T⟩
      refine ⟨caRightUB p0 ε₀, ?_⟩
      rw [Finset.mem_image]
      exact ⟨p0, hp0T, rfl⟩
    let u : ℝ := S.min' hSne
    have humem : u ∈ S := Finset.min'_mem S hSne
    have hAllGt : ∀ v ∈ S, ε₀ < v := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨p, hpT, rfl⟩
      have hpT' : p ∈ T := hpT
      have hpR0 : p ∈ R0 := (Finset.mem_filter.mp hpT').1
      have hp : Nat.Prime p := (Finset.mem_filter.mp hpR0).2
      have ha1 : 1 ≤ caExp p ε₀ := (Finset.mem_filter.mp hpT').2
      unfold caRightUB
      by_cases hj : caMu p ε₀ = (caExp p ε₀ : ℝ)
      · by_cases ha2 : 2 ≤ caExp p ε₀
        · rw [if_pos hj, if_pos ha2]
          exact caF_pred_gt_of_jump (p := p) (ε₀ := ε₀) hp hε₀ hj ha2
        · rw [if_pos hj, if_neg ha2]
          linarith
      · rw [if_neg hj]
        exact caF_gt_of_nonjump (p := p) (ε₀ := ε₀) hp hε₀ (fun h => hj h.1) ha1
    have hε₀ltu : ε₀ < u := hAllGt u humem
    let δ : ℝ := min ε₀ (u - ε₀)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min_iff.mpr ⟨hε₀, sub_pos.mpr hε₀ltu⟩
    refine ⟨δ, hδ, ?_⟩
    intro ε' hgt hlt
    have hε' : 0 < ε' := lt_trans hε₀ hgt
    have hε'lt2 : ε' < 2 * ε₀ := by
      have hδle : δ ≤ ε₀ := by
        dsimp [δ]
        exact min_le_left ε₀ (u - ε₀)
      have hε'le : ε' < ε₀ + ε₀ := lt_of_lt_of_le hlt (by linarith)
      linarith
    have hε'leu : ε' < u := by
      have hδle : δ ≤ u - ε₀ := by
        dsimp [δ]
        exact min_le_right ε₀ (u - ε₀)
      have h' : ε₀ + (u - ε₀) = u := by ring
      linarith
    have hleU : ∀ p : ℕ, p ∈ T → ε' ≤ caRightUB p ε₀ := by
      intro p hpT
      have hmem : caRightUB p ε₀ ∈ S := by
        rw [Finset.mem_image]
        exact ⟨p, hpT, rfl⟩
      have hu : u ≤ caRightUB p ε₀ := Finset.min'_le S (caRightUB p ε₀) hmem
      exact le_of_lt (lt_of_lt_of_le hε'leu hu)
    -- per-prime exponent identity on the whole prime range R0
    have hexp : ∀ p : ℕ, p ∈ R0 → caExp p ε' = caMinusExp p ε₀ := by
      intro p hpR0
      have hp : Nat.Prime p := (Finset.mem_filter.mp hpR0).2
      by_cases ha0 : caExp p ε₀ = 0
      · -- exponent 0 at ε₀: stays 0
        have hz' : caExp p ε' = 0 := caExp_eq_zero_of_right (p := p) (ε₀ := ε₀) (ε' := ε') hp.two_le hε₀ hgt ha0
        rw [hz', caMinusExp_eq_zero_of_caExp_zero (p := p) (ε₀ := ε₀) ha0]
      · have ha1 : 1 ≤ caExp p ε₀ := by omega
        have hpT : p ∈ T := by
          dsimp [T]
          exact Finset.mem_filter.mpr ⟨hpR0, ha1⟩
        have hU := hleU p hpT
        unfold caRightUB at hU
        by_cases hj : caMu p ε₀ = (caExp p ε₀ : ℝ)
        · by_cases ha2 : 2 ≤ caExp p ε₀
          · -- jump a ≥ 2: exponent a−1
            have hz' : caExp p ε' = caExp p ε₀ - 1 := by
              rw [if_pos hj, if_pos ha2] at hU
              exact caExp_eq_pred_of_right_jump (p := p) (ε₀ := ε₀) (ε' := ε') hp hε₀ hε' hgt hU hj ha2
            rw [hz']
            have hmin := caMinusExp_eq_pred (p := p) (ε := ε₀) ⟨hj, ha1⟩
            rw [hmin]
          · -- jump a = 1: exponent 0
            have ha1' : caExp p ε₀ = 1 := by omega
            have hz' : caExp p ε' = 0 := by
              have hj' : caMu p ε₀ = (1 : ℝ) := by simpa [ha1'] using hj
              exact caExp_eq_zero_of_right_jump_one (p := p) (ε₀ := ε₀) (ε' := ε') hp hε₀ hgt hj'
            rw [hz']
            have hmin := caMinusExp_eq_pred (p := p) (ε := ε₀) ⟨hj, ha1⟩
            rw [hmin, ha1']
        · -- non-jump: exponent a
          have hz' : caExp p ε' = caExp p ε₀ := by
            rw [if_neg hj] at hU
            exact caExp_eq_of_right_nonjump (p := p) (ε₀ := ε₀) (ε' := ε') hp.two_le hε₀ hε' hgt hU (fun h => hj h.1) ha1
          rw [hz']
          have hmin := caMinusExp_eq_caExp (p := p) (ε := ε₀) (fun h => hj h.1)
          rw [hmin]
    -- value identity
    have hBe : caEpsBound ε' ≤ caEpsBound ε₀ := caEpsBound_mono hε₀ hε' (le_of_lt hgt)
    have h1 := Nε_eq_prod_range (ε := ε') (N := caEpsBound ε₀) hε' hBe
    have h2 : Nminus ε₀ = Finset.prod R0 (fun p => p ^ caMinusExp p ε₀) := rfl
    rw [h1]
    rw [h2]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hpR0 : p ∈ R0 := by simpa [R0] using hp
    exact congrArg (fun e : ℕ => p ^ e) (hexp p hpR0)
  · -- empty constraints: every exponent is 0 on (ε₀, 2ε₀)
    have hzero : ∀ p ∈ R0, caExp p ε₀ = 0 := by
      intro p hpR0
      by_contra hz
      have ha1 : 1 ≤ caExp p ε₀ := by omega
      have hpT : p ∈ T := by
        dsimp [T]
        exact Finset.mem_filter.mpr ⟨hpR0, ha1⟩
      exact hT ⟨p, hpT⟩
    refine ⟨ε₀, hε₀, ?_⟩
    intro ε' hgt hlt
    have hε' : 0 < ε' := lt_trans hε₀ hgt
    have hBe : caEpsBound ε' ≤ caEpsBound ε₀ := caEpsBound_mono hε₀ hε' (le_of_lt hgt)
    have h1 := Nε_eq_prod_range (ε := ε') (N := caEpsBound ε₀) hε' hBe
    have hNminus : Nminus ε₀ = 1 := by
      calc
        Nminus ε₀ = Finset.prod R0 (fun p => p ^ caMinusExp p ε₀) := rfl
        _ = Finset.prod R0 (fun p => p ^ 0) := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          congr 1
          exact caMinusExp_eq_zero_of_caExp_zero (p := p) (ε₀ := ε₀) (hzero p hp)
        _ = 1 := by simp
    rw [h1, hNminus]
    have hz' : ∀ p ∈ R0, caExp p ε' = 0 := by
      intro p hpR0
      exact caExp_eq_zero_of_right (p := p) (ε₀ := ε₀) (ε' := ε')
        (Nat.Prime.two_le (Finset.mem_filter.mp hpR0).2) hε₀ hgt (hzero p hpR0)
    apply Finset.prod_eq_one
    intro p hp
    have hpR0 : p ∈ R0 := by simpa [R0] using hp
    rw [hz' p hpR0]
    simp

/-- COVERING (T3-E): every `n ≥ 55441` lies in the pair `Nminus ε₀ < n ≤ Nε ε₀` with the
previous F-member `Nminus ε₀ ≥ 55440`. -/
private theorem ca_robin_cover_aux (n : ℕ) (hn : 55441 ≤ n) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ Nminus ε₀ < n ∧ n ≤ Nε ε₀ ∧ 55440 ≤ Nminus ε₀ := by
  classical
  let pV : ℕ → Prop := fun V => caFval V ∧ n ≤ V
  have hnonempty : ∃ V : ℕ, pV V := by
    rcases caFval_unbounded n with ⟨V, hV, hVle⟩
    exact ⟨V, ⟨hV, hVle⟩⟩
  let W : ℕ := Nat.find hnonempty
  have hW : pV W := Nat.find_spec hnonempty
  have hWmin : ∀ V : ℕ, pV V → W ≤ V := by
    intro V hV
    exact Nat.find_min' hnonempty hV
  have hWpos : 0 < W := by
    dsimp [pV] at hW
    omega
  rcases hW.1 with ⟨ε_W, hεWpos, hεW⟩
  let P : Set ℝ := {ε : ℝ | 0 < ε ∧ Nε ε = W}
  have hPnonempty : P.Nonempty := ⟨ε_W, ⟨hεWpos, hεW⟩⟩
  have hbdd : BddAbove P := by
    refine ⟨1, ?_⟩
    intro ε hε
    have hε1 : ¬(1 < ε) := by
      intro h1
      have hN : Nε ε = 1 := Nε_eq_one_of_one_le (le_of_lt h1)
      have hW1 : W = 1 := by rw [← hε.2, hN]
      omega
    exact le_of_not_gt hε1
  let est : ℝ := sSup P
  have hestpos : 0 < est := by
    have hle : ε_W ≤ est := le_csSup hbdd ⟨hεWpos, hεW⟩
    dsimp [est] at hle
    linarith
  -- attachment: est ∈ P (left-constancy + sup)
  rcases Nε_left_local_const hestpos with ⟨δ₁, hδ₁, hL⟩
  have hestP : est ∈ P := by
    by_cases h : est ∈ P
    · exact h
    · exfalso
      have happrox : ∃ ε₁ : ℝ, ε₁ ∈ P ∧ est - δ₁ < ε₁ := by
        by_contra hnone
        have hleAll : ∀ b ∈ P, b ≤ est - δ₁ := by
          intro b hb
          by_contra hbgt
          have : est - δ₁ < b := lt_of_not_ge hbgt
          exact hnone ⟨b, hb, this⟩
        have hsup : est ≤ est - δ₁ := csSup_le hPnonempty hleAll
        linarith
      rcases happrox with ⟨ε₁, hε₁P, hgt₁⟩
      have hε₁le : ε₁ ≤ est := le_csSup hbdd hε₁P
      have hε₁lt : ε₁ < est := by
        apply lt_of_le_of_ne hε₁le
        intro heq
        exact h (by simpa [heq] using hε₁P)
      have hval : Nε ε₁ = Nε est := hL ε₁ hgt₁ hε₁lt
      have hEq : Nε est = W := by
        rw [← hval]
        exact hε₁P.2
      exact h ⟨hestpos, hEq⟩
  have hWest : Nε est = W := hestP.2
  -- right-constancy at est: value Nminus est strictly below W
  rcases Nε_right_local_const hestpos with ⟨δ₂, hδ₂, hR⟩
  have hNm_lt_W : Nminus est < W := by
    have hNm_le : Nminus est ≤ W := by
      have hdvd : Nminus est ∣ Nε est := Nminus_dvd_Nε est
      rw [hWest] at hdvd
      exact Nat.le_of_dvd hWpos hdvd
    have hNm_ne : Nminus est ≠ W := by
      intro heq
      let ε'' : ℝ := est + δ₂ / 2
      have hgt'' : est < ε'' := by dsimp [ε'']; linarith
      have hlt'' : ε'' < est + δ₂ := by dsimp [ε'']; linarith
      have hval : Nε ε'' = Nminus est := hR ε'' hgt'' hlt''
      have hP'' : ε'' ∈ P := by
        exact ⟨lt_trans hestpos hgt'', by rw [hval, heq]⟩
      have hle'' : ε'' ≤ est := le_csSup hbdd hP''
      dsimp [ε''] at hle''
      linarith
    exact lt_of_le_of_ne hNm_le hNm_ne
  -- n ≤ Nε est
  have hnWε : n ≤ Nε est := by
    rw [hWest]
    exact hW.2
  -- Nminus est < n
  have hNm_lt_n : Nminus est < n := by
    by_contra hnot
    have hnle : n ≤ Nminus est := le_of_not_gt hnot
    let ε'' : ℝ := est + δ₂ / 2
    have hgt'' : est < ε'' := by dsimp [ε'']; linarith
    have hlt'' : ε'' < est + δ₂ := by dsimp [ε'']; linarith
    have hε''pos : 0 < ε'' := lt_trans hestpos hgt''
    have hval : Nε ε'' = Nminus est := hR ε'' hgt'' hlt''
    have hWle : W ≤ Nminus est := by
      have hV : caFval (Nε ε'') ∧ n ≤ Nε ε'' := by
        constructor
        · exact ⟨ε'', hε''pos, rfl⟩
        · rw [hval]
          exact hnle
      have hmin := hWmin (Nε ε'') hV
      rwa [hval] at hmin
    exact (not_lt_of_ge hWle) hNm_lt_W
  -- 55440 ≤ Nminus est
  have h55440le : 55440 ≤ Nminus est := by
    by_contra hnot
    have hlt : Nminus est < 55440 := lt_of_not_ge hnot
    rcases caFval_55440 with ⟨ε₅, hε₅pos, hε₅⟩
    let ε'' : ℝ := est + δ₂ / 2
    have hgt'' : est < ε'' := by dsimp [ε'']; linarith
    have hlt'' : ε'' < est + δ₂ := by dsimp [ε'']; linarith
    have hε''pos : 0 < ε'' := lt_trans hestpos hgt''
    have hval : Nε ε'' = Nminus est := hR ε'' hgt'' hlt''
    have hε5lt' : ε₅ < ε'' := by
      have hv : Nε ε'' < Nε ε₅ := by
        rw [hval, hε₅]
        exact hlt
      exact Nε_strict_order hε''pos hε₅pos hv
    have hε5gt : est < ε₅ := by
      have hv : Nε ε₅ < Nε est := by
        rw [hε₅, hWest]
        omega
      exact Nε_strict_order hε₅pos hestpos hv
    have hR₅ : Nε ε₅ = Nminus est := hR ε₅ hε5gt (lt_trans hε5lt' hlt'')
    have hEq : Nminus est = 55440 := by
      rw [← hR₅]
      exact hε₅
    rw [hEq] at hlt
    linarith
  exact ⟨est, hestpos, hNm_lt_n, hnWε, h55440le⟩



private lemma Nε_eq_raw (ε : ℝ) (hε : 0 < ε) :
    Nε ε = Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime)
      (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊) := by
  unfold Nε caEpsBound caExp caMu
  rw [if_pos hε]

private lemma Nminus_eq_raw (ε : ℝ) (hε : 0 < ε) :
    Nminus ε = Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime)
      (fun p : ℕ => p ^ (if Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ) = (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ : ℝ) ∧ 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ then ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ - 1 else ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) := by
  unfold Nminus caEpsBound caMinusExp caExp caMu
  rw [if_pos hε]


/-- sigma-ratio log: `log (σ m / m) = log σ(m) − log m` for `m ≥ 1`. -/
private lemma log_sigma_div_self {m : ℕ} (hm : 0 < m) :
    Real.log ((((ArithmeticFunction.sigma 1 m : ℕ) : ℝ)) / (m : ℝ)) =
      Real.log (((ArithmeticFunction.sigma 1 m : ℕ) : ℝ)) - Real.log (m : ℝ) := by
  have hσ' : 0 < ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) := by
    exact_mod_cast (ArithmeticFunction.sigma_pos_iff).2 hm
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Real.log_div hσ'.ne' hmr.ne']

/-- a value of the CA family `N_ε` is also a product in the explicitly written range form. -/
private lemma Nε_mem_raw (ε : ℝ) (hε : 0 < ε) (M : ℕ) (h : Nε ε = M) :
    (Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime)
      (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) = M := by
  rw [← Nε_eq_raw ε hε]
  exact h
theorem robin_of_ca_cover
    (hRobin : ∀ M : ℕ, (∃ ε : ℝ, 0 < ε ∧ (Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) = M) → 55440 ≤ M →
      ((ArithmeticFunction.sigma 1 ((M) : ℕ) : ℕ) : ℝ) ≤ Real.exp Real.eulerMascheroniConstant * (((M) : ℕ) : ℝ) * Real.log (Real.log (((M) : ℕ) : ℝ))) :
    ∀ n : ℕ, 55441 ≤ n → ((ArithmeticFunction.sigma 1 ((n) : ℕ) : ℕ) : ℝ) ≤ Real.exp Real.eulerMascheroniConstant * (((n) : ℕ) : ℝ) * Real.log (Real.log (((n) : ℕ) : ℝ)) := by
  intro n hn
  obtain ⟨ε₀, hε₀pos, hNm_lt, hnle, h55440le⟩ := ca_robin_cover_aux n hn
  have hnpos : 0 < n := by omega
  have hNmpos : 0 < Nminus ε₀ := by
    have h := one_le_Nminus ε₀
    omega
  have hNpos : 0 < Nε ε₀ := by
    have h := Nε_pos ε₀
    omega
  -- `Nminus ε₀` is itself a value of the CA family (right-local constancy)
  have hNmF : ∃ ε' : ℝ, 0 < ε' ∧
      (Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε')) + 2)).filter Nat.Prime)
        (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε')) - 1) / (((p : ℝ) ^ (1 + ε')) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) = Nminus ε₀ := by
    rcases Nε_right_local_const hε₀pos with ⟨δ, hδ, hR⟩
    refine ⟨ε₀ + δ / 2, by linarith, ?_⟩
    have hgt : ε₀ < ε₀ + δ / 2 := by linarith
    have hlt : ε₀ + δ / 2 < ε₀ + δ := by linarith
    have hε' : 0 < ε₀ + δ / 2 := by linarith
    have hval : Nε (ε₀ + δ / 2) = Nminus ε₀ := hR (ε₀ + δ / 2) hgt hlt
    exact Nε_mem_raw (ε₀ + δ / 2) hε' (Nminus ε₀) hval
  have hNF : ∃ ε' : ℝ, 0 < ε' ∧
      (Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε')) + 2)).filter Nat.Prime)
        (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε')) - 1) / (((p : ℝ) ^ (1 + ε')) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) = Nε ε₀ :=
    ⟨ε₀, hε₀pos, Nε_mem_raw ε₀ hε₀pos (Nε ε₀) rfl⟩
  refine robin_pair_bridge (by omega : 5040 ≤ Nminus ε₀) hNm_lt hnle
    (hRobin (Nminus ε₀) hNmF (by omega)) (hRobin (Nε ε₀) hNF (by omega)) ?_
  refine ⟨ε₀, hε₀pos, ?_, ?_⟩
  · -- maximality of `Nminus ε₀` for the benefit with parameter `ε₀`, against `n`
    have hm := Port2.ca_minus_maximality_log (ε := ε₀) hε₀pos n (by omega : n ≠ 0)
    simp only [← Nat.cast_prod, ← Nat.cast_pow] at hm
    rw [← Nminus_eq_raw ε₀ hε₀pos] at hm
    rw [log_sigma_div_self hnpos, log_sigma_div_self hNmpos]
    nlinarith [hm]
  · -- endpoint equality `ben_{ε₀}(Nminus ε₀) = ben_{ε₀}(Nε ε₀)`
    have hb := Port3.ca_minus_ben_eq (ε := ε₀) hε₀pos
    simp only [← Nat.cast_prod, ← Nat.cast_pow] at hb
    rw [← Nminus_eq_raw ε₀ hε₀pos, ← Nε_eq_raw ε₀ hε₀pos] at hb
    rw [log_sigma_div_self hNmpos, log_sigma_div_self hNpos]
    nlinarith [hb]

end Port1

/-! ## The published theorem -/

/-- The family of values of the CA product `N_ε` that are at least `55440`. -/
private def Gfam (M : ℕ) : Prop := (∃ ε : ℝ, 0 < ε ∧ Port1.Nε ε = M) ∧ 55440 ≤ M

theorem robin_of_ca_cover_clean
    (hRobin : ∀ M : ℕ, (∃ ε : ℝ, 0 < ε ∧ (Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)) = M) → 55440 ≤ M →
      ((ArithmeticFunction.sigma 1 ((M) : ℕ) : ℕ) : ℝ) ≤ Real.exp Real.eulerMascheroniConstant * (((M) : ℕ) : ℝ) * Real.log (Real.log (((M) : ℕ) : ℝ))) :
    ∀ n : ℕ, 55441 ≤ n → ((ArithmeticFunction.sigma 1 ((n) : ℕ) : ℕ) : ℝ) ≤ Real.exp Real.eulerMascheroniConstant * (((n) : ℕ) : ℝ) * Real.log (Real.log (((n) : ℕ) : ℝ)) := by
  intro n hn
  -- `hRobin` transported to the predicate `Gfam`
  have hRobinG : ∀ M : ℕ, Gfam M → 5040 ≤ M →
      ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) ≤
        Real.exp Real.eulerMascheroniConstant * (M : ℝ) * Real.log (Real.log (M : ℝ)) := by
    intro M hG _
    rcases hG with ⟨⟨ε, hε, heq⟩, h55440⟩
    exact hRobin M ⟨ε, hε, by rw [← Port1.Nε_eq_raw ε hε]; exact heq⟩ h55440
  refine Commons.NumberTheory.Robin.robin_of_good_family Gfam ?_ hRobinG n hn
  intro n' hn'
  rcases Port1.ca_robin_cover_aux n' hn' with ⟨ε₀, hε₀pos, hNm_lt, hnle, h55440le⟩
  have hnpos : 0 < n' := by omega
  have hNmpos : 0 < Port1.Nminus ε₀ := by
    have h := Port1.one_le_Nminus ε₀
    omega
  have hNpos : 0 < Port1.Nε ε₀ := by
    have h := Port1.Nε_pos ε₀
    omega
  refine ⟨Port1.Nminus ε₀, Port1.Nε ε₀, ?_, ?_, ?_, hNm_lt, hnle, ?_⟩
  · -- `Nminus ε₀` is a value of the CA family
    refine ⟨?_, h55440le⟩
    rcases Port1.Nε_right_local_const hε₀pos with ⟨δ, hδ, hR⟩
    refine ⟨ε₀ + δ / 2, by linarith, ?_⟩
    exact hR (ε₀ + δ / 2) (by linarith) (by linarith)
  · -- `Nε ε₀` is a value of the CA family, and it is `≥ 55440`
    exact ⟨⟨ε₀, hε₀pos, rfl⟩, by omega⟩
  · -- `5040 ≤ Nminus ε₀`
    omega
  · -- maximality at `n'` against `Nminus ε₀`, and co-optimality of `Nminus ε₀` and `Nε ε₀`
    refine ⟨ε₀, hε₀pos, ?_, ?_⟩
    · have hm := Port2.ca_minus_maximality_log (ε := ε₀) hε₀pos n' (by omega : n' ≠ 0)
      simp only [← Nat.cast_prod, ← Nat.cast_pow] at hm
      rw [← Port1.Nminus_eq_raw ε₀ hε₀pos] at hm
      rw [Port1.log_sigma_div_self hnpos, Port1.log_sigma_div_self hNmpos]
      nlinarith [hm]
    · have hb := Port3.ca_minus_ben_eq (ε := ε₀) hε₀pos
      simp only [← Nat.cast_prod, ← Nat.cast_pow] at hb
      rw [← Port1.Nminus_eq_raw ε₀ hε₀pos, ← Port1.Nε_eq_raw ε₀ hε₀pos] at hb
      rw [Port1.log_sigma_div_self hNmpos, Port1.log_sigma_div_self hNpos]
      nlinarith [hb]

end

end Commons.NumberTheory.Robin
