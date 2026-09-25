import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Colossally-abundant core: definitions `caMu`, `caExp`, `Nε` (Alaoglu–Erdős / Nicolas (4.11))

We implement the parameter-`ε` CA family used in the analytic (n > 55440) part of
`robin_upper_rh_aux` (Robin 1984 Thm 1 ⇒ direction).  For a prime `p` and `ε > 0`:

  μ(p,ε) := log((p^{1+ε} − 1) / (p^{1+ε} − p)) / log p        -- Nicolas (4.11)
  a(p,ε) := ⌊μ(p,ε)⌋₊  (exponent of p in the CA number N_ε)
  N_ε     := ∏_{p prime, p < bound(ε)} p^{a(p,ε)}  (finite product)

Finite support: a(p,ε) ≥ 1 ⟺ ε ≤ F(p,1) = log(1+1/p)/log p < 1/p for p ≥ 3, so
contributing primes have p ≤ 1/ε (p = 2 handled separately) — `caExp_eq_zero_of_lt`.
-/

open scoped BigOperators

namespace Commons.NumberTheory.Robin

noncomputable section

/-- `μ(p,ε) = log((p^{1+ε}−1)/(p^{1+ε}−p))/log p`, the (4.11)-exponent parameter. -/
private def caMu (p : ℕ) (ε : ℝ) : ℝ :=
  Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)

/-- The exponent of the prime `p` in the CA number `N_ε`: `⌊μ(p,ε)⌋₊`. -/
private def caExp (p : ℕ) (ε : ℝ) : ℕ := ⌊caMu p ε⌋₊

/-- `F(p,k) = log((p^{k+1}−1)/(p^{k+1}−p))/log p` for `k ≥ 1` (Nicolas (4.5)). -/
private def caF (p : ℕ) (k : ℕ) : ℝ :=
  Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) / Real.log (p : ℝ)

/-- A finite bound for the support of `p ↦ caExp p ε`: primes with `caExp p ε ≠ 0` satisfy
`p < caEpsBound ε` (see `caExp_eq_zero_of_lt`); for `ε > 1` no prime contributes. -/
private def caEpsBound (ε : ℝ) : ℕ := if 0 < ε ∧ ε ≤ 1 then Nat.ceil ((1 : ℝ) / ε) + 2 else 3

/-- The CA number `N_ε = ∏_{p < caEpsBound ε, p prime} p^{caExp p ε}` (Nicolas (4.11)). -/
private def Nε (ε : ℝ) : ℕ :=
  Finset.prod ((Finset.range (caEpsBound ε)).filter Nat.Prime) (fun p => p ^ caExp p ε)

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



/-- `caF p 1 = log(1 + 1/p)/log p` for `p ≥ 2` (F(p,1), Nicolas (4.15)). -/
private lemma caF1_eq_log_one_add {p : ℕ} (hp : 2 ≤ p) :
    caF p 1 = Real.log (1 + 1 / (p : ℝ)) / Real.log (p : ℝ) := by
  unfold caF
  have hk : (1 + 1 : ℕ) = 2 := by norm_num
  rw [hk, pow_two]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by
    have hpne : (p : ℝ) ≠ 1 := by exact_mod_cast (by omega : p ≠ 1)
    exact sub_ne_zero.mpr hpne
  have hmain : ((p : ℝ) * (p : ℝ) - 1) / ((p : ℝ) * (p : ℝ) - (p : ℝ)) =
      1 + 1 / (p : ℝ) := by
    have hnum : (p : ℝ) * (p : ℝ) - 1 = ((p : ℝ) + 1) * ((p : ℝ) - 1) := by ring
    have hden : (p : ℝ) * (p : ℝ) - (p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by ring
    rw [hnum, hden]
    field_simp [hp0, hpm1]
  rw [hmain]

/-- `caF p 1 < 1` for every `p ≥ 2`. -/
private lemma caF1_lt_one {p : ℕ} (hp : 2 ≤ p) : caF p 1 < 1 := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  rw [caF1_eq_log_one_add hp]
  -- 1 + 1/p < p  (p ≥ 2)
  have hlt : Real.log (1 + 1 / (p : ℝ)) < Real.log (p : ℝ) := by
    apply Real.log_lt_log (by positivity : 0 < 1 + 1 / (p : ℝ))
    have h : 1 + 1 / (p : ℝ) < (p : ℝ) := by
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      have h1p : 1 / (p : ℝ) < 1 := by
        rw [div_lt_iff₀ hp0]
        norm_num
        exact_mod_cast (by omega : 1 < p)
      have hlt2 : 1 + 1 / (p : ℝ) < 2 := by linarith
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      exact lt_of_lt_of_le hlt2 hp2
    exact h
  have : Real.log (1 + 1 / (p : ℝ)) / Real.log (p : ℝ) < 1 := by
    exact (div_lt_one hlogp).mpr hlt
  simpa using this

/-- `caF p 1 ≤ 1/(p·log p)` for `p ≥ 2` (crude support bound). -/
private lemma caF1_le_inv_mul_log {p : ℕ} (hp : 2 ≤ p) :
    caF p 1 ≤ 1 / ((p : ℝ) * Real.log (p : ℝ)) := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp0ne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hloglt : Real.log (1 + 1 / (p : ℝ)) ≤ 1 / (p : ℝ) := by
    have hle := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (p : ℝ))
    linarith
  rw [caF1_eq_log_one_add hp]
  have hden : 1 / ((p : ℝ) * Real.log (p : ℝ)) = (1 / (p : ℝ)) / Real.log (p : ℝ) := by
    field_simp [hp0ne, hlogp.ne']
  rw [hden]
  rw [div_le_div_iff₀ hlogp hlogp]
  have hmul : Real.log (1 + 1 / (p : ℝ)) * Real.log (p : ℝ) ≤ (1 / (p : ℝ)) * Real.log (p : ℝ) :=
    mul_le_mul_of_nonneg_right hloglt (le_of_lt hlogp)
  nlinarith [hmul]

/-- `caF p 1 < 1/(p·log p)` for `p ≥ 2`. -/
private lemma caF1_lt_inv_mul_log {p : ℕ} (hp : 2 ≤ p) :
    caF p 1 < 1 / ((p : ℝ) * Real.log (p : ℝ)) := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hloglt : Real.log (1 + 1 / (p : ℝ)) < 1 / (p : ℝ) := by
    have hle := Real.log_lt_sub_one_of_pos (by positivity : 0 < 1 + 1 / (p : ℝ))
    have hne : 1 + 1 / (p : ℝ) ≠ 1 := by
      have : 0 < 1 / (p : ℝ) := by positivity
      linarith
    have hle' := hle hne
    linarith
  rw [caF1_eq_log_one_add hp]
  have hden : 1 / ((p : ℝ) * Real.log (p : ℝ)) = (1 / (p : ℝ)) / Real.log (p : ℝ) := by
    field_simp [ne_of_gt hp0, hlogp.ne']
  rw [hden]
  rw [div_lt_div_iff₀ hlogp hlogp]
  have hmul : Real.log (1 + 1 / (p : ℝ)) * Real.log (p : ℝ) < (1 / (p : ℝ)) * Real.log (p : ℝ) :=
    mul_lt_mul_of_pos_right hloglt hlogp
  nlinarith [hmul]


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


/-- `log a ≤ log b ⟺ a ≤ b` for positive `a, b`. -/
private lemma log_le_log_iff_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a ≤ Real.log b ↔ a ≤ b := by
  constructor
  · intro h
    have hexp := (Real.exp_le_exp).mpr h
    rwa [Real.exp_log ha, Real.exp_log hb] at hexp
  · intro h
    exact Real.log_le_log ha h

/-- algebraic identity `(p^{k+1}−1)/(p^{k+1}−p) = ((p^{k+1}−1)/(p^k−1))/p`. -/
private lemma caF_quot_eq_div (p : ℕ) (k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)) =
      ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1)) / (p : ℝ) := by
  have hp0r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0r
  have hpkpos : 0 < ((p : ℝ) ^ k) - 1 := by
    have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hpk : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
    linarith
  have hden2ne : ((p : ℝ) ^ k) - 1 ≠ 0 := ne_of_gt hpkpos
  have hden_eq : ((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ) = (p : ℝ) * (((p : ℝ) ^ k) - 1) := by
    rw [pow_succ]
    ring
  rw [hden_eq]
  field_simp [hpne, hden2ne]

/-- `ε ≤ F(p,k) ⟺ p^{1+ε} ≤ (p^{k+1}−1)/(p^k−1)` for `p ≥ 2`, `ε > 0`, `k ≥ 1`. -/
private lemma caF_ge_iff_rpow_le (p : ℕ) (ε : ℝ) (k : ℕ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hk : 1 ≤ k) :
    ε ≤ caF p k ↔ (p : ℝ) ^ (1 + ε) ≤ (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  have hden2pos : 0 < ((p : ℝ) ^ k) - 1 := by
    have hpk : 1 < (p : ℝ) ^ k := one_lt_pow₀ hp1r (by omega : k ≠ 0)
    linarith
  have hden2ne : ((p : ℝ) ^ k) - 1 ≠ 0 := ne_of_gt hden2pos
  have hden_pos : 0 < ((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ) := by
    have hden_eq : ((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ) = (p : ℝ) * (((p : ℝ) ^ k) - 1) := by
      rw [pow_succ]
      ring
    rw [hden_eq]
    exact mul_pos hp0r hden2pos
  have hnum2pos : 0 < ((p : ℝ) ^ (k + 1 : ℕ)) - 1 := by
    have hpk : 1 < (p : ℝ) ^ (k + 1 : ℕ) := one_lt_pow₀ hp1r (by omega : k + 1 ≠ 0)
    linarith
  have hfrac2pos : 0 < (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) :=
    div_pos hnum2pos hden2pos
  have hfrac_pos :
      0 < (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)) :=
    div_pos hnum2pos hden_pos
  have hrpow_pos : 0 < (p : ℝ) ^ ε := Real.rpow_pos_of_pos hp0r ε
  have hpadd : (p : ℝ) ^ (1 + ε) = (p : ℝ) * (p : ℝ) ^ ε := by
    rw [Real.rpow_add hp0r, Real.rpow_one]
  have hpadd' : (p : ℝ) ^ (1 + ε) = (p : ℝ) ^ ε * (p : ℝ) := by
    rw [hpadd]
    ring
  have hfrac_eq :
      (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)) =
        ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1)) / (p : ℝ) :=
    caF_quot_eq_div p k hp hk
  constructor
  · intro h
    unfold caF at h
    have h1 : ε * Real.log (p : ℝ) ≤
        Real.log ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) :=
      (le_div_iff₀ hlogp).mp h
    have h2 : Real.log ((p : ℝ) ^ ε) ≤
        Real.log ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) := by
      simpa [Real.log_rpow hp0r ε] using h1
    have h3 : (p : ℝ) ^ ε ≤
        (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)) := by
      have hexp := (Real.exp_le_exp).mpr h2
      rwa [Real.exp_log hrpow_pos, Real.exp_log hfrac_pos] at hexp
    have h4 : (p : ℝ) ^ ε ≤
        ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1)) / (p : ℝ) := by
      rw [hfrac_eq] at h3
      exact h3
    have h5 : (p : ℝ) ^ ε * (p : ℝ) ≤
        (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) :=
      (le_div_iff₀ hp0r).mp h4
    calc
      (p : ℝ) ^ (1 + ε) = (p : ℝ) ^ ε * (p : ℝ) := hpadd'
      _ ≤ (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := h5
  · intro h
    unfold caF
    have h6 : (p : ℝ) ^ ε * (p : ℝ) ≤
        (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1) := by
      simpa [hpadd'] using h
    have h7 : (p : ℝ) ^ ε ≤
        ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ k) - 1)) / (p : ℝ) :=
      (le_div_iff₀ hp0r).mpr h6
    have h8 : (p : ℝ) ^ ε ≤
        (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)) := by
      rw [← hfrac_eq] at h7
      exact h7
    have h9 : Real.log ((p : ℝ) ^ ε) ≤
        Real.log ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) :=
      Real.log_le_log hrpow_pos h8
    have h10 : ε * Real.log (p : ℝ) ≤
        Real.log ((((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) := by
      simpa [Real.log_rpow hp0r ε] using h9
    exact (le_div_iff₀ hlogp).mpr h10

/-- `k ≤ μ(p,ε) ⟺ ε ≤ F(p,k)` for `p ≥ 2`, `ε > 0`, `k ≥ 1` (Nicolas (4.11)/(4.5)). -/
theorem caMu_ge_iff_caF (p : ℕ) (ε : ℝ) (k : ℕ) (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k) :
    (k : ℝ) ≤ Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ) ↔
    ε ≤ Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) / Real.log (p : ℝ) := by
  change (k : ℝ) ≤ caMu p ε ↔ ε ≤ caF p k
  rw [caMu_ge_iff_rpow_le hp hε hk]
  rw [caF_ge_iff_rpow_le p ε k hp hε hk]

end
end Commons.NumberTheory.Robin
