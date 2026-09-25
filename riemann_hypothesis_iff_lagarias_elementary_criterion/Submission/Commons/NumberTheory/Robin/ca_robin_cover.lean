import Mathlib
import Submission.Commons.NumberTheory.Robin.caMu_ge_iff_caF
import Submission.Commons.NumberTheory.Robin.caExp_mono_of_le
import Submission.Commons.NumberTheory.Robin.caExp_eq_zero_of_ge_bound
import Submission.Commons.NumberTheory.Robin.caF1_lt_one
import Submission.Commons.NumberTheory.Robin.ca_55440_in_family
import Submission.Commons.NumberTheory.Robin.ca_Neps_unbounded

/-!
# Robin covering lemma on the colossally abundant family

For every `n ≥ 55441` there is `ε > 0` with `N⁻_ε < n ≤ N_ε` and `N⁻_ε ≥ 55440`,
where `N_ε` is the colossally abundant product (Nicolas (4.11)) and `N⁻_ε` the previous
F-member.  The definitions and all helper lemmas are inlined and kept private; the
published statement is written out in full.
-/

open scoped BigOperators

namespace Commons.NumberTheory.Robin

noncomputable section

-- The CA core definitions and lemmas are private mirrors of
-- `Submission/Work/NumberTheory/Robin/caCore.lean` / `caOpt.lean` / `caCover.lean`
-- (the shared commons only exports fully inlined statements).
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
private def caEpsBound (ε : ℝ) : ℕ := if 0 < ε then Nat.ceil (Real.exp (2 / ε)) + 2 else 3

/-- The CA number `N_ε = ∏_{p < caEpsBound ε, p prime} p^{caExp p ε}` (Nicolas (4.11)). -/
private def Nε (ε : ℝ) : ℕ :=
  Finset.prod ((Finset.range (caEpsBound ε)).filter Nat.Prime) (fun p => p ^ caExp p ε)

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


theorem ca_robin_cover (n : ℕ) (hn : 55441 ≤ n) :
    ∃ ε : ℝ, 0 < ε ∧ ((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ (if Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ) = (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ : ℝ) ∧ 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ then ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ - 1 else ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)))) < n ∧ n ≤ ((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊))) ∧ 55440 ≤ ((Finset.prod ((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime) (fun p : ℕ => p ^ (if Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ) = (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ : ℝ) ∧ 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ then ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ - 1 else ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)))) := by
  obtain ⟨ε, hε, hlt, hle, h55440⟩ := ca_robin_cover_aux n hn
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · rw [← Nminus_eq_raw ε hε]; exact hlt
  · rw [← Nε_eq_raw ε hε]; exact hle
  · rw [← Nminus_eq_raw ε hε]; exact h55440


end

end Commons.NumberTheory.Robin
