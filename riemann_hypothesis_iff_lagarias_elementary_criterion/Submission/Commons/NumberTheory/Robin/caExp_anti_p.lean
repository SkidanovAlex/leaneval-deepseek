import Mathlib
import Submission.Commons.NumberTheory.Robin.caMu_ge_iff_caF

/-!
# Antitonicity of the CA exponent in the prime: `caExp q ε ≤ caExp p ε` for `2 ≤ p < q`

Port of `Work/NumberTheory/Robin/caU.lean` (`caExp_anti_p`, `caF_anti_p`) over the
commons threshold lemma `Commons.NumberTheory.Robin.caMu_ge_iff_caF`.
All helpers are inlined as `private`.

The key input is that for fixed exponent `k ≥ 1` the threshold
`F(p,k) = log((p^{k+1}−1)/(p^{k+1}−p))/log p` is strictly decreasing in the prime `p`
(`caF_anti_p`), proved via `(p^{k+1}−1)/(p^{k+1}−p) = 1 + 1/(p + p² + … + p^k)`.
-/

namespace Commons.NumberTheory.Robin

noncomputable section

/-- `μ(p,ε) = log((p^{1+ε}−1)/(p^{1+ε}−p))/log p` (Nicolas (4.11), inlined). -/
private def caMu (p : ℕ) (ε : ℝ) : ℝ :=
  Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)

/-- `F(p,k) = log((p^{k+1}−1)/(p^{k+1}−p))/log p` for `k ≥ 1` (Nicolas (4.5), inlined). -/
private def caF (p : ℕ) (k : ℕ) : ℝ :=
  Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) / Real.log (p : ℝ)

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

/-- `S_k(p) := p + p² + … + p^k` (natural-valued; the geometric partial sum of `p`). -/
private def caSsumN (p : ℕ) (k : ℕ) : ℕ := Finset.sum (Finset.range k) (fun i => p ^ (i + 1))

private lemma caSsumN_pos {p k : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) : 1 ≤ caSsumN p k := by
  unfold caSsumN
  have hmem : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hle : (p ^ (0 + 1) : ℕ) ≤ Finset.sum (Finset.range k) (fun i => p ^ (i + 1)) :=
    Finset.single_le_sum (s := Finset.range k) (f := fun i => p ^ (i + 1))
      (fun i hi => Nat.zero_le _) hmem
  have hp1 : 1 ≤ p ^ (0 + 1) := by simpa using hp
  omega

private lemma caSsumN_lt {p q k : ℕ} (hk : 1 ≤ k) (hlt : p < q) :
    caSsumN p k < caSsumN q k := by
  unfold caSsumN
  refine Finset.sum_lt_sum ?hle ?hlt_
  · intro i hi
    exact pow_le_pow_left₀ (Nat.zero_le p) (le_of_lt hlt) (i + 1)
  · refine ⟨0, ?mem, ?lt⟩
    · exact Finset.mem_range.mpr (by omega)
    · simpa using hlt

/-- `p^{k+1} − p = (p−1)·S_k(p)` (reals). -/
private lemma pow_succ_sub_self_eq_mul_caSsumN {p k : ℕ} :
    (p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ) = ((p : ℝ) - 1) * (caSsumN p k : ℝ) := by
  have hmul : (Finset.sum (Finset.range k) (fun i => (p : ℝ) ^ (i + 1 : ℕ))) =
      (p : ℝ) * (Finset.sum (Finset.range k) (fun i => (p : ℝ) ^ i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [pow_succ']
  have hg : (p : ℝ) ^ k - 1 =
      ((p : ℝ) - 1) * (Finset.sum (Finset.range k) (fun i => (p : ℝ) ^ i)) := by
    have h := geom_sum_mul (x := (p : ℝ)) k
    calc
      (p : ℝ) ^ k - 1 =
          (Finset.sum (Finset.range k) (fun i => (p : ℝ) ^ i)) * ((p : ℝ) - 1) := h.symm
      _ = ((p : ℝ) - 1) * (Finset.sum (Finset.range k) (fun i => (p : ℝ) ^ i)) := by ring
  calc
    (p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ) = (p : ℝ) * ((p : ℝ) ^ k - 1) := by
        rw [pow_succ']
        ring
    _ = ((p : ℝ) - 1) *
          ((p : ℝ) * (Finset.sum (Finset.range k) (fun i => (p : ℝ) ^ i))) := by
        rw [hg]
        ring
    _ = ((p : ℝ) - 1) * (Finset.sum (Finset.range k) (fun i => (p : ℝ) ^ (i + 1 : ℕ))) := by
        rw [← hmul]
    _ = ((p : ℝ) - 1) * (caSsumN p k : ℝ) := by
        congr 1
        unfold caSsumN
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Nat.cast_pow]

/-- the CA ratio at `p` (exponent `k`) `= (p^{k+1}−1)/(p^{k+1}−p) = 1 + 1/S_k(p)`. -/
private lemma ratio_eq_one_add_inv_caSsumN {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)) =
      1 + 1 / (caSsumN p k : ℝ) := by
  have hfac := pow_succ_sub_self_eq_mul_caSsumN (p := p) (k := k)
  have hnum : (p : ℝ) ^ (k + 1 : ℕ) - 1 = ((p : ℝ) - 1) * ((caSsumN p k : ℝ) + 1) := by
    calc
      (p : ℝ) ^ (k + 1 : ℕ) - 1 =
          ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ)) + ((p : ℝ) - 1) := by ring
      _ = ((p : ℝ) - 1) * (caSsumN p k : ℝ) + ((p : ℝ) - 1) := by rw [hfac]
      _ = ((p : ℝ) - 1) * ((caSsumN p k : ℝ) + 1) := by ring
  have hpmin : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  have hS : 1 ≤ caSsumN p k := caSsumN_pos (by omega : 1 ≤ p) hk
  have hSpos : (0 : ℝ) < (caSsumN p k : ℝ) := by exact_mod_cast hS
  have hSne : (caSsumN p k : ℝ) ≠ 0 := ne_of_gt hSpos
  rw [hnum, hfac]
  field_simp [hpmin, hSne]

/-- `F(p,k)` (as the log-ratio) is strictly decreasing in the prime argument `p`:
`2 ≤ p < q`, `k ≥ 1` ⟹ `F(q,k) < F(p,k)`. -/
private lemma caF_anti_p {p q k : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 1 ≤ k) (hlt : p < q) :
    caF q k < caF p k := by
  let Ap : ℝ := (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))
  let Aq : ℝ := (((q : ℝ) ^ (k + 1 : ℕ)) - 1) / (((q : ℝ) ^ (k + 1 : ℕ)) - (q : ℝ))
  have hSp : 1 ≤ caSsumN p k := caSsumN_pos (by omega : 1 ≤ p) hk
  have hSq : 1 ≤ caSsumN q k := caSsumN_pos (by omega : 1 ≤ q) hk
  have hSppos : (0 : ℝ) < (caSsumN p k : ℝ) := by exact_mod_cast hSp
  have hSqpos : (0 : ℝ) < (caSsumN q k : ℝ) := by exact_mod_cast hSq
  have hS : (caSsumN p k : ℝ) < (caSsumN q k : ℝ) := by
    exact_mod_cast (caSsumN_lt (p := p) (q := q) (k := k) hk hlt)
  have hA : Aq < Ap := by
    dsimp [Ap, Aq]
    rw [ratio_eq_one_add_inv_caSsumN hp hk, ratio_eq_one_add_inv_caSsumN hq hk]
    have hinv : 1 / (caSsumN q k : ℝ) < 1 / (caSsumN p k : ℝ) :=
      one_div_lt_one_div_of_lt hSppos hS
    linarith
  have hAq1 : 1 < Aq := by
    dsimp [Aq]
    rw [ratio_eq_one_add_inv_caSsumN hq hk]
    have h : (0 : ℝ) < 1 / (caSsumN q k : ℝ) := one_div_pos.mpr hSqpos
    linarith
  have hAp1 : 1 < Ap := by
    dsimp [Ap]
    rw [ratio_eq_one_add_inv_caSsumN hp hk]
    have h : (0 : ℝ) < 1 / (caSsumN p k : ℝ) := one_div_pos.mpr hSppos
    linarith
  have hlogA : Real.log Aq < Real.log Ap := Real.log_lt_log (lt_trans zero_lt_one hAq1) hA
  have hlogAqpos : 0 < Real.log Aq := Real.log_pos hAq1
  have hlogAppos : 0 < Real.log Ap := Real.log_pos hAp1
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hloglt : Real.log (p : ℝ) < Real.log (q : ℝ) :=
    Real.log_lt_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast (by omega : p < q))
  unfold caF
  rw [div_lt_div_iff₀ hlogq hlogp]
  have hm1 : Real.log Aq * Real.log (p : ℝ) < Real.log Aq * Real.log (q : ℝ) :=
    mul_lt_mul_of_pos_left hloglt hlogAqpos
  have hm2 : Real.log Aq * Real.log (q : ℝ) < Real.log Ap * Real.log (q : ℝ) :=
    mul_lt_mul_of_pos_right hlogA hlogq
  exact lt_trans hm1 hm2

/-- exponents of `N_ε` are non-increasing in the prime: `p < q` primes ⟹ `a_q ≤ a_p`. -/
theorem caExp_anti_p {p q : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hε : 0 < ε) (hlt : p < q) :
    ⌊Real.log ((((q : ℝ) ^ (1 + ε)) - 1) / (((q : ℝ) ^ (1 + ε)) - (q : ℝ))) / Real.log (q : ℝ)⌋₊ ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ := by
  change ⌊caMu q ε⌋₊ ≤ ⌊caMu p ε⌋₊
  by_cases hk0 : ⌊caMu q ε⌋₊ = 0
  · rw [hk0]
    exact Nat.zero_le _
  · have hk : 1 ≤ ⌊caMu q ε⌋₊ := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    have hmuq : (⌊caMu q ε⌋₊ : ℝ) ≤ caMu q ε :=
      Nat.floor_le (le_of_lt (caMu_pos hq hε))
    have hεFq : ε ≤ caF q ⌊caMu q ε⌋₊ := by
      have h := (Commons.NumberTheory.Robin.caMu_ge_iff_caF q ε ⌊caMu q ε⌋₊ hq hε hk).mp hmuq
      simpa [caF] using h
    have hF : caF q ⌊caMu q ε⌋₊ < caF p ⌊caMu q ε⌋₊ := caF_anti_p hp hq hk hlt
    have hεFp : ε ≤ caF p ⌊caMu q ε⌋₊ := le_of_lt (lt_of_le_of_lt hεFq hF)
    have hmup : (⌊caMu q ε⌋₊ : ℝ) ≤ caMu p ε := by
      have h := (Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε ⌊caMu q ε⌋₊ hp hε hk).mpr
        (by simpa [caF] using hεFp)
      simpa [caMu] using h
    exact Nat.le_floor hmup

end

end Commons.NumberTheory.Robin
