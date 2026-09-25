import Mathlib
import Submission.Commons.NumberTheory.Robin.caMu_ge_iff_caF
import Submission.Commons.NumberTheory.Robin.caMu_pos

/-!
# `k ≤ a_p(ε) ⟺ p ≤ ξ_k(ε)` (raw-expression form)

Self-contained (Mathlib + commons only) port of the block-structure lemma
`caExp_ge_k_iff_le_xiK` of `Submission.Work.NumberTheory.Robin.caU.lean`.

For the colossally-abundant family with exponents
`a_p = ⌊μ(p,ε)⌋₊`, `μ(p,ε) = log((p^{1+ε}−1)/(p^{1+ε}−p))/log p`, and support
`supp(ε) = {p prime, p < ⌈exp(2/ε)⌉+2 : 1 ≤ a_p}`, the exponent-`k` level set
`{p ∈ supp : k ≤ a_p}` is exactly the primes `p ≤ ξ_k(ε) := max{p ∈ supp : k ≤ a_p}`.

The only ingredient beyond the support structure is the monotonicity of
`F(·,k) = log((p^{k+1}−1)/(p^{k+1}−p))/log p` in the prime argument `p`
(strictly decreasing), i.e. that exponents of the CA-family are non-increasing in
the prime — Nicolas Lemma 4.4 (4.18).

All helper definitions stay private so nothing leaks into the commons namespace.
-/

namespace Commons.NumberTheory.Robin

noncomputable section

open scoped BigOperators

/-- `μ(p,ε) = log((p^{1+ε}−1)/(p^{1+ε}−p))/log p`, the (4.11)-exponent parameter. -/
private def caMuL (p : ℕ) (ε : ℝ) : ℝ :=
  Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)

/-- `F(p,k) = log((p^{k+1}−1)/(p^{k+1}−p))/log p` for `k ≥ 1` (Nicolas (4.5)). -/
private def caFL (p : ℕ) (k : ℕ) : ℝ :=
  Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))) / Real.log (p : ℝ)

/-- The support bound `⌈exp(2/ε)⌉+2` of `N_ε`. -/
private abbrev caBL (ε : ℝ) : ℕ := Nat.ceil (Real.exp (2 / ε)) + 2

/-- The prime support of `N_ε`: primes `p < caBL ε` with `1 ≤ ⌊μ(p,ε)⌋₊`. -/
private abbrev caSL (ε : ℝ) : Finset ℕ :=
  ((Finset.range (caBL ε)).filter Nat.Prime).filter (fun p => 1 ≤ ⌊caMuL p ε⌋₊)

/-- The exponent-`k` level set of the support. -/
private abbrev caTL (ε : ℝ) (k : ℕ) : Finset ℕ :=
  (caSL ε).filter (fun p => k ≤ ⌊caMuL p ε⌋₊)

private lemma mem_caSL {ε : ℝ} {p : ℕ} :
    p ∈ caSL ε ↔ Nat.Prime p ∧ p < caBL ε ∧ 1 ≤ ⌊caMuL p ε⌋₊ := by
  simp only [caSL, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨h.1.2, h.1.1, h.2⟩, fun h => ⟨⟨h.2.1, h.1⟩, h.2.2⟩⟩

/-- `μ(p,ε) > 0` for `p ≥ 2`, `ε > 0` (commons port). -/
private lemma caMu_posL {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) : 0 < caMuL p ε := by
  simpa [caMuL] using Commons.NumberTheory.Robin.caMu_pos (p := p) (ε := ε) hp hε

/-- `p ≥ 2`, `ε > 0`, `k ≥ 1`: `k ≤ μ(p,ε) ⟺ ε ≤ F(p,k)` (commons (4.11)/(4.5)). -/
private lemma caMu_ge_iff_caFL {p : ℕ} {ε : ℝ} {k : ℕ} (hp : 2 ≤ p) (hε : 0 < ε) (hk : 1 ≤ k) :
    (k : ℝ) ≤ caMuL p ε ↔ ε ≤ caFL p k := by
  simpa [caMuL, caFL] using Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε k hp hε hk

/-! ### Monotonicity of `F(·,k)` in the prime argument

`F(p,k) = log(1 + 1/S_k(p))/log p` with `S_k(p) = p + p² + … + p^k` strictly
increasing in `p`; hence `F(·,k)` is strictly decreasing. -/

/-- `S_k(p) := p + p² + … + p^k` (natural-valued; `k ≥ 1`). -/
private def caSp (p : ℕ) (k : ℕ) : ℕ := Finset.sum (Finset.range k) (fun i => p ^ (i + 1))

private lemma caSp_pos {p k : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) : 1 ≤ caSp p k := by
  unfold caSp
  have hmem : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have hle : (p ^ (0 + 1) : ℕ) ≤ Finset.sum (Finset.range k) (fun i => p ^ (i + 1)) :=
    Finset.single_le_sum (s := Finset.range k) (f := fun i => p ^ (i + 1))
      (fun i hi => Nat.zero_le _) hmem
  have hp1 : 1 ≤ p ^ (0 + 1) := by simpa using hp
  omega

private lemma caSp_lt {p q k : ℕ} (hk : 1 ≤ k) (hlt : p < q) : caSp p k < caSp q k := by
  unfold caSp
  refine Finset.sum_lt_sum ?hle ?hlt_
  · intro i hi
    exact pow_le_pow_left₀ (Nat.zero_le p) (le_of_lt hlt) (i + 1)
  · refine ⟨0, ?mem, ?lt⟩
    · exact Finset.mem_range.mpr (by omega)
    · simpa using hlt

/-- `p^{k+1} − p = (p−1)·S_k(p)` (reals). -/
private lemma pow_succ_sub_self_eq_mul_caSp {p k : ℕ} :
    (p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ) = ((p : ℝ) - 1) * (caSp p k : ℝ) := by
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
        rw [hg]; ring
    _ = ((p : ℝ) - 1) *
          (Finset.sum (Finset.range k) (fun i => (p : ℝ) ^ (i + 1 : ℕ))) := by
        rw [← hmul]
    _ = ((p : ℝ) - 1) * (caSp p k : ℝ) := by
        congr 1
        unfold caSp
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Nat.cast_pow]

/-- the CA ratio at `p` (exponent `k`) `= (p^{k+1}−1)/(p^{k+1}−p) = 1 + 1/S_k(p)`. -/
private lemma ratio_eq_one_add_inv_caSp {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)) =
      1 + 1 / (caSp p k : ℝ) := by
  have hfac := pow_succ_sub_self_eq_mul_caSp (p := p) (k := k)
  have hnum : (p : ℝ) ^ (k + 1 : ℕ) - 1 = ((p : ℝ) - 1) * ((caSp p k : ℝ) + 1) := by
    calc
      (p : ℝ) ^ (k + 1 : ℕ) - 1 = ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ)) + ((p : ℝ) - 1) := by ring
      _ = ((p : ℝ) - 1) * (caSp p k : ℝ) + ((p : ℝ) - 1) := by rw [hfac]
      _ = ((p : ℝ) - 1) * ((caSp p k : ℝ) + 1) := by ring
  have hpmin : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  have hS : 1 ≤ caSp p k := caSp_pos (by omega : 1 ≤ p) hk
  have hSpos : (0 : ℝ) < (caSp p k : ℝ) := by exact_mod_cast hS
  have hSne : (caSp p k : ℝ) ≠ 0 := ne_of_gt hSpos
  rw [hnum, hfac]
  field_simp [hpmin, hSne]

/-- **`F(·,k)` is strictly decreasing in the prime `p`**: `2 ≤ p < q`, `k ≥ 1` ⟹
`F(q,k) < F(p,k)` (Nicolas (4.5); the engine of Lemma 4.4). -/
private lemma caFL_anti_p {p q k : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 1 ≤ k) (hlt : p < q) :
    caFL q k < caFL p k := by
  let Ap : ℝ := (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ))
  let Aq : ℝ := (((q : ℝ) ^ (k + 1 : ℕ)) - 1) / (((q : ℝ) ^ (k + 1 : ℕ)) - (q : ℝ))
  have hSp : 1 ≤ caSp p k := caSp_pos (by omega : 1 ≤ p) hk
  have hSq : 1 ≤ caSp q k := caSp_pos (by omega : 1 ≤ q) hk
  have hSppos : (0 : ℝ) < (caSp p k : ℝ) := by exact_mod_cast hSp
  have hSqpos : (0 : ℝ) < (caSp q k : ℝ) := by exact_mod_cast hSq
  have hS : (caSp p k : ℝ) < (caSp q k : ℝ) := by
    exact_mod_cast (caSp_lt (p := p) (q := q) (k := k) hk hlt)
  have hA : Aq < Ap := by
    dsimp [Ap, Aq]
    rw [ratio_eq_one_add_inv_caSp hp hk, ratio_eq_one_add_inv_caSp hq hk]
    have hinv : 1 / (caSp q k : ℝ) < 1 / (caSp p k : ℝ) :=
      one_div_lt_one_div_of_lt hSppos hS
    linarith
  have hAq1 : 1 < Aq := by
    dsimp [Aq]
    rw [ratio_eq_one_add_inv_caSp hq hk]
    have h : (0 : ℝ) < 1 / (caSp q k : ℝ) := one_div_pos.mpr hSqpos
    linarith
  have hAp1 : 1 < Ap := by
    dsimp [Ap]
    rw [ratio_eq_one_add_inv_caSp hp hk]
    have h : (0 : ℝ) < 1 / (caSp p k : ℝ) := one_div_pos.mpr hSppos
    linarith
  have hlogA : Real.log Aq < Real.log Ap := Real.log_lt_log (lt_trans zero_lt_one hAq1) hA
  have hlogAqpos : 0 < Real.log Aq := Real.log_pos hAq1
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlogAppos : 0 < Real.log Ap := Real.log_pos hAp1
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have hloglt : Real.log (p : ℝ) < Real.log (q : ℝ) :=
    Real.log_lt_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast (by omega : p < q))
  unfold caFL
  rw [div_lt_div_iff₀ hlogq hlogp]
  have hm1 : Real.log Aq * Real.log (p : ℝ) < Real.log Aq * Real.log (q : ℝ) :=
    mul_lt_mul_of_pos_left hloglt hlogAqpos
  have hm2 : Real.log Aq * Real.log (q : ℝ) < Real.log Ap * Real.log (q : ℝ) :=
    mul_lt_mul_of_pos_right hlogA hlogq
  exact lt_trans hm1 hm2

/-- the CA exponent is non-increasing in the prime argument: for `p < m` primes with
`1 ≤ ⌊μ(m,ε)⌋₊`, one has `⌊μ(m,ε)⌋₊ ≤ ⌊μ(p,ε)⌋₊` (Nicolas Lemma 4.4, exponent form). -/
private lemma caGL_anti {ε : ℝ} (hε : 0 < ε) {p m : ℕ} (hp : Nat.Prime p) (hm : Nat.Prime m)
    (hj : 1 ≤ ⌊caMuL m ε⌋₊) (hle : p ≤ m) :
    ⌊caMuL m ε⌋₊ ≤ ⌊caMuL p ε⌋₊ := by
  rcases eq_or_lt_of_le hle with h | h
  · rw [← h]
  · have hjle : ((⌊caMuL m ε⌋₊ : ℕ) : ℝ) ≤ caMuL m ε :=
      Nat.floor_le (le_of_lt (caMu_posL hm.two_le hε))
    have hεFm : ε ≤ caFL m ⌊caMuL m ε⌋₊ :=
      (caMu_ge_iff_caFL hm.two_le hε hj).mp hjle
    have hltF : caFL m ⌊caMuL m ε⌋₊ < caFL p ⌊caMuL m ε⌋₊ :=
      caFL_anti_p hp.two_le hm.two_le hj h
    have hεFp : ε ≤ caFL p ⌊caMuL m ε⌋₊ := le_of_lt (lt_of_le_of_lt hεFm hltF)
    have hjlep : ((⌊caMuL m ε⌋₊ : ℕ) : ℝ) ≤ caMuL p ε :=
      (caMu_ge_iff_caFL hp.two_le hε hj).mpr hεFp
    exact Nat.le_floor hjlep

/-- **`k ≤ a_p(ε) ⟺ p ≤ ξ_k(ε)`**: for a prime `p` in the CA-support, the exponent
`a_p = ⌊μ(p,ε)⌋₊` is `≥ k` exactly when `p` is at most the largest prime `ξ_k(ε)`
with exponent `≥ k` (Nicolas Lemma 4.4 (4.18)). -/
theorem caExp_ge_k_iff_le_xiK {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k)
    (hs : ((((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).filter (fun p : ℕ => k ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).Nonempty) {p : ℕ} (hp : Nat.Prime p) (hps : p ∈ (((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊))) :
    k ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ ↔ p ≤ (((((Finset.range (Nat.ceil (Real.exp (2 / ε)) + 2)).filter Nat.Prime).filter (fun p : ℕ => 1 ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).filter (fun p : ℕ => k ≤ ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)⌋₊)).max' hs) := by
  change k ≤ ⌊caMuL p ε⌋₊ ↔ p ≤ (caTL ε k).max' hs
  constructor
  · intro hkexp
    exact Finset.le_max' (caTL ε k) p (Finset.mem_filter.mpr ⟨hps, hkexp⟩)
  · intro hple
    have hm_mem : (caTL ε k).max' hs ∈ caTL ε k := Finset.max'_mem (caTL ε k) hs
    have hmS : (caTL ε k).max' hs ∈ caSL ε := (Finset.mem_filter.mp hm_mem).1
    have hkm : k ≤ ⌊caMuL ((caTL ε k).max' hs) ε⌋₊ := (Finset.mem_filter.mp hm_mem).2
    have hmprime : Nat.Prime ((caTL ε k).max' hs) := (mem_caSL.mp hmS).1
    have hj : 1 ≤ ⌊caMuL ((caTL ε k).max' hs) ε⌋₊ := le_trans hk hkm
    have hanti := caGL_anti hε hp hmprime hj hple
    exact le_trans hkm hanti

end

end Commons.NumberTheory.Robin
