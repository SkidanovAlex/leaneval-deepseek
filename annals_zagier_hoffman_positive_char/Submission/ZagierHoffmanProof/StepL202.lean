import Submission.ZagierHoffmanProof.StepL201

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators WithZero Topology
open WithZero

/-!
# Step L202: non-vanishing for Frobenius-scaled entries `q^k·n` (per entry)

StepL199 proves `ζ_A(𝔰) ≠ 0` for tuples whose entries are all `≤ q`, and StepL201 extends it by
scaling *all* entries of a tuple by the same power `q^k` (using `ζ_A(q·𝔰) = ζ_A(𝔰)^q`).  Here we
allow a *different* power of `q` in each entry.

The mechanism is that the whole StepL199 chain only ever uses the depth-one input

  `C(n) :  ∀ d, v (P_d(n)) = exp (−n · Sexp d)`

("`n` is valuation-good"), and `C` is closed under `n ↦ q·n` because of the finite-sum Frobenius
`P_d(q·n) = P_d(n)^q`.  Hence every `n = q^k·m` with `m ≤ q` is valuation-good, and the block
domination argument of StepL199 goes through verbatim.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## 1. Valuation-good exponents -/

/-- A positive exponent `n` is *valuation-good*: the depth-one power sum `P_d(n)` has valuation
exponent `n · Sexp d` at every level `d`. -/
def EntryVal (n : ℕ+) : Prop :=
  ∀ d : ℕ, Valued.v (P F d n) = WithZero.exp (-(Se F n d))

/-- A tuple all of whose entries are valuation-good. -/
def EntriesVal {r : ℕ} (𝔰 : Fin r → ℕ+) : Prop := ∀ j, EntryVal F (𝔰 j)

/-- `EntriesVal` is inherited by the tail of the tuple. -/
lemma EntriesVal.tail {r : ℕ} {𝔰 : Fin r → ℕ+} (h : EntriesVal F 𝔰) :
    EntriesVal F (expTail 𝔰) :=
  fun j => h ⟨(j : ℕ) + 1, by have := j.2; omega⟩

/-- Every exponent `n ≤ q` is valuation-good (StepL199). -/
lemma entryVal_of_le_card (n : ℕ+) (hn : (n : ℕ) ≤ Nat.card F) : EntryVal F n :=
  fun d => val_P_se F n hn d

/-! ## 2. Frobenius closure of valuation-goodness -/

/-- ★ `P_d(q·n) = P_d(n)^q`: the `q`-th power map permutes the monic polynomials of degree `d`
(indeed `a ↦ a^q` is bijective on them), so it acts on the finite sum `P_d(n)` as Frobenius. -/
lemma P_mul_card (d : ℕ) (n : ℕ+) :
    P F d (qExp F * n) = (P F d n) ^ (Nat.card F) := by
  rw [P_eq_sum F d (qExp F * n), P_eq_sum F d n, sum_pow_natCard F]
  apply Finset.sum_congr rfl
  intro p _
  rw [inv_pow]
  congr 1
  have h : ((qExp F * n : ℕ+) : ℕ) = (n : ℕ) * Nat.card F := by
    rw [PNat.mul_coe, mul_comm]
    rfl
  rw [h, ← pow_mul]

/-- `Se (m·n) d = m · Se n d` (the exponent is additive in the entry). -/
lemma Se_mul (m n : ℕ+) (d : ℕ) : Se F (m * n) d = (m : ℤ) * Se F n d := by
  rw [Se, Se]
  have hq : (((m * n : ℕ+)) : ℤ) = (m : ℤ) * (n : ℤ) := by
    rw [PNat.mul_coe]; push_cast; ring
  rw [hq]; ring

/-- `Se (q·n) d = q · Se n d`. -/
lemma Se_mul_card (n : ℕ+) (d : ℕ) :
    Se F (qExp F * n) d = (Nat.card F : ℤ) * Se F n d := by
  rw [Se_mul F (qExp F) n d]
  rfl

/-- ★★ Valuation-goodness is closed under multiplication of the exponent by `q`. -/
lemma entryVal_mul_card (n : ℕ+) (h : EntryVal F n) : EntryVal F (qExp F * n) := by
  intro d
  rw [P_mul_card F d n, map_pow, h d]
  rw [← WithZero.exp_nsmul, WithZero.exp_inj]
  rw [Se_mul_card F n d]
  ring

/-- ★★ Iterated Frobenius: `q^k·n` is valuation-good whenever `n` is. -/
lemma entryVal_pow (k : ℕ) (n : ℕ+) (h : EntryVal F n) :
    EntryVal F ((qExp F) ^ k * n) := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [pow_succ', mul_assoc]; exact entryVal_mul_card F _ ih

/-! ## 3. The block valuation `bloExp` is strictly monotone (hypothesis-free) -/

/-- ★ `bloExp r 𝔰` is strictly increasing in the index, with no hypothesis on the entries
(StepL199 proves the same statement under the superfluous assumption `EntriesOK`). -/
lemma bloExp_strictMono (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) :
    StrictMono (fun d => bloExp F r 𝔰 d) := by
  refine strictMono_nat_of_lt_succ fun d => ?_
  match r with
  | 0 => exact absurd hr (by omega)
  | 1 =>
      rw [bloExp_one F 𝔰 d, bloExp_one F 𝔰 (d + 1)]
      exact Se_lt_succ F (𝔰 0) d
  | (k + 2) =>
      rw [bloExp_succ F k 𝔰 d, bloExp_succ F k 𝔰 (d + 1)]
      have h := Se_lt_succ F (𝔰 0) d
      linarith

/-! ## 4. The valuation of the blocks, for valuation-good tuples -/

/-- ★★ `v (S_d(𝔰)) = exp (−bloExp r 𝔰 d)` for every `d ≥ r - 1`, for tuples all of whose
entries are valuation-good (verbatim StepL199 argument, with the depth-one input generalised). -/
theorem val_S_bloExp_val : ∀ (r : ℕ) (hr : 0 < r) (𝔰 : Fin r → ℕ+) (h𝔰 : EntriesVal F 𝔰) (d : ℕ),
    r - 1 ≤ d → Valued.v (S F r hr 𝔰 d) = WithZero.exp (-(bloExp F r 𝔰 d)) := by
  intro r
  induction r with
  | zero => intro hr; exact absurd hr (by omega)
  | succ r ih =>
      intro hr 𝔰 h𝔰 d hd
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · subst hr0
        rw [S_one_eq_P F d (by norm_num) 𝔰, bloExp_one F 𝔰 d]
        exact h𝔰 0 d
      · obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        have hT : 0 < k + 1 := by omega
        have htail : EntriesVal F (expTail 𝔰) := EntriesVal.tail F h𝔰
        have hrec : S F (k + 2) hr 𝔰 d
            = P F d (𝔰 0) * S_lt F (k + 1) hT (expTail 𝔰) d :=
          S_d_recursion F (k + 2) (by omega) (by omega) (by omega) 𝔰 d
        rw [hrec, S_lt_eq_sum_levels F (k + 1) hT (expTail 𝔰) d]
        have hIHk : Valued.v (S F (k + 1) hT (expTail 𝔰) k)
            = WithZero.exp (-(bloExp F (k + 1) (expTail 𝔰) k)) :=
          ih hT (expTail 𝔰) htail k (by omega)
        have hdom : Valued.v (∑ i ∈ Finset.range d, S F (k + 1) hT (expTail 𝔰) i)
            = WithZero.exp (-(bloExp F (k + 1) (expTail 𝔰) k)) := by
          refine (Valuation.map_sum_eq_of_lt (v := Valued.v) (j := k)
            (Finset.mem_range.mpr (by omega)) ?_).trans hIHk
          intro i hi
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
          obtain ⟨hir, hik⟩ := hi
          have hid : i < d := Finset.mem_range.mp hir
          rcases lt_trichotomy i k with h | h | h
          · have hzero : S F (k + 1) hT (expTail 𝔰) i = 0 :=
              S_eq_zero_of_lt F (by omega : 0 < k + 1) (expTail 𝔰) (by omega : i < k + 1 - 1)
            rw [hzero, map_zero, hIHk]
            exact exp_neg_pos (bloExp F (k + 1) (expTail 𝔰) k)
          · exact absurd h hik
          · rw [ih hT (expTail 𝔰) htail i (by omega), hIHk, WithZero.exp_lt_exp]
            have hmono :=
              (bloExp_strictMono F (k + 1) (by omega) (expTail 𝔰)).lt_iff_lt.mpr h
            linarith
        rw [map_mul, hdom, h𝔰 0 d, bloExp_succ F k 𝔰 d,
          ← WithZero.exp_add]
        congr 1
        ring

/-! ## 5. Non-vanishing of the MZVs with valuation-good entries -/

/-- ★★★ `v (ζ_A(𝔰)) = exp (−Σ_j Se(𝔰_j, r−1−j))` for tuples with valuation-good entries:
the blocks with `d < r-1` vanish and the dominating one is the diagonal `d = r-1`. -/
theorem val_zeta_val {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) (h𝔰 : EntriesVal F 𝔰) :
    Valued.v (ζ_A F 𝔰) = WithZero.exp (-(bloExp F r 𝔰 (r - 1))) := by
  classical
  have hsumm := summable_S F hr 𝔰
  rw [zeta_eq_tsum_block F hr 𝔰]
  refine val_tsum_eq_of_dominates F _ (r - 1) _ WithZero.exp_ne_zero ?_ hsumm ?_
  · exact val_S_bloExp_val F r hr 𝔰 h𝔰 (r - 1) (by omega)
  · intro d hd
    rcases lt_trichotomy d (r - 1) with h | h | h
    · have hzero : S F r hr 𝔰 d = 0 := S_eq_zero_of_lt F hr 𝔰 h
      rw [hzero, map_zero]
      exact exp_neg_pos (bloExp F r 𝔰 (r - 1))
    · exact absurd h hd
    · rw [val_S_bloExp_val F r hr 𝔰 h𝔰 d (by omega), WithZero.exp_lt_exp]
      have hmono := (bloExp_strictMono F r hr 𝔰).lt_iff_lt.mpr h
      linarith

/-- ★★★ Every MZV with valuation-good entries is nonzero. -/
theorem zeta_val_ne_zero {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+) (h𝔰 : EntriesVal F 𝔰) :
    ζ_A F 𝔰 ≠ 0 := by
  intro h0
  have h := val_zeta_val F hr 𝔰 h𝔰
  rw [h0, map_zero] at h
  exact WithZero.exp_ne_zero h.symm

/-! ## 6. Instance: entries `q^{k_j}·m_j` with `m_j ≤ q` (a different power in each entry) -/

/-- ★★ Entry `q^k·n` with `n ≤ q` is valuation-good. -/
lemma entryVal_pow_of_le_card (k : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ Nat.card F) :
    EntryVal F ((qExp F) ^ k * n) :=
  entryVal_pow F k n (entryVal_of_le_card F n hn)

/-- ★★★ Let `𝔰` be a tuple whose `j`-th entry is `q^{k_j}·m_j` with `m_j ≤ q`.  Then
`ζ_A(𝔰) ≠ 0`.  This strictly contains both StepL199 (`k_j = 0`) and StepL201 (all `k_j` equal,
`m_j` all equal). -/
theorem zeta_scaled_entries_ne_zero {r : ℕ} (hr : 0 < r) (𝔰 : Fin r → ℕ+)
    (k : Fin r → ℕ) (m : Fin r → ℕ+) (hm : ∀ j, (m j : ℕ) ≤ Nat.card F)
    (h : ∀ j, 𝔰 j = (qExp F) ^ (k j) * m j) : ζ_A F 𝔰 ≠ 0 := by
  refine zeta_val_ne_zero F hr 𝔰 (fun j => ?_)
  rw [h j]
  exact entryVal_pow_of_le_card F (k j) (m j) (hm j)

/-- Consistency: StepL199's hypothesis (`EntriesOK`) implies the new one. -/
lemma entriesVal_of_entriesOK {r : ℕ} {𝔰 : Fin r → ℕ+} (h : EntriesOK F 𝔰) :
    EntriesVal F 𝔰 :=
  fun j => entryVal_of_le_card F (𝔰 j) (h j)

end ZagierHoffmanPositiveChar
