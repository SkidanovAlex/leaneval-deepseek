import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.ChenPlan.H1.Defs
import Submission.Work.ChenPlan.H1.RemBound
import Submission.Work.ChenPlan.H1.weighted_triv_bound
import Submission.Work.ChenPlan.H1.isLinear_chenSieve
import Submission.Work.ChenPlan.H1.isLinearRange_chenSieve
import Submission.Work.ChenPlan.H1.chenLevel_eventually
import Submission.Work.NumberTheory.Chen.mertens_lower_tenth
import Submission.Work.ChenPlan.H2.vsieve_ratio_lower_int
import Submission.Work.ChenPlan.H2.prod_odd_range_eq_vsieve
import Submission.Commons.NumberTheory.Mertens.sum_log_div_le_log_sharp

/-!
# Chen's `h1` from the linear sieve, against the v6 interface

REPAIR JOB, round 3: `Submission/ChenPlan/Interfaces.lean` (v6) adds `IsLinearMertens s z K` to
`LinearSieveLower`.  This file copies the proof of `Work.ChenPlan.H1.h1_of_sieve_two` and supplies
the extra hypothesis for Chen's sieve `chenSieve x M` (density `ν p = 1/(p-1)` on the odd primes).
-/

open Finset Filter
open scoped BigOperators

namespace Work.ChenPlan.H1

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight
open Commons.NumberTheory.Chen (Vsieve Vsieve_pos)

/-! ## Richert's condition `IsLinearMertens` for Chen's sieve -/

/-- `|a - b| ≤ |a| + |b|`. -/
private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  simpa using abs_add_le a (-b)

/-- The prefix sum `Σ_{3 ≤ p < n, p prime} log p/(p-1)`. -/
private def pref (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico 0 n, (if i.Prime ∧ 3 ≤ i then Real.log (i : ℝ) / ((i : ℝ) - 1) else 0)

/-- The full prime sum `Σ_{p ≤ m} log p/(p-1)`. -/
private def primeSum (m : ℕ) : ℝ :=
  ∑ p ∈ m.primesLE, Real.log (p : ℝ) / ((p : ℝ) - 1)

/-- Splitting the prefix sum at `W`. -/
private lemma pref_split {W Z : ℕ} (hWZ : W ≤ Z) :
    pref W + (∑ i ∈ Finset.Ico W Z,
        (if i.Prime ∧ 3 ≤ i then Real.log (i : ℝ) / ((i : ℝ) - 1) else 0)) = pref Z :=
  Finset.sum_Ico_consecutive _ (Nat.zero_le W) hWZ

/-- `pref` as a sum over `primesLE`. -/
private lemma pref_eq (n : ℕ) (hn : 3 ≤ n) :
    pref n = ∑ p ∈ (n - 1).primesLE.filter (fun p : ℕ => 3 ≤ p),
      Real.log (p : ℝ) / ((p : ℝ) - 1) := by
  rw [pref, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_Ico, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨-, hi⟩, hp, h3⟩
    exact ⟨⟨by omega, hp⟩, h3⟩
  · rintro ⟨⟨hle, hp⟩, h3⟩
    exact ⟨⟨by omega, by omega⟩, hp, h3⟩

/-- The odd primes `≤ m` contribute `primeSum m - log 2`. -/
private lemma primeSum_erase_two (m : ℕ) (hm : 2 ≤ m) :
    primeSum m = Real.log 2 + ∑ p ∈ m.primesLE.filter (fun p : ℕ => 3 ≤ p),
      Real.log (p : ℝ) / ((p : ℝ) - 1) := by
  have h2mem : (2 : ℕ) ∈ m.primesLE := Nat.mem_primesLE.mpr ⟨hm, Nat.prime_two⟩
  have hset : m.primesLE.filter (fun p : ℕ => 3 ≤ p) = m.primesLE.erase 2 := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpm, hp⟩, h3⟩
      exact ⟨by rintro rfl; omega, hpm, hp⟩
    · rintro ⟨hne, hpm, hp⟩
      exact ⟨⟨hpm, hp⟩, by have := hp.two_le; omega⟩
  rw [primeSum, ← Finset.sum_erase_add m.primesLE (fun p : ℕ => Real.log (p : ℝ) / ((p : ℝ) - 1)) h2mem, hset]
  have hf2 : Real.log ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) = Real.log 2 := by norm_num
  rw [hf2]
  ring

/-- **Mertens' bound for the prefix sum**: `|pref n - log n| ≤ A + 3`. -/
private lemma pref_sub_log_le {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ y : ℕ, 2 ≤ y → |primeSum y - Real.log (y : ℝ)| ≤ A)
    (n : ℕ) (hn : 2 ≤ n) : |pref n - Real.log (n : ℝ)| ≤ A + 3 := by
  rcases eq_or_lt_of_le hn with h2 | h3
  · subst h2
    have hpref2 : pref 2 = 0 := by
      rw [pref, show Finset.Ico 0 2 = ({0, 1} : Finset ℕ) by decide]
      norm_num
    rw [hpref2, zero_sub, abs_neg, abs_of_nonneg (Real.log_nonneg (by norm_num))]
    have hle : Real.log ((2 : ℕ) : ℝ) ≤ 1 := by
      have h : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
      rw [h]
      exact le_trans Real.log_two_lt_d9.le (by norm_num)
    linarith
  · have hn1 : 1 ≤ n := by omega
    have hm2 : 2 ≤ n - 1 := by omega
    have hnp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hmp : (0 : ℝ) < (((n - 1 : ℕ)) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
    have hsubcast : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1, Nat.cast_one]
    have hle : pref n = primeSum (n - 1) - Real.log 2 := by
      rw [pref_eq n (by omega), primeSum_erase_two (n - 1) (by omega)]
      ring
    have hnonneg : 0 ≤ Real.log ((n : ℕ) : ℝ) - Real.log (((n - 1 : ℕ)) : ℝ) :=
      sub_nonneg.mpr (Real.log_le_log hmp (by rw [hsubcast]; linarith))
    have hdivlog : Real.log ((n : ℕ) : ℝ) - Real.log (((n - 1 : ℕ)) : ℝ)
        = Real.log ((n : ℝ) / (((n - 1 : ℕ)) : ℝ)) :=
      (Real.log_div (ne_of_gt hnp) (ne_of_gt hmp)).symm
    have hratio : (n : ℝ) / (((n - 1 : ℕ)) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hmp, hsubcast]
      linarith [show (2 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn]
    have hmid : |Real.log ((n : ℕ) : ℝ) - Real.log (((n - 1 : ℕ)) : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg hnonneg, hdivlog]
      calc Real.log ((n : ℝ) / (((n - 1 : ℕ)) : ℝ))
          ≤ Real.log 2 := Real.log_le_log (div_pos hnp hmp) hratio
        _ ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
    have hb := hA (n - 1) hm2
    have hmid' : |Real.log (((n - 1 : ℕ)) : ℝ) - Real.log (n : ℝ)| ≤ 1 := by
      rw [abs_sub_comm]; exact hmid
    have hlogtwo : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
    calc |pref n - Real.log (n : ℝ)|
        = |(primeSum (n - 1) - Real.log (((n - 1 : ℕ)) : ℝ))
            + (Real.log (((n - 1 : ℕ)) : ℝ) - Real.log (n : ℝ)) - Real.log 2| := by
          rw [hle]; ring_nf
      _ ≤ |(primeSum (n - 1) - Real.log (((n - 1 : ℕ)) : ℝ))
            + (Real.log (((n - 1 : ℕ)) : ℝ) - Real.log (n : ℝ))| + |Real.log 2| :=
          abs_sub_le_abs_add _ _
      _ ≤ (|primeSum (n - 1) - Real.log (((n - 1 : ℕ)) : ℝ)|
            + |Real.log (((n - 1 : ℕ)) : ℝ) - Real.log (n : ℝ)|) + |Real.log 2| :=
          add_le_add (abs_add_le _ _) le_rfl
      _ ≤ A + 3 := by
          rw [abs_of_nonneg (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
          linarith [hmid', hb, hlogtwo]

/-- The ceiling slop `|log ⌈t⌉ - log t| ≤ 1` for `t ≥ 2`. -/
private lemma log_ceil_sub_log_le {t : ℝ} (ht : 2 ≤ t) :
    |Real.log ((⌈t⌉₊ : ℕ) : ℝ) - Real.log t| ≤ 1 := by
  have ht0 : 0 < t := by linarith
  have h1t : (1 : ℝ) ≤ t := by linarith
  have hcp : (0 : ℝ) < ((⌈t⌉₊ : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) (le_trans h1t (Nat.le_ceil t))
  have hnonneg : 0 ≤ Real.log ((⌈t⌉₊ : ℕ) : ℝ) - Real.log t :=
    sub_nonneg.mpr (Real.log_le_log ht0 (Nat.le_ceil t))
  have hceil : ((⌈t⌉₊ : ℕ) : ℝ) < t + 1 := Nat.ceil_lt_add_one (by linarith)
  have hratio : ((⌈t⌉₊ : ℕ) : ℝ) / t ≤ 2 := by
    rw [div_le_iff₀ ht0]
    linarith
  rw [abs_of_nonneg hnonneg, ← Real.log_div (ne_of_gt hcp) (ne_of_gt ht0)]
  calc Real.log (((⌈t⌉₊ : ℕ) : ℝ) / t)
      ≤ Real.log 2 := Real.log_le_log (div_pos hcp ht0) hratio
    _ ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)

/-- The ceiling slop on the `w` side: `|log w - log ⌈w⌉| ≤ 1` for `w ≥ 2`. -/
private lemma log_sub_log_ceil_le {w : ℝ} (hw : 2 ≤ w) :
    |Real.log w - Real.log ((⌈w⌉₊ : ℕ) : ℝ)| ≤ 1 := by
  have hw0 : 0 < w := by linarith
  have h1w : (1 : ℝ) ≤ w := by linarith
  have hcp : (0 : ℝ) < ((⌈w⌉₊ : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) (le_trans h1w (Nat.le_ceil w))
  have hnonneg : 0 ≤ Real.log ((⌈w⌉₊ : ℕ) : ℝ) - Real.log w :=
    sub_nonneg.mpr (Real.log_le_log hw0 (Nat.le_ceil w))
  have hceil : ((⌈w⌉₊ : ℕ) : ℝ) < w + 1 := Nat.ceil_lt_add_one (by linarith)
  have hratio : ((⌈w⌉₊ : ℕ) : ℝ) / w ≤ 2 := by
    rw [div_le_iff₀ hw0]
    linarith
  rw [abs_sub_comm, abs_of_nonneg hnonneg, ← Real.log_div (ne_of_gt hcp) (ne_of_gt hw0)]
  calc Real.log (((⌈w⌉₊ : ℕ) : ℝ) / w)
      ≤ Real.log 2 := Real.log_le_log (div_pos hcp hw0) hratio
    _ ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)

/-- **Richert's condition `IsLinearMertens` for Chen's sieve**, with a constant independent of `x`
and `M`: for `chenSieve x M` the density is `ν p = 1/(p-1)` on the odd primes, so `ν p ≤ 1/2`, and
for `2 ≤ w < z' ≤ M`,
`|Σ_{w ≤ p < z', p odd prime} log p/(p-1) − log(z'/w)| ≤ 2A + 8`,
where `A` is the constant of the sharp Mertens theorem `sum_log_div_le_log_sharp`
(`|Σ_{p ≤ y} log p/(p-1) − log y| ≤ A`).

Proof.  With `Z = ⌈z'⌉₊`, `W = ⌈w⌉₊` the sifting set is the odd primes in `[W, Z)`
(`pref_split` splits the prefix sum `pref` at `W`), and `pref n = Σ_{p ≤ n-1, p ≥ 3} log p/(p-1)`
(`pref_eq`), so `pref n = primeSum (n-1) - log 2` (`primeSum_erase_two`).  Comparing with
`log n = log (n-1) + log (n/(n-1))`, `log (n/(n-1)) ≤ log 2 ≤ 1`, gives
`|pref n - log n| ≤ A + 3` (`pref_sub_log_le`), and the ceiling slop contributes `≤ 1` on each side
(`log_ceil_sub_log_le`, `log_sub_log_ceil_le`). -/
theorem exists_isLinearMertens_chenSieve :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x M : ℕ),
      Submission.ChenPlan.IsLinearMertens (chenSieve x M) (M : ℝ) K := by
  obtain ⟨A, hA0, hA⟩ := Commons.NumberTheory.Mertens.sum_log_div_le_log_sharp
  have hAprime : ∀ y : ℕ, 2 ≤ y → |primeSum y - Real.log (y : ℝ)| ≤ A := by
    intro y hy
    have hset : y.primesLE.filter (fun p : ℕ => 2 ≤ p) = y.primesLE :=
      Finset.filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2.two_le)
    have h := hA y hy
    rw [hset] at h
    simpa only [primeSum] using h
  refine ⟨2 * A + 8, by linarith, fun x M => ⟨?_, ?_⟩⟩
  · -- the density bound `ν p ≤ 1/2`
    intro p hp
    rw [show (chenSieve x M).prodPrimes = oddPrimLt M from rfl, primeFactors_oddPrimLt] at hp
    obtain ⟨hpp, hp3, -⟩ := Submission.mem_oddLt.mp hp
    rw [show (chenSieve x M).nu = invTotient from rfl, invTotient_apply,
      Nat.totient_prime hpp, Nat.cast_sub hpp.one_le, Nat.cast_one]
    have hp2 : (2 : ℝ) ≤ ((p : ℝ) - 1) := by
      have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
      linarith
    have hpos : (0 : ℝ) < 2 := by norm_num
    calc (((p : ℝ) - 1))⁻¹ ≤ ((2 : ℝ))⁻¹ := inv_anti₀ hpos hp2
      _ = 1 / 2 := by norm_num
  · -- the weighted Mertens estimate on every sub-range
    intro w z' hw2 hwz hz'M
    set W : ℕ := ⌈w⌉₊ with hW
    set Z : ℕ := ⌈z'⌉₊ with hZ
    have hWZ : W ≤ Z := by
      rw [hW, hZ]; exact Nat.ceil_mono (le_of_lt hwz)
    have hZM : Z ≤ M := by rw [hZ]; exact Nat.ceil_le.mpr hz'M
    have hZ3 : 3 ≤ Z := by
      rw [hZ]
      have h : 2 < ⌈z'⌉₊ := Nat.lt_ceil.mpr (by push_cast; linarith)
      omega
    have hW2 : 2 ≤ W := by
      rw [hW]
      simpa using (Nat.ceil_mono hw2 : ⌈(2 : ℝ)⌉₊ ≤ ⌈w⌉₊)
    -- the sifting filter is exactly the odd primes in `[W, Z)`
    have hfilter : (oddLt M).filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z')
        = (Finset.Ico W Z).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨hpodd, hwp, hpz⟩
        obtain ⟨hpp, hp3, -⟩ := Submission.mem_oddLt.mp hpodd
        refine ⟨⟨?_, ?_⟩, hpp, hp3⟩
        · rw [hW]; exact Nat.ceil_le.mpr hwp
        · rw [hZ]; exact Nat.lt_ceil.mpr hpz
      · rintro ⟨⟨hWp, hpZ⟩, hpp, hp3⟩
        refine ⟨Submission.mem_oddLt.mpr ⟨hpp, hp3, lt_of_lt_of_le hpZ hZM⟩, ?_, ?_⟩
        · have h1 : w ≤ (W : ℝ) := by rw [hW]; exact Nat.le_ceil w
          exact le_trans h1 (by exact_mod_cast hWp)
        · have h1 : ((p : ℝ)) + 1 ≤ (Z : ℝ) := by exact_mod_cast (by omega : p + 1 ≤ Z)
          have h2 : (Z : ℝ) < z' + 1 := by rw [hZ]; exact Nat.ceil_lt_add_one (by linarith)
          linarith
    rw [show (chenSieve x M).prodPrimes = oddPrimLt M from rfl, primeFactors_oddPrimLt, hfilter]
    have hnu : ∀ p ∈ (Finset.Ico W Z).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p),
        (chenSieve x M).nu p * Real.log (p : ℝ)
          = Real.log (p : ℝ) / ((p : ℝ) - 1) := by
      intro p hp
      obtain ⟨-, hpp, -⟩ := Finset.mem_filter.mp hp
      rw [show (chenSieve x M).nu = invTotient from rfl, invTotient_apply, Nat.totient_prime hpp,
        Nat.cast_sub hpp.one_le, Nat.cast_one, inv_mul_eq_div]
    rw [Finset.sum_congr rfl hnu]
    -- the sieve sum is `pref Z - pref W`
    have hsz : (∑ p ∈ (Finset.Ico W Z).filter (fun p : ℕ => p.Prime ∧ 3 ≤ p),
        Real.log (p : ℝ) / ((p : ℝ) - 1)) = pref Z - pref W := by
      have h := pref_split (W := W) (Z := Z) hWZ
      rw [← Finset.sum_filter] at h
      linarith
    rw [hsz]
    have hbZ := pref_sub_log_le (le_of_lt hA0) hAprime Z (by omega)
    have hbW := pref_sub_log_le (le_of_lt hA0) hAprime W hW2
    have hcZ : |Real.log ((Z : ℕ) : ℝ) - Real.log z'| ≤ 1 := by
      rw [hZ]; exact log_ceil_sub_log_le (by linarith)
    have hcW : |Real.log w - Real.log ((W : ℕ) : ℝ)| ≤ 1 := by
      rw [hW]; exact log_sub_log_ceil_le hw2
    have hZb : |pref Z - Real.log z'| ≤ A + 4 := by
      calc |pref Z - Real.log z'|
          = |(pref Z - Real.log (Z : ℝ)) + (Real.log ((Z : ℕ) : ℝ) - Real.log z')| := by ring_nf
        _ ≤ |pref Z - Real.log (Z : ℝ)| + |Real.log ((Z : ℕ) : ℝ) - Real.log z'| := abs_add_le _ _
        _ ≤ (A + 3) + 1 := add_le_add hbZ hcZ
        _ = A + 4 := by ring
    have hWb : |pref W - Real.log w| ≤ A + 4 := by
      calc |pref W - Real.log w|
          = |(pref W - Real.log (W : ℝ)) + (Real.log ((W : ℕ) : ℝ) - Real.log w)| := by ring_nf
        _ ≤ |pref W - Real.log (W : ℝ)| + |Real.log ((W : ℕ) : ℝ) - Real.log w| := abs_add_le _ _
        _ ≤ (A + 3) + 1 := by
            refine add_le_add hbW ?_
            exact le_trans (le_of_eq (abs_sub_comm _ _)) hcW
        _ = A + 4 := by ring
    have hlogdiv : Real.log (z' / w) = Real.log z' - Real.log w :=
      Real.log_div (by linarith) (by linarith)
    rw [hlogdiv]
    calc |(pref Z - pref W) - (Real.log z' - Real.log w)|
        = |(pref Z - Real.log z') - (pref W - Real.log w)| := by ring_nf
      _ ≤ |pref Z - Real.log z'| + |pref W - Real.log w| := abs_sub_le_abs_add _ _
      _ ≤ (A + 4) + (A + 4) := add_le_add hZb hWb
      _ = 2 * A + 8 := by ring

/-! ## Monotonicity of `IsLinearLower` in the sieve constant

`IsLinearLower` is *downward* closed in the constant: a larger `K` only shrinks the left-hand
side `(log z'/log w)(1 - K/log w)`.  This lets us raise the constant of
`exists_isLinearLower_chenSieve` to the maximum of all the constants the three hypotheses of the
sieve require. -/

private lemma isLinearLower_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearLower s z K) (hKK' : K ≤ K') :
    Submission.ChenPlan.IsLinearLower s z K' := by
  intro w z' hw hwz hz'z
  refine le_trans ?_ (h w z' hw hwz hz'z)
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hnn : 0 ≤ Real.log z' / Real.log w := div_nonneg (Real.log_nonneg (by linarith)) hlogw.le
  have hle : 1 - K' / Real.log w ≤ 1 - K / Real.log w := by
    have := div_le_div_of_nonneg_right hKK' hlogw.le
    linarith
  exact mul_le_mul_of_nonneg_left hle hnn

/-! ## The lower dimension bound for the sieve product

The lower half of Mertens' ratio for the odd sieve product `Vsieve` is the mirror image of
`prod_sieve_le_range` of `Submission/Work/ChenPlan/H2/`: at the integer limits
`s = max ⌈w⌉₊ 3`, `t = ⌈z'⌉₊` it is the proved `Work.ChenPlan.H2.vsieve_ratio_lower_int`, and the
reduction from a real range `[w, z')` to those limits uses `log ⌈w⌉ ≤ log w + 1/w` and
`z' ≤ ⌈z'⌉`.  The `[w, z')` product identity is the proved
`Work.ChenPlan.H2.prod_odd_range_eq_vsieve`. -/

/-- The algebra of the range reduction for the lower bound: if `0 ≤ T ≤ Lt`, `0 < W ≤ Ls`,
`Ls ≤ W(1+ε)`, `0 ≤ c ≤ W` and `c + εW ≤ K`, then
`(T/W)(1 - K/W) ≤ (Lt/Ls)(1 - c/Ls)`. -/
private lemma lower_key_step {T W Lt Ls K c ε : ℝ}
    (hT : 0 ≤ T) (hW : 0 < W) (hLs : 0 < Ls) (hTLt : T ≤ Lt)
    (hWLs : W ≤ Ls) (hLsW : Ls ≤ W * (1 + ε))
    (hε : 0 ≤ ε) (hc0 : 0 ≤ c) (hcW : c ≤ W) (hKW : c + ε * W ≤ K) :
    T / W * (1 - K / W) ≤ Lt / Ls * (1 - c / Ls) := by
  have hLt0 : 0 ≤ Lt := le_trans hT hTLt
  have hWe : 0 < 1 + ε := by linarith
  have hfac : 1 - ε ≤ 1 / (1 + ε) := by
    rw [le_div_iff₀ hWe]
    nlinarith
  have h1 : T / W * (1 - ε) ≤ Lt / Ls :=
    calc T / W * (1 - ε) ≤ T / W * (1 / (1 + ε)) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = T / (W * (1 + ε)) := by field_simp
      _ ≤ Lt / (W * (1 + ε)) := div_le_div_of_nonneg_right hTLt (by positivity)
      _ ≤ Lt / Ls := div_le_div_of_nonneg_left hLt0 hLs hLsW
  have h2 : 1 - c / W ≤ 1 - c / Ls := by
    have hcLs : c / Ls ≤ c / W := div_le_div_of_nonneg_left hc0 hW hWLs
    linarith
  have hcW' : 0 ≤ c / W := div_nonneg hc0 hW.le
  have h3 : 1 - K / W ≤ (1 - ε) * (1 - c / W) := by
    have hK : (c + ε * W) / W ≤ K / W := div_le_div_of_nonneg_right hKW hW.le
    have hexp : (c + ε * W) / W = c / W + ε := by field_simp
    have hexp2 : (1 - ε) * (1 - c / W) = 1 - c / W - ε + ε * (c / W) := by ring
    rw [hexp2]
    nlinarith [mul_nonneg hε hcW']
  have hb : 0 ≤ 1 - c / W := by
    have h : c / W ≤ 1 := by rw [div_le_one hW]; exact hcW
    linarith
  have hLtLs : 0 ≤ Lt / Ls := div_nonneg hLt0 hLs.le
  calc T / W * (1 - K / W)
      ≤ T / W * ((1 - ε) * (1 - c / W)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (T / W * (1 - ε)) * (1 - c / W) := by ring
    _ ≤ Lt / Ls * (1 - c / Ls) := mul_le_mul h1 h2 hb hLtLs

/-- **The lower dimension bound `IsLinearLower` for Chen's sieve problem**, with a constant that
is independent of `x` and `M`.  `chenSieve x M` sifts the odd primes `< M` with density
`ν = 1/φ`, so the sub-range product is the odd sieve product ratio
`Vsieve (max ⌈w⌉₊ 3) / Vsieve ⌈z'⌉₊`, and the claimed inequality is the lower half of Mertens'
ratio for `Vsieve` (`vsieve_ratio_lower_int`). -/
private theorem exists_isLinearLower_chenSieve :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x M : ℕ),
      Submission.ChenPlan.IsLinearLower (chenSieve x M) (M : ℝ) K := by
  obtain ⟨c, hc0, N₀, hratio⟩ := Work.ChenPlan.H2.vsieve_ratio_lower_int
  set Kb : ℝ := max (max (c + 1) 4) (Real.log ((N₀ : ℝ) + 1) + 1) with hKb
  have hc1 : c + 1 ≤ Kb := by rw [hKb]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have h4 : (4 : ℝ) ≤ Kb := by rw [hKb]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hN : Real.log ((N₀ : ℝ) + 1) + 1 ≤ Kb := by rw [hKb]; exact le_max_right _ _
  have hKb0 : 0 ≤ Kb := le_trans (by linarith : (0 : ℝ) ≤ c + 1) hc1
  refine ⟨Kb, hKb0, fun x M => ?_⟩
  intro w z' hw hwz hz'M
  rw [show (chenSieve x M).prodPrimes = oddPrimLt M from rfl,
    show (chenSieve x M).nu = invTotient from rfl]
  rw [Work.ChenPlan.H2.prod_odd_range_eq_vsieve M hw hwz hz'M]
  have hwpos : 0 < w := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz' : 0 < Real.log z' := Real.log_pos (by linarith)
  by_cases hcase : Real.log w ≤ Kb
  · have h1 : 1 - Kb / Real.log w ≤ 0 := by
      have h2 : (1 : ℝ) ≤ Kb / Real.log w := by rw [one_le_div hlogw]; exact hcase
      linarith
    have h2 : (Real.log z' / Real.log w) * (1 - Kb / Real.log w) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (div_nonneg hlogz'.le hlogw.le) h1
    have h3 : (0 : ℝ) ≤ Vsieve (max ⌈w⌉₊ 3) / Vsieve ⌈z'⌉₊ :=
      div_nonneg (le_of_lt (Vsieve_pos _)) (le_of_lt (Vsieve_pos _))
    linarith
  · rw [not_le] at hcase
    -- basic size of `w`
    have hw1 : (1 : ℝ) < w := by linarith
    have hw5 : (5 : ℝ) < w := by
      have := Real.log_le_sub_one_of_pos hwpos
      linarith
    have hs_eq : max ⌈w⌉₊ 3 = ⌈w⌉₊ := by
      apply max_eq_left
      have h : 2 < ⌈w⌉₊ := Nat.lt_ceil.mpr (by push_cast; linarith)
      omega
    -- the integer bounds
    have hNw : (N₀ : ℝ) + 1 < w :=
      (Real.log_lt_log_iff (by positivity) hwpos).mp (by linarith)
    have hN_le_s : N₀ ≤ max ⌈w⌉₊ 3 := by
      have h1 : ((N₀ : ℕ) : ℝ) ≤ ((max ⌈w⌉₊ 3 : ℕ) : ℝ) := by
        have h2 : w ≤ ((⌈w⌉₊ : ℕ) : ℝ) := Nat.le_ceil w
        have h3 : ((⌈w⌉₊ : ℕ) : ℝ) ≤ ((max ⌈w⌉₊ 3 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_max_left ⌈w⌉₊ 3
        linarith
      exact_mod_cast h1
    have hst : max ⌈w⌉₊ 3 ≤ ⌈z'⌉₊ := by
      refine max_le (Nat.ceil_mono (le_of_lt hwz)) ?_
      have h : 2 < ⌈z'⌉₊ := Nat.lt_ceil.mpr (by push_cast; linarith)
      omega
    have hint := hratio (max ⌈w⌉₊ 3) ⌈z'⌉₊ hN_le_s hst
    -- the algebra
    have hLs : 0 < Real.log ((max ⌈w⌉₊ 3 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < max ⌈w⌉₊ 3))
    have hTLt : Real.log z' ≤ Real.log ((⌈z'⌉₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (Nat.le_ceil z')
    have hWLs : Real.log w ≤ Real.log ((max ⌈w⌉₊ 3 : ℕ) : ℝ) :=
      Real.log_le_log hwpos
        (le_trans (Nat.le_ceil w) (by exact_mod_cast Nat.le_max_left ⌈w⌉₊ 3))
    have hLsW : Real.log ((max ⌈w⌉₊ 3 : ℕ) : ℝ)
        ≤ Real.log w * (1 + 1 / (w * Real.log w)) := by
      rw [hs_eq]
      have hceil : ((⌈w⌉₊ : ℕ) : ℝ) < w + 1 := Nat.ceil_lt_add_one (by linarith)
      have h1 : Real.log ((⌈w⌉₊ : ℕ) : ℝ) ≤ Real.log (w + 1) :=
        Real.log_le_log (by positivity) (le_of_lt hceil)
      have h2 : Real.log (w + 1) = Real.log w + Real.log (1 + 1 / w) := by
        rw [show w + 1 = w * (1 + 1 / w) by field_simp]
        rw [Real.log_mul (by linarith) (by positivity)]
      have h3 : Real.log (1 + 1 / w) ≤ 1 / w := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / w by positivity)
        linarith
      have h4 : Real.log w * (1 + 1 / (w * Real.log w)) = Real.log w + 1 / w := by
        field_simp
      rw [h4]
      linarith
    have hKW : c + 1 / (w * Real.log w) * Real.log w ≤ Kb := by
      have h1 : 1 / (w * Real.log w) * Real.log w = 1 / w := by field_simp
      have h2 : 1 / w ≤ 1 := by
        rw [div_le_one hwpos]; linarith
      linarith
    have hcW : c ≤ Real.log w := by linarith
    have hkey := lower_key_step (T := Real.log z') (W := Real.log w)
      (Lt := Real.log ((⌈z'⌉₊ : ℕ) : ℝ)) (Ls := Real.log ((max ⌈w⌉₊ 3 : ℕ) : ℝ))
      (K := Kb) (c := c) (ε := 1 / (w * Real.log w))
      (le_of_lt hlogz') hlogw hLs hTLt hWLs hLsW (by positivity) hc0 hcW hKW
    exact hkey.trans hint


/-! ## Chen's `h1` from the lower linear sieve -/

/-- Monotonicity of `IsLinearMertens` in the constant `K`. -/
private lemma isLinearMertens_mono {s : BoundingSieve} {z K K' : ℝ}
    (h : Submission.ChenPlan.IsLinearMertens s z K) (hKK' : K ≤ K') :
    Submission.ChenPlan.IsLinearMertens s z K' :=
  ⟨h.1, fun w z' hw hwz hz => le_trans (h.2 w z' hw hwz hz) hKK'⟩

/-- Chen's h1 from the linear sieve, against the v6 interface (`IsLinearMertens`).

The proof is the proof of `Work.ChenPlan.H1.h1_of_sieve_two` with the third extra hypothesis of the
v6 interface supplied: `IsLinearMertens (chenSieve x M) (M : ℝ) Kmert` is
`exists_isLinearMertens_chenSieve`, raised by monotonicity to the common constant
`max (max (rangeK Z₀) Klow) Kmert`.  The sieve is applied at that constant, `η = 1/1000`, level
`D = M^{49/10}`. -/
theorem h1_of_sieve_three (hL : Submission.ChenPlan.LinearSieveLower) :
    Submission.ChenPlan.H1Statement := by
  show ∀ᶠ x : ℕ in Filter.atTop,
    (1 - (1 : ℝ) / 100) * (x : ℝ) * VsieveOdd (Submission.chenSiftLimitTenth x)
      ≤ goodSum x (Submission.chenSiftLimitTenth x)
  obtain ⟨Z₀, hZ₀⟩ := Commons.NumberTheory.Sieve.oddEulerProduct_ratio_le_log_p5
  obtain ⟨Klow, hKlow0, hLow⟩ := exists_isLinearLower_chenSieve
  obtain ⟨Kmert, hKmert0, hMert⟩ := exists_isLinearMertens_chenSieve
  set Kbig : ℝ := max (max (rangeK Z₀) Klow) Kmert with hKbig
  have hKbig0 : (0 : ℝ) ≤ Kbig := by
    rw [hKbig]
    exact le_trans (le_of_lt (rangeK_pos Z₀)) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hrangeK_le : rangeK Z₀ ≤ Kbig := by
    rw [hKbig]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hK100 : (100 : ℝ) ≤ Kbig := le_trans (rangeK_ge_100 Z₀) hrangeK_le
  have hKlow_le : Klow ≤ Kbig := by
    rw [hKbig]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hKmert_le : Kmert ≤ Kbig := by rw [hKbig]; exact le_max_right _ _
  -- the linear sieve at the common constant, `η = 1/1000`
  obtain ⟨D₀, z₀, hD₀⟩ := hL Kbig hKbig0 (1 / 1000) (by norm_num)
  -- the inputs
  obtain ⟨C, hC, hW⟩ := weighted_triv_bound
  obtain ⟨B, hB, hbv⟩ := bv_level_of_distribution
  have hcl := chenLevel_eventually B hB
  have hrem := remBound_of_inputs C hC hW B hB hbv hcl
    Work.NumberTheory.Chen.mertens_lower_tenth
  obtain ⟨hD0ev, hlevev⟩ := hcl
  filter_upwards [hrem, isLinear_chenSieve, hlevev, hD0ev D₀,
    eventually_chenSiftLimitTenth_ge (⌈z₀⌉₊ + 1)] with x hremx hisLinx hlevx hD0x hz0x
  obtain ⟨hM1, hD4, hDle⟩ := hlevx
  set M : ℕ := Submission.chenSiftLimitTenth x with hMdef
  have hD0' : D₀ ≤ (M : ℝ) ^ ((49 : ℝ) / 10) := by rw [hMdef]; exact hD0x
  have hM1n : 1 < M := by exact_mod_cast hM1
  have hz2 : (2 : ℝ) ≤ (M : ℝ) := by
    have h2 : 2 ≤ M := by omega
    exact_mod_cast h2
  -- the third extra v6 hypothesis
  have hz0le : z₀ ≤ (M : ℝ) := by
    have h1 : z₀ ≤ ((⌈z₀⌉₊ : ℕ) : ℝ) := Nat.le_ceil z₀
    have h2 : ((⌈z₀⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) := by
      have h3 : ⌈z₀⌉₊ + 1 ≤ M := by rw [hMdef]; exact hz0x
      exact_mod_cast (by omega : ⌈z₀⌉₊ ≤ M)
    linarith
  have hisLin' : Submission.ChenPlan.IsLinear (chenSieve x M) (M : ℝ) 100 := by
    rw [hMdef]; exact hisLinx
  have hisLin : Submission.ChenPlan.IsLinear (chenSieve x M) (M : ℝ) Kbig :=
    isLinear_mono hisLin' hK100
  have hisLinR : Submission.ChenPlan.IsLinearRange (chenSieve x M) (M : ℝ) Kbig :=
    isLinearRange_mono (isLinearRange_chenSieve Z₀ hZ₀ x M) hrangeK_le
  have hisLinL : Submission.ChenPlan.IsLinearLower (chenSieve x M) (M : ℝ) Kbig :=
    isLinearLower_mono (hLow x M) hKlow_le
  have hisLinM : Submission.ChenPlan.IsLinearMertens (chenSieve x M) (M : ℝ) Kbig :=
    isLinearMertens_mono (hMert x M) hKmert_le
  have hlevel : (49 : ℝ) / 10 ≤ Real.log ((M : ℝ) ^ ((49 : ℝ) / 10)) / Real.log (M : ℝ) := by
    have hMpos : (0 : ℝ) < (M : ℝ) := by
      have : 0 < M := by omega
      exact_mod_cast this
    have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM1)
    rw [Real.log_rpow hMpos, mul_div_assoc, div_self (ne_of_gt hlogM), mul_one]
  have htm : (0 : ℝ) ≤ (chenSieve x M).totalMass := by
    show (0 : ℝ) ≤ (x : ℝ)
    positivity
  have hmain := hD₀ (chenSieve x M) (M : ℝ) ((M : ℝ) ^ ((49 : ℝ) / 10))
    hD0' hz0le hz2 hisLin hisLinR hisLinL hisLinM htm hlevel
  rw [chenSieve_siftedSum, chenSieve_sieveV, chenSieve_remSum,
    show (chenSieve x M).totalMass = (x : ℝ) from rfl] at hmain
  nlinarith [hmain, hremx]

end

end Work.ChenPlan.H1
