/-
# `Submission.Work.FIArea7.sepPair_bounds`

Size relations between the three components of the *FI* §24 separation triple
`(d, m, n)` of a squarefree number, `ℓ = d·m·n`.

Let `r ≥ 2` and let `ℓ` have `k` prime factors, enumerated in decreasing order,
`p₁ > p₂ > … > p_k`.  Positions are 1-based, `j = i + 1`, and a position is written
`j = q r + s` with `q = j / r`, `s = j % r`.  Then (`SepDiv.lean`)

* `d` collects the primes with `s = 0` (all multiples of `r`), together with the whole first
  block `s = 1, …, r` (`dIdx`);
* `m` collects the primes with `s ≠ 0` and `q` odd (`mIdx`);
* `n` collects the primes with `s ≠ 0`, `q` even and `q > 0` (`nIdx`).

Because the enumeration is *decreasing*, "larger position" means "smaller prime", so comparing
two products reduces to a matching of positions: if `A, B` are two of these sets and there is an
injection `φ : A → B` with `φ i ≤ i` for all `i ∈ A`, then `∏_{i∈A} p_i ≤ ∏_{j∈B} p_j`.

The matching is the same in both cases and is simply *shift the position down by `r`*, i.e.
`(q, s) ↦ (q - 1, s)`:

* `n → m`: an `n`-position has `q` even, `q ≥ 2`, hence after the shift `q - 1` is odd and `≥ 1`:
  `mIdx`.  This gives `n ≤ m`.
* `m → d ∪ n`: an `m`-position has `q` odd.  If `q = 1` the shifted position is `s ≤ r - 1`, i.e.
  it lies in the first block: `dIdx`; if `q ≥ 3` then `q - 1` is even and `≥ 2`: `nIdx`.  This
  gives `m ≤ d·n` (the two target sets are disjoint).

The two remaining inequalities of the statement are multiplicative: `m·m ≤ d·m·n` is `m ≤ d·n`
multiplied by `m`, and `n·n ≤ d·m·n` follows from `n ≤ m ≤ d·m`.

Everything is formalised below, including the arithmetic facts about `Nat.div`/`Nat.mod`; the
crucial one is `div_shift`: shifting a position down by `r` decreases `j / r` by one and leaves
`j % r` unchanged.
-/
import Mathlib
import Submission.Work.FIArea7.SepDiv

set_option autoImplicit false

namespace Work.FIArea7

open Finset

/-! ## Membership characterisations of the three index sets -/

lemma mem_dIdx {r k : ℕ} {i : Fin k} :
    (i ∈ dIdx r k) ↔ i.val < r ∨ ((i.val + 1) % r = 0 ∧ 2 * r ≤ i.val + 1) := by
  simp only [dIdx, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_mIdx {r k : ℕ} {i : Fin k} :
    (i ∈ mIdx r k) ↔ 0 < (i.val + 1) % r ∧ ((i.val + 1) / r) % 2 = 1 := by
  simp only [mIdx, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_nIdx {r k : ℕ} {i : Fin k} :
    (i ∈ nIdx r k) ↔
      0 < (i.val + 1) % r ∧ ((i.val + 1) / r) % 2 = 0 ∧ 0 < (i.val + 1) / r := by
  simp only [nIdx, Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## Arithmetic: shifting a position down by `r` -/

/-- Writing the 1-based position `r * q + s` (`s < r`, `q > 0`) and shifting it down by `r`
gives `r * (q - 1) + s`: the quotient `j / r` drops by one and the remainder `j % r` is
unchanged. -/
lemma div_shift {r q s : ℕ} (hr : 0 < r) (hs : s < r) (hq : 0 < q) :
    (r * q + s - r) / r = q - 1 ∧ (r * q + s - r) % r = s := by
  have hle : r ≤ r * q := by nlinarith [hq]
  have key : r * q + s - r = r * (q - 1) + s := by
    rw [Nat.sub_add_comm hle, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [key]
  exact ⟨by rw [Nat.mul_add_div hr, Nat.div_eq_of_lt hs, add_zero],
    by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]⟩

/-- If the 1-based position `v` satisfies `v / r > 0` and `v % r > 0` (i.e. `v = q r + s` with
`q ≥ 1`, `s ≥ 1`), then the 0-based index `v - 1` is at least `r`. -/
lemma le_pred_of_pos_div_and_mod {r v : ℕ} (_hr : 0 < r) (h0 : 0 < v / r) (h1 : 0 < v % r) :
    r ≤ v - 1 := by
  have hdecomp : r * (v / r) + v % r = v := Nat.div_add_mod v r
  have hmul : r ≤ r * (v / r) := by
    have := Nat.mul_le_mul_left r h0; simpa using this
  have hsum : r + 1 ≤ r * (v / r) + v % r := by omega
  omega

lemma three_le_of_odd_mod_two {q : ℕ} (h : q % 2 = 1) (_h1 : q ≠ 1) : 3 ≤ q := by omega

lemma pos_pred_of_odd_ne_one {q : ℕ} (h : q % 2 = 1) (h1 : q ≠ 1) : 0 < q - 1 := by omega

lemma mod_two_pred_of_odd {q : ℕ} (h : q % 2 = 1) (_h1 : q ≠ 1) : (q - 1) % 2 = 0 := by omega

lemma pos_pred_of_even_pos {q : ℕ} (h : q % 2 = 0) (h0 : 0 < q) : 0 < q - 1 := by omega

lemma mod_two_pred_of_even {q : ℕ} (h : q % 2 = 0) (h0 : 0 < q) : (q - 1) % 2 = 1 := by omega

/-! ## The shift map and its membership properties -/

/-- Shift a position down by `r` (truncated at `0`; it is only used where the value is `≥ r`). -/
def shiftDown (r k : ℕ) (i : Fin k) : Fin k :=
  ⟨i.val - r, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- The 1-based position of a member of `nIdx` is `> r`, so the shift is not truncated. -/
lemma r_le_val_of_mem_nIdx {r k : ℕ} (hr : 0 < r) {i : Fin k} (hi : i ∈ nIdx r k) :
    r ≤ i.val := by
  rw [mem_nIdx] at hi
  obtain ⟨hs0, hqe, hq0⟩ := hi
  have := le_pred_of_pos_div_and_mod hr hq0 hs0
  simpa using this

/-- The 1-based position of a member of `mIdx` is `> r`, so the shift is not truncated. -/
lemma r_le_val_of_mem_mIdx {r k : ℕ} (hr : 0 < r) {i : Fin k} (hi : i ∈ mIdx r k) :
    r ≤ i.val := by
  rw [mem_mIdx] at hi
  obtain ⟨hs0, hqo⟩ := hi
  have hqpos : 0 < (i.val + 1) / r := by
    rcases Nat.eq_zero_or_pos ((i.val + 1) / r) with h | h
    · rw [h] at hqo; simp at hqo
    · exact h
  have := le_pred_of_pos_div_and_mod hr hqpos hs0
  simpa using this

/-- Shifting an `n`-position down by `r` lands in `mIdx`: `q` even `≥ 2` becomes `q - 1` odd
`≥ 1`, and `s ∈ (0, r)` is unchanged. -/
lemma shiftDown_mem_mIdx_of_mem_nIdx {r k : ℕ} (hr : 0 < r) {i : Fin k}
    (hi : i ∈ nIdx r k) : shiftDown r k i ∈ mIdx r k := by
  rw [mem_nIdx] at hi
  obtain ⟨hs0, hqe, hq0⟩ := hi
  have hslt : (i.val + 1) % r < r := Nat.mod_lt _ hr
  obtain ⟨hdiv, hmod⟩ := div_shift (r := r) (q := (i.val + 1) / r)
    (s := (i.val + 1) % r) hr hslt hq0
  have hdecomp : r * ((i.val + 1) / r) + (i.val + 1) % r = i.val + 1 := Nat.div_add_mod _ _
  have hrv : r ≤ i.val := by
    have := le_pred_of_pos_div_and_mod hr hq0 hs0
    simpa using this
  have hv : i.val - r + 1 = i.val + 1 - r := by omega
  have hjeq : (shiftDown r k i).val + 1 =
      r * ((i.val + 1) / r) + (i.val + 1) % r - r := by
    change i.val - r + 1 = r * ((i.val + 1) / r) + (i.val + 1) % r - r
    rw [hv, hdecomp]
  rw [mem_mIdx, hjeq, hmod, hdiv]
  exact ⟨hs0, mod_two_pred_of_even hqe hq0⟩

/-- Shifting an `m`-position down by `r` lands in `dIdx ∪ nIdx`: if `q = 1` the shifted position
is `s ≤ r - 1` and hence in the initial block `dIdx`; otherwise `q ≥ 3` and `q - 1 ≥ 2` is even,
so the shifted position lies in `nIdx`. -/
lemma shiftDown_mem_dIdx_or_nIdx_of_mem_mIdx {r k : ℕ} (hr : 0 < r) {i : Fin k}
    (hi : i ∈ mIdx r k) : shiftDown r k i ∈ dIdx r k ∪ nIdx r k := by
  rw [mem_mIdx] at hi
  obtain ⟨hs0, hqo⟩ := hi
  have hslt : (i.val + 1) % r < r := Nat.mod_lt _ hr
  have hqpos : 0 < (i.val + 1) / r := by
    rcases Nat.eq_zero_or_pos ((i.val + 1) / r) with h | h
    · rw [h] at hqo; simp at hqo
    · exact h
  obtain ⟨hdiv, hmod⟩ := div_shift (r := r) (q := (i.val + 1) / r)
    (s := (i.val + 1) % r) hr hslt hqpos
  have hdecomp : r * ((i.val + 1) / r) + (i.val + 1) % r = i.val + 1 := Nat.div_add_mod _ _
  have hrv : r ≤ i.val := by
    have := le_pred_of_pos_div_and_mod hr hqpos hs0
    simpa using this
  have hv : i.val - r + 1 = i.val + 1 - r := by omega
  have hjeq : (shiftDown r k i).val + 1 =
      r * ((i.val + 1) / r) + (i.val + 1) % r - r := by
    change i.val - r + 1 = r * ((i.val + 1) / r) + (i.val + 1) % r - r
    rw [hv, hdecomp]
  rw [Finset.mem_union]
  rcases eq_or_ne ((i.val + 1) / r) 1 with h1 | h1
  · left
    rw [mem_dIdx]
    left
    have h2 : r + (i.val + 1) % r = i.val + 1 := by
      have := hdecomp; rw [h1, Nat.mul_one] at this; exact this
    show i.val - r < r
    omega
  · right
    rw [mem_nIdx, hjeq, hmod, hdiv]
    exact ⟨hs0, mod_two_pred_of_odd hqo h1, pos_pred_of_odd_ne_one hqo h1⟩

/-- The shift is injective on `nIdx`. -/
lemma shiftDown_injOn_nIdx (r k : ℕ) (hr : 0 < r) :
    Set.InjOn (shiftDown r k) ↑(nIdx r k) := by
  intro i hi j hj heq
  have hi' : r ≤ i.val := r_le_val_of_mem_nIdx hr (by simpa using hi)
  have hj' : r ≤ j.val := r_le_val_of_mem_nIdx hr (by simpa using hj)
  have hval : i.val - r = j.val - r := by
    have h1 := congrArg (fun t : Fin k => t.val) heq
    unfold shiftDown at h1
    simpa using h1
  exact Fin.ext (by omega)

/-- The shift is injective on `mIdx`. -/
lemma shiftDown_injOn_mIdx (r k : ℕ) (hr : 0 < r) :
    Set.InjOn (shiftDown r k) ↑(mIdx r k) := by
  intro i hi j hj heq
  have hi' : r ≤ i.val := r_le_val_of_mem_mIdx hr (by simpa using hi)
  have hj' : r ≤ j.val := r_le_val_of_mem_mIdx hr (by simpa using hj)
  have hval : i.val - r = j.val - r := by
    have h1 := congrArg (fun t : Fin k => t.val) heq
    unfold shiftDown at h1
    simpa using h1
  exact Fin.ext (by omega)

/-- `dIdx` and `nIdx` are disjoint (they are parts of a partition of the prime positions). -/
lemma disjoint_dIdx_nIdx (r k : ℕ) : Disjoint (dIdx r k) (nIdx r k) := by
  rw [Finset.disjoint_left]
  intro i hd hn
  rw [mem_dIdx] at hd
  rw [mem_nIdx] at hn
  obtain ⟨hs0, hqe, hq0⟩ := hn
  rcases hd with hd | ⟨hd, -⟩
  · have hlt : i.val + 1 < r := by
      rcases lt_or_ge (i.val + 1) r with h | h
      · exact h
      · exfalso
        have heq : i.val + 1 = r := by omega
        rw [heq, Nat.mod_self] at hs0
        omega
    have hzero : (i.val + 1) / r = 0 := Nat.div_eq_of_lt hlt
    omega
  · rw [hd] at hs0; omega

/-! ## The product comparison -/

/-- **Matching of positions.**  If `φ` maps `A` injectively into `B` and never moves a position
up (`φ i ≤ i`), then the product of a strictly decreasing positive sequence over `A` is at most
the same product over `B`: each factor `p i` is dominated by the factor `p (φ i)` sitting at the
matched, no later position. -/
lemma prod_le_prod_of_shift {k : ℕ} {p : Fin k → ℕ} (hp : StrictAnti p) (hp1 : ∀ i, 1 ≤ p i)
    {A B : Finset (Fin k)} {φ : Fin k → Fin k} (hmem : ∀ i ∈ A, φ i ∈ B)
    (hle : ∀ i ∈ A, φ i ≤ i) (hinj : Set.InjOn φ ↑A) :
    ∏ i ∈ A, p i ≤ ∏ j ∈ B, p j := by
  have hpoint : ∀ i ∈ A, p i ≤ p (φ i) := fun i hi => hp.antitone (hle i hi)
  calc ∏ i ∈ A, p i ≤ ∏ i ∈ A, p (φ i) :=
        Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) hpoint
    _ = ∏ j ∈ A.image φ, p j := (Finset.prod_image (f := p) hinj).symm
    _ ≤ ∏ j ∈ B, p j :=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.image_subset_iff.mpr hmem)
          (fun i _ => Nat.zero_le _) (fun j _ _ => hp1 j)

/-! ## The statement -/

theorem sepPair_bounds {r d m n : ℕ} (hr : 2 ≤ r) (h : IsSepPair r d m n) :
    n ≤ m ∧ m ≤ d * n ∧ m * m ≤ d * m * n ∧ n * n ≤ d * m * n := by
  obtain ⟨k, p, hp, hd, hm, hn⟩ := h
  obtain ⟨hpanti, hpprime, -⟩ := hp
  have hp1 : ∀ i : Fin k, 1 ≤ p i := fun i => (hpprime i).one_le
  have hr0 : 0 < r := by omega
  -- `n ≤ m`: match every `n`-position with the `m`-position `r` places before it
  have hnm : n ≤ m := by
    rw [hn, hm]
    exact prod_le_prod_of_shift hpanti hp1 (φ := shiftDown r k)
      (fun i hi => shiftDown_mem_mIdx_of_mem_nIdx hr0 hi)
      (fun _ _ => Nat.sub_le _ _)
      (shiftDown_injOn_nIdx r k hr0)
  -- `m ≤ d * n`: match every `m`-position with the position `r` places before it, which lies in
  -- `dIdx` (for `q = 1`) or in `nIdx` (for `q ≥ 3`)
  have hmdn : m ≤ d * n := by
    rw [hm, hd, hn]
    rw [← Finset.prod_union (disjoint_dIdx_nIdx r k)]
    exact prod_le_prod_of_shift hpanti hp1 (φ := shiftDown r k)
      (fun i hi => shiftDown_mem_dIdx_or_nIdx_of_mem_mIdx hr0 hi)
      (fun _ _ => Nat.sub_le _ _)
      (shiftDown_injOn_mIdx r k hr0)
  have hd1 : 1 ≤ d := by rw [hd]; exact Finset.one_le_prod₀ (fun i _ => hp1 i)
  refine ⟨hnm, hmdn, ?_, ?_⟩
  · calc m * m ≤ (d * n) * m := Nat.mul_le_mul_right m hmdn
      _ = d * m * n := by ring
  · calc n * n ≤ m * n := Nat.mul_le_mul_right n hnm
      _ ≤ d * m * n := by
          have h1 : m ≤ d * m := Nat.le_mul_of_pos_left m (by omega)
          calc m * n ≤ (d * m) * n := Nat.mul_le_mul_right n h1
            _ = d * m * n := by ring

end Work.FIArea7
