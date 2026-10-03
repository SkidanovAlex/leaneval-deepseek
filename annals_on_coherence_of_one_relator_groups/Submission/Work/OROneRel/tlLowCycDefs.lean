/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The low window `[0, p+q-1]` of the two-letter relator `a^p b^q`: the cyclic window

This file fixes the vocabulary of the description of the *low* window of the two-letter band: for
coprime `p, q ≥ 1` and the weight `tlW p q` (`a ↦ q`, `b ↦ -p`), the window `[0, p+q-1]` of the
level graph of the `Z`-cover is a single *cycle*: every level `i ∈ [0, p+q-1]` has exactly one
outgoing window edge (the `a`-edge when `i < p`, the `b`-edge when `i ≥ p`), and the `p+q` edges
form a single cycle visiting every level.

The cycle is indexed from the level `0`:

* `cycLevel p q k = (k * q) % (p+q)` -- the level reached after `k` steps of the cycle;
* `cycLetter p q k` -- the generator of the outgoing window edge at the level `cycLevel p q k`;
* `cycList p q` / `cycWord p q` -- the word of the full cycle (`p+q` letters), the generator of
  `tlWin p q (p+q-1)`;
* `cycLift p q l` / `cycU p q l` -- the word of the walk from the level `0` to the *lifted*
  position `l ∈ ℤ` (positive for the forward direction, negative for the backward direction), i.e.
  the universal lift of the cycle to the line.

The main arithmetic content is that `cycLevel (k+1)` is obtained from `cycLevel k` by the rule
`i ↦ i + q` if `i < p` and `i ↦ i - p` if `i ≥ p` (`cycLevel_succ_below`, `cycLevel_succ_above`),
with the converse rule `cycLevel_pred_*` for `k - 1`.

This file contains definitions and elementary arithmetic only.
-/
import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs

namespace Work.OROneRel

/-! ## The integer size of the window -/

/-- `p + q`, as an integer: the number of levels of the low window `[0, p+q-1]`. -/
def tlN (p q : ℕ) : ℤ := (p : ℤ) + (q : ℤ)

theorem tlN_pos (p q : ℕ) (hp : 1 ≤ p) : 0 < tlN p q := by
  have : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  simp only [tlN]; omega

theorem tlN_ne_zero (p q : ℕ) (hp : 1 ≤ p) : tlN p q ≠ 0 :=
  ne_of_gt (tlN_pos p q hp)

theorem tlN_cast (p q : ℕ) : tlN p q = ((p + q : ℕ) : ℤ) := by
  simp only [tlN]; push_cast; ring

/-! ## The levels of the cycle -/

/-- **The level of the cycle at index `k`**: `(k * q) mod (p+q)`.  The cycle of the low window
turns by `q` at each step, so the level after `k` steps is `k * q` modulo the size `p+q` of the
window. -/
def cycLevel (p q : ℕ) (k : ℤ) : ℤ := (k * (q : ℤ)) % tlN p q

theorem cycLevel_bounds (p q : ℕ) (hp : 1 ≤ p) (k : ℤ) :
    0 ≤ cycLevel p q k ∧ cycLevel p q k < tlN p q := by
  have hN : 0 < tlN p q := tlN_pos p q hp
  exact ⟨Int.emod_nonneg _ (ne_of_gt hN), Int.emod_lt_of_pos _ hN⟩

theorem cycLevel_zero (p q : ℕ) : cycLevel p q 0 = 0 := by
  simp [cycLevel]

theorem cycLevel_succ (p q : ℕ) (hp : 1 ≤ p) (k : ℤ) :
    cycLevel p q (k + 1) = (cycLevel p q k + (q : ℤ)) % tlN p q := by
  have h1 : (0 : ℤ) ≤ (q : ℤ) := by omega
  have h2 : (q : ℤ) < tlN p q := by
    have : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    simp only [tlN]; omega
  have hqN : (q : ℤ) % tlN p q = (q : ℤ) := Int.emod_eq_of_lt h1 h2
  have h : (k + 1) * (q : ℤ) = k * (q : ℤ) + (q : ℤ) := by ring
  rw [cycLevel, h, Int.add_emod, hqN, cycLevel]

/-- **The step of the cycle below `p`**: at a level `i < p` the (unique) outgoing window edge is
the `a`-edge, which raises the level by `q`. -/
theorem cycLevel_succ_below (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {k : ℤ}
    (h : cycLevel p q k < (p : ℤ)) :
    cycLevel p q (k + 1) = cycLevel p q k + (q : ℤ) := by
  have hb := cycLevel_bounds p q hp k
  have hN : 0 < tlN p q := tlN_pos p q hp
  have hlt : cycLevel p q k + (q : ℤ) < tlN p q := by
    simp only [tlN] at hb ⊢
    omega
  rw [cycLevel_succ p q hp k, Int.emod_eq_of_lt (by omega) hlt]

/-- **The step of the cycle at or above `p`**: at a level `i ≥ p` the (unique) outgoing window edge
is the `b`-edge, which lowers the level by `p`. -/
theorem cycLevel_succ_above (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {k : ℤ}
    (h : (p : ℤ) ≤ cycLevel p q k) :
    cycLevel p q (k + 1) = cycLevel p q k - (p : ℤ) := by
  have hb := cycLevel_bounds p q hp k
  rw [cycLevel_succ p q hp k]
  have hdvd : tlN p q ∣ (cycLevel p q k + (q : ℤ)) - (cycLevel p q k - (p : ℤ)) :=
    ⟨1, by simp only [tlN]; ring⟩
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hdvd)]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- **The level `cycLevel p q k` is congruent to `k * q` modulo `p+q`** (the level is the
reduction of `k * q`). -/
theorem cycLevel_modEq (p q : ℕ) (k : ℤ) : cycLevel p q k ≡ k * (q : ℤ) [ZMOD tlN p q] := by
  rw [cycLevel, Int.modEq_iff_dvd]
  refine ⟨(k * (q : ℤ)) / tlN p q, ?_⟩
  have h := Int.emod_add_mul_ediv (k * (q : ℤ)) (tlN p q)
  linarith

/-- **The inverse step of the cycle below `q`**: the level `cycLevel (k-1)` preceding `cycLevel k`
is `cycLevel k + p` when `cycLevel k < q` (the incoming edge is then the `b`-edge traversed
backwards). -/
theorem cycLevel_pred_below (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {k : ℤ}
    (h : cycLevel p q k < (q : ℤ)) :
    cycLevel p q (k - 1) = cycLevel p q k + (p : ℤ) := by
  have hb := cycLevel_bounds p q hp k
  have hm := cycLevel_modEq p q k
  have hdvd : tlN p q ∣ ((k - 1) * (q : ℤ)) - (cycLevel p q k + (p : ℤ)) := by
    have h' := Int.modEq_iff_dvd.mp hm
    rw [show ((k - 1) * (q : ℤ)) - (cycLevel p q k + (p : ℤ))
        = (k * (q : ℤ) - cycLevel p q k) - tlN p q from by simp only [tlN]; ring]
    exact dvd_sub h' (dvd_refl _)
  rw [show cycLevel p q (k - 1) = ((k - 1) * (q : ℤ)) % tlN p q from rfl,
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hdvd)]
  exact Int.emod_eq_of_lt (by omega) (by simp only [tlN] at hb ⊢; omega)

/-- **The inverse step of the cycle at or above `q`**: `cycLevel (k-1) = cycLevel k - q` when
`cycLevel k ≥ q` (the incoming edge is then the `a`-edge traversed backwards). -/
theorem cycLevel_pred_above (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {k : ℤ}
    (h : (q : ℤ) ≤ cycLevel p q k) :
    cycLevel p q (k - 1) = cycLevel p q k - (q : ℤ) := by
  have hb := cycLevel_bounds p q hp k
  have hm := cycLevel_modEq p q k
  have hdvd : tlN p q ∣ ((k - 1) * (q : ℤ)) - (cycLevel p q k - (q : ℤ)) := by
    have h' := Int.modEq_iff_dvd.mp hm
    rw [show ((k - 1) * (q : ℤ)) - (cycLevel p q k - (q : ℤ))
        = k * (q : ℤ) - cycLevel p q k from by ring]
    exact h'
  rw [show cycLevel p q (k - 1) = ((k - 1) * (q : ℤ)) % tlN p q from rfl,
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hdvd)]
  exact Int.emod_eq_of_lt (by omega) (by simp only [tlN] at hb ⊢; omega)

/-! ## Periodicity -/

theorem cycLevel_eq_of_dvd_sub (p q : ℕ) {k k' : ℤ} (h : tlN p q ∣ k' - k) :
    cycLevel p q k' = cycLevel p q k := by
  rw [cycLevel, cycLevel, Int.emod_eq_emod_iff_emod_sub_eq_zero]
  have h' : (k' * (q : ℤ) - k * (q : ℤ)) = (k' - k) * (q : ℤ) := by ring
  rw [h', Int.emod_eq_zero_of_dvd]
  exact Dvd.dvd.mul_right h _

theorem cycLevel_periodic (p q : ℕ) (k : ℤ) :
    cycLevel p q (k + tlN p q) = cycLevel p q k :=
  cycLevel_eq_of_dvd_sub p q ⟨1, by ring⟩

theorem cycLevel_periodic_nat (p q : ℕ) (k : ℤ) :
    cycLevel p q (k + ((p + q : ℕ) : ℤ)) = cycLevel p q k :=
  cycLevel_eq_of_dvd_sub p q ⟨1, by rw [tlN_cast]; ring⟩

theorem cycLevel_add_tlN_mul (p q : ℕ) (k m : ℤ) :
    cycLevel p q (k + tlN p q * m) = cycLevel p q k :=
  cycLevel_eq_of_dvd_sub p q ⟨m, by ring⟩

/-- **The index of the level `0`**: since `gcd (p+q) q = 1`, the cycle returns to the level `0`
exactly at the multiples of `p+q`. -/
theorem cycLevel_eq_zero_iff (p q : ℕ) (hp : 1 ≤ p) (hcop : Nat.Coprime p q) (k : ℤ) :
    cycLevel p q k = 0 ↔ tlN p q ∣ k := by
  have hN : 0 < tlN p q := tlN_pos p q hp
  have hcop' : IsCoprime (tlN p q) (q : ℤ) := by
    have h1 : Nat.Coprime (p + q) q := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have h2 : (p + q).gcd q = p.gcd q := Nat.gcd_add_self_left q p
      rw [h2, Nat.coprime_iff_gcd_eq_one.mp hcop]
    have h2 : IsCoprime (((p + q : ℕ) : ℤ)) ((q : ℕ) : ℤ) := h1.isCoprime
    rwa [← tlN_cast] at h2
  constructor
  · intro h
    have h' : (k * (q : ℤ)) % tlN p q = 0 := h
    have hdvd : tlN p q ∣ k * (q : ℤ) := Int.dvd_of_emod_eq_zero h'
    exact hcop'.dvd_of_dvd_mul_right hdvd
  · rintro ⟨m, rfl⟩
    rw [cycLevel]
    exact Int.emod_eq_zero_of_dvd (Dvd.intro (m * (q : ℤ)) (by ring))

/-! ## The letters of the cycle -/

/-- **The generator of the outgoing window edge at the level `cycLevel p q k`**: `a` (`= 0`) if the
level is `< p`, and `b` (`= 1`) otherwise. -/
def cycLetter (p q : ℕ) (k : ℤ) : Fin 2 := if cycLevel p q k < (p : ℤ) then 0 else 1

theorem cycLetter_zero_iff (p q : ℕ) (k : ℤ) : cycLetter p q k = 0 ↔ cycLevel p q k < (p : ℤ) := by
  rw [cycLetter]
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    exact absurd h (by decide)
  · intro h
    rw [if_pos h]

theorem cycLetter_one_iff (p q : ℕ) (k : ℤ) : cycLetter p q k = 1 ↔ (p : ℤ) ≤ cycLevel p q k := by
  rw [cycLetter]
  constructor
  · intro h
    by_contra hc
    rw [if_pos (lt_of_not_ge hc)] at h
    exact absurd h (by decide)
  · intro h
    rw [if_neg (not_lt.mpr h)]

/-- The weight of the letter of the cycle at index `k`. -/
theorem tlW_cycLetter (p q : ℕ) (k : ℤ) :
    tlW p q (cycLetter p q k) = if cycLevel p q k < (p : ℤ) then (q : ℤ) else -(p : ℤ) := by
  rw [cycLetter]
  split_ifs with h
  · rfl
  · rfl

theorem cycLetter_eq_of_dvd_sub (p q : ℕ) {k k' : ℤ} (h : tlN p q ∣ k' - k) :
    cycLetter p q k' = cycLetter p q k := by
  rw [cycLetter, cycLetter, cycLevel_eq_of_dvd_sub p q h]

theorem cycLetter_periodic (p q : ℕ) (k : ℤ) :
    cycLetter p q (k + tlN p q) = cycLetter p q k :=
  cycLetter_eq_of_dvd_sub p q ⟨1, by ring⟩

/-! ## The cycle word, and the lifted walk -/

/-- **The word of the cycle**, as a list of letters: the `k`-th letter for `0 ≤ k < p+q`. -/
def cycList (p q : ℕ) : List (Fin 2 × Bool) :=
  (List.range (p + q)).map (fun k : ℕ => (cycLetter p q (k : ℤ), true))

/-- **The cycle word** `w ∈ F₂`, the generator of the low window subgroup. -/
noncomputable def cycWord (p q : ℕ) : FreeGroup (Fin 2) := FreeGroup.mk (cycList p q)

/-- **The lifted walk to the position `l ∈ ℤ`**, as a list of letters.  For `l ≥ 0` this is the
sequence of letters of the cycle read forward from `0`; for `l < 0` it is the sequence of letters
read backward from `0`, i.e. the inverses of the letters at the positions `-1, -2, …, l`. -/
def cycLift (p q : ℕ) (l : ℤ) : List (Fin 2 × Bool) :=
  if 0 ≤ l then (List.range l.toNat).map (fun k : ℕ => (cycLetter p q (k : ℤ), true))
  else (List.range l.natAbs).map (fun k : ℕ => (cycLetter p q (-1 - (k : ℤ)), false))

/-- **The lifted walk element** `cycU l ∈ F₂`, the label of the walk from the level `0` to the
lifted position `l`. -/
noncomputable def cycU (p q : ℕ) (l : ℤ) : FreeGroup (Fin 2) := FreeGroup.mk (cycLift p q l)

theorem cycLift_zero (p q : ℕ) : cycLift p q 0 = [] := by
  simp [cycLift]

theorem cycU_zero (p q : ℕ) : cycU p q 0 = 1 := by
  rw [cycU, cycLift_zero]
  rfl

theorem cycWord_eq (p q : ℕ) : cycWord p q = cycU p q ((p + q : ℕ) : ℤ) := by
  rw [cycWord, cycU, cycLift, if_pos (by positivity), Int.toNat_natCast]
  rfl

end Work.OROneRel
