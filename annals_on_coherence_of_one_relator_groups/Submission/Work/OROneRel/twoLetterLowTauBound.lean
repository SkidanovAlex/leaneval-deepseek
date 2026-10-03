/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# A bounded "low" stable letter for the two-letter weight `tlW p q`

For the weight `tlW p q : Fin 2 → ℤ` (`a = 0 ↦ q`, `b = 1 ↦ -p`) of the two-letter case and coprime
`p, q ≥ 1`, this file exhibits an element `τ` of `F {0,1}` with `cohom (tlW p q) τ = 1` whose
decorated word uses only edges of the window `[0, p q]` of the level graph, and whose read and target
levels are *all* bounded by a level `L` satisfying `L + max p q - 1 ≤ p q` (so `L` is no larger than
`p q - max p q + 1`).

This is the statement `Work.OROneRel.twoLetterLowTauBound`, a strengthening of
`Work.OROneRel.twoLetterLowTau` (which bounds only the *target* level `e.1.2 + tlW p q e.1.1`):
the extra conjunct `e.1.2 ≤ L` bounds the *source* level of every decorated letter as well.  It is
exactly the form in which the "low stable letter" of the two-letter Magnus--Moldavanskii step is
consumed (`Work.OROneRel.winE (tlW p q) 0 (p q)` must contain the whole walk of `τ`, including its
bottom end).

The construction is the Bézout word of `twoLetterLowTau`: for `p ≥ 2` take `s < p` with
`q s ≡ 1 (mod p)`, `t = (q s - 1) / p` and
`τ = a ^ s * b ^ t = FreeGroup.of 0 ^ s * FreeGroup.of 1 ^ t`, whose decoration is
`[((0, j q), true)]_{j < s} ++ [((1, s q - k p), true)]_{k < t}` (`decor_of_pow_pow_tlW`).  The walk
runs from level `0` up to level `s q` and back down to the level `1`, and `s q = p t + 1` together
with `s < p` gives `s q ≤ p q - max p q + 1` (`twoLetterLowTau_arith`).  For `p = 1` we take
`τ = b⁻¹` and `L = p q - max p q + 1 = 1`.

The numeric input is isolated in `Work.OROneRel.twoLetterLowTauBound_arith`, the window membership in
`Work.OROneRel.decor_pow_pow_tlW_winE` and the level bound in
`Work.OROneRel.decor_pow_pow_tlW_levelBound`.
-/
import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetterLowTau
import Submission.Work.OROneRel.decor_of_pow_pow_tlW

namespace Work.OROneRel

/-! ## Reading the decoration of a single negative letter -/

/-- The reduced word of the inverse of a generator is the single negative letter. -/
private theorem wordOf_inv_generator_fin2 (a : Fin 2) :
    Work.OROneRel.wordOf ((FreeGroup.of a)⁻¹) = [(a, false)] := by
  show ((FreeGroup.of a)⁻¹).toWord = _
  rw [FreeGroup.toWord_inv, FreeGroup.toWord_of]
  rfl

/-- The decoration of the single negative letter `(a, false)` read at level `0`. -/
private theorem decor_singleton_false_fin2 (c : Fin 2 → ℤ) (a : Fin 2) :
    Work.OROneRel.decor c 0 [(a, false)] = [((a, 0 - c a), false)] := rfl

/-! ## The arithmetic of the level bound -/

/-- **The numerics of the low stable letter.**  For `p ≥ 2`, `q ≥ 1` and the Bézout data
`q * s = p * t + 1`, `s < p` of `Work.OROneRel.exists_low_bezout`, the level
`L = p q - max p q + 1` is non-negative, the bound `L + max p q - 1 ≤ p q` of
`Work.OROneRel.twoLetterLowTauBound` holds, and the top level `s q` of the Bézout walk is at most
`L` (which is what bounds *both* endpoints of every decorated letter of the walk). -/
theorem twoLetterLowTauBound_arith (p q s t : ℕ) (hp : 2 ≤ p) (hq : 1 ≤ q) (hsp : s < p)
    (hst : q * s = p * t + 1) :
    0 ≤ (p : ℤ) * (q : ℤ) - max (p : ℤ) (q : ℤ) + 1 ∧
    ((p : ℤ) * (q : ℤ) - max (p : ℤ) (q : ℤ) + 1) + max (p : ℤ) (q : ℤ) - 1 ≤ (p : ℤ) * (q : ℤ) ∧
    (s : ℤ) * (q : ℤ) ≤ (p : ℤ) * (q : ℤ) - max (p : ℤ) (q : ℤ) + 1 := by
  have hsB := (twoLetterLowTau_arith p q s t hp hq hsp hst).2
  have h1 : (p : ℤ) ≤ (p : ℤ) * (q : ℤ) := by
    nlinarith [show (1 : ℤ) ≤ (q : ℤ) by exact_mod_cast hq, show (0 : ℤ) ≤ (p : ℤ) by positivity]
  have h2 : (q : ℤ) ≤ (p : ℤ) * (q : ℤ) := by
    nlinarith [show (1 : ℤ) ≤ (p : ℤ) by exact_mod_cast (by omega : 1 ≤ p),
      show (0 : ℤ) ≤ (q : ℤ) by positivity]
  have hmax : max (p : ℤ) (q : ℤ) ≤ (p : ℤ) * (q : ℤ) + 1 := by linarith [max_le h1 h2]
  refine ⟨by linarith, by ring_nf; linarith, ?_⟩
  linarith [hsB, mul_comm (q : ℤ) (s : ℤ)]

/-! ## The window membership of the Bézout walk -/

/-- **The Bézout walk stays in the band `[0, p q]`.**  Every decorated letter of the word
`a ^ s * b ^ t` traverses an edge of the window `[0, p q]` of the level graph of the weight
`tlW p q`, for the Bézout data `s < p`, `q * s = p * t + 1` and `p ≥ 2`, `q ≥ 1`. -/
theorem decor_pow_pow_tlW_winE (p q s t : ℕ) (hp : 2 ≤ p) (hq : 1 ≤ q) (hsp : s < p)
    (hst : q * s = p * t + 1) :
    ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (FreeGroup.of (0 : Fin 2) ^ s * FreeGroup.of (1 : Fin 2) ^ t)),
      Work.OROneRel.coverEdge e ∈
        Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
  have hsB := (twoLetterLowTau_arith p q s t hp hq hsp hst).2
  have hstZ : (q : ℤ) * (s : ℤ) = (p : ℤ) * (t : ℤ) + 1 := by exact_mod_cast hst
  have hq0 : (0 : ℤ) ≤ (q : ℤ) := by positivity
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  have hmax1 : (1 : ℤ) ≤ max (p : ℤ) (q : ℤ) :=
    le_trans (by exact_mod_cast (by omega : 1 ≤ p)) (le_max_left _ _)
  have hBpq : (p : ℤ) * (q : ℤ) - max (p : ℤ) (q : ℤ) + 1 ≤ (p : ℤ) * (q : ℤ) := by linarith
  intro e he
  rw [decor_of_pow_pow_tlW] at he
  rw [List.mem_append] at he
  rcases he with he | he
  · obtain ⟨j, hj⟩ := List.mem_ofFn.mp he
    rw [← hj]
    have hj1 : (j : ℤ) + 1 ≤ (s : ℤ) := by
      have := Nat.succ_le_of_lt j.isLt
      exact_mod_cast this
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
    simp only [Work.OROneRel.coverEdge, Work.OROneRel.mem_winE]
    rw [Work.OROneRel.tlW_zero]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hj0, hq0, hsB, hBpq, hj1]
  · obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
    rw [← hk]
    have hk1 : (k : ℤ) + 1 ≤ (t : ℤ) := by
      have := Nat.succ_le_of_lt k.isLt
      exact_mod_cast this
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    simp only [Work.OROneRel.coverEdge, Work.OROneRel.mem_winE]
    rw [Work.OROneRel.tlW_one]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hstZ, hk1, hp0, hq0, hsB, hBpq, hk0]

/-! ## The level bound of the Bézout walk -/

/-- **Both endpoints of every decorated letter of the Bézout walk are at most `L`**, as soon as `L`
is above the top level `s q` of the walk.  Indeed the first block `a ^ s` is decorated at the levels
`j q ≤ s q` and `(j + 1) q ≤ s q` (`j < s`), while the second block `b ^ t` is decorated at the
levels `s q - k p ≤ s q` and `s q - (k + 1) p ≤ s q` (`k < t`). -/
theorem decor_pow_pow_tlW_levelBound (p q s t : ℕ) (L : ℤ) (hq : 1 ≤ q)
    (hsL : (s : ℤ) * (q : ℤ) ≤ L) :
    ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (FreeGroup.of (0 : Fin 2) ^ s * FreeGroup.of (1 : Fin 2) ^ t)),
      e.1.2 ≤ L ∧ e.1.2 + Work.OROneRel.tlW p q e.1.1 ≤ L := by
  intro e he
  rw [decor_of_pow_pow_tlW] at he
  rw [List.mem_append] at he
  have hq0 : (0 : ℤ) ≤ (q : ℤ) := by positivity
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
  rcases he with he | he
  · obtain ⟨j, hj⟩ := List.mem_ofFn.mp he
    have hjle : (j : ℤ) ≤ (s : ℤ) := by exact_mod_cast Nat.le_of_lt j.isLt
    have hj1 : ((j : ℤ) + 1) ≤ (s : ℤ) := by
      have := Nat.succ_le_of_lt j.isLt
      exact_mod_cast this
    rw [← hj]
    constructor
    · change (j : ℤ) * (q : ℤ) ≤ L
      nlinarith [hjle, hq0, hsL]
    · change (j : ℤ) * (q : ℤ) + Work.OROneRel.tlW p q (0 : Fin 2) ≤ L
      rw [Work.OROneRel.tlW_zero]
      nlinarith [hj1, hq0, hsL]
  · obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
    rw [← hk]
    constructor
    · change (s : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ) ≤ L
      nlinarith [hk0, hp0, hsL]
    · change (s : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ) + Work.OROneRel.tlW p q (1 : Fin 2) ≤ L
      rw [Work.OROneRel.tlW_one]
      nlinarith [hk0, hp0, hsL]

/-! ## The low stable letter, with both level bounds -/

theorem twoLetterLowTauBound (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∃ (τ : FreeGroup (Fin 2)) (L : ℤ),
      Work.OROneRel.cohom (Work.OROneRel.tlW p q) τ = Multiplicative.ofAdd 1 ∧
      0 ≤ L ∧ L + max (p : ℤ) (q : ℤ) - 1 ≤ (p : ℤ) * (q : ℤ) ∧
      (∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf τ),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) ∧
      (∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf τ),
        e.1.2 ≤ L ∧ e.1.2 + Work.OROneRel.tlW p q e.1.1 ≤ L) := by
  classical
  rcases Nat.lt_or_ge p 2 with hp_lt | hp_ge
  · -- ## `p = 1`: take `τ = b⁻¹` and `L = p q - max p q + 1 = 1`.
    have hp1 : p = 1 := by omega
    subst hp1
    have htl1 : Work.OROneRel.tlW 1 q 1 = -(1 : ℤ) := Work.OROneRel.tlW_one 1 q
    have hmax : max ((1 : ℕ) : ℤ) (q : ℤ) = (q : ℤ) := by
      rw [max_eq_right]
      exact_mod_cast hq
    have hdec : Work.OROneRel.decor (Work.OROneRel.tlW 1 q) 0
        (Work.OROneRel.wordOf ((FreeGroup.of (1 : Fin 2))⁻¹)) =
          [(((1 : Fin 2), (1 : ℤ)), false)] := by
      rw [wordOf_inv_generator_fin2, decor_singleton_false_fin2, htl1]
      norm_num
    refine ⟨(FreeGroup.of (1 : Fin 2))⁻¹,
      ((1 : ℕ) : ℤ) * (q : ℤ) - max ((1 : ℕ) : ℤ) (q : ℤ) + 1, ?_, ?_, ?_, ?_, ?_⟩
    · -- the weight of `b⁻¹` is `1`
      rw [map_inv, Work.OROneRel.cohom_of, htl1, ofAdd_neg, inv_inv]
    · -- `0 ≤ L`
      rw [hmax]
      ring_nf
      linarith
    · -- `L + max p q - 1 ≤ p q`
      rw [hmax]
      ring_nf
      linarith
    · -- window membership
      intro e he
      rw [hdec] at he
      simp only [List.mem_singleton] at he
      subst he
      simp only [Work.OROneRel.coverEdge, Work.OROneRel.mem_winE]
      rw [htl1]
      refine ⟨by norm_num, ?_, by norm_num, ?_⟩
      · simpa using (show (1 : ℤ) ≤ (q : ℤ) from by exact_mod_cast hq)
      · simpa using (show (0 : ℤ) ≤ (q : ℤ) from by exact_mod_cast Nat.zero_le q)
    · -- both level bounds
      intro e he
      rw [hdec] at he
      simp only [List.mem_singleton] at he
      subst he
      constructor
      · show (1 : ℤ) ≤ ((1 : ℕ) : ℤ) * (q : ℤ) - max ((1 : ℕ) : ℤ) (q : ℤ) + 1
        rw [hmax]
        ring_nf
        linarith
      · show (1 : ℤ) + Work.OROneRel.tlW 1 q (1 : Fin 2) ≤
            ((1 : ℕ) : ℤ) * (q : ℤ) - max ((1 : ℕ) : ℤ) (q : ℤ) + 1
        rw [htl1, hmax]
        ring_nf
        linarith
  · -- ## `2 ≤ p`: the Bézout word `a ^ s * b ^ t`.
    obtain ⟨s, t, hsp, hst⟩ := exists_low_bezout p q hp_ge hcop.symm
    have hstZ : (q : ℤ) * (s : ℤ) = (p : ℤ) * (t : ℤ) + 1 := by exact_mod_cast hst
    obtain ⟨hL0, hLmax, hsL⟩ := twoLetterLowTauBound_arith p q s t hp_ge hq hsp hst
    refine ⟨FreeGroup.of (0 : Fin 2) ^ s * FreeGroup.of (1 : Fin 2) ^ t,
      (p : ℤ) * (q : ℤ) - max (p : ℤ) (q : ℤ) + 1, ?_, hL0, hLmax, ?_, ?_⟩
    · -- the weight is `1`
      rw [map_mul, map_pow, map_pow, Work.OROneRel.cohom_of, Work.OROneRel.cohom_of,
        Work.OROneRel.tlW_zero, Work.OROneRel.tlW_one,
        ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add]
      congr 1
      rw [nsmul_eq_mul, nsmul_eq_mul]
      nlinarith [hstZ]
    · -- window membership
      exact decor_pow_pow_tlW_winE p q s t hp_ge hq hsp hst
    · -- both level bounds
      exact decor_pow_pow_tlW_levelBound p q s t _ hq hsL

end Work.OROneRel
