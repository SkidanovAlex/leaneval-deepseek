/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# A "low" stable letter for the two-letter weight `tlW p q`

For the weight `tlW p q : Fin 2 → ℤ` (`a = 0 ↦ q`, `b = 1 ↦ -p`) and coprime `p, q ≥ 1`, this file
exhibits an element `τ` of `F {0,1}` with `cohom (tlW p q) τ = 1` whose decorated word
`decor (tlW p q) 0 (wordOf τ)` uses only edges of the window `[0, p q]` of the level graph, and
moreover whose read/target levels are bounded by `p q - max p q + 1`.

The construction is a Bézout word: for `p ≥ 2` we take `s ∈ [1, p-1]` with `q s ≡ 1 (mod p)`,
`t = (q s - 1) / p`, and
`τ = a ^ s * b ^ t` (so `cohom τ = ofAdd (q s - p t) = ofAdd 1`).  Its decoration is
`[((0, j q), true)]_{j < s} ++ [((1, s q - k p), true)]_{k < t}`; the walk rises from `0` to `s q`
along the `a`-edges and descends to `1` along the `b`-edges, and the maximum level `s q` is at most
`p q - max p q + 1` because `s ≤ p - 1` and (in the case `p > q`) `t ≤ q - 1`.  For `p = 1` one takes
`τ = b⁻¹`.

-/
import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.decor_tlU_tlW_at
import Submission.Work.OROneRel.wordOf_of_pow_mul_of_pow
import Submission.Work.OROneRel.exists_low_bezout
import Submission.Work.OROneRel.decor_of_pow_pow_tlW
import Submission.Work.OROneRel.twoLetterLowTau_arith

namespace Work.OROneRel

/-- The reduced word of the inverse of a generator is the single negative letter. -/
private lemma wordOf_inv_generator (a : Fin 2) :
    Work.OROneRel.wordOf ((FreeGroup.of a)⁻¹) = [(a, false)] := by
  show ((FreeGroup.of a)⁻¹).toWord = _
  rw [FreeGroup.toWord_inv, FreeGroup.toWord_of]
  rfl

/-- The decoration of the single negative letter `(a, false)` read at level `0`. -/
private lemma decor_singleton_false (c : Fin 2 → ℤ) (a : Fin 2) :
    Work.OROneRel.decor c 0 [(a, false)] = [((a, 0 - c a), false)] := rfl

theorem twoLetterLowTau (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∃ τ : FreeGroup (Fin 2),
      Work.OROneRel.cohom (Work.OROneRel.tlW p q) τ = Multiplicative.ofAdd 1 ∧
      (∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf τ),
        Work.OROneRel.coverEdge e ∈
          Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ))) ∧
      (∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf τ),
        e.1.2 + Work.OROneRel.tlW p q e.1.1 ≤
          (p : ℤ) * (q : ℤ) - max (p : ℤ) (q : ℤ) + 1) := by
  classical
  rcases Nat.lt_or_ge p 2 with hp_lt | hp_ge
  · -- ## `p = 1`: take `τ = b⁻¹`.
    have hp1 : p = 1 := by omega
    subst hp1
    have htl1 : Work.OROneRel.tlW 1 q 1 = -(1 : ℤ) := Work.OROneRel.tlW_one 1 q
    have hdec : Work.OROneRel.decor (Work.OROneRel.tlW 1 q) 0
        (Work.OROneRel.wordOf ((FreeGroup.of (1 : Fin 2))⁻¹)) =
          [(((1 : Fin 2), (1 : ℤ)), false)] := by
      rw [wordOf_inv_generator, decor_singleton_false, htl1]
      norm_num
    refine ⟨(FreeGroup.of (1 : Fin 2))⁻¹, ?_, ?_, ?_⟩
    · -- the weight of `b⁻¹` is `1`
      rw [map_inv, Work.OROneRel.cohom_of, htl1, ofAdd_neg, inv_inv]
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
    · -- level bound
      intro e he
      rw [hdec] at he
      simp only [List.mem_singleton] at he
      subst he
      have hmax : max ((1 : ℕ) : ℤ) (q : ℤ) = (q : ℤ) := by
        rw [max_eq_right]
        exact_mod_cast hq
      rw [htl1, hmax]
      norm_num
  · -- ## `2 ≤ p`: the Bézout word `a ^ s * b ^ t`.
    obtain ⟨s, t, hsp, hst⟩ := exists_low_bezout p q hp_ge hcop.symm
    obtain ⟨htq, hsB⟩ := twoLetterLowTau_arith p q s t hp_ge hq hsp hst
    have hstZ : (q : ℤ) * (s : ℤ) = (p : ℤ) * (t : ℤ) + 1 := by exact_mod_cast hst
    have hq0 : (0 : ℤ) ≤ (q : ℤ) := by positivity
    have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
    have hmax1 : (1 : ℤ) ≤ max (p : ℤ) (q : ℤ) :=
      le_trans (by exact_mod_cast (by omega : 1 ≤ p)) (le_max_left _ _)
    have hBpq : (p : ℤ) * (q : ℤ) - max (p : ℤ) (q : ℤ) + 1 ≤ (p : ℤ) * (q : ℤ) := by
      linarith
    refine ⟨FreeGroup.of (0 : Fin 2) ^ s * FreeGroup.of (1 : Fin 2) ^ t, ?_, ?_, ?_⟩
    · -- the weight is `1`
      rw [map_mul, map_pow, map_pow, Work.OROneRel.cohom_of, Work.OROneRel.cohom_of,
        Work.OROneRel.tlW_zero, Work.OROneRel.tlW_one,
        ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add]
      congr 1
      rw [nsmul_eq_mul, nsmul_eq_mul]
      nlinarith [hstZ]
    · -- window membership
      intro e he
      rw [decor_of_pow_pow_tlW] at he
      rw [List.mem_append] at he
      rcases he with he | he
      · obtain ⟨j, hj⟩ := List.mem_ofFn.mp he
        rw [← hj]
        have hj1 : (j : ℤ) + 1 ≤ (s : ℤ) := by
          have : (j : ℕ) + 1 ≤ s := Nat.succ_le_of_lt j.isLt
          exact_mod_cast this
        have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
        simp only [Work.OROneRel.coverEdge, Work.OROneRel.mem_winE]
        rw [Work.OROneRel.tlW_zero]
        refine ⟨?_, ?_, ?_, ?_⟩
        · nlinarith [hj0, hq0]
        · nlinarith [hsB, hBpq, hj1, hj0, hq0]
        · nlinarith [hj0, hq0]
        · nlinarith [hsB, hBpq, hj1, hj0, hq0]
      · obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
        rw [← hk]
        have hk1 : (k : ℤ) + 1 ≤ (t : ℤ) := by
          have : (k : ℕ) + 1 ≤ t := Nat.succ_le_of_lt k.isLt
          exact_mod_cast this
        have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
        simp only [Work.OROneRel.coverEdge, Work.OROneRel.mem_winE]
        rw [Work.OROneRel.tlW_one]
        refine ⟨?_, ?_, ?_, ?_⟩
        · nlinarith [hstZ, hk1, hp0]
        · nlinarith [hsB, hBpq, hk0, hp0, hq0]
        · nlinarith [hstZ, hk1, hp0]
        · nlinarith [hsB, hBpq, hk0, hp0, hq0]
    · -- level bound
      intro e he
      rw [decor_of_pow_pow_tlW] at he
      rw [List.mem_append] at he
      rcases he with he | he
      · obtain ⟨j, hj⟩ := List.mem_ofFn.mp he
        rw [← hj]
        have hj1 : (j : ℤ) + 1 ≤ (s : ℤ) := by
          have : (j : ℕ) + 1 ≤ s := Nat.succ_le_of_lt j.isLt
          exact_mod_cast this
        have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
        change (j : ℤ) * (q : ℤ) + Work.OROneRel.tlW p q (0 : Fin 2) ≤
          (p : ℤ) * (q : ℤ) - max (p : ℤ) (q : ℤ) + 1
        rw [Work.OROneRel.tlW_zero]
        nlinarith [hsB, hj1, hq0, hj0]
      · obtain ⟨k, hk⟩ := List.mem_ofFn.mp he
        rw [← hk]
        have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
        change (s : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ) + Work.OROneRel.tlW p q (1 : Fin 2) ≤
          (p : ℤ) * (q : ℤ) - max (p : ℤ) (q : ℤ) + 1
        rw [Work.OROneRel.tlW_one]
        nlinarith [hsB, hp0, hk0]

end Work.OROneRel
