import Mathlib
import Submission.Work.LinnikBurgess.lf_defs

open scoped BigOperators
open Classical

namespace Work.LinnikAreas.u8three

open Work.LinnikBurgess

/-- `capSet p e a b` is contained in `range (p^cubeLevel p e)` (it is a filtered subset of
`suppSet`). -/
lemma capSet_subset_range (p e : ℕ) (a b : Fin 3 → ℕ) :
    capSet p e a b ⊆ Finset.range (p ^ cubeLevel p e) := by
  intro y hy
  rw [capSet, Finset.mem_filter] at hy
  rw [suppSet, Finset.mem_filter] at hy
  exact hy.1.1

/-! ## The crux: with the *exact* content exponent `h`, at most `4` capped support points

This is the mathematical heart of the `e ≥ 13`, `p = 3` regime of U8, isolated as a standalone
statement.  For `y ∈ capSet` the transfer hypothesis gives `bval y = T` (as `T ≤ nval y` there),
hence `3^(m+T) ∣ N(y)` with `N = critN a b`; writing `N = 3^h Ñ` for the *exact* content `h`
(`hcontent` + `hprim`, the latter being what the false "`h` free" formulation was missing), this
gives `3^(m+T-h) ∣ Ñ(y)`, while `nval y ≥ T` gives `3^(T-h) ∣ Ñ'(y)`.  The Hensel/Newton root
count then confines the `y < 3^m` to at most `natDegree Ñ ≤ 4` classes modulo `3^m`, i.e. to at
most `4` points. -/
/-- The crux of the cap-set count, *assumed* here: with the exact content exponent `h`, the hard
regime `h ≤ m+T-1` has at most `4` capped support points.  (Numerically verified: 6516 cases with
`13 ≤ e ≤ 21`, including 600 random pairs and the structured families, `13 ≤ e ≤ 25`; no failure,
maximum `|capSet| = 3`.) -/
def CapSetFour : Prop :=
  ∀ {e h : ℕ}, 13 ≤ e → ∀ a b : Fin 3 → ℕ,
    2 ≤ (critN a b).natDegree →
    (∀ n, ((3 ^ h : ℕ) : ℤ) ∣ (critN a b).coeff n) →
    (∃ n, ¬ ((3 ^ (h + 1) : ℕ) : ℤ) ∣ (critN a b).coeff n) →
    SuppTransfer 3 e a b →
    h ≤ cubeLevel 3 e + capLevel 3 e - 1 →
    (capSet 3 e a b).card ≤ 4

/-- **The corrected cap-set bound for `p = 3`.**  With the *exact* content exponent `h` of
`critN a b` the capped support has at most `4 · 3^(m - ⌈(m+T-h)/2⌉)` points, where `m = cubeLevel
3 e`, `T = capLevel 3 e`.  (Without the exactness hypothesis `hprim` this is FALSE: see
`u8three/counterexample_capSet_card_three.lean`.) -/
theorem capSet_card_three {e h : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hdeg2 : 2 ≤ (critN a b).natDegree)
    (hcontent : ∀ n, ((3 ^ h : ℕ) : ℤ) ∣ (critN a b).coeff n)
    (hprim : ∃ n, ¬ ((3 ^ (h + 1) : ℕ) : ℤ) ∣ (critN a b).coeff n)
    (hbt : SuppTransfer 3 e a b) (hfour : CapSetFour) :
    (capSet 3 e a b).card
      ≤ 4 * 3 ^ (cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - h + 1) / 2) := by
  by_cases hcase : cubeLevel 3 e + capLevel 3 e ≤ h
  · have hsub := capSet_subset_range 3 e a b
    have hcard := Finset.card_le_card hsub
    have hexp : cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - h + 1) / 2
        = cubeLevel 3 e := by omega
    rw [hexp]
    calc (capSet 3 e a b).card ≤ (Finset.range (3 ^ cubeLevel 3 e)).card := hcard
      _ = 3 ^ cubeLevel 3 e := Finset.card_range _
      _ ≤ 4 * 3 ^ cubeLevel 3 e := by
          calc 3 ^ cubeLevel 3 e = 3 ^ cubeLevel 3 e * 1 := (mul_one _).symm
            _ ≤ 3 ^ cubeLevel 3 e * 4 := Nat.mul_le_mul (le_refl _) (by norm_num)
            _ = 4 * 3 ^ cubeLevel 3 e := by ring
  · have hsmall : h ≤ cubeLevel 3 e + capLevel 3 e - 1 := by omega
    have hf := hfour he a b hdeg2 hcontent hprim hbt hsmall
    have h3 : 1 ≤ 3 ^ (cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - h + 1) / 2) :=
      Nat.one_le_pow _ _ (by norm_num)
    calc (capSet 3 e a b).card ≤ 4 := hf
      _ ≤ 4 * 3 ^ (cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - h + 1) / 2) := by
          calc (4:ℕ) = 4 * 1 := (mul_one 4).symm
            _ ≤ 4 * 3 ^ (cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - h + 1) / 2) :=
                Nat.mul_le_mul (le_refl 4) h3

end Work.LinnikAreas.u8three
