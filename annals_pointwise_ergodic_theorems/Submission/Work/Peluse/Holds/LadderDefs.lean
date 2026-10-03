import Mathlib
import Submission.Work.Peluse.Concat.Defs
import Submission.Work.Peluse.BoxNorm.boxNormPow_perm

/-!
# The "ladder" state of Peluse's §5 (the concatenation chapter)

Peluse's proof of the concatenation theorem (Theorem 3.5 of *Bounds for sets with no polynomial
progressions*, Forum Math. Pi **8** (2020), arXiv:1909.00309) runs in two halves:

* the first half (expansion of the box norm plus her Lemma 4.10 — the tree's
  `Work.Peluse.PetLinear.linear_boxnorm_control_paper`, proved) produces the average over
  `h, h' ∈ [M₁]^s` of the level-`(2^s-1)` box-norm power with the direction sets
  `c·((h-h')·ω)[γ'M₂]` — this is (`Concat/Defs.lean`) `Work.Peluse.Concat.boxAvg s M₁ c ωOf D N f`
  at the **short** direction length `D = ⌊γ'M₂⌋`;
* the second half is `s` applications of her Lemma 5.6: each application lowers the level from
  `2^j-1` to `2^{j-1}-1`, keeps the short direction length, and *adds* a batch of new shifts
  `c(ℓ,ℓ')` of length `⌊γ'M₁M₂⌋`.  After `s` applications the state is the level-`n` box-norm power
  with the single long window `c[⌊γ'M₁M₂⌋]` for every `n` accumulated slot — i.e. the power of the
  uniformity norm `uNormPow n (arithIcc c ⌊γ'M₁M₂⌋) (symIcc N) f`.

This module fixes the intermediate states of that ladder so that the one-step lemma (Peluse's
Lemma 5.6, in the form needed here) can be stated and iterated.

## The state

`boxLadder j n M₁ c ωOf L D' N f` is the average over `h, h' ∈ [M₁]^j` of the level-`(2^j-1+n)`
box-norm power whose first `2^j-1` slots are the short slots `c·((h-h')·ω)[L]` (`ω` running over the
nonzero sign patterns, enumerated by `ωOf`) and whose remaining `n` slots are all the long window
`c[D']`.

The two ends of the ladder are `boxLadder s 0 … = boxAvg s …` (the hypothesis of
`ConcatBridgeShort`) and `boxLadder 0 n … = uNormPow n (arithIcc c D') …` (its conclusion, up to the
`1/2^n` root and the identification `D' = ⌊γ'M₁M₂⌋`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Holds

noncomputable section

/-- The nonzero sign patterns of `Fin j → Bool`, as a `Finset`. -/
def patterns (j : ℕ) : Finset (Fin j → Bool) := Finset.univ.filter (fun ω => ω ≠ 0)

/-- There are exactly `2^j - 1` nonzero sign patterns. -/
lemma patterns_card (j : ℕ) : (patterns j).card = 2 ^ j - 1 := by
  classical
  have hfil : patterns j = Finset.univ.erase (0 : Fin j → Bool) := by
    ext ω
    simp [patterns, Finset.mem_filter, Finset.mem_erase, and_comm]
  rw [hfil, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- A canonical enumeration of the nonzero sign patterns. -/
noncomputable def omegaOf (j : ℕ) : Fin (2 ^ j - 1) → (Fin j → Bool) :=
  fun i => ((Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe]; exact (patterns_card j).symm) :
      Fin (2 ^ j - 1) ≃ {ω : Fin j → Bool // ω ∈ patterns j}) i).1

lemma omegaOf_mem (j : ℕ) (i : Fin (2 ^ j - 1)) : omegaOf j i ∈ patterns j :=
  ((Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe]; exact (patterns_card j).symm) :
      Fin (2 ^ j - 1) ≃ {ω : Fin j → Bool // ω ∈ patterns j}) i).2

lemma omegaOf_injective (j : ℕ) : Function.Injective (omegaOf j) := by
  intro i i' h
  exact (Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe]; exact (patterns_card j).symm) :
      Fin (2 ^ j - 1) ≃ {ω : Fin j → Bool // ω ∈ patterns j}).injective (Subtype.ext h)

lemma omegaOf_ne_zero (j : ℕ) (i : Fin (2 ^ j - 1)) : omegaOf j i ≠ 0 := by
  have := omegaOf_mem j i
  simpa [patterns] using this

/-- The slot family of the ladder state: the short slots `c·((h-h')·ω)[L]` (indexed by the nonzero
sign patterns) followed by `n` copies of the long window `c[D']`. -/
def ladderSlots (j n : ℕ) (M₁ : ℕ) (c : ℤ) (ωOf : Fin (2 ^ j - 1) → (Fin j → Bool))
    (L D' : ℕ) (h h' : Fin j → Fin M₁) : Fin (2 ^ j - 1 + n) → Finset ℤ :=
  fun i => if hi : (i : ℕ) < 2 ^ j - 1 then
      arithIcc (c * Concat.dotZ (ωOf ⟨(i : ℕ), hi⟩) (Concat.tupSub h h')) L
    else arithIcc c D'

/-- The ladder state: the average over `h, h' ∈ [M₁]^j` of the level-`(2^j-1+n)` box-norm power with
the short slots `c·((h-h')·ω)[L]` and `n` long slots `c[D']`. -/
def boxLadder (j n : ℕ) (M₁ : ℕ) (c : ℤ) (ωOf : Fin (2 ^ j - 1) → (Fin j → Bool))
    (L D' N : ℕ) (f : ℤ → ℂ) : ℝ :=
  ((M₁ : ℝ))⁻¹ ^ (2 * j) *
    ∑ h : Fin j → Fin M₁, ∑ h' : Fin j → Fin M₁,
      boxNormPow (2 ^ j - 1 + n) (ladderSlots j n M₁ c ωOf L D' h h') (symIcc N) f

/-- Reindexing a box-norm power along an equality of the level. -/
lemma boxNormPow_cast {t t' : ℕ} (h : t = t') (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) :
    boxNormPow t Q S f = boxNormPow t' (fun i => Q (Fin.cast h.symm i)) S f := by
  subst h
  rfl

/-- The bottom of the ladder is the power of the uniformity norm at the long window. -/
lemma boxLadder_bot {n M₁ : ℕ} {c : ℤ} {L D' N : ℕ} {f : ℤ → ℂ}
    (ωOf : Fin (2 ^ 0 - 1) → (Fin 0 → Bool)) :
    boxLadder 0 n M₁ c ωOf L D' N f = uNormPow n (arithIcc c D') (symIcc N) f := by
  have hlev : 2 ^ 0 - 1 + n = n := by norm_num
  have hslots : ∀ h h' : Fin 0 → Fin M₁,
      ladderSlots 0 n M₁ c ωOf L D' h h'
        = fun _ : Fin (2 ^ 0 - 1 + n) => arithIcc c D' := by
    intro h h'
    funext i
    rw [ladderSlots, dif_neg (by simp)]
  unfold boxLadder uNormPow
  rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => by
    rw [hslots h h', boxNormPow_cast hlev]))]
  simp

/-- The top of the ladder (no long slots) is `boxAvg`. -/
lemma boxLadder_top {j M₁ : ℕ} {c : ℤ} {L N : ℕ} {f : ℤ → ℂ}
    (ωOf : Fin (2 ^ j - 1) → (Fin j → Bool)) :
    boxLadder j 0 M₁ c ωOf L 0 N f = Concat.boxAvg j M₁ c ωOf L N f := by
  have hlev : 2 ^ j - 1 + 0 = 2 ^ j - 1 := by omega
  have hslots : ∀ h h' : Fin j → Fin M₁,
      ladderSlots j 0 M₁ c ωOf L 0 h h'
        = fun i : Fin (2 ^ j - 1 + 0) => arithIcc (c * Concat.dotZ (ωOf (Fin.cast hlev.symm i))
            (Concat.tupSub h h')) L := by
    intro h h'
    funext i
    rw [ladderSlots, dif_pos (by simpa using i.isLt)]
    congr 3
  unfold boxLadder Concat.boxAvg
  rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => by
    rw [hslots h h', boxNormPow_cast hlev]))]
  simp

end

end Work.Peluse.Holds
