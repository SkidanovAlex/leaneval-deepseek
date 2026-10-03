import Mathlib
import Submission.Work.Peluse.Holds.LadderP
import Submission.Work.Peluse.LadderA.supportIn_iterDelta
import Submission.Work.Peluse.Prop36SW.meanPeelLeBoxNorm

/-!
# The one-step lemma of the power-loss ladder: structural core

Definitions and structural identities for the proof of `ladderStepP_of_lemma51P`
(the ladder's next-step lemma, Peluse's Lemma 5.6 with the carried long slots).

The ladder state `boxLadderNorm` peels along the sign patterns of `Fin (j+1)`: the level-`j` state
keeps the `2^j` slots whose pattern takes the value `true` in the last coordinate (these are the
directions of the averaged parameter `a`), while the `2^j - 1` slots with last coordinate `false`
and the long slots `c[D]` are peeled off.

This file fixes the notation: the pattern paddings `padL`/`padR`, the canonical enumeration
`augEnum` of the nonzero patterns of `Fin (j+1)` (the `padL`-patterns first, then the `padR`-ones),
the three slot blocks, the shifts `stepShift` of the `a`-average and the exceptional set `stepBad`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- The first `j` coordinates of a tuple, as a tuple of `Fin j`. -/
def headPart {j M₁ : ℕ} (h : Fin (j+1) → Fin M₁) : Fin j → Fin M₁ :=
  fun i => h (Fin.castSucc i)

/-- Pad a sign pattern of `Fin j` by `false` in the last coordinate. -/
def padL (j : ℕ) (ω : Fin j → Bool) : Fin (j+1) → Bool :=
  fun i => if h : (i : ℕ) < j then ω ⟨(i : ℕ), h⟩ else false

/-- Pad a sign pattern of `Fin j` by `true` in the last coordinate. -/
def padR (j : ℕ) (ω : Fin j → Bool) : Fin (j+1) → Bool :=
  fun i => if h : (i : ℕ) < j then ω ⟨(i : ℕ), h⟩ else true

@[simp] lemma padL_castSucc (j : ℕ) (ω : Fin j → Bool) (i : Fin j) :
    padL j ω (Fin.castSucc i) = ω i := by
  simp [padL]

@[simp] lemma padR_castSucc (j : ℕ) (ω : Fin j → Bool) (i : Fin j) :
    padR j ω (Fin.castSucc i) = ω i := by
  simp [padR]

@[simp] lemma padL_last (j : ℕ) (ω : Fin j → Bool) : padL j ω (Fin.last j) = false := by
  simp [padL]

@[simp] lemma padR_last (j : ℕ) (ω : Fin j → Bool) : padR j ω (Fin.last j) = true := by
  simp [padR]

/-- The dot product against a `padL`-pattern sees only the first `j` coordinates. -/
lemma dotZ_padL {j M₁ : ℕ} (ω : Fin j → Bool) (h h' : Fin (j+1) → Fin M₁) :
    Concat.dotZ (padL j ω) (Concat.tupSub h h')
      = Concat.dotZ ω (Concat.tupSub (headPart h) (headPart h')) := by
  simp only [Concat.dotZ]
  rw [Fin.sum_univ_castSucc, padL_last, if_neg (by simp), add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : ω i <;> simp [hi, Concat.tupSub, headPart]

/-- The dot product against a `padR`-pattern is the last coordinate plus the first `j`. -/
lemma dotZ_padR {j M₁ : ℕ} (ω : Fin j → Bool) (h h' : Fin (j+1) → Fin M₁) :
    Concat.dotZ (padR j ω) (Concat.tupSub h h')
      = Concat.tupSub h h' (Fin.last j)
        + Concat.dotZ ω (Concat.tupSub (headPart h) (headPart h')) := by
  simp only [Concat.dotZ]
  rw [Fin.sum_univ_castSucc, padR_last, if_pos rfl]
  have hsum : (∑ i : Fin j,
        (if padR j ω (Fin.castSucc i) then Concat.tupSub h h' (Fin.castSucc i) else (0 : ℤ)))
      = ∑ i : Fin j,
        (if ω i then Concat.tupSub (headPart h) (headPart h') i else (0 : ℤ)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : ω i <;> simp [hi, Concat.tupSub, headPart]
  rw [hsum, add_comm]

lemma card_fun_fin (j : ℕ) : 2^j = Fintype.card (Fin j → Bool) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- The canonical bijection `Fin (2^j) ≃ (Fin j → Bool)`. -/
noncomputable def enumAll (j : ℕ) : Fin (2^j) ≃ (Fin j → Bool) :=
  (finCongr (card_fun_fin j)).trans (Fintype.equivFin (Fin j → Bool)).symm

/-- The tail index of the last `2^j` entries of `augEnum`. -/
lemma tail_lt {j : ℕ} {i : Fin (2^(j+1) - 1)} (h : ¬ (i : ℕ) < 2^j - 1) :
    (i : ℕ) - (2^j - 1) < 2^j := by
  have h1 : (i : ℕ) < 2^(j+1) - 1 := i.isLt
  have h2 : ¬ (i : ℕ) < 2^j - 1 := h
  have h3 : 2^(j+1) = 2 * 2^j := by rw [pow_succ']
  have h4 : 1 ≤ 2^j := Nat.one_le_two_pow
  omega

/-- The enumeration of the nonzero sign patterns of `Fin (j+1)` whose first `2^j - 1` entries are
the `padL`-images of the nonzero patterns of `Fin j` and whose last `2^j` entries are the
`padR`-images of all the patterns of `Fin j`. -/
noncomputable def augEnum (j : ℕ) : Fin (2^(j+1) - 1) → (Fin (j+1) → Bool) :=
  fun i => if h : (i : ℕ) < 2^j - 1
    then padL j (Holds.omegaOf j ⟨(i : ℕ), h⟩)
    else padR j (enumAll j ⟨(i : ℕ) - (2^j - 1), tail_lt h⟩)

lemma augEnum_low {j : ℕ} {i : Fin (2^(j+1) - 1)} (h : (i : ℕ) < 2^j - 1) :
    augEnum j i = padL j (Holds.omegaOf j ⟨(i : ℕ), h⟩) := dif_pos h

lemma augEnum_high {j : ℕ} {i : Fin (2^(j+1) - 1)} (h : ¬ (i : ℕ) < 2^j - 1) :
    augEnum j i = padR j (enumAll j ⟨(i : ℕ) - (2^j - 1), tail_lt h⟩) := dif_neg h

lemma padL_ne_zero {j : ℕ} {ω : Fin j → Bool} (h : ω ≠ 0) : padL j ω ≠ 0 := by
  intro hc
  apply h
  funext i
  have := congrFun hc (Fin.castSucc i)
  simpa using this

lemma padR_ne_zero (j : ℕ) (ω : Fin j → Bool) : padR j ω ≠ 0 := by
  intro hc
  have := congrFun hc (Fin.last j)
  simp at this

lemma augEnum_ne_zero (j : ℕ) (i : Fin (2^(j+1) - 1)) : augEnum j i ≠ 0 := by
  by_cases h : (i : ℕ) < 2^j - 1
  · rw [augEnum_low h]
    exact padL_ne_zero (Holds.omegaOf_ne_zero j ⟨(i : ℕ), h⟩)
  · rw [augEnum_high h]
    exact padR_ne_zero j _

lemma augEnum_injective (j : ℕ) : Function.Injective (augEnum j) := by
  intro i i' hi
  by_cases h : (i : ℕ) < 2^j - 1 <;> by_cases h' : (i' : ℕ) < 2^j - 1
  · rw [augEnum_low h, augEnum_low h'] at hi
    have h1 : Holds.omegaOf j ⟨(i : ℕ), h⟩ = Holds.omegaOf j ⟨(i' : ℕ), h'⟩ := by
      funext k
      have := congrFun hi (Fin.castSucc k)
      simpa using this
    have h2 := Holds.omegaOf_injective j h1
    have h3 : (i : ℕ) = (i' : ℕ) := congrArg (fun x : Fin (2^j - 1) => (x : ℕ)) h2
    exact Fin.ext h3
  · rw [augEnum_low h, augEnum_high h'] at hi
    have := congrFun hi (Fin.last j)
    simp at this
  · rw [augEnum_high h, augEnum_low h'] at hi
    have := congrFun hi (Fin.last j)
    simp at this
  · rw [augEnum_high h, augEnum_high h'] at hi
    have h1 : enumAll j ⟨(i : ℕ) - (2^j - 1), tail_lt h⟩
        = enumAll j ⟨(i' : ℕ) - (2^j - 1), tail_lt h'⟩ := by
      funext k
      have := congrFun hi (Fin.castSucc k)
      simpa using this
    have h2 := (enumAll j).injective h1
    have h3 : (i : ℕ) - (2^j - 1) = (i' : ℕ) - (2^j - 1) :=
      congrArg (fun x : Fin (2^j) => (x : ℕ)) h2
    have h1i : (i : ℕ) < 2^(j+1) - 1 := i.isLt
    have h1i' : (i' : ℕ) < 2^(j+1) - 1 := i'.isLt
    have h3' : 2^(j+1) = 2 * 2^j := by rw [pow_succ']
    have h4 : 1 ≤ 2^j := Nat.one_le_two_pow
    exact Fin.ext (by omega)

end

end Work.Peluse.LadderP
