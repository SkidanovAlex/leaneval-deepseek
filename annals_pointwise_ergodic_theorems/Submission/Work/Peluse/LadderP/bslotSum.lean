import Mathlib
import Submission.Work.Peluse.LadderP.stepPState

/-!
# The `B`-block sum: the averaged parameter `a` read off the completed head tuple

The one-step ladder lemma `ladderStepP_of_lemma51P` compares the peeled `(j+1)`-state — an average
over `h, h' : Fin (j+1) → Fin M₁` of the level-`2^j` box-norm-power of the iterated difference at
the `B`-slots

`BBlk j M₁ c L (enumAll j) h h' i = c[((h - h') · padR (ω i))]`,  `i : Fin (2^j)`,

— with Peluse's Lemma 5.1 input, which is the *averaged* box-norm at the direction family
`c[(a + b_{ω})[L]]`, `a ∈ [1, M₁]`.

This file records the elementary reindexing that identifies the two: for the completed tuple
`Fin.snoc (headPart h) hs` (whose last entry plays the role of the averaged parameter `a = h_s + 1`)
the `B`-slot directions are exactly `c[(a + stepShift h h' ω)[L]]`, and the sum over `hs : Fin M₁`
is the sum over `a ∈ [1, M₁]`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- **The `padR`-slot of the completed head tuple.**  For the tuple `Fin.snoc (headPart h) hs`,
whose first `j` coordinates are those of `h` and whose last coordinate is `hs`, the `padR`-pattern
dot product against the difference tuple is the averaged parameter `a = ↑hs + 1` plus the step shift
`stepShift h h' ω`. -/
lemma dotZ_padR_snoc {j M₁ : ℕ} (h h' : Fin (j+1) → Fin M₁) (hs : Fin M₁) (ω : Fin j → Bool) :
    Concat.dotZ (padR j ω) (Concat.tupSub (Fin.snoc (headPart h) hs) h')
      = (((hs : ℕ) : ℤ) + 1) + stepShift h h' ω := by
  rw [dotZ_padR, stepShift]
  have hlast : (Fin.snoc (headPart h) hs : Fin (j+1) → Fin M₁) (Fin.last j) = hs := by
    simp
  have hhead : headPart (Fin.snoc (headPart h) hs : Fin (j+1) → Fin M₁) = headPart h := by
    funext i
    simp only [headPart, Fin.snoc_castSucc]
  simp only [Concat.tupSub]
  rw [hlast, hhead]
  ring

/-- **The `B`-block of the completed head tuple.**  The `B`-slot family of the completed tuple
`Fin.snoc (headPart h) hs` is the direction family `c[(↑hs + 1 + stepShift h h' (ω i))[L]]` of the
averaged parameter `a = ↑hs + 1`. -/
lemma BBlk_snoc_eq (j M₁ : ℕ) (c : ℤ) (L : ℕ) (h h' : Fin (j+1) → Fin M₁) (hs : Fin M₁) :
    BBlk j M₁ c L (enumAll j) (Fin.snoc (headPart h) hs) h'
      = fun i : Fin (2^j) =>
          arithIcc (c * ((((hs : ℕ) + 1 : ℕ) : ℤ) + stepShiftE (enumAll j) h h' i)) L := by
  funext i
  simp only [BBlk, stepShiftE]
  rw [dotZ_padR_snoc]
  rw [show (((hs : ℕ) + 1 : ℕ) : ℤ) = ((hs : ℕ) : ℤ) + 1 from by
    simp only [Nat.cast_add, Nat.cast_one]]

/-- **The `B`-block sum is the averaged box-norm of Lemma 5.1.**  Summing the level-`2^j`
box-norm over the completed head tuple `Fin.snoc (headPart h) hs`, `hs : Fin M₁`, is the same as
summing Peluse's averaged box-norm `boxAvgA (2^j) c M₁ L (stepShiftE (enumAll j) h h') N f` over
the averaged parameter `a ∈ [1, M₁]`. -/
theorem bslotSum (j M₁ : ℕ) (hM₁ : 1 ≤ M₁) (c : ℤ) (L N : ℕ) (f : ℤ → ℂ)
    (h h' : Fin (j+1) → Fin M₁) :
    ((M₁ : ℝ))⁻¹ * (∑ hs : Fin M₁,
        Work.Peluse.boxNorm (2^j)
          (Work.Peluse.LadderP.BBlk j M₁ c L (Work.Peluse.LadderP.enumAll j)
            (Fin.snoc (Work.Peluse.LadderP.headPart h) hs) h') (Work.Peluse.symIcc N) f)
      = Work.Peluse.LadderQ.boxAvgA (2^j) c M₁ L
          (Work.Peluse.LadderP.stepShiftE (Work.Peluse.LadderP.enumAll j) h h') N f := by
  have _ : 1 ≤ M₁ := hM₁
  have hsum : (∑ hs : Fin M₁,
        boxNorm (2^j) (BBlk j M₁ c L (enumAll j) (Fin.snoc (headPart h) hs) h')
          (symIcc N) f)
      = ∑ a ∈ Finset.Icc 1 M₁,
        boxNorm (2^j)
          (fun i : Fin (2^j) => arithIcc (c * (((a : ℤ) + stepShiftE (enumAll j) h h' i))) L)
          (symIcc N) f := by
    refine Finset.sum_bij (fun hs _ => (hs : ℕ) + 1) ?_ ?_ ?_ ?_
    · intro hs _
      exact Finset.mem_Icc.mpr ⟨by omega, by have := hs.isLt; omega⟩
    · intro a₁ _ a₂ _ heq
      exact Fin.ext (by omega)
    · intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
      refine ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      show b - 1 + 1 = b
      omega
    · intro hs _
      exact congrArg (fun Q => boxNorm (2^j) Q (symIcc N) f) (BBlk_snoc_eq j M₁ c L h h' hs)
  rw [Work.Peluse.LadderQ.boxAvgA, hsum]

end

end Work.Peluse.LadderP
