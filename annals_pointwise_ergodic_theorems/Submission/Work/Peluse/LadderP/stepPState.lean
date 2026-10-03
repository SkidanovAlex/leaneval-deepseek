import Mathlib
import Submission.Work.Peluse.LadderP.stepPPeel
import Submission.Work.Peluse.LadderP.enumIndep

/-!
# The one-step lemma of the power-loss ladder: the states and the exceptional set

This file sets up the two states compared by the ladder step

* `augNormState`/`augPowState` — the state `boxLadderNorm (j+1) n` rewritten in the `augEnum` shape
  (the `A`-block, the `B`-block and the long block) and its box-norm-**power** version;
* `patNormState`/`patPowState` — the state `boxLadderNorm j (n+s')` rewritten in the concatenated
  shape and its power version;

together with the shifts `stepShift` of the averaged parameter `a` and the exceptional set
`stepBad` (the set of `a ∈ [1,M₁]` at which the gcd-or-size condition of the Lemma 5.1 input fails).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-! ## The states -/

/-- The (j+1)-state with the `augEnum` slot family, as an average of box **norms**. -/
def augNormState (j n M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) : ℝ :=
  ((M₁ : ℝ))⁻¹ ^ (2 * (j+1)) *
    ∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
      boxNorm (2^(j+1) - 1 + n) (augSlots j n M₁ c L D h h') (symIcc N) f

/-- The (j+1)-state with the `augEnum` slot family, as an average of box-norm **powers**. -/
def augPowState (j n M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) : ℝ :=
  ((M₁ : ℝ))⁻¹ ^ (2 * (j+1)) *
    ∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
      boxNormPow (2^(j+1) - 1 + n) (augSlots j n M₁ c L D h h') (symIcc N) f

/-- The j-state with the concatenated slot family, as an average of box **norms**. -/
def patNormState (j n' M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) : ℝ :=
  ((M₁ : ℝ))⁻¹ ^ (2 * j) *
    ∑ h : Fin j → Fin M₁, ∑ h' : Fin j → Fin M₁,
      boxNorm (2^j - 1 + n') (patSlots j n' M₁ c L D h h') (symIcc N) f

/-- The j-state with the concatenated slot family, as an average of box-norm **powers**. -/
def patPowState (j n' M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) : ℝ :=
  ((M₁ : ℝ))⁻¹ ^ (2 * j) *
    ∑ h : Fin j → Fin M₁, ∑ h' : Fin j → Fin M₁,
      boxNormPow (2^j - 1 + n') (patSlots j n' M₁ c L D h h') (symIcc N) f

/-- Rewriting the j-state along the concatenation of its slot family. -/
theorem boxLadderNorm_eq_patNormState (j n' M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) :
    boxLadderNorm j n' M₁ c (Holds.omegaOf j) L D N f
      = patNormState j n' M₁ c L D N f := by
  simp only [boxLadderNorm, patNormState]
  refine congrArg (fun z => ((M₁ : ℝ))⁻¹ ^ (2 * j) * z) ?_
  refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
  rw [ladderSlots_j_eq, patSlots]

/-- Rewriting the (j+1)-state in the `augEnum` shape: the enumeration `Holds.omegaOf (j+1)` is
replaced by `augEnum j` (the box norm only sees the slot family up to a permutation), and the slot
family is the concatenation of the `A`-block, the `B`-block and the long block. -/
theorem boxLadderNorm_succ_eq_augNormState (j n M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) :
    boxLadderNorm (j+1) n M₁ c (Holds.omegaOf (j+1)) L D N f
      = augNormState j n M₁ c L D N f := by
  rw [enumIndep (j+1) n M₁ c L D N f (Holds.omegaOf (j+1)) (augEnum j)
    (Holds.omegaOf_injective (j+1)) (augEnum_injective j)
    (fun i => Holds.omegaOf_ne_zero (j+1) i) (augEnum_ne_zero j)]
  simp only [boxLadderNorm, augNormState]
  refine congrArg (fun z => ((M₁ : ℝ))⁻¹ ^ (2 * (j+1)) * z) ?_
  refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
  rw [augSlots_eq]

/-! ## The shifts and the exceptional set -/

/-- The shift attached to the pattern `ω`: `b_ω = -h'_s - 1 + (h-h')_{<s}·ω`, in the shape in which
it is used (the head of `h` and the last coordinate of `h'`). -/
def stepShift3 {j M₁ : ℕ} (h₁ : Fin j → Fin M₁) (h₁' : Fin j → Fin M₁) (hs' : Fin M₁)
    (ω : Fin j → Bool) : ℤ :=
  - ((hs' : ℤ)) - 1 + Concat.dotZ ω (Concat.tupSub h₁ h₁')

/-- The shifts attached to the patterns in the order of the enumeration `E`. -/
def stepShift3E {j M₁ : ℕ} (E : Fin (2^j) ≃ (Fin j → Bool)) (h₁ : Fin j → Fin M₁)
    (h₁' : Fin j → Fin M₁) (hs' : Fin M₁) (i : Fin (2^j)) : ℤ :=
  stepShift3 h₁ h₁' hs' (E i)

/-- The shift attached to the pattern `ω`: `b_ω = -h'_s - 1 + (h-h')_{<s}·ω`, chosen so that
`a + b_ω = (h-h')·(ω,1)` for `a = h_s + 1` (i.e. for `a` the parameter averaged by Lemma 5.1). -/
def stepShift {j M₁ : ℕ} (h h' : Fin (j+1) → Fin M₁) (ω : Fin j → Bool) : ℤ :=
  - ((h' (Fin.last j) : ℤ)) - 1 + Concat.dotZ ω (Concat.tupSub (headPart h) (headPart h'))

/-- The shifts attached to the patterns in the order of the enumeration `E`. -/
def stepShiftE {j M₁ : ℕ} (E : Fin (2^j) ≃ (Fin j → Bool)) (h h' : Fin (j+1) → Fin M₁)
    (i : Fin (2^j)) : ℤ :=
  stepShift h h' (E i)

lemma stepShift_eq_stepShift3 {j M₁ : ℕ} (h₁ : Fin j → Fin M₁) (hs : Fin M₁) (h₁' : Fin j → Fin M₁)
    (hs' : Fin M₁) (ω : Fin j → Bool) :
    stepShift (Fin.snoc h₁ hs) (Fin.snoc h₁' hs') ω = stepShift3 h₁ h₁' hs' ω := by
  have hA : headPart (Fin.snoc h₁ hs) = h₁ := by
    funext i
    exact Fin.snoc_castSucc (n := j) (α := fun _ : Fin (j+1) => Fin M₁) hs h₁ i
  have hB : headPart (Fin.snoc h₁' hs') = h₁' := by
    funext i
    exact Fin.snoc_castSucc (n := j) (α := fun _ : Fin (j+1) => Fin M₁) hs' h₁' i
  rw [stepShift, stepShift3, hA, hB, Fin.snoc_last (n := j) (α := fun _ : Fin (j+1) => Fin M₁) hs' h₁']

/-- The iterated difference peeled off in the ladder step, as a function of the shift tuple. -/
def Gof (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (h₁ h₁' : Fin j → Fin M₁)
    (km : ((i : Fin (2^j - 1)) → ↥(ABlk0 j M₁ c L h₁ h₁' i) × ↥(ABlk0 j M₁ c L h₁ h₁' i)) ×
          ((i : Fin n) → ↥(arithIcc c D) × ↥(arithIcc c D))) (f : ℤ → ℂ) : ℤ → ℂ :=
  Ulower.iterDelta n (fun i : Fin n => (((km.2 i).1 : ℤ), ((km.2 i).2 : ℤ)))
    (Ulower.iterDelta (2^j - 1)
      (fun i : Fin (2^j - 1) => (((km.1 i).1 : ℤ), ((km.1 i).2 : ℤ))) f)

/-- The product weight of the shift tuple `km` (a probability weight). -/
def Gwt (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (h₁ h₁' : Fin j → Fin M₁) : ℝ :=
  (∏ i : Fin (2^j - 1), (((ABlk0 j M₁ c L h₁ h₁' i).card : ℝ))⁻¹ ^ 2) *
    (∏ _i : Fin n, (((arithIcc c D).card : ℝ))⁻¹ ^ 2)

/-- The box-norm power of the peeled difference at the remaining `s'` long slots. -/
def Gpow (j n s' M₁ : ℕ) (c : ℤ) (L D N : ℕ) (h₁ h₁' : Fin j → Fin M₁)
    (km : ((i : Fin (2^j - 1)) → ↥(ABlk0 j M₁ c L h₁ h₁' i) × ↥(ABlk0 j M₁ c L h₁ h₁' i)) ×
          ((i : Fin n) → ↥(arithIcc c D) × ↥(arithIcc c D))) (f : ℤ → ℂ) : ℝ :=
  boxNormPow s' (longBlk s' c D) (symIcc N) (Gof j n M₁ c L D h₁ h₁' km f)

/-- The box-norm power of the peeled difference at the `B`-slots. -/
def GpowB (j n M₁ : ℕ) (c : ℤ) (L D N : ℕ) (h₁ h₁' : Fin j → Fin M₁) (hs h'_s : Fin M₁)
    (km : ((i : Fin (2^j - 1)) → ↥(ABlk0 j M₁ c L h₁ h₁' i) × ↥(ABlk0 j M₁ c L h₁ h₁' i)) ×
          ((i : Fin n) → ↥(arithIcc c D) × ↥(arithIcc c D))) (f : ℤ → ℂ) : ℝ :=
  boxNormPow (2^j) (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)) (symIcc N)
    (Gof j n M₁ c L D h₁ h₁' km f)

/-- The exceptional set of the ladder step: the `a ∈ [1,M₁]` at which the gcd-or-size condition of
the Lemma 5.1 input fails for the shifts `b_ω`. -/
def stepBad (j M₁ : ℕ) (η : ℝ) (E : Fin (2^j) ≃ (Fin j → Bool))
    (h h' : Fin (j+1) → Fin M₁) : Finset ℕ :=
  (Finset.Icc 1 M₁).filter fun a => ¬ (
    (∀ i k : Fin (2^j), i ≠ k →
        ((Int.gcd ((a : ℤ) + stepShiftE E h h' i) ((a : ℤ) + stepShiftE E h h' k) : ℕ) : ℝ)
          ≤ 1 / η)
      ∧ ∀ i : Fin (2^j), η * (M₁ : ℝ) ≤ ((|((a : ℤ) + stepShiftE E h h' i)| : ℤ) : ℝ))

/-- The direction `a + b_ω` is the dot product of the `padR`-pattern with the difference tuple. -/
lemma stepShift_add {j M₁ : ℕ} (h h' : Fin (j+1) → Fin M₁) (ω : Fin j → Bool) :
    ((h (Fin.last j) : ℤ) + 1) + stepShift h h' ω
      = Concat.dotZ (padR j ω) (Concat.tupSub h h') := by
  rw [stepShift, dotZ_padR]
  simp only [Concat.tupSub]
  ring

lemma stepShift_irrel_last {j M₁ : ℕ} (h₁ : Fin j → Fin M₁) (hs hs' : Fin M₁)
    (h' : Fin (j+1) → Fin M₁) (ω : Fin j → Bool) :
    stepShift (Fin.snoc h₁ hs) h' ω = stepShift (Fin.snoc h₁ hs') h' ω := by
  have hA : headPart (Fin.snoc h₁ hs) = h₁ := by
    funext i
    exact Fin.snoc_castSucc (n := j) (α := fun _ : Fin (j+1) => Fin M₁) hs h₁ i
  have hB : headPart (Fin.snoc h₁ hs') = h₁ := by
    funext i
    exact Fin.snoc_castSucc (n := j) (α := fun _ : Fin (j+1) => Fin M₁) hs' h₁ i
  rw [stepShift, stepShift, hA, hB]

end

end Work.Peluse.LadderP

