import Mathlib
import Submission.Work.Peluse.LadderP.stepPAve
import Submission.Work.Peluse.LadderP.bslotSum
-- import Submission.Work.Peluse.LadderP.stepShift3Bound  -- P4 child, in flight

/-!
# The one-step lemma of the power-loss ladder: the bridges to the Lemma 5.1 input

Three small bridges used when the Lemma 5.1 input (`lemma51P`, taken as the hypothesis of the node)
is applied to the peeled difference:

* `stepShiftE_snoc`: the shifts `stepShiftE (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)` are
  the head-indexed shifts `stepShift3E (enumAll j) h₁ h₁' h'_s`;
* `bslotSum3`: the box average of the `B`-slots at those shifts, in the head-indexed form;
* `LadderQ.boxAvgA_shift` / `uNormPow_shift` / `boxNorm_shift`: translation invariance of the box average and
  of the uniformity norm, which turns the peeled difference (supported in a *translate* of
  `symIcc N`) into a function satisfying the `SupportIn · N` hypothesis of the Lemma 5.1 input.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

@[simp] lemma stepShiftE_snoc (j M₁ : ℕ) (h₁ h₁' : Fin j → Fin M₁) (hs h'_s : Fin M₁) (i : Fin (2^j)) :
    stepShiftE (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s) i
      = stepShift3E (enumAll j) h₁ h₁' h'_s i := by
  simp only [stepShiftE, stepShift3E]
  exact stepShift_eq_stepShift3 h₁ hs h₁' h'_s (enumAll j i)

/-- The box average of the `B`-slots, in the head-indexed form of the ladder step. -/
theorem bslotSum3 (j n M₁ : ℕ) (hM₁ : 1 ≤ M₁) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ)
    (h₁ h₁' : Fin j → Fin M₁) (hs h'_s : Fin M₁)
    (km : KmT j n M₁ c L D h₁ h₁') :
    ((M₁ : ℝ))⁻¹ * (∑ hs' : Fin M₁,
        boxNorm (2^j) (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs') (Fin.snoc h₁' h'_s))
          (symIcc N) (Gof j n M₁ c L D h₁ h₁' km f))
      = LadderQ.boxAvgA (2^j) c M₁ L (stepShift3E (enumAll j) h₁ h₁' h'_s) N
          (Gof j n M₁ c L D h₁ h₁' km f) := by
  have h := bslotSum j M₁ hM₁ c L N (Gof j n M₁ c L D h₁ h₁' km f) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)
  have hhead : headPart (Fin.snoc h₁ hs) = h₁ := by
    funext i
    exact Fin.snoc_castSucc (n := j) (α := fun _ : Fin (j+1) => Fin M₁) hs h₁ i
  rw [hhead] at h
  rw [h]
  congr 1
  funext i
  exact stepShiftE_snoc j M₁ h₁ h₁' hs h'_s i

/-- Translation invariance of the box average. -/
lemma boxAvgA_shift (s : ℕ) (c : ℤ) (M₁ M₂ N : ℕ) (b : Fin s → ℤ) (f : ℤ → ℂ) (p : ℤ)
    (hf : FinSuppZ f) :
    LadderQ.boxAvgA s c M₁ M₂ b N (shift p f) = LadderQ.boxAvgA s c M₁ M₂ b N f := by
  simp only [LadderQ.boxAvgA]
  refine congrArg (fun z => ((M₁ : ℝ))⁻¹ * z) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [boxNorm]
  congr 1
  exact BoxNorm.boxNormPow_shift s _ (symIcc N) f p hf

/-- Translation invariance of the uniformity-norm power. -/
lemma uNormPow_shift (s' : ℕ) (Q : Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) (p : ℤ)
    (hf : FinSuppZ f) :
    uNormPow s' Q S (shift p f) = uNormPow s' Q S f :=
  BoxNorm.boxNormPow_shift s' (fun _ : Fin s' => Q) S f p hf

/-- Translation invariance of the uniformity norm. -/
lemma uNorm_shift (s' : ℕ) (Q : Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) (p : ℤ)
    (hf : FinSuppZ f) :
    uNorm s' Q S (shift p f) = uNorm s' Q S f := by
  simp only [uNorm, uNormPow_shift s' Q S f p hf]

end

end Work.Peluse.LadderP
