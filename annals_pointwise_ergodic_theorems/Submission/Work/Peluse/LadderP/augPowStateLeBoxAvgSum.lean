import Mathlib
import Submission.Work.Peluse.LadderP.stateBSumBound
import Submission.Work.Peluse.LadderP.stepPBridge

/-!
# The averaged form of the power-loss ladder step

`stateBSumBound` bounds the peeled `(j+1)`-state by the average, over the pairs `(h₁,h₁')`, the last
coordinates `h'_s` and the shift tuples `km`, of the level-`2^j` box-norm of the iterated difference
at the `B`-slots, still averaged over the *remaining* last coordinate `hs` of `h`:

`augPowState ≤ M₁^{-(2j+2)} * Σ_{h₁,h₁',h'_s} Σ_{km} Gwt * (Σ_{hs} boxNorm …)`.

`bslotSum3` identifies that inner average `M₁⁻¹ * Σ_{hs} boxNorm` with the box average `boxAvgA`
of Peluse's Lemma 5.1 input.  Combining the two gives the averaged form (with the constant
`M₁^{-(2j+1)}`) consumed by the ladder step.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

theorem augPowStateLeBoxAvgSum (j n M₁ : ℕ) (hM₁ : 1 ≤ M₁) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ)
    (hfin : Work.Peluse.FinSuppZ f) (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (hsup : Work.Peluse.SupportIn f N) :
    Work.Peluse.LadderP.augPowState j n M₁ c L D N f
      ≤ ((M₁ : ℝ))⁻¹ ^ (2 * j + 1) *
        ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
          ∑ km : Work.Peluse.LadderP.KmT j n M₁ c L D h₁ h₁',
            Work.Peluse.LadderP.Gwt j n M₁ c L D h₁ h₁' *
              Work.Peluse.LadderQ.boxAvgA (2^j) c M₁ L
                (Work.Peluse.LadderP.stepShift3E (Work.Peluse.LadderP.enumAll j) h₁ h₁' h'_s) N
                (Work.Peluse.LadderP.Gof j n M₁ c L D h₁ h₁' km f) := by
  have hM₁ne : ((M₁ : ℝ)) ≠ 0 := by
    have hpos : (0 : ℝ) < (M₁ : ℝ) := by exact_mod_cast hM₁
    exact ne_of_gt hpos
  -- The inner `hs`-average of the box norms is `M₁` times the box average.
  have hinner : ∀ (h₁ : Fin j → Fin M₁) (h₁' : Fin j → Fin M₁) (h'_s : Fin M₁)
      (km : KmT j n M₁ c L D h₁ h₁'),
      Gwt j n M₁ c L D h₁ h₁' *
        (∑ hs : Fin M₁,
          boxNorm (2^j) (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s))
            (symIcc N) (Gof j n M₁ c L D h₁ h₁' km f))
      = (M₁ : ℝ) * (Gwt j n M₁ c L D h₁ h₁' *
          LadderQ.boxAvgA (2^j) c M₁ L (stepShift3E (enumAll j) h₁ h₁' h'_s) N
            (Gof j n M₁ c L D h₁ h₁' km f)) := by
    intro h₁ h₁' h'_s km
    have hb := bslotSum3 j n M₁ hM₁ c L D N f h₁ h₁' ⟨0, by omega⟩ h'_s km
    have hsumeq : (∑ hs : Fin M₁,
          boxNorm (2^j) (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s))
            (symIcc N) (Gof j n M₁ c L D h₁ h₁' km f))
        = (M₁ : ℝ) * LadderQ.boxAvgA (2^j) c M₁ L (stepShift3E (enumAll j) h₁ h₁' h'_s) N
            (Gof j n M₁ c L D h₁ h₁' km f) := by
      rw [← hb, ← mul_assoc, mul_inv_cancel₀ hM₁ne, one_mul]
    rw [hsumeq]
    ring
  -- The same average with the box norm replaced by the box average.
  have hsumEq : (∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
          ∑ km : KmT j n M₁ c L D h₁ h₁',
            Gwt j n M₁ c L D h₁ h₁' *
              (∑ hs : Fin M₁,
                boxNorm (2^j) (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s))
                  (symIcc N) (Gof j n M₁ c L D h₁ h₁' km f)))
      = (M₁ : ℝ) * (∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
          ∑ km : KmT j n M₁ c L D h₁ h₁',
            Gwt j n M₁ c L D h₁ h₁' *
              LadderQ.boxAvgA (2^j) c M₁ L (stepShift3E (enumAll j) h₁ h₁' h'_s) N
                (Gof j n M₁ c L D h₁ h₁' km f)) := by
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h₁ _ => ?_)
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h₁' _ => ?_)
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h'_s _ => ?_)
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun km _ => ?_)
    exact hinner h₁ h₁' h'_s km
  -- Arithmetic: `M₁^{-(2(j+1))} (M₁ X) = M₁^{-(2j+1)} X`.
  have harith : ∀ X : ℝ, ((M₁ : ℝ))⁻¹ ^ (2 * (j+1)) * ((M₁ : ℝ) * X)
      = ((M₁ : ℝ))⁻¹ ^ (2 * j + 1) * X := by
    intro X
    rw [show 2 * (j+1) = 2 * j + 1 + 1 by ring, pow_succ, mul_assoc]
    congr 1
    rw [← mul_assoc, inv_mul_cancel₀ hM₁ne, one_mul]
  calc augPowState j n M₁ c L D N f
      ≤ ((M₁ : ℝ))⁻¹ ^ (2 * (j+1)) *
          (∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
            ∑ km : KmT j n M₁ c L D h₁ h₁',
              Gwt j n M₁ c L D h₁ h₁' *
                (∑ hs : Fin M₁,
                  boxNorm (2^j)
                    (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)) (symIcc N)
                    (Gof j n M₁ c L D h₁ h₁' km f))) :=
        stateBSumBound j n M₁ hM₁ c L D N f hfin hbd hsup
    _ = ((M₁ : ℝ))⁻¹ ^ (2 * j + 1) *
          (∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
            ∑ km : KmT j n M₁ c L D h₁ h₁',
              Gwt j n M₁ c L D h₁ h₁' *
                LadderQ.boxAvgA (2^j) c M₁ L (stepShift3E (enumAll j) h₁ h₁' h'_s) N
                  (Gof j n M₁ c L D h₁ h₁' km f)) := by
        rw [hsumEq]
        exact harith _

end

end Work.Peluse.LadderP
