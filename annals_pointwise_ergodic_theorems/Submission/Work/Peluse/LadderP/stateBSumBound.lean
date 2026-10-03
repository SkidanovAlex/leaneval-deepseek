import Mathlib
import Submission.Work.Peluse.LadderP.stepPAve

/-!
# The `B`-slot sum bound of the power-loss ladder

The peeled `(j+1)`-state (`augPowState_peel`) is an average, over the pairs `(h, h')` of
`Fin (j+1) → Fin M₁` and over the shift tuples `km`, of the level-`2^j` box-norm **power** of the
iterated difference `Gof … km f` at the `B`-slots `BBlk … h h'`.

This file proves `stateBSumBound`: that average is at most the same average with the box-norm power
replaced by the box norm, and with the head `h = Fin.snoc h₁ hs` of `h` split off (the box norm is
`≤ 1` for a `1`-bounded function of small support, and `boxNormPow = boxNorm ^ (2^t)`, so
`boxNormPow ≤ boxNorm` — `boxNormPow_le_boxNorm_of_suppSmall`).

The formal content is

* the reindexing `h ↦ (headPart h, h (last))` of the two outer sums (`augPowState_reindex`), which
  needs the dependent rewrite `headPart (Fin.snoc h₁ hs) = h₁`; the sums are first split by
  `Finset.sum_congr` so that the head and the last coordinate are *free* variables and `rw` can
  transport the binder types of the shift tuples `KmT`;
* the reordering `augPowState_reorder` moving the sum over the last coordinate `hs` inside the sums
  over `(h₁', h'_s, km)`;
* the pointwise comparison of the box-norm power with the box norm.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- The head of `Fin.snoc h₁ hs` is `h₁`. -/
lemma headPart_snoc {j M₁ : ℕ} (h₁ : Fin j → Fin M₁) (hs : Fin M₁) :
    headPart (Fin.snoc h₁ hs) = h₁ := by
  funext i
  exact Fin.snoc_castSucc (α := fun _ : Fin (j+1) => Fin M₁) hs h₁ i

/-- A sum over `Fin (j+1) → Fin M₁` splits as a sum over the head and the last coordinate. -/
lemma sum_univ_snoc (j M₁ : ℕ) (F : (Fin (j+1) → Fin M₁) → ℝ) :
    (∑ h : Fin (j+1) → Fin M₁, F h)
      = ∑ h₁ : Fin j → Fin M₁, ∑ hs : Fin M₁, F (Fin.snoc h₁ hs) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (j+1) => Fin M₁)) F]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun x _ => ?_))
  rfl

/-- The iterated difference `Gof` of a function of small support has small support. -/
lemma SuppSmall_Gof {j n M₁ : ℕ} (c : ℤ) (L D : ℕ) (h₁ h₁' : Fin j → Fin M₁)
    (km : KmT j n M₁ c L D h₁ h₁') {N : ℕ} {f : ℤ → ℂ} (h : SuppSmall N f) :
    SuppSmall N (Gof j n M₁ c L D h₁ h₁' km f) := by
  unfold Gof
  exact SuppSmall.iterDelta n _ (SuppSmall.iterDelta (2^j - 1) _ h)

/-- The iterated difference `Gof` of a `1`-bounded function is `1`-bounded. -/
lemma norm_Gof_le_one {j n M₁ : ℕ} (c : ℤ) (L D : ℕ) (h₁ h₁' : Fin j → Fin M₁)
    (km : KmT j n M₁ c L D h₁ h₁') {f : ℤ → ℂ} (h : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    ∀ x : ℤ, ‖Gof j n M₁ c L D h₁ h₁' km f x‖ ≤ 1 := by
  unfold Gof
  exact Ulower.norm_iterDelta_le_one n _ _ (Ulower.norm_iterDelta_le_one (2^j - 1) _ _ h)

/-- **Reindexing** the peeled `(j+1)`-state sum: the two outer sums over
`h, h' : Fin (j+1) → Fin M₁` are written as sums over their head and last coordinate. -/
lemma augPowState_reindex (j n M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) :
    (∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
      ∑ km : KmT j n M₁ c L D (headPart h) (headPart h'),
        Gwt j n M₁ c L D (headPart h) (headPart h') *
          boxNormPow (2^j) (BBlk j M₁ c L (enumAll j) h h') (symIcc N)
            (Gof j n M₁ c L D (headPart h) (headPart h') km f))
    = ∑ h₁ : Fin j → Fin M₁, ∑ hs : Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
        ∑ km : KmT j n M₁ c L D h₁ h₁',
          Gwt j n M₁ c L D h₁ h₁' *
            boxNormPow (2^j)
              (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)) (symIcc N)
              (Gof j n M₁ c L D h₁ h₁' km f) := by
  rw [sum_univ_snoc j M₁ (fun h => ∑ h' : Fin (j+1) → Fin M₁,
      ∑ km : KmT j n M₁ c L D (headPart h) (headPart h'),
        Gwt j n M₁ c L D (headPart h) (headPart h') *
          boxNormPow (2^j) (BBlk j M₁ c L (enumAll j) h h') (symIcc N)
            (Gof j n M₁ c L D (headPart h) (headPart h') km f))]
  refine Finset.sum_congr rfl (fun h₁ _ => Finset.sum_congr rfl (fun hs _ => ?_))
  rw [headPart_snoc]
  rw [sum_univ_snoc j M₁ (fun h' => ∑ km : KmT j n M₁ c L D h₁ (headPart h'),
        Gwt j n M₁ c L D h₁ (headPart h') *
          boxNormPow (2^j) (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) h') (symIcc N)
            (Gof j n M₁ c L D h₁ (headPart h') km f))]
  refine Finset.sum_congr rfl (fun h₁' _ => Finset.sum_congr rfl (fun h'_s _ => ?_))
  rw [headPart_snoc]

/-- **Reordering**: moving the sum over the last coordinate `hs` of `h` inside the sums over the
head `h₁'` and the last coordinate `h'_s` of `h'` and over the shift tuples `km`. -/
lemma augPowState_reorder (j n M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) :
    (∑ h₁ : Fin j → Fin M₁, ∑ hs : Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
        ∑ km : KmT j n M₁ c L D h₁ h₁',
          Gwt j n M₁ c L D h₁ h₁' *
            boxNormPow (2^j)
              (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)) (symIcc N)
              (Gof j n M₁ c L D h₁ h₁' km f))
    = ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
        ∑ km : KmT j n M₁ c L D h₁ h₁',
          Gwt j n M₁ c L D h₁ h₁' *
            (∑ hs : Fin M₁,
              boxNormPow (2^j)
                (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)) (symIcc N)
                (Gof j n M₁ c L D h₁ h₁' km f)) := by
  have step1 : (∑ h₁ : Fin j → Fin M₁, ∑ hs : Fin M₁, ∑ h₁' : Fin j → Fin M₁,
        ∑ h'_s : Fin M₁, ∑ km : KmT j n M₁ c L D h₁ h₁',
          Gwt j n M₁ c L D h₁ h₁' *
            boxNormPow (2^j)
              (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)) (symIcc N)
              (Gof j n M₁ c L D h₁ h₁' km f))
      = ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
        ∑ km : KmT j n M₁ c L D h₁ h₁', ∑ hs : Fin M₁,
          Gwt j n M₁ c L D h₁ h₁' *
            boxNormPow (2^j)
              (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)) (symIcc N)
              (Gof j n M₁ c L D h₁ h₁' km f) := by
    refine Finset.sum_congr rfl (fun h₁ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h₁' _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h'_s _ => ?_)
    rw [Finset.sum_comm]
  rw [step1]
  refine Finset.sum_congr rfl (fun h₁ _ => Finset.sum_congr rfl (fun h₁' _ =>
    Finset.sum_congr rfl (fun h'_s _ => Finset.sum_congr rfl (fun km _ => ?_))))
  exact (Finset.mul_sum Finset.univ (fun hs =>
      boxNormPow (2^j)
        (BBlk j M₁ c L (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)) (symIcc N)
        (Gof j n M₁ c L D h₁ h₁' km f)) (Gwt j n M₁ c L D h₁ h₁')).symm

theorem stateBSumBound (j n M₁ : ℕ) (hM₁ : 1 ≤ M₁) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ)
    (hf : Work.Peluse.FinSuppZ f) (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsup : Work.Peluse.SupportIn f N) :
    Work.Peluse.LadderP.augPowState j n M₁ c L D N f
      ≤ ((M₁ : ℝ))⁻¹ ^ (2 * (j+1)) *
        ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
          ∑ km : Work.Peluse.LadderP.KmT j n M₁ c L D h₁ h₁',
            Work.Peluse.LadderP.Gwt j n M₁ c L D h₁ h₁' *
              (∑ hs : Fin M₁,
                Work.Peluse.boxNorm (2^j)
                  (Work.Peluse.LadderP.BBlk j M₁ c L (Work.Peluse.LadderP.enumAll j)
                    (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)) (Work.Peluse.symIcc N)
                  (Work.Peluse.LadderP.Gof j n M₁ c L D h₁ h₁' km f)) := by
  rw [augPowState_peel j n M₁ c L D N f hf]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [augPowState_reindex j n M₁ c L D N f, augPowState_reorder j n M₁ c L D N f]
  refine Finset.sum_le_sum (fun h₁ _ => Finset.sum_le_sum (fun h₁' _ =>
    Finset.sum_le_sum (fun h'_s _ => Finset.sum_le_sum (fun km _ => ?_))))
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun hs _ => ?_))
    (Gwt_nonneg j n M₁ c L D h₁ h₁')
  exact boxNormPow_le_boxNorm_of_suppSmall (norm_Gof_le_one c L D h₁ h₁' km hbd)
    (SuppSmall_Gof c L D h₁ h₁' km (SuppSmall.of_supportIn hsup))

end

end Work.Peluse.LadderP
