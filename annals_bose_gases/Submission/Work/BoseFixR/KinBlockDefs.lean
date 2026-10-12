import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.BlockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.KinBlockDefs` — the two-block splitting of the configuration space

`Work.BoseFixR.KinSplit` states that the box-restricted kinetic word of a `(k+j)`-particle state
splits as the sum of the two block words:

`kinFormB (k+j) ℓ d s εT b Φ = ∫_{abox j ℓ} kinFormB k ℓ d s εT b (bfL Φ y)
                              + ∫_{abox k ℓ} kinFormB j ℓ d s εT b (bfR Φ z)`,

the two integration domains and the inner words all carrying the **same** box side `ℓ` (this is
what makes the identity true, as opposed to the `wordB` inequality of `SplitTwo`, whose integrands
already carried their own box side).

The present module provides the one structural object behind the identity: the *block
equivalence* `blockME k j : X k × X j ≃ᵐ X (k+j)` which concatenates the two blocks of
coordinates, together with

* its coordinates (`blockME_castAdd`, `blockME_natAdd`) and its `Fin.append` form;
* its measure preservation and the image of the configuration box
  (`blockME_image_abox`: the product of the two boxes is the box of the concatenation);
* the compatibility with `Function.update` (`update_blockME_castAdd`, `update_blockME_natAdd`),
  from which the slot-fibre identities `fibre_blockME_castAdd` / `fibre_blockME_natAdd`
  (`fibreᵢ Φ = fibreᵢ (bfL Φ y)` for the first block and dually for `bfR`) follow;
* the smoothness of the block fibres (`contDiff_bfL`, `contDiff_bfR`), needed to feed the smooth
  block states to the integrability of the box-restricted word.

Everything here is `sorry`-free; the two analytic inputs of `KinSplit` live in the sibling modules
`Submission.Work.BoseFixR.KinBlockFubini` (the Fubini splitting of the box integral) and
`Submission.Work.BoseFixR.KinBlockIntegrable` (the integrability of the slot integrand).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixR

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The block equivalence -/

/-- **The block equivalence** `X k × X j ≃ᵐ X (k+j)`: concatenation of the two blocks of
coordinates, i.e. `(z, y) ↦ Fin.append z y`.  It is the composition of the product splitting of
the `Fin`-indexed product (`sumPiEquivProdPi`, measure preserving) with the reindexing along
`Fin k ⊕ Fin j ≃ Fin (k+j)`. -/
def blockME (k j : ℕ) : Submission.BoseGases.X k × Submission.BoseGases.X j ≃ᵐ
    Submission.BoseGases.X (k + j) :=
  (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin k ⊕ Fin j => EuclideanSpace ℝ (Fin 3))).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (k + j) => EuclideanSpace ℝ (Fin 3))
      finSumFinEquiv)

/-- The coordinates of the block equivalence: at the index `finSumFinEquiv (Sum.inl i)` it is the
first block and at `finSumFinEquiv (Sum.inr i)` the second. -/
lemma blockME_coord (k j : ℕ) (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j)
    (b : Fin k ⊕ Fin j) : blockME k j (z, y) (finSumFinEquiv b) = Sum.rec z y b := by
  show ((MeasurableEquiv.piCongrLeft (fun _ : Fin (k + j) => EuclideanSpace ℝ (Fin 3))
        finSumFinEquiv)
      ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin k ⊕ Fin j => EuclideanSpace ℝ (Fin 3))).symm (z, y)))
      (finSumFinEquiv b) = _
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [show ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin k ⊕ Fin j => EuclideanSpace ℝ (Fin 3))).symm (z, y))
      = (Equiv.sumPiEquivProdPi
        (fun _ : Fin k ⊕ Fin j => EuclideanSpace ℝ (Fin 3))).symm (z, y) from rfl]
  rw [Equiv.sumPiEquivProdPi_symm_apply]

/-- The first block of coordinates. -/
lemma blockME_castAdd (k j : ℕ) (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j)
    (i : Fin k) : blockME k j (z, y) (Fin.castAdd j i) = z i := by
  rw [← finSumFinEquiv_apply_left (n := j) i, blockME_coord]

/-- The second block of coordinates. -/
lemma blockME_natAdd (k j : ℕ) (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j)
    (i : Fin j) : blockME k j (z, y) (Fin.natAdd k i) = y i := by
  rw [← finSumFinEquiv_apply_right (m := k) i, blockME_coord]

/-- The block equivalence is `Fin.append`. -/
lemma blockME_append (k j : ℕ) (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j) :
    blockME k j (z, y) = Fin.append z y := by
  funext i
  exact Fin.addCases (motive := fun i => blockME k j (z, y) i = Fin.append z y i)
    (fun i => by rw [blockME_castAdd, Fin.append_left])
    (fun i => by rw [blockME_natAdd, Fin.append_right]) i

/-- **The block equivalence preserves Lebesgue measure.** -/
lemma measurePreserving_blockME (k j : ℕ) :
    MeasurePreserving (blockME k j) (volume : Measure (Submission.BoseGases.X k ×
      Submission.BoseGases.X j)) (volume : Measure (Submission.BoseGases.X (k + j))) := by
  have h1 : MeasurePreserving (⇑(MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin k ⊕ Fin j => EuclideanSpace ℝ (Fin 3))).symm)
      (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j))
      (volume : Measure (Fin k ⊕ Fin j → EuclideanSpace ℝ (Fin 3))) :=
    (MeasureTheory.volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Fin k ⊕ Fin j => EuclideanSpace ℝ (Fin 3))).symm
  have h2 : MeasurePreserving (⇑(MeasurableEquiv.piCongrLeft
      (fun _ : Fin (k + j) => EuclideanSpace ℝ (Fin 3)) (finSumFinEquiv (m := k) (n := j))))
      (volume : Measure (Fin k ⊕ Fin j → EuclideanSpace ℝ (Fin 3)))
      (volume : Measure (Submission.BoseGases.X (k + j))) :=
    MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin (k + j) => EuclideanSpace ℝ (Fin 3)) (finSumFinEquiv (m := k) (n := j))
  have h3 := h2.comp h1
  simpa [blockME, MeasurableEquiv.coe_trans, Function.comp_def] using h3

/-- **The block equivalence maps the product of the two boxes onto the box of the
concatenation.** -/
lemma blockME_image_abox (k j : ℕ) (ℓ : ℝ) :
    blockME k j '' (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
      = Submission.BoseGases.abox (k + j) ℓ := by
  ext x
  constructor
  · rintro ⟨⟨z, y⟩, ⟨hz, hy⟩, rfl⟩
    intro m
    exact Fin.addCases (motive := fun m => blockME k j (z, y) m ∈ Submission.BoseGases.acube ℓ)
      (fun i => by rw [blockME_castAdd]; exact hz i)
      (fun i => by rw [blockME_natAdd]; exact hy i) m
  · intro hx
    refine ⟨(fun i : Fin k => x (Fin.castAdd j i), fun i : Fin j => x (Fin.natAdd k i)),
      ⟨?_, ?_⟩, ?_⟩
    · intro i; exact hx _
    · intro i; exact hx _
    · funext m
      exact Fin.addCases (motive := fun m => blockME k j
          (fun i : Fin k => x (Fin.castAdd j i), fun i : Fin j => x (Fin.natAdd k i)) m = x m)
        (fun i => by rw [blockME_castAdd]) (fun i => by rw [blockME_natAdd]) m

/-! ## 2. The block fibres -/

/-- The concatenation of a configuration with a fixed second block, as a function of the first
block: this is the configuration map whose composition with `Φ` is `bfL Φ y`. -/
lemma mkConfig_eq_blockME {k j : ℕ} (z : Submission.BoseGases.X k)
    (y : Submission.BoseGases.X j) :
    (fun i : Fin (k + j) => if h : (i : ℕ) < k then z ⟨i, h⟩
        else y ⟨(i : ℕ) - k, by omega⟩) = blockME k j (z, y) := by
  funext i
  refine Fin.addCases (motive := fun i => (if h : (i : ℕ) < k then z ⟨i, h⟩
      else y ⟨(i : ℕ) - k, by omega⟩) = blockME k j (z, y) i) (fun i' => ?_) (fun i' => ?_) i
  · rw [blockME_castAdd]
    simp only [Fin.val_castAdd, dif_pos i'.isLt]
  · rw [blockME_natAdd]
    simp only [Fin.val_natAdd]
    rw [dif_neg (by omega : ¬ (k + (i' : ℕ) < k))]
    congr 1
    exact Fin.ext (by simp)

/-- The first-block fibre is the state composed with the block equivalence. -/
lemma bfL_eq_blockME {k j : ℕ} (Φ : Submission.BoseGases.X (k + j) → ℝ)
    (y : Submission.BoseGases.X j) :
    bfL Φ y = fun z : Submission.BoseGases.X k => Φ (blockME k j (z, y)) := by
  funext z
  simp only [bfL_apply, mkConfig_eq_blockME]

/-- The second-block fibre is the state composed with the block equivalence. -/
lemma bfR_eq_blockME {k j : ℕ} (Φ : Submission.BoseGases.X (k + j) → ℝ)
    (z : Submission.BoseGases.X k) :
    bfR Φ z = fun y : Submission.BoseGases.X j => Φ (blockME k j (z, y)) := by
  funext y
  simp only [bfR_apply, mkConfig_eq_blockME]

/-- Replacing the `i`-th coordinate of a first-block slot of the concatenation is the same as
concatenating the updated first block. -/
lemma update_blockME_castAdd {k j : ℕ} (z : Submission.BoseGases.X k)
    (y : Submission.BoseGases.X j) (i : Fin k) (ζ : EuclideanSpace ℝ (Fin 3)) :
    Function.update (blockME k j (z, y)) (Fin.castAdd j i) ζ
      = blockME k j (Function.update z i ζ, y) := by
  funext m
  refine Fin.addCases (motive := fun m => Function.update (blockME k j (z, y)) (Fin.castAdd j i) ζ m
      = blockME k j (Function.update z i ζ, y) m) (fun i' => ?_) (fun i' => ?_) m
  · rw [Function.update_apply, blockME_castAdd, blockME_castAdd, Function.update_apply]
    simp only [Fin.castAdd_inj]
  · have hne : Fin.natAdd k i' ≠ Fin.castAdd j i := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    rw [Function.update_apply, blockME_natAdd, blockME_natAdd, if_neg hne]

/-- The dual of `update_blockME_castAdd` for a second-block slot. -/
lemma update_blockME_natAdd {k j : ℕ} (z : Submission.BoseGases.X k)
    (y : Submission.BoseGases.X j) (i : Fin j) (ζ : EuclideanSpace ℝ (Fin 3)) :
    Function.update (blockME k j (z, y)) (Fin.natAdd k i) ζ
      = blockME k j (z, Function.update y i ζ) := by
  funext m
  refine Fin.addCases (motive := fun m => Function.update (blockME k j (z, y)) (Fin.natAdd k i) ζ m
      = blockME k j (z, Function.update y i ζ) m) (fun i' => ?_) (fun i' => ?_) m
  · have hne : Fin.castAdd j i' ≠ Fin.natAdd k i := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    rw [Function.update_apply, blockME_castAdd, blockME_castAdd, if_neg hne]
  · rw [Function.update_apply, blockME_natAdd, blockME_natAdd, Function.update_apply]
    simp only [Fin.natAdd_inj]

/-- **The slot fibre of the concatenation in a first-block slot is the slot fibre of the
first-block word**: `fibreᵢ Φ = fibreᵢ (bfL Φ y)` at the slots `i < k`. -/
lemma fibre_blockME_castAdd {k j : ℕ} (Φ : Submission.BoseGases.X (k + j) → ℝ)
    (i : Fin k) (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j) :
    Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ (blockME k j (z, y))
      = Work.BoseKinLoc.fibre k i (bfL Φ y) z := by
  funext ζ
  simp only [Work.BoseKinLoc.fibre]
  rw [update_blockME_castAdd, bfL_eq_blockME]

/-- **The slot fibre of the concatenation in a second-block slot is the slot fibre of the
second-block word**. -/
lemma fibre_blockME_natAdd {k j : ℕ} (Φ : Submission.BoseGases.X (k + j) → ℝ)
    (i : Fin j) (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j) :
    Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ (blockME k j (z, y))
      = Work.BoseKinLoc.fibre j i (bfR Φ z) y := by
  funext ζ
  simp only [Work.BoseKinLoc.fibre]
  rw [update_blockME_natAdd, bfR_eq_blockME]

/-! ## 3. Smoothness of the block fibres -/

/-- The concatenation with a fixed second block is smooth in the first block. -/
lemma contDiff_blockME_right (k j : ℕ) (y : Submission.BoseGases.X j) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Submission.BoseGases.X k => blockME k j (z, y)) := by
  rw [contDiff_pi]
  intro m
  exact Fin.addCases (motive := fun m =>
      ContDiff ℝ (⊤ : ℕ∞) (fun z : Submission.BoseGases.X k => blockME k j (z, y) m))
    (fun i => by
      have hfun : (fun z : Submission.BoseGases.X k => blockME k j (z, y) (Fin.castAdd j i))
          = fun z => z i := by
        funext z; rw [blockME_castAdd]
      rw [hfun]
      exact ContinuousLinearMap.contDiff
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin k => EuclideanSpace ℝ (Fin 3)) i))
    (fun i => by
      have hfun : (fun z : Submission.BoseGases.X k => blockME k j (z, y) (Fin.natAdd k i))
          = fun _ => y i := by
        funext z; rw [blockME_natAdd]
      rw [hfun]
      exact contDiff_const) m

/-- The concatenation with a fixed first block is smooth in the second block. -/
lemma contDiff_blockME_left (k j : ℕ) (z : Submission.BoseGases.X k) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Submission.BoseGases.X j => blockME k j (z, y)) := by
  rw [contDiff_pi]
  intro m
  exact Fin.addCases (motive := fun m =>
      ContDiff ℝ (⊤ : ℕ∞) (fun y : Submission.BoseGases.X j => blockME k j (z, y) m))
    (fun i => by
      have hfun : (fun y : Submission.BoseGases.X j => blockME k j (z, y) (Fin.castAdd j i))
          = fun _ => z i := by
        funext y; rw [blockME_castAdd]
      rw [hfun]
      exact contDiff_const)
    (fun i => by
      have hfun : (fun y : Submission.BoseGases.X j => blockME k j (z, y) (Fin.natAdd k i))
          = fun y => y i := by
        funext y; rw [blockME_natAdd]
      rw [hfun]
      exact ContinuousLinearMap.contDiff
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin j => EuclideanSpace ℝ (Fin 3)) i)) m

/-- **The first block fibre of a smooth state is smooth.** -/
lemma contDiff_bfL {k j : ℕ} {Φ : Submission.BoseGases.X (k + j) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (y : Submission.BoseGases.X j) :
    ContDiff ℝ (⊤ : ℕ∞) (bfL Φ y) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z : Submission.BoseGases.X k => blockME k j (z, y)) :=
    contDiff_blockME_right k j y
  rw [bfL_eq_blockME]
  exact hΦ.comp hs

/-- **The second block fibre of a smooth state is smooth.** -/
lemma contDiff_bfR {k j : ℕ} {Φ : Submission.BoseGases.X (k + j) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (z : Submission.BoseGases.X k) :
    ContDiff ℝ (⊤ : ℕ∞) (bfR Φ z) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y : Submission.BoseGases.X j => blockME k j (z, y)) :=
    contDiff_blockME_left k j z
  rw [bfR_eq_blockME]
  exact hΦ.comp hs

end Work.BoseFixR
