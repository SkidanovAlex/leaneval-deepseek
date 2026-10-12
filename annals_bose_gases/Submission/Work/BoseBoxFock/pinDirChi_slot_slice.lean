import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairDirChi_slices
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinDirChi_slot_slice`

The **one-slot slice identity of the `χ_ℓ`-weighted Dirichlet content**: the `(i,j)`-summand of
`pinDirChi ℓ (fun x => (Φ x : ℂ))` is exactly the slice integral of the squared derivative of the
*fibre* `z ↦ Φ (insertCoord i z x')` along the `j`-th coordinate direction.

Concretely the theorem rewrites

    ∫_{x ∈ abox n ℓ} χ_ℓ(x i)² ‖∂_{i,j}(x ↦ (Φ x : ℂ))‖²

as the iterated integral over the slice box `boxL ℓ × boxPiSet ({k // k ≠ i}) ℓ` of
`χ_ℓ(w)² (∂_j (z ↦ Φ (insertCoord i z x'))(w))²`.

The mathematics is three independent ingredients.

* **The measure-theoretic slice identity** `setIntegral_insertCoord_slice_weight` (proved in
  `pairDirChi_slices.lean`): for continuous `W`, `g` the box integral of `W (x i) · g x` equals the
  iterated slice integral over `(w, x') ↦ insertCoord i w x'`, the weight sitting at the inserted
  coordinate.  (This is the corpus's `setIntegral_insertCoord_slice` — which we also import — with
  the continuous function `x ↦ W (x i) · g x`.)

* **The complex cast is an isometry on the derivative**: `Φ` is real valued and the state is its
  complexification, so `‖fderiv ℝ (fun y => (Φ y : ℂ)) x v‖² = (fderiv ℝ Φ x v)²`
  (`norm_fderiv_ofReal_sq`): the derivative of the complexification is `Complex.ofRealCLM` composed
  with the real derivative (`HasFDerivAt.comp`), and `‖(r : ℂ)‖² = r²`.

* **The chain rule at the inserted coordinate** (`fderiv_insertCoord_slice`): the insertion
  `z ↦ insertCoord i z x'` is affine with derivative the slot embedding
  `ContinuousLinearMap.single ℝ (fun _ : Fin n => E3) i`, which sends the `j`-th standard basis
  vector to the slot direction `slotDirVec i j = Function.update 0 i (single j 1)`.

Everything is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## 1. The insertion `w ↦ insertCoord i w x'` and its derivative -/

/-- The insertion `w' ↦ insertCoord i w' x'` is affine, with derivative the slot embedding
`ContinuousLinearMap.single ℝ (fun _ : Fin n => E3) i` (`v ↦ Function.update 0 i v`). -/
private theorem hasFDerivAt_insertCoord {n : ℕ} (i : Fin n)
    (x' : {k : Fin n // k ≠ i} → E3) (w : E3) :
    HasFDerivAt (fun w' : E3 => insertCoord i w' x')
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => E3) i) w := by
  have hfun : (fun w' : E3 => insertCoord i w' x')
      = fun w' => insertCoord i (0 : E3) x'
          + (ContinuousLinearMap.single ℝ (fun _ : Fin n => E3) i) w' := by
    funext w' k
    by_cases hk : k = i
    · subst hk
      simp [insertCoord_eq, ContinuousLinearMap.single_apply, Pi.single_eq_same]
    · simp [insertCoord_eq, hk, ContinuousLinearMap.single_apply]
  rw [hfun]
  exact (ContinuousLinearMap.hasFDerivAt _).const_add _

/-- **The chain rule of the one-slot slice**: the derivative of the fibre
`z ↦ Φ (insertCoord i z x')` at `w` along the `j`-th coordinate direction is the derivative of the
master function `Φ` at `insertCoord i w x'` along the slot direction `slotDirVec i j`. -/
theorem fderiv_insertCoord_slice {n : ℕ} (i : Fin n) {Φ : Xn n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (x' : {k : Fin n // k ≠ i} → E3) (w : E3) (j : Fin 3) :
    fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w (Submission.BoseGases.kcStdBasis j)
      = fderiv ℝ Φ (insertCoord i w x') (slotDirVec i j) := by
  have hd : HasFDerivAt Φ (fderiv ℝ Φ (insertCoord i w x')) (insertCoord i w x') :=
    ((hΦ.differentiable (by simp)) (insertCoord i w x')).hasFDerivAt
  have hcomp := hd.comp w (hasFDerivAt_insertCoord i x' w)
  have hf : fderiv ℝ (fun z : E3 => Φ (insertCoord i z x')) w
      = (fderiv ℝ Φ (insertCoord i w x')).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => E3) i) := by
    change (fderiv ℝ (Φ ∘ fun z : E3 => insertCoord i z x') w) = _
    rw [hcomp.fderiv]
  rw [hf, ContinuousLinearMap.comp_apply]
  rfl

/-! ## 2. The complexification of a real function -/

/-- The derivative of the complexification `y ↦ ((Φ y : ℝ) : ℂ)` of a real function `Φ` is the
complexification of the real derivative. -/
theorem fderiv_ofReal_apply {n : ℕ} {Φ : Xn n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (x v : Xn n) :
    fderiv ℝ (fun y : Xn n => ((Φ y : ℝ) : ℂ)) x v = ((fderiv ℝ Φ x v : ℝ) : ℂ) := by
  have hd : HasFDerivAt Φ (fderiv ℝ Φ x) x := ((hΦ.differentiable (by simp)) x).hasFDerivAt
  have h1 : HasFDerivAt (fun y : Xn n => ((Φ y : ℝ) : ℂ))
      ((Complex.ofRealCLM).comp (fderiv ℝ Φ x)) x :=
    (ContinuousLinearMap.hasFDerivAt Complex.ofRealCLM).comp x hd
  rw [h1.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

/-- The complexification is an isometry on derivatives: for real `Φ` the norm squared of the
derivative of `y ↦ (Φ y : ℂ)` is the square of the real derivative. -/
theorem norm_fderiv_ofReal_sq {n : ℕ} {Φ : Xn n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (x v : Xn n) :
    ‖fderiv ℝ (fun y : Xn n => ((Φ y : ℝ) : ℂ)) x v‖ ^ 2 = (fderiv ℝ Φ x v) ^ 2 := by
  rw [fderiv_ofReal_apply hΦ x v, Complex.sq_norm, Complex.normSq_ofReal]
  ring

/-! ## 3. The slice identity -/

theorem pinDirChi_slot_slice {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin n) (j : Fin 3) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
              (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ x' in Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ i}) ℓ,
            (Submission.BoseGases.chiScale ℓ w) ^ 2 *
              (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
                  Φ (Work.BoseBoxFock.insertCoord i z x')) w
                (Submission.BoseGases.kcStdBasis j)) ^ 2 := by
  have hW : Continuous (fun w : E3 => (Submission.BoseGases.chiScale ℓ w) ^ 2) :=
    (Submission.BoseGases.chiScale_continuous ℓ).pow 2
  have hg : Continuous (fun x : Xn n => (fderiv ℝ Φ x (slotDirVec i j)) ^ 2) :=
    (((hΦ.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := slotDirVec i j))).pow 2)
  -- Replace the complexified derivative by the real one, pointwise on the box.
  have hcompl : (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
              (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          (fderiv ℝ Φ x (Work.BoseBoxFock.slotDirVec i j)) ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [norm_fderiv_ofReal_sq hΦ x (slotDirVec i j)])
  rw [hcompl]
  -- The weighted one-slot slice identity.
  rw [← setIntegral_insertCoord_slice_weight (n := n) hℓ i hW hg]
  -- The chain rule at the inserted coordinate, pointwise.
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  dsimp only
  rw [← fderiv_insertCoord_slice i hΦ x' w j]

end Work.BoseBoxFock
