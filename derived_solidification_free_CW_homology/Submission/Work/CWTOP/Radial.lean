/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Submission.Work.CWTOP.Basic
import Submission.Work.CWTOP.Pieces
import Submission.Work.CWTOP.isQuotientMap_stepGlue
import Submission.Work.CWTOP.stepHomPiece_factors
import Mathlib.Topology.CompactOpen

/-!
# CWTOP: the collar space retracts onto the `n`-skeleton

The collar space `stepCollar C n` is an open neighbourhood of the `n`-skeleton in the
`(n+1)`-skeleton, obtained by deleting the inner halves of the top cells.  Its pieces are the
`n`-skeleton itself and the collars `1/2 < ‖y‖ ≤ 1` of the top cells, glued along the boundary
spheres.  The canonical map from the pieces to the collar space is a quotient map, so the radial
projection (and the radial homotopy) defined on the pieces descend to continuous maps

* `stepRadial : stepCollar C n → skel C n` and
* `stepHom : I × stepCollar C n → stepCollar C n`,

exhibiting `stepCollar C n` as a deformation retract of `skel C n`.  Hence
`stepCollar C n ≃ₕ skel C n` (`homotopyEquiv_stepCollar_skel`).
-/

open CategoryTheory Limits Topology Set Function Metric

noncomputable section

namespace Work.CWTOP

variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

/-- The glued pieces map to the collar space as a quotient map. -/
lemma isQuotientMap_stepGlueMap (n : ℕ) :
    IsQuotientMap (stepGlue C n) := isQuotientMap_stepGlue (C := C) n

/-- `stepGlue` as a bundled continuous map. -/
def stepGlueHom (n : ℕ) : C(stepPieces C n, stepCollar C n) :=
  ⟨stepGlue C n, continuous_stepGlue n⟩

/-- The product of `stepGlue` with the identity on the interval is a quotient map. -/
lemma isQuotientMap_prodMap_id_stepGlue (n : ℕ) :
    IsQuotientMap (Prod.map (id : unitInterval → unitInterval) (stepGlue C n)) := by
  have hq := isQuotientMap_stepGlue (C := C) n
  refine (isQuotientMap_iff (Prod.map (id : unitInterval → unitInterval) (stepGlue C n))).2
    ⟨?_, Function.surjective_id.prodMap hq.surjective⟩
  rw [isCoinducing_iff]
  intro s
  have hcont : Continuous (Prod.map (id : unitInterval → unitInterval) (stepGlue C n)) :=
    (continuous_id : Continuous (id : unitInterval → unitInterval)).prodMap hq.continuous
  exact ⟨fun hs => by
    rw [isOpen_iff_continuous_mem] at hs ⊢
    exact hq.continuous_lift_prod_right hs,
    fun hs => hs.preimage hcont⟩

/-- The radial projection of the collar space onto the `n`-skeleton. -/
def stepRadial (n : ℕ) : C(stepCollar C n, skel C n) :=
  IsQuotientMap.lift (f := stepGlueHom n) (isQuotientMap_stepGlue (C := C) n)
    ⟨stepRadialPiece C n, continuous_stepRadialPiece n⟩ (stepRadialPiece_factors (C := C) n)

/-- The radial homotopy of the collar space. -/
def stepHom (n : ℕ) : C(unitInterval × stepCollar C n, stepCollar C n) :=
  IsQuotientMap.lift
    (f := ⟨Prod.map (id : unitInterval → unitInterval) (stepGlue C n),
      (continuous_id : Continuous (id : unitInterval → unitInterval)).prodMap
        (continuous_stepGlue n)⟩)
    (isQuotientMap_prodMap_id_stepGlue n)
    ⟨stepHomPiece C n, continuous_stepHomPiece n⟩ (stepHomPiece_factors n)

@[simp]
lemma stepRadial_apply_glue (n : ℕ) (p : stepPieces C n) :
    stepRadial n (stepGlue C n p) = stepRadialPiece C n p :=
  congrFun (congrArg (fun (F : C(stepPieces C n, skel C n)) => (F : stepPieces C n → skel C n))
    (IsQuotientMap.lift_comp (f := stepGlueHom n) (isQuotientMap_stepGlue (C := C) n)
      ⟨stepRadialPiece C n, continuous_stepRadialPiece n⟩
      (stepRadialPiece_factors (C := C) n))) p

@[simp]
lemma stepHom_apply_glue (n : ℕ) (p : unitInterval × stepPieces C n) :
    stepHom n (Prod.map id (stepGlue C n) p) = stepHomPiece C n p :=
  congrFun (congrArg (fun (F : C(unitInterval × stepPieces C n, stepCollar C n)) =>
      (F : unitInterval × stepPieces C n → stepCollar C n))
    (IsQuotientMap.lift_comp
      (f := ⟨Prod.map (id : unitInterval → unitInterval) (stepGlue C n),
        (continuous_id : Continuous (id : unitInterval → unitInterval)).prodMap
          (continuous_stepGlue n)⟩)
      (isQuotientMap_prodMap_id_stepGlue n)
      ⟨stepHomPiece C n, continuous_stepHomPiece n⟩ (stepHomPiece_factors n))) p

/-- The inclusion of the `n`-skeleton into the collar space. -/
def skelIncl (n : ℕ) : C(skel C n, stepCollar C n) :=
  ⟨fun x => ⟨(x : X), skel_subset_stepCollar x.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩

lemma stepHomPiece_zero (n : ℕ) (p : stepPieces C n) :
    stepHomPiece C n (0, p) = stepGlue C n p := by
  rcases p with x | ⟨j, y⟩
  · exact Subtype.ext (stepHomPiece_inl_val n 0 x)
  · refine Subtype.ext ((stepHomPiece_inr_val n 0 j y).trans ?_)
    show RelCWComplex.map (n + 1) j (radialInterpSafe (y : Fin (n + 1) → ℝ) ((0 : unitInterval) : ℝ))
      = RelCWComplex.map (n + 1) j (y : Fin (n + 1) → ℝ)
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, radialInterpSafe_zero]

lemma stepHomPiece_one (n : ℕ) (p : stepPieces C n) :
    stepHomPiece C n (1, p) = stepGlue C n (Sum.inl (stepRadialPiece C n p)) := by
  rcases p with x | ⟨j, y⟩
  · exact Subtype.ext (stepHomPiece_inl_val n 1 x)
  · refine Subtype.ext ?_
    rw [stepHomPiece_inr_val]
    show RelCWComplex.map (n + 1) j (radialInterpSafe (y : Fin (n + 1) → ℝ) ((1 : unitInterval) : ℝ))
      = RelCWComplex.map (n + 1) j (radialUnitSafe (y : Fin (n + 1) → ℝ))
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, radialInterpSafe_one]

lemma stepHom_zero (n : ℕ) (x : stepCollar C n) : stepHom n ((0 : unitInterval), x) = x := by
  obtain ⟨p, hp⟩ := (isQuotientMap_stepGlue (C := C) n).surjective x
  rw [← hp]
  exact (stepHom_apply_glue n ((0 : unitInterval), p)).trans (stepHomPiece_zero n p)

lemma stepHom_one (n : ℕ) (x : stepCollar C n) :
    stepHom n ((1 : unitInterval), x) = skelIncl n (stepRadial n x) := by
  obtain ⟨p, hp⟩ := (isQuotientMap_stepGlue (C := C) n).surjective x
  rw [← hp, stepRadial_apply_glue]
  exact (stepHom_apply_glue n ((1 : unitInterval), p)).trans (stepHomPiece_one n p)

lemma stepRadial_skelIncl (n : ℕ) (x : skel C n) : stepRadial n (skelIncl n x) = x := by
  obtain ⟨p, hp⟩ := (isQuotientMap_stepGlue (C := C) n).surjective (skelIncl n x)
  have hpval : (stepGlue C n p : X) = (x : X) := congrArg Subtype.val hp
  rw [← hp, stepRadial_apply_glue]
  refine Subtype.ext ?_
  rcases p with x' | ⟨j, y⟩
  · exact hpval
  · by_cases hy : ‖(y : Fin (n + 1) → ℝ)‖ = 1
    · show RelCWComplex.map (n + 1) j (radialUnitSafe (y : Fin (n + 1) → ℝ)) = (x : X)
      rw [radialUnitSafe_eq_self_of_norm_eq_one hy]
      exact hpval
    · exfalso
      have hSk : (x : X) ∈ skel C n := x.2
      rw [← hpval] at hSk
      exact hy (norm_eq_one_of_map_mem_skel j (mem_closedBall_of_mem_modelCollar y.2) hSk)

/-- **The collar space is homotopy equivalent to the `n`-skeleton.** -/
def stepHomEquiv (n : ℕ) : ContinuousMap.HomotopyEquiv (stepCollar C n) (skel C n) where
  toFun := stepRadial n
  invFun := skelIncl n
  left_inv :=
    ⟨ContinuousMap.Homotopy.symm
      { toFun := stepHom n
        map_zero_left := stepHom_zero n
        map_one_left := stepHom_one n }⟩
  right_inv := by
    have h : (stepRadial n).comp (skelIncl n) = ContinuousMap.id (skel C n) := by
      ext x
      simpa using stepRadial_skelIncl n x
    rw [h]

/-- **The collar space is homotopy equivalent to the `n`-skeleton.** -/
theorem homotopyEquiv_stepCollar_skel (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv (stepCollar C n) (skel C n)) := ⟨stepHomEquiv n⟩

end Work.CWTOP
