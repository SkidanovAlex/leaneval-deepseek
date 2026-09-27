import Mathlib
import Submission.Work.KT.Idx.WPen
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.wPen_admissible
import Submission.Work.KT.FP.lindDefs

/-!
# `Work.KT.FP.prepend_admissible`

The pencil of the coefficient sequence `Idx.preSeq X b = (0, b₀, …, b_d)` — i.e. of the polynomial
`z · q_b(z)` — is invertible wherever the pencil of `b` is, on the same annulus.

The proof is pointwise.  A matrix over `C(X, ℂ)` is a unit iff all its pointwise evaluations are
units (`isUnit_map_evalC_iff`), and the pointwise companion-pencil kernel correspondence
(`Work.KT.FP.wPen_kernel`) identifies the invertibility of the pointwise pencil with that of the
polynomial matrix `∑_j z^j • b_j`.  For `preSeq X b` this polynomial is `z • ∑_i z^i • b_i`
(`sum_preSeq_smul_map`), and `z ≠ 0` on the annulus, so it is invertible exactly when the
polynomial of `b` is.
-/

namespace Work.KT.FP

open Matrix

/-- A matrix over `C(X, ℂ)`, on an arbitrary finite index type, is a unit iff all its pointwise
evaluations at points of `X` are units. -/
lemma isUnit_map_evalC_iff {X : Type} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι C(X, ℂ)) :
    IsUnit M ↔ ∀ x : X, IsUnit (M.map (evalC x)) := by
  have hdet : ∀ x : X, (M.map (evalC x)).det = M.det x := by
    intro x
    have h := RingHom.map_det (evalC x).toRingHom M
    rw [RingHom.mapMatrix_apply] at h
    exact h.symm
  rw [Matrix.isUnit_iff_isUnit_det, ContinuousMap.isUnit_iff_forall_isUnit]
  constructor
  · intro hu x
    rw [Matrix.isUnit_iff_isUnit_det, hdet x]
    exact hu x
  · intro h x
    rw [← hdet x]
    exact (Matrix.isUnit_iff_isUnit_det _).mp (h x)

/-- Pointwise evaluation at `x` commutes with taking the pencil `z • A + B`. -/
lemma map_evalC_smul_add {X : Type} [TopologicalSpace X] {ι : Type*} (x : X) (z : ℂ)
    {A B : Matrix ι ι C(X, ℂ)} :
    (z • A + B).map (evalC x) = z • A.map (evalC x) + B.map (evalC x) := by
  rw [Matrix.map_add (⇑(evalC x)) (fun a b => map_add (evalC x) a b),
      Matrix.map_smul (⇑(evalC x)) z (fun a => map_smul (evalC x) z a)]

/-- The polynomial matrix of `Idx.preSeq X b = (0, b₀, …, b_d)` is `z` times that of `b`. -/
lemma sum_preSeq_smul_map {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {n d : ℕ}
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ) (x : X) :
    (∑ j : Fin (d + 2), z ^ (j : ℕ) • (((Idx.preSeq X b) j).map (evalC x)))
      = z • (∑ i : Fin (d + 1), z ^ (i : ℕ) • ((b i).map (evalC x))) := by
  rw [Fin.sum_univ_succ]
  have h0 : (z ^ ((0 : Fin (d + 2)) : ℕ)) • (((Idx.preSeq X b) (0 : Fin (d + 2))).map (evalC x))
      = 0 := by
    rw [Idx.preSeq_apply]
    simp
  rw [h0, zero_add]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (Idx.preSeq X b) (i.succ : Fin (d + 2)) = b i := by
    rw [Idx.preSeq_apply, dif_pos (by rw [Fin.val_succ]; omega)]
    congr 1
  rw [h1, Fin.val_succ, pow_succ', smul_smul]

theorem prepend_admissible (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b)) :
    ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • Work.KT.Idx.wPenA X n (d + 1) + Work.KT.Idx.wPenB X n (d + 1)
        (Work.KT.Idx.preSeq X b)) := by
  intro z hzρ hz1
  have hzne : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hzρ
    linarith
  rw [isUnit_map_evalC_iff]
  intro x
  -- The polynomial matrix of `b` is a unit at every point of `X`.
  have hQ : IsUnit (∑ i : Fin (d + 1), z ^ (i : ℕ) • ((b i).map (evalC x))) := by
    have hbmap : IsUnit ((z • Idx.wPenA X n d + Idx.wPenB X n d b).map (evalC x)) :=
      (isUnit_map_evalC_iff (z • Idx.wPenA X n d + Idx.wPenB X n d b)).mp (h z hzρ hz1) x
    rw [map_evalC_smul_add x z] at hbmap
    exact ((isUnit_iff_mulVec_eq_zero
        (z • (Idx.wPenA X n d).map (evalC x) + (Idx.wPenB X n d b).map (evalC x))).trans
      ((wPen_kernel n d z (fun j => (b j).map (evalC x))
        ((Idx.wPenA X n d).map (evalC x)) ((Idx.wPenB X n d b).map (evalC x))
        (fun i j => wPenA_map_apply X n d x i j)
        (fun i j => wPenB_map_apply X n d b x i j)).trans
        (isUnit_iff_mulVec_eq_zero
          (∑ i : Fin (d + 1), z ^ (i : ℕ) • ((b i).map (evalC x)))).symm)).mp hbmap
  -- The polynomial matrix of `preSeq X b` is `z` times that of `b`, hence also a unit.
  have hpre : IsUnit (∑ j : Fin (d + 2), z ^ (j : ℕ) • (((Idx.preSeq X b) j).map (evalC x))) := by
    rw [sum_preSeq_smul_map b z x]
    exact (isUnit_smul_of_ne_zero hzne).mpr hQ
  rw [map_evalC_smul_add x z]
  exact ((isUnit_iff_mulVec_eq_zero
      (z • (Idx.wPenA X n (d + 1)).map (evalC x)
        + (Idx.wPenB X n (d + 1) (Idx.preSeq X b)).map (evalC x))).trans
    ((wPen_kernel n (d + 1) z (fun j => ((Idx.preSeq X b) j).map (evalC x))
      ((Idx.wPenA X n (d + 1)).map (evalC x))
      ((Idx.wPenB X n (d + 1) (Idx.preSeq X b)).map (evalC x))
      (fun i j => wPenA_map_apply X n (d + 1) x i j)
      (fun i j => wPenB_map_apply X n (d + 1) (Idx.preSeq X b) x i j)).trans
      (isUnit_iff_mulVec_eq_zero
        (∑ j : Fin (d + 2), z ^ (j : ℕ) • (((Idx.preSeq X b) j).map (evalC x)))).symm)).mpr hpre

end Work.KT.FP
