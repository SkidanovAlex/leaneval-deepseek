import Mathlib
import Submission.Work.Diff.Alg.Pinch.DtensorDefs
import Submission.Work.Diff.Alg.Pinch.EFun_rot
import Submission.Work.Diff.Alg.Pinch.EFun_X_aux
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic
import Submission.Work.Diff.Alg.Pinch.rot_knProd_id2
import Submission.Work.Diff.Alg.Pinch.rot_ne_zero_of_orthogonal
import Submission.Work.Diff.Alg.Pinch.isAlgCurv_rot
import Submission.Work.Diff.Alg.Pinch.exists_rot_diag_ric
import Submission.Work.Diff.Alg.Pinch.Dtensor_rot_orth
import Submission.Work.Diff.Alg.Pinch.ric_rot
import Submission.Work.Diff.Alg.Pinch.scalAlg_rot
import Submission.Work.Diff.Alg.rot_contract4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Reduction to the diagonal-Ricci case: positivity of the Böhm–Wilking difference tensor

`Work.Diff.Alg.Pinch.EFun_Dtensor_pos_diag` proves that `EFun (Dtensor n b S) x y z w > 0` for
every non-isotropic direction, under the extra hypothesis that the Ricci tensor of `S` is
*diagonal in the standard frame*, `ric S i j = 0` for `i ≠ j`.

This module removes that hypothesis.  The Ricci tensor of an algebraic curvature tensor is
symmetric (`Work.Diff.Alg.Pinch.ric_symm`), hence admits an orthonormal eigenbasis: by
`Work.Diff.Alg.Pinch.exists_rot_diag_ric` there is `A ∈ O(n)` with `ric (rot A S) i j = 0` for
`i ≠ j`.  Every ingredient of the statement is equivariant under such a change of frame:

* `IsAlgCurv` (`isAlgCurv_rot`), `InPIC2` (`Cone.inPIC2_rot`) and `RicPinch` (`dtpr_ricPinch_rot`),
  so the rotated tensor still satisfies the hypotheses;
* `rot A` is injective on curvature arrays (`rot_ne_zero_of_orthogonal`), so `S ≠ 0` transfers;
* `Dtensor n b` is equivariant, `rot A (Dtensor n b S) = Dtensor n b (rot A S)`
  (`Dtensor_rot_orth`), and `EFun` is transported by the transpose (`EFun_rot`), while
  `EFun (Iso n)` is invariant (`EFun_Iso_mulVec_orth`); hence

  `EFun (Dtensor n b S) x y z w = EFun (Dtensor n b (rot A S)) (A x) (A y) (A z) (A w)`,

  and the hypothesis `EFun (Iso n) x y z w ≠ 0` is preserved as well.

This is the standard "we may assume that the frame diagonalises `Ric`" reduction.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

open scoped Matrix

variable {n : ℕ}

/-- The isotropic-curvature form of the round sphere is invariant under an orthogonal change of
frame: `EFun_rot` combined with `rot A (Iso n) = Iso n`. -/
private theorem dtpr_EFun_Iso_rot (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (x y z w : Fin n → ℝ) :
    Q2P.EFun (Iso n) (A *ᵥ x) (A *ᵥ y) (A *ᵥ z) (A *ᵥ w)
      = Q2P.EFun (Iso n) x y z w := by
  have hA' : Aᵀ ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff', Matrix.transpose_transpose]
    exact (Matrix.mem_orthogonalGroup_iff (n := Fin n) (R := ℝ)).mp hA
  have h := EFun_rot n Aᵀ (Iso n) x y z w
  rw [rot_Iso_of_orthogonal Aᵀ hA'] at h
  exact h.symm

/-- Frame transport of the positivity statement: evaluating `EFun` of `Dtensor n b (rot A R)` at
the rotated directions `A v` gives `EFun` of `Dtensor n b R` at `v`. -/
private theorem dtpr_EFun_Dtensor_rot (b : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) (x y z w : Fin n → ℝ) :
    Q2P.EFun (Dtensor n b (rot A R)) (A *ᵥ x) (A *ᵥ y) (A *ᵥ z) (A *ᵥ w)
      = Q2P.EFun (Dtensor n b R) x y z w := by
  rw [← Dtensor_rot_orth n b A hA R,
    EFun_rot n A (Dtensor n b R) (A *ᵥ x) (A *ᵥ y) (A *ᵥ z) (A *ᵥ w)]
  have e : ∀ v : Fin n → ℝ, (fun i => ∑ j, A j i * (A *ᵥ v) j) = v := by
    intro v
    have h : Aᵀ *ᵥ (A *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA,
        Matrix.one_mulVec]
    exact h
  rw [e x, e y, e z, e w]

/-- `RicPinch` is invariant under an orthogonal change of frame: the Ricci quadratic form and the
scalar curvature are transported by `A` and `Aᵀ`, which preserves the Euclidean norm. -/
private theorem dtpr_ricPinch_rot (p : ℝ) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) {R : Curv4 n}
    (h : RicPinch p R) : RicPinch p (rot A R) := by
  have hAA : A * Aᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (n := Fin n) (R := ℝ)).mp hA
  have hAA' : Aᵀ * A = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA
  intro v
  -- pull `v` back to `w = Aᵀ v`, so that `A w = v`
  set w : Fin n → ℝ := Aᵀ *ᵥ v with hw
  have hwv : A *ᵥ w = v := by
    rw [hw, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hscal : scalAlg (rot A R) = scalAlg R := scalAlg_rot n A hA R
  -- the Ricci quadratic form of `rot A R` at `v = A w` is that of `R` at `w`
  have hq : (∑ i, ∑ j, ric (rot A R) i j * v i * v j)
      = ∑ a, ∑ b, ric R a b * w a * w b := by
    have h1 : (∑ i, ∑ j, (A *ᵥ w) i * (A *ᵥ w) j * rot2 A (ric R) i j)
        = ∑ i, ∑ j, ric (rot A R) i j * v i * v j := by
      rw [hwv]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [ric_rot n A hA R]
      ring
    have h2 : (∑ i, ∑ j, (A *ᵥ w) i * (A *ᵥ w) j * rot2 A (ric R) i j)
        = ∑ a, ∑ b, w a * w b * ric R a b := by
      simpa only [rot2] using Work.Diff.Alg.collapse2 hA (ric R) w w
    rw [← h1, h2]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  -- and the Euclidean norm is preserved
  have hn : (∑ i, v i * v i) = ∑ i, w i * w i := by
    rw [← hwv]
    have hcol : ∀ b k : Fin n, (∑ i, A i b * A i k) = (if b = k then (1 : ℝ) else 0) :=
      fun b k => col_sum_eq n A hAA' b k
    have h1 : (∑ i, (A *ᵥ w) i * (A *ᵥ w) i)
        = ∑ i, ∑ j, (A *ᵥ w) i * (A *ᵥ w) j * rot2 A (id2 n) i j := by
      rw [dorth_rot2_id2_orth n A hA]
      exact (sum_ai_id2 (fun i => (A *ᵥ w) i) (fun i => (A *ᵥ w) i)).symm
    have h2 : (∑ i, ∑ j, (A *ᵥ w) i * (A *ᵥ w) j * rot2 A (id2 n) i j)
        = ∑ a, ∑ b, w a * w b * id2 n a b := by
      simpa only [rot2] using Work.Diff.Alg.collapse2 hA (id2 n) w w
    rw [h1, h2, sum_ai_id2 (fun a => w a) (fun a => w a)]
  rw [hscal, hq, hn]
  exact h w

theorem Dtensor_pos_reduce (n : ℕ) (hn2 : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    (∀ (S : Submission.Diff.Alg.Curv4 n), Submission.Diff.Alg.IsAlgCurv S →
        (∀ i j : Fin n, i ≠ j → Work.Diff.Alg.Pinch.ric S i j = 0) → S ≠ 0 →
        Submission.Diff.Alg.InPIC2 S → Work.Diff.Alg.Pinch.RicPinch (Work.Diff.Alg.Pinch.ccP n b) S →
        ∀ x y z w : Fin n → ℝ, Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w ≠ 0 →
          0 < Work.Diff.Alg.Q2P.EFun (Work.Diff.Alg.Pinch.Dtensor n b S) x y z w) →
    ∀ (S : Submission.Diff.Alg.Curv4 n), Submission.Diff.Alg.IsAlgCurv S → S ≠ 0 →
      Submission.Diff.Alg.InPIC2 S → Work.Diff.Alg.Pinch.RicPinch (Work.Diff.Alg.Pinch.ccP n b) S →
      ∀ x y z w : Fin n → ℝ, Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w ≠ 0 →
        0 < Work.Diff.Alg.Q2P.EFun (Work.Diff.Alg.Pinch.Dtensor n b S) x y z w := by
  intro H S hS hS0 hP hRicS x y z w hIso
  -- diagonalise `Ric S` by an orthogonal change of frame
  obtain ⟨A, hA, hdiagA⟩ := exists_rot_diag_ric n S hS
  -- the non-isotropy hypothesis is frame independent
  have hIso' : Q2P.EFun (Iso n) (A *ᵥ x) (A *ᵥ y) (A *ᵥ z) (A *ᵥ w) ≠ 0 := by
    rw [dtpr_EFun_Iso_rot A hA x y z w]
    exact hIso
  -- apply the diagonal-Ricci hypothesis to the rotated tensor
  have hmain := H (rot A S) (isAlgCurv_rot n A hS) hdiagA (rot_ne_zero_of_orthogonal n A hA hS0)
    (Cone.inPIC2_rot n A S hP) (dtpr_ricPinch_rot (ccP n b) hA hRicS)
    (A *ᵥ x) (A *ᵥ y) (A *ᵥ z) (A *ᵥ w) hIso'
  -- transport the conclusion back to the original frame
  rwa [dtpr_EFun_Dtensor_rot b A hA S x y z w] at hmain

end Work.Diff.Alg.Pinch
