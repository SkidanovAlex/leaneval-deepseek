import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Pinch.linv_Q_ell
import Submission.Work.Diff.Alg.Pinch.DtensorDefs
import Submission.Work.Diff.Alg.Pinch.EFun_Dtensor_pos_diag
import Submission.Work.Diff.Alg.Pinch.inPIC2_Q_pointwise
import Submission.Work.Diff.Alg.Pinch.EFun_rot
import Submission.Work.Diff.Alg.Pinch.EFun_X_aux
import Submission.Work.Diff.Alg.Pinch.isAlgCurv_rot
import Submission.Work.Diff.Alg.Pinch.exists_rot_diag_ric
import Submission.Work.Diff.Alg.Pinch.Dtensor_rot_orth
import Submission.Work.Diff.Alg.Pinch.rot_ne_zero_of_orthogonal
import Submission.Work.Diff.Alg.Pinch.Dtensor_pos_reduce

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Strict positivity of the pulled-back reaction term at degenerate directions

With `X := linv (ccA n b) b (Q (ell (ccA n b) b S))` the Böhm–Wilking identity
(`Work.Diff.Alg.Pinch.linv_Q_ell`, BW Theorem 2) writes `X = Q S + Dtensor n b S`, so on a
degenerate direction `EFun S x y z w = 0` the two summands split:

* `0 ≤ EFun (Q S) x y z w` -- tangential invariance of the `PIC2` cone
  (`Work.Diff.Alg.Pinch.inPIC2_Q_pointwise`, Brendle–Schoen §2);
* `0 < EFun (Dtensor n b S) x y z w` -- the Böhm–Wilking eigenvalue computation in the
  diagonal-Ricci normal form (`EFun_Dtensor_pos_diag`), transported to an arbitrary tensor by
  diagonalising `Ric` with an orthonormal frame (`Dtensor_pos_reduce`).

This is the pointwise strictness statement behind the transversal invariance of the cones
`Ĉ(b)`, `0 < b ≤ 1/2` (BS Prop. 13 / Böhm–Wilking Lemma 3.4).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- `R4` is additive in the tensor. -/
theorem chat_R4_add (R T : Curv4 n) (a b e f : Fin n → ℝ) :
    R4 (R + T) a b e f = R4 R a b e f + R4 T a b e f := by
  simp only [R4, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- `EFun` is additive in the tensor. -/
theorem chat_EFun_add (R T : Curv4 n) (x y z w : Fin n → ℝ) :
    Q2P.EFun (R + T) x y z w = Q2P.EFun R x y z w + Q2P.EFun T x y z w := by
  simp only [Q2P.EFun]
  rw [chat_R4_add, chat_R4_add, chat_R4_add, chat_R4_add, chat_R4_add]
  ring

/-- The Böhm–Wilking identity (`linv_Q_ell`) in the form `X = Q S + Dtensor n b S`. -/
lemma chat_linv_Q_ell_eq (n : ℕ) {b : ℝ} (hn1 : 1 ≤ n) (hn0 : 0 < n) (hb : 0 < b)
    (hb' : b ≤ 1 / 2) {S : Curv4 n} (hS : IsAlgCurv S) :
    linv (ccA n b) b (Q (ell (ccA n b) b S)) = Q S + Dtensor n b S := by
  have ha : 1 + 2 * ((n : ℝ) - 1) * ccA n b ≠ 0 := ccA_denom_ne hn1 hb hb'
  have hbne : 1 + ((n : ℝ) - 2) * b ≠ 0 := ccB_denom_ne hn0 hb hb'
  rw [linv_Q_ell n (ccA n b) b ha hbne hS]
  simp only [Dtensor]
  abel

theorem ChatT_pic_b_v2 (n : ℕ) (hn : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S) (hS0 : S ≠ 0)
    (hP : Submission.Diff.Alg.InPIC2 S) (hric : Work.Diff.Alg.Pinch.RicPinch (ccP n b) S) :
    ∀ x y z w : Fin n → ℝ,
      Work.Diff.Alg.Q2P.EFun S x y z w = 0 →
      Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w ≠ 0 →
      0 < Work.Diff.Alg.Q2P.EFun
        (Work.Diff.Alg.Pinch.linv (ccA n b) b
          (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell (ccA n b) b S))) x y z w := by
  intro x y z w hdeg hIso
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hX : linv (ccA n b) b (Q (ell (ccA n b) b S)) = Q S + Dtensor n b S :=
    chat_linv_Q_ell_eq n hn1 hn0 hb hb' hS
  rw [hX, chat_EFun_add]
  have hQ : 0 ≤ Q2P.EFun (Q S) x y z w := inPIC2_Q_pointwise n S hS hP x y z w hdeg
  have hD : 0 < Q2P.EFun (Dtensor n b S) x y z w :=
    Dtensor_pos_reduce n hn hb hb'
      (fun S hS hdiag hS0 hP hric =>
        EFun_Dtensor_pos_diag n hn hb hb' hS hdiag hS0 hP hric)
      S hS hS0 hP hric x y z w hIso
  linarith

end Work.Diff.Alg.Pinch
