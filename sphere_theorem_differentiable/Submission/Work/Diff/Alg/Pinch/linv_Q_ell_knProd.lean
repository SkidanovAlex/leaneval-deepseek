import Mathlib
import Submission.Work.Diff.Alg.Pinch.BQDefs
import Submission.Work.Diff.Alg.Pinch.lqkDefs
import Submission.Work.Diff.Alg.Pinch.lqkSums
import Submission.Work.Diff.Alg.Pinch.lqkPrep
import Submission.Work.Diff.Alg.Pinch.lqk_Q_knProd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Böhm–Wilking identity `linv a b (Q (ell a b (A ∧ id))) = Q (A ∧ id) + D_{a,b}(A ∧ id)`

Böhm–Wilking, *Manifolds with positive curvature operators are space forms*, Theorem 2, in the
special case of a curvature tensor of the form `A ∧ id` (`A` a symmetric `2`-tensor, `knProd` the
Kulkarni–Nomizu product without the factor `1/2`).

The proof expands both sides into the four `knProd`-monomials `A ∧ A`, `A ∧ id`, `A² ∧ id`,
`id ∧ id`, using

* `Work.Diff.Alg.Pinch.lqk_Q_knProd`: Hamilton's `Q` on `knProd A id2`,
* `Work.Diff.Alg.Pinch.lqk_ric0_Q_knProd_fun` and `lqk_scalAlg_Q_knProd`: the Ricci data of
  `Q (knProd A id2)`,
* `Work.Diff.Alg.Pinch.lqk_ell_knProd`: `ell a b (knProd A id2) = knProd B id2` for the explicit
  affine `B = (1 + (n-2)b) A + ((2a(n-1) - (n-2)b) tr A / n) · id`,
* the affine behaviour of `trT`, `sqT`, `frobT` and the `knProd`-bilinearity lemmas,

and then compares the coefficients by `field_simp`/`ring`.
-/

set_option maxHeartbeats 2000000

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The symmetric `2`-tensor `B = A + b (n-2) A0 + (2a(n-1) tr A / n) . id` for which
`ell a b (knProd A id2) = knProd B id2`. -/
noncomputable def lqkB (n : ℕ) (a b : ℝ) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  A + (b * ((n : ℝ) - 2)) • traceless A + ((2 * a * ((n : ℝ) - 1) * trT A) / (n : ℝ)) • (id2 n)

theorem lqk_B_symm (a b : ℝ) {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) :
    ∀ i j, lqkB n a b A i j = lqkB n a b A j i := by
  intro i j
  rw [lqkB]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hA i j, lqk_traceless_apply, lqk_traceless_apply, hA i j, id2_symm i j]

theorem lqk_B_affine (a b : ℝ) (A : Fin n → Fin n → ℝ) :
    lqkB n a b A = (1 + ((n : ℝ) - 2) * b) • A
      + (((2 * a * ((n : ℝ) - 1) - ((n : ℝ) - 2) * b) * trT A) / (n : ℝ)) • (id2 n) := by
  funext i j
  rw [lqkB]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [lqk_traceless_apply]
  simp only [id2]
  ring

theorem linv_Q_ell_knProd (n : ℕ) (a b : ℝ) (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0)
    (hb : 1 + ((n : ℝ) - 2) * b ≠ 0) {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) :
    Work.Diff.Alg.Pinch.linv a b (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell a b
        (Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n))))
      = Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n))
        + Work.Diff.Alg.Pinch.bwCorr a b (Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n)) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    funext i j k l; exact i.elim0
  · have hn : (n : ℝ) ≠ 0 := by
      have hpos' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
      exact ne_of_gt hpos'
    have hBsym : ∀ i j, lqkB n a b A i j = lqkB n a b A j i := lqk_B_symm a b hA
    have hell : ell a b (knProd A (id2 n)) = knProd (lqkB n a b A) (id2 n) := by
      rw [lqkB]
      exact lqk_ell_knProd a b A
    rw [hell, linv]
    rw [lqk_ric0_Q_knProd_fun hBsym, lqk_scalAlg_Q_knProd hBsym]
    rw [lqk_Q_knProd n hBsym]
    simp only [two_nsmul]
    rw [lqk_B_affine a b A]
    rw [lqk_trT_affine, lqk_sqT_affine, lqk_frobT_affine]
    simp only [knProd_add_left_linv, knProd_sub_left, knProd_smul_left_linv, knProd_add_right,
      knProd_sub_right, lqk_knProd_smul_right, smul_smul]
    rw [lqk_Q_knProd n hA, two_nsmul, bwCorr, lqk_ric0_knProd, lqk_ric_knProd,
      lqk_ric0sq_knProd, lqk_ric0Frob2_knProd, lqk_sqT_traceless A,
      lqk_frobT_traceless A hn, lqk_traceless_eq A]
    simp only [knProd_add_left_linv, knProd_sub_left, knProd_smul_left_linv, knProd_add_right,
      knProd_sub_right, lqk_knProd_smul_right, lqk_knProd_I_left, smul_smul]
    simp only [smul_add, smul_sub, add_smul, sub_smul, smul_smul, one_smul]
    funext i j k l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have ha2 : 1 + 2 * a * ((n : ℝ) - 1) ≠ 0 := by
      have h : (1 + 2 * a * ((n : ℝ) - 1)) = (1 + 2 * ((n : ℝ) - 1) * a) := by ring
      rw [h]; exact ha
    field_simp
    ring

end Work.Diff.Alg.Pinch
