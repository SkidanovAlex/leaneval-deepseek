import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowQ2.chatTail_quad_le
import Submission.Work.BoseRowQ2.form_GchiA
import Submission.Work.BoseRowQ2.gram_f_decomp_proof
import Submission.Work.BoseRowQ2.hvec_gram
import Submission.Work.BoseRowQ2.mc_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseRowQ2/maskSharpMain.lean` — the sharp mask row at the matrix level

This is the assembly of the one-body inequality

`⟨u, GchiA u⟩ ≤ (1+ε)⟨u, GchiF u⟩ + ((1+1/ε)·(96/π))·⟨u, Dmask u⟩ + δ·⟨u, u⟩`

from the dictionary of `maskSharpCore`, the analytic tail estimates `tail_quad_le`,
`chatTail_quad_le`, the operator bound `chatSq_form_le`, the `z`-elimination `zTriangle`
and the scalar core `maskArith`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseB4
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

section Honest

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
  {fc fu : Work.BoseBoxFix.LowCut}

/-- The constant of the `Tail` bound (`tail_quad_le`). -/
noncomputable def tailD : ℝ := Classical.choose tail_quad_le

theorem tailD_nonneg : 0 ≤ tailD :=
  (Classical.choose_spec tail_quad_le).1

/-- The constant of the `⟨Cw, Tail Cw⟩` bound (`chatTail_quad_le`). -/
noncomputable def chatTailD : ℝ := Classical.choose chatTail_quad_le

theorem chatTailD_nonneg : 0 ≤ chatTailD :=
  (Classical.choose_spec chatTail_quad_le).1

/-- The lattice gap `2π(N+1) − 2ℓκ`. -/
noncomputable def gap (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (N : ℕ) : ℝ :=
  2 * Real.pi * ((N : ℝ) + 1) - 2 * RowGchiMaskRowAux.honCutRad v μ

/-- The `Tail` constant at the labels of `Lab N`. -/
noncomputable def tailLam (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (N : ℕ) : ℝ :=
  tailD * (Fintype.card (Lab N) : ℝ) / (gap v μ N) ^ 101

/-- The `⟨Cw, Tail Cw⟩` constant at the labels of `Lab N`. -/
noncomputable def chatTailLam (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (N : ℕ) : ℝ :=
  chatTailD * (Fintype.card (Lab N) : ℝ) / (gap v μ N) ^ 101

theorem chatTailLam_nonneg (μ : ℝ) (N : ℕ) (hgap : 0 < gap v μ N) :
    0 ≤ chatTailLam v μ N := by
  rw [chatTailLam]
  exact div_nonneg (mul_nonneg chatTailD_nonneg (Nat.cast_nonneg _)) (by positivity)

theorem tailLam_nonneg (μ : ℝ) (N : ℕ) (hgap : 0 < gap v μ N) :
    0 ≤ tailLam v μ N := by
  rw [tailLam]
  exact div_nonneg (mul_nonneg tailD_nonneg (Nat.cast_nonneg _)) (by positivity)

/-- The norm bound of the labels that carry nonzero `w`. -/
theorem wfun_norm_le (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (u : Fin (HM μ).m → ℝ) {i : Lab (HM μ).N}
    (hi : wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i ≠ 0) :
    ‖Work.BoseB4.vec (labVec (HM μ).N i)‖ ≤ 2 * RowGchiMaskRowAux.honCutRad v μ := by
  rw [wfun] at hi
  split_ifs at hi with hmem
  · have hfL : (Work.BoseRowsFS.honE v h fc fu HM μ).fL i ≠ 0 := by
      intro h
      exact hi (by rw [h, zero_mul])
    have h1 : ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom i‖
        ≤ 2 * RowGchiMaskRowAux.honKap v μ :=
      RowGchiMaskRowAux.honE_fL_supp HM hμ hav i hfL
    have h2 : Work.BoseB4.vec (labVec (HM μ).N i)
        = Work.BoseBoxFock.ellH v μ • (Work.BoseRowsFS.honF v h fc fu HM μ).kmom i := by
      rw [show (Work.BoseRowsFS.honF v h fc fu HM μ).kmom
          = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N from rfl]
      exact (RowGchiMaskRowAux.smul_kmomLab_eq (ne_of_gt (Work.BoseBoxFock.ellH_pos v μ))
        (HM μ).N i).symm
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos (Work.BoseBoxFock.ellH_pos v μ)]
    calc Work.BoseBoxFock.ellH v μ * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom i‖
        ≤ Work.BoseBoxFock.ellH v μ * (2 * RowGchiMaskRowAux.honKap v μ) :=
          mul_le_mul_of_nonneg_left h1 (Work.BoseBoxFock.ellH_pos v μ).le
      _ = 2 * RowGchiMaskRowAux.honCutRad v μ := by
          rw [RowGchiMaskRowAux.honCutRad]; ring
  · exact absurd hi (by simp [hi])


/-- The `w`-sum of squares, over the excited labels. -/
theorem wfun_sq_sum (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    (∑ i : Lab (HM μ).N,
        (wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i) ^ 2)
      = ∑ i ∈ excited (Lab (HM μ).N),
          ((Work.BoseRowsFS.honE v h fc fu HM μ).fL i * gcoord HM μ u i) ^ 2 := by
  have h1 : ∀ i : Lab (HM μ).N,
      (wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i) ^ 2
        = (if i ∈ excited (Lab (HM μ).N)
            then ((Work.BoseRowsFS.honE v h fc fu HM μ).fL i * gcoord HM μ u i) ^ 2
              else 0) := by
    intro i
    rw [wfun]
    split_ifs with hcon
    · rfl
    · rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp only [h1]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The `w'`-sum of squares, over the excited labels. -/
theorem wpfun_sq_sum (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    (∑ i : Lab (HM μ).N,
        (wpfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i) ^ 2)
      = ∑ i ∈ excited (Lab (HM μ).N),
          ((1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL i) * gcoord HM μ u i) ^ 2 := by
  have h1 : ∀ i : Lab (HM μ).N,
      (wpfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i) ^ 2
        = (if i ∈ excited (Lab (HM μ).N)
            then ((1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL i)
              * gcoord HM μ u i) ^ 2 else 0) := by
    intro i
    rw [wpfun]
    split_ifs with hcon
    · rfl
    · rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp only [h1]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- A general `Σa + Σb ≤ Σc` from a pointwise bound. -/
lemma sum_add_le_sum {α : Type*} (s : Finset α) (a b c : α → ℝ)
    (h : ∀ i ∈ s, a i + b i ≤ c i) : (∑ i ∈ s, a i) + (∑ i ∈ s, b i) ≤ ∑ i ∈ s, c i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum h

/-- A pointwise bound: `(cv)² + ((1−c)v)² ≤ v²` for `c ∈ [0,1]`. -/
lemma sq_sq_le_sq {c v : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    (c * v) ^ 2 + ((1 - c) * v) ^ 2 ≤ v ^ 2 := by
  nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 - c), sq_nonneg v]

/-- The `g`-sum of squares dominates `w` plus `w'`. -/
theorem gcoord_sq_ge (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    (∑ i ∈ excited (Lab (HM μ).N),
        ((Work.BoseRowsFS.honE v h fc fu HM μ).fL i * gcoord HM μ u i) ^ 2)
      + (∑ i ∈ excited (Lab (HM μ).N),
        ((1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL i) * gcoord HM μ u i) ^ 2)
      ≤ ∑ i ∈ excited (Lab (HM μ).N), (gcoord HM μ u i) ^ 2 :=
  sum_add_le_sum _
    (fun i => ((Work.BoseRowsFS.honE v h fc fu HM μ).fL i * gcoord HM μ u i) ^ 2)
    (fun i => ((1 - (Work.BoseRowsFS.honE v h fc fu HM μ).fL i) * gcoord HM μ u i) ^ 2)
    (fun i => (gcoord HM μ u i) ^ 2)
    (fun i _ => sq_sq_le_sq (LowCut.nonneg fc _) (LowCut.le_one fc _))


/-! ## 5. The matrix-level sharp mask inequality

The statement (and its proof) `⟨u, GchiA u⟩ ≤ (1+ε)⟨u, GchiF u⟩ + γ⟨u, Dmask u⟩ + δ‖u‖²` now
lives in `Submission/Work/BoseRowQ2/maskMatLe.lean` as `Work.BoseRowQ2.maskMatLe`: that module
imports this one, so the theorem cannot be re-exported here without a cycle.  Consumers should
import `Submission.Work.BoseRowQ2.maskMatLe`. -/

end Honest

end Work.BoseRowQ2
