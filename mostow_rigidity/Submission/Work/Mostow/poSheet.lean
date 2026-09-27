import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- `mat A *ᵥ hlift u = tsign A • hlift (actO A u)`: the inverse form of the sheet lemma. -/
lemma poSheet_mat_mulVec_hlift (A : O1 n) (u : E n) :
    (mat A).mulVec (hlift u) = tsign A • hlift (actO A u) := by
  rw [Submission.Mostow.Hyper.hlift_actO A u, smul_smul, tsign_sq, one_smul]

/-- The sign identity derived from the sheet lemma: `tsign (A*B) * tsign B * tsign A = 1`. -/
lemma poSheet_tsign_aux (A B : O1 n) : tsign (A * B) * tsign B * tsign A = 1 := by
  have key : hlift (actO (A * B) (0 : E n)) =
      (tsign (A * B) * tsign B * tsign A) • hlift (actO A (actO B (0 : E n))) := by
    calc hlift (actO (A * B) (0 : E n))
        = tsign (A * B) • (mat (A * B)).mulVec (hlift (0 : E n)) :=
          Submission.Mostow.Hyper.hlift_actO (A * B) (0 : E n)
      _ = tsign (A * B) • ((mat A).mulVec ((mat B).mulVec (hlift (0 : E n)))) := by
          rw [mat_mul, Matrix.mulVec_mulVec]
      _ = tsign (A * B) • ((mat A).mulVec (tsign B • hlift (actO B (0 : E n)))) := by
          rw [poSheet_mat_mulVec_hlift B (0 : E n)]
      _ = tsign (A * B) • (tsign B • ((mat A).mulVec (hlift (actO B (0 : E n))))) := by
          rw [Matrix.mulVec_smul]
      _ = (tsign (A * B) * tsign B) • ((mat A).mulVec (hlift (actO B (0 : E n)))) := by
          rw [smul_smul]
      _ = (tsign (A * B) * tsign B) • (tsign A • hlift (actO A (actO B (0 : E n)))) := by
          rw [poSheet_mat_mulVec_hlift A (actO B (0 : E n))]
      _ = (tsign (A * B) * tsign B * tsign A) • hlift (actO A (actO B (0 : E n))) := by
          rw [smul_smul]
  have hpos : 0 < tsign (A * B) * tsign B * tsign A := by
    have ht : 0 < (tsign (A * B) * tsign B * tsign A) *
        tpart (actO A (actO B (0 : E n))) := by
      have h2 : 0 < ((tsign (A * B) * tsign B * tsign A) •
          hlift (actO A (actO B (0 : E n)))) (Sum.inr 0) := by
        rw [← key, hlift_inr]
        exact tpart_pos _
      simpa [Pi.smul_apply, smul_eq_mul, hlift_inr] using h2
    exact (mul_pos_iff.mp ht).elim (fun h => h.1)
      (fun h => absurd h.2 (not_lt.mpr (le_of_lt (tpart_pos _))))
  have hsq : (tsign (A * B) * tsign B * tsign A) * (tsign (A * B) * tsign B * tsign A) = 1 := by
    calc (tsign (A * B) * tsign B * tsign A) * (tsign (A * B) * tsign B * tsign A)
        = (tsign (A * B) * tsign (A * B)) * (tsign B * tsign B) * (tsign A * tsign A) := by
          ring
      _ = 1 := by rw [tsign_sq, tsign_sq, tsign_sq]; norm_num
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact h
  · rw [h] at hpos; norm_num at hpos

/-- `tsign` is multiplicative. -/
lemma poSheet_tsign_mul (A B : O1 n) : tsign (A * B) = tsign A * tsign B := by
  have hAB := poSheet_tsign_aux A B
  have hbc : (tsign B * tsign A) * (tsign B * tsign A) = 1 := by
    calc (tsign B * tsign A) * (tsign B * tsign A)
        = (tsign B * tsign B) * (tsign A * tsign A) := by ring
      _ = 1 := by rw [tsign_sq, tsign_sq]; norm_num
  calc tsign (A * B) = tsign (A * B) * ((tsign B * tsign A) * (tsign B * tsign A)) := by
        rw [hbc, mul_one]
    _ = (tsign (A * B) * tsign B * tsign A) * (tsign B * tsign A) := by ring
    _ = 1 * (tsign B * tsign A) := by rw [hAB]
    _ = tsign A * tsign B := by rw [one_mul, mul_comm]

/-- `actO` is a group action. -/
lemma poSheet_actO_mul (A B : O1 n) (u : E n) :
    actO (A * B) u = actO A (actO B u) := by
  apply hlift_injective
  calc hlift (actO (A * B) u)
      = tsign (A * B) • (mat (A * B)).mulVec (hlift u) :=
        Submission.Mostow.Hyper.hlift_actO (A * B) u
    _ = tsign (A * B) • ((mat A).mulVec ((mat B).mulVec (hlift u))) := by
        rw [mat_mul, Matrix.mulVec_mulVec]
    _ = tsign (A * B) • ((mat A).mulVec (tsign B • hlift (actO B u))) := by
        rw [poSheet_mat_mulVec_hlift B u]
    _ = tsign (A * B) • (tsign B • ((mat A).mulVec (hlift (actO B u)))) := by
        rw [Matrix.mulVec_smul]
    _ = (tsign (A * B) * tsign B) • ((mat A).mulVec (hlift (actO B u))) := by
        rw [smul_smul]
    _ = (tsign (A * B) * tsign B) • (tsign A • hlift (actO A (actO B u))) := by
        rw [poSheet_mat_mulVec_hlift A (actO B u)]
    _ = (tsign (A * B) * tsign B * tsign A) • hlift (actO A (actO B u)) := by
        rw [smul_smul]
    _ = hlift (actO A (actO B u)) := by rw [poSheet_tsign_aux A B, one_smul]

lemma poSheet_tsign_one : tsign (1 : O1 n) = 1 := by
  rw [tsign_eq_one_iff, mat_one]
  simp

lemma poSheet_actO_one (u : E n) : actO (1 : O1 n) u = u := by
  apply hlift_injective
  rw [Submission.Mostow.Hyper.hlift_actO (1 : O1 n) u, poSheet_tsign_one, mat_one,
    Matrix.one_mulVec, one_smul]

lemma poSheet_tsign_neg (A : O1 n) : tsign (-A) = -tsign A := by
  have hne := Submission.Mostow.Hyper.mat00_ne_zero A
  have h1 : (mat (-A)) (Sum.inr 0) (Sum.inr 0) = -((mat A) (Sum.inr 0) (Sum.inr 0)) := by
    rw [mat_neg]; rfl
  rcases lt_or_gt_of_ne hne with h | h
  · rw [(tsign_eq_one_iff (-A)).mpr (by rw [h1]; linarith), (tsign_eq_neg_one_iff A).mpr h]
    norm_num
  · rw [(tsign_eq_neg_one_iff (-A)).mpr (by rw [h1]; linarith), (tsign_eq_one_iff A).mpr h]

lemma poSheet_actO_neg (A : O1 n) (u : E n) : actO (-A) u = actO A u := by
  ext i
  simp only [actO, WithLp.ofLp_toLp, poSheet_tsign_neg, mat_neg, Matrix.neg_mulVec,
    Pi.neg_apply]
  ring

theorem poSheet (n : ℕ) :
    (∀ (A : O1 n) (u : E n), hlift (actO A u) = tsign A • ((mat A).mulVec (hlift u))) ∧
    (∀ A B : O1 n, tsign (A * B) = tsign A * tsign B) ∧
    (∀ (A B : O1 n) (u : E n), actO (A * B) u = actO A (actO B u)) ∧
    (∀ u : E n, actO (1 : O1 n) u = u) ∧
    (∀ (A : O1 n) (u : E n), actO (-A) u = actO A u) :=
  ⟨fun A u => Submission.Mostow.Hyper.hlift_actO A u, fun A B => poSheet_tsign_mul A B,
    fun A B u => poSheet_actO_mul A B u, fun u => poSheet_actO_one u,
    fun A u => poSheet_actO_neg A u⟩

end

end Work.Mostow
