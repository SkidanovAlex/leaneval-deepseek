import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs
import Submission.Work.Diff.Alg.Pinch.qform_kernel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A tight direction of the Ricci form is an eigenvector of `Ric₀`

If `RicPinch p S` (the quadratic form of `ric S` is bounded below by `(p/n)·scal S · |v|²`) and a
vector `v` saturates this bound, then `v` is an eigenvector of the traceless Ricci tensor:

`ric0 S · v = (p - 1) · (scal S / n) · v`.

The point is that `M = ric S - (p/n)·scal S · id` is symmetric (pair symmetry of `IsAlgCurv`) and
positive semidefinite (`RicPinch`), so its vanishing quadratic form forces `M v = 0`
(`Work.Diff.Alg.Pinch.qform_kernel`); substituting `ric S = ric0 S + (scal S/n)·id` gives the claim.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- The quadratic form of the identity `2`-tensor is `∑ᵢ vᵢ²`. -/
private lemma qform_id2' {n : ℕ} (w : Fin n → ℝ) :
    qform (id2 n) w = ∑ i, w i * w i := by
  simp only [qform]
  simpa only [id2] using sum_delta_sq w

/-- Contracting the identity `2`-tensor with a vector. -/
private lemma sum_id2_mul' {n : ℕ} (w : Fin n → ℝ) (i : Fin n) :
    (∑ j, id2 n i j * w j) = w i := by
  rw [Finset.sum_eq_single i]
  · simp [id2]
  · intro j _ hj
    have hij : ¬ (i = j) := fun h => hj h.symm
    simp only [id2, hij, ite_false, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

set_option linter.unusedVariables false in
theorem ric0_mulVec_of_tight (n : ℕ) {p : ℝ} (hp : p < 1)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S)
    (hric : Work.Diff.Alg.Pinch.RicPinch p S) {v : Fin n → ℝ}
    (htight : (p * Submission.Diff.Alg.scalAlg S / (n : ℝ)) * (∑ i, v i * v i)
        = ∑ i, ∑ j, Work.Diff.Alg.Pinch.ric S i j * v i * v j) :
    ∀ i, ∑ j, Work.Diff.Alg.Pinch.ric0 S i j * v j
      = (p - 1) * (Submission.Diff.Alg.scalAlg S / (n : ℝ)) * v i := by
  set c : ℝ := p * scalAlg S / (n : ℝ) with hc
  -- the matrix `M = ric S - c · id`; its quadratic form vanishes exactly on the tight directions
  have hMsym : ∀ i j : Fin n, (fun i j => ric S i j - c * id2 n i j) i j
      = (fun i j => ric S i j - c * id2 n i j) j i := by
    intro i j
    simp only
    rw [ric_symm hS i j, id2_symm i j]
  have hqM : ∀ w : Fin n → ℝ,
      qform (fun i j : Fin n => ric S i j - c * id2 n i j) w
        = (∑ i, ∑ j, ric S i j * w i * w j) - c * (∑ i, w i * w i) := by
    intro w
    have hfun : (fun i j : Fin n => ric S i j - c * id2 n i j) = ric S - c • id2 n := by
      funext i j
      simp [Pi.sub_apply, smul_eq_mul]
    rw [hfun, qform_sub, qform_smul, qform_id2']
    rfl
  have hMpsd : ∀ w : Fin n → ℝ,
      0 ≤ qform (fun i j : Fin n => ric S i j - c * id2 n i j) w := by
    intro w
    rw [hqM w]
    have h := hric w
    rw [← hc] at h
    linarith
  have hv : qform (fun i j : Fin n => ric S i j - c * id2 n i j) v = 0 := by
    rw [hqM v]
    linarith [htight]
  have hker := qform_kernel n hMsym hMpsd hv
  intro i
  have hki : (∑ j, (ric S i j - c * id2 n i j) * v j) = 0 := hker i
  have hsplit : (∑ j, (ric S i j - c * id2 n i j) * v j)
      = (∑ j, ric S i j * v j) - c * v i := by
    have h1 : ∀ j : Fin n, (ric S i j - c * id2 n i j) * v j
        = ric S i j * v j - c * (id2 n i j * v j) := fun j => by ring
    simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_id2_mul']
  have hricvec : (∑ j, ric S i j * v j) = c * v i := by linarith
  have hric0 : (∑ j, ric0 S i j * v j)
      = (∑ j, ric S i j * v j) - (scalAlg S / (n : ℝ)) * v i := by
    have h1 : ∀ j : Fin n, ric0 S i j * v j
        = ric S i j * v j - (scalAlg S / (n : ℝ)) * (id2 n i j * v j) := by
      intro j
      simp only [ric0]
      ring
    simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_id2_mul']
  rw [hric0, hricvec, hc]
  ring

end Work.Diff.Alg.Pinch
