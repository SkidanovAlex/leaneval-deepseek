import Mathlib
import Submission.Work.Diff.Alg.Pinch.DiagDefs
import Submission.Work.Diff.Alg.Pinch.Dtensor_weight_pos
import Submission.Work.Diff.Alg.Pinch.EFun_Dtensor_diag
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Strict positivity of `EFun (Dtensor n b S)` for diagonal Ricci

This assembles the two independent halves of the diagonal-Ricci case of the Böhm–Wilking
strictness computation (Böhm–Wilking Cor. 2.3 / first step of Lemma 3.4, Brendle–Schoen
Prop. 13):

* `EFun_Dtensor_diag`: for diagonal Ricci, `EFun (Dtensor n b S)` is the double sum
  `∑ᵢⱼ Wt n b S i j · Zf x y z w i j` of the pair weights, each `Zf` being nonnegative;
* `Dtensor_weight_pos`: each pair weight is strictly positive in the range `2 ≤ n`, `0 < b ≤ 1/2`
  as soon as the Ricci eigenvalues satisfy the pinching `λᵢ ≥ p λ̄` (`p = ccP n b`).

The pinching hypothesis comes from `RicPinch (ccP n b) S` evaluated on the standard basis
vectors (`ric S i i ≥ ccP n b · scal S / n`), and `scal S > 0` follows from `InPIC2 S` with
`S ≠ 0` (`inPIC2_metric_basic`, `inPIC2_comp_bound`).  Nondegeneracy of the direction supplies a
pair `(i,j)` with `Zf x y z w i j > 0`, since `EFun (Iso n) = ½ ∑ᵢⱼ Zf`
(`EFun_Iso_eq_half_sum_Zf`).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg
open Work.Diff.Alg.Q2P (EFun)

variable {n : ℕ}

/-- Evaluating a quadratic form on a standard basis vector, in the form appearing in
`RicPinch`. -/
private lemma sum_ite_self_mul {n : ℕ} (i : Fin n) :
    (∑ k : Fin n, (if k = i then (1 : ℝ) else 0) * (if k = i then (1 : ℝ) else 0)) = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The bilinear form `∑ᵢⱼ M i j vᵢ vⱼ` at the standard basis vector `e_k` is `M k k`. -/
private lemma sum_sum_ite_self {n : ℕ} (M : Fin n → Fin n → ℝ) (i : Fin n) :
    (∑ k : Fin n, ∑ l : Fin n,
        M k l * (if k = i then (1 : ℝ) else 0) * (if l = i then (1 : ℝ) else 0))
      = M i i := by
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro l _ hl; simp [hl]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    simp [hk]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem EFun_Dtensor_pos_diag (n : ℕ) (hn2 : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S)
    (hdiag : ∀ i j : Fin n, i ≠ j → Work.Diff.Alg.Pinch.ric S i j = 0)
    (hS0 : S ≠ 0) (hP : Submission.Diff.Alg.InPIC2 S)
    (hric : Work.Diff.Alg.Pinch.RicPinch (Work.Diff.Alg.Pinch.ccP n b) S) :
    ∀ x y z w : Fin n → ℝ,
      Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w ≠ 0 →
      0 < Work.Diff.Alg.Q2P.EFun (Work.Diff.Alg.Pinch.Dtensor n b S) x y z w := by
  intro x y z w hIso
  have hn0 : 0 < n := by omega
  -- the scalar curvature is strictly positive
  have hscal_nn : 0 ≤ scalAlg S := (inPIC2_metric_basic n).2.2 S hP
  have hscal_ne : scalAlg S ≠ 0 := fun h0 => hS0 ((inPIC2_comp_bound n).2 S hP h0)
  have hscal : 0 < scalAlg S := lt_of_le_of_ne hscal_nn (Ne.symm hscal_ne)
  have hlbar : 0 < scalAlg S / (n : ℝ) := div_pos hscal (by exact_mod_cast hn0)
  -- Ricci pinching on the standard basis
  have hric_ii : ∀ i : Fin n, ccP n b * (scalAlg S / (n : ℝ)) ≤ ric S i i := by
    intro i
    have h := hric (fun k => if k = i then (1 : ℝ) else 0)
    rw [sum_ite_self_mul i, sum_sum_ite_self (fun k l => ric S k l) i] at h
    have h2 : ccP n b * (scalAlg S / (n : ℝ)) = ccP n b * scalAlg S / (n : ℝ) := by ring
    rw [h2]
    linarith [h]
  -- each pair weight is strictly positive
  have hFnn : 0 ≤ ∑ k : Fin n, (ric0 S k k) ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hW : ∀ i j : Fin n, 0 < Wt n b S i j := by
    intro i j
    refine Dtensor_weight_pos n hn2 hb hb' hlbar hFnn ?_ ?_
    · have h1 : (1 - ccP n b) * (scalAlg S / (n : ℝ)) + ric0 S i i
          = ric S i i - ccP n b * (scalAlg S / (n : ℝ)) := by
        simp only [ric0, id2, if_true, mul_one]
        ring
      rw [h1]; linarith [hric_ii i]
    · have h1 : (1 - ccP n b) * (scalAlg S / (n : ℝ)) + ric0 S j j
          = ric S j j - ccP n b * (scalAlg S / (n : ℝ)) := by
        simp only [ric0, id2, if_true, mul_one]
        ring
      rw [h1]; linarith [hric_ii j]
  -- some pair is nondegenerate
  have hZnn : 0 ≤ ∑ i, ∑ j, Zf x y z w i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Zf_nonneg x y z w i j))
  have hZne : (∑ i, ∑ j, Zf x y z w i j) ≠ 0 := by
    intro h0
    refine hIso ?_
    rw [EFun_Iso_eq_half_sum_Zf n x y z w, h0]
    ring
  obtain ⟨i₀, j₀, hij₀⟩ : ∃ i j : Fin n, Zf x y z w i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hZne (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => h i j)
  have hZpos : 0 < Zf x y z w i₀ j₀ :=
    lt_of_le_of_ne (Zf_nonneg x y z w i₀ j₀) (Ne.symm hij₀)
  -- conclude
  rw [EFun_Dtensor_diag n hn2 hb hb' hdiag x y z w]
  calc (0 : ℝ) < Wt n b S i₀ j₀ * Zf x y z w i₀ j₀ := mul_pos (hW i₀ j₀) hZpos
    _ ≤ ∑ j, Wt n b S i₀ j * Zf x y z w i₀ j :=
        Finset.single_le_sum (fun j _ => mul_nonneg (le_of_lt (hW i₀ j)) (Zf_nonneg x y z w i₀ j))
          (Finset.mem_univ j₀)
    _ ≤ ∑ i, ∑ j, Wt n b S i j * Zf x y z w i j :=
        Finset.single_le_sum
          (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (le_of_lt (hW i j))
            (Zf_nonneg x y z w i j))) (Finset.mem_univ i₀)

end Work.Diff.Alg.Pinch
