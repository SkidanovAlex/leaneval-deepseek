import Mathlib
import Submission.Work.PTCert.Interfaces

namespace Work.PTCert

open Submission.PTCert

/-- The outer-product Gram form factors as a product of two single sums: multiplying the
`of`-monomials `of ((b1 r a)⁻¹)` and `of (b1 r b)` and using that `of` is multiplicative
turns `gramL` of `fun a b => x a * y b` into the product of the two letter sums. -/
private lemma gramL_of_prod (r : ℕ) (x y : ℕ → ℚ) :
    (Submission.PTCert.gramL r (fun a b => x a * y b) =
      (∑ a ∈ Finset.range (Submission.PTCert.NB1 r),
          (x a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) ((Submission.PTCert.b1 r a)⁻¹)) *
      (∑ b ∈ Finset.range (Submission.PTCert.NB1 r),
          (y b : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r b))) := by
  rw [Submission.PTCert.gramL, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  rw [smul_mul_smul, Rat.cast_mul, map_mul]

/-- A single sum of letters `(b1 r a)⁻¹` weighted by a coefficient vector concentrated at
`0` (where `b1 r 0 = 1`) collapses to the algebra unit. -/
private lemma sum_smul_inv_one (r : ℕ) (c : ℕ → ℚ) (hc : c 0 = 1) (hc0 : ∀ a, a ≠ 0 → c a = 0) :
    (∑ a ∈ Finset.range (Submission.PTCert.NB1 r),
      (c a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) ((Submission.PTCert.b1 r a)⁻¹)) = 1 := by
  have hmem : 0 ∈ Finset.range (Submission.PTCert.NB1 r) :=
    Finset.mem_range.mpr (by unfold Submission.PTCert.NB1; omega)
  rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hc0 b hb]) (fun h => absurd hmem h)]
  simp [hc, Submission.PTCert.b1, ← MonoidAlgebra.one_def]

/-- A single sum of letters `b1 r a` weighted by a coefficient vector concentrated at `0`
collapses to the algebra unit. -/
private lemma sum_smul_one (r : ℕ) (c : ℕ → ℚ) (hc : c 0 = 1) (hc0 : ∀ a, a ≠ 0 → c a = 0) :
    (∑ a ∈ Finset.range (Submission.PTCert.NB1 r),
      (c a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a)) = 1 := by
  have hmem : 0 ∈ Finset.range (Submission.PTCert.NB1 r) :=
    Finset.mem_range.mpr (by unfold Submission.PTCert.NB1; omega)
  rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hc0 b hb]) (fun h => absurd hmem h)]
  simp [hc, Submission.PTCert.b1, ← MonoidAlgebra.one_def]

theorem gramLOuter (r : ℕ) (x y : ℕ → ℚ) :
    (Submission.PTCert.gramL r (fun a b => x a * y b) =
      (∑ a ∈ Finset.range (Submission.PTCert.NB1 r),
          (x a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) ((Submission.PTCert.b1 r a)⁻¹)) *
      (∑ b ∈ Finset.range (Submission.PTCert.NB1 r),
          (y b : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r b))) ∧
    (Submission.PTCert.gramL r (fun a b => if a = 0 then y b else 0) =
      ∑ b ∈ Finset.range (Submission.PTCert.NB1 r),
        (y b : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r b)) ∧
    (Submission.PTCert.gramL r (fun a b => if b = 0 then x a else 0) =
      ∑ a ∈ Finset.range (Submission.PTCert.NB1 r),
        (x a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) ((Submission.PTCert.b1 r a)⁻¹)) := by
  refine ⟨gramL_of_prod r x y, ?_, ?_⟩
  · have h := gramL_of_prod r (fun a => if a = 0 then (1:ℚ) else 0) y
    rw [show (fun a b => (if a = 0 then (1:ℚ) else 0) * y b) = (fun a b => if a = 0 then y b else 0)
        from by funext a b; by_cases h : a = 0 <;> simp [h]] at h
    rw [h, sum_smul_inv_one r (fun a => if a = 0 then (1:ℚ) else 0) (by simp) (by intro a ha; simp [ha]),
      one_mul]
  · have h := gramL_of_prod r x (fun b => if b = 0 then (1:ℚ) else 0)
    rw [show (fun a b => x a * (if b = 0 then (1:ℚ) else 0)) = (fun a b => if b = 0 then x a else 0)
        from by funext a b; by_cases h : b = 0 <;> simp [h]] at h
    rw [h, sum_smul_one r (fun b => if b = 0 then (1:ℚ) else 0) (by simp) (by intro a ha; simp [ha]),
      mul_one]

end Work.PTCert
