import Mathlib

namespace Work.GM.Affine

open Finset

/-- Sum of an even (symmetric) function over a symmetric integer interval reduces to the
central value plus twice the sum over the positive half. -/
theorem sum_Icc_neg_self (M : ℕ) (A : ℤ → ℝ) (hA : ∀ k : ℤ, A (-k) = A k) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), A k
      = A 0 + 2 * ∑ k ∈ Finset.Icc 1 M, A (k : ℤ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hdecomp : Finset.Icc (-(((M + 1 : ℕ)) : ℤ)) (((M + 1 : ℕ)) : ℤ) =
        insert (-(((M + 1 : ℕ)) : ℤ))
          (insert (((M + 1 : ℕ)) : ℤ) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hk : k = -(((M + 1 : ℕ)) : ℤ)
        · exact Or.inl hk
        · right
          by_cases hk2 : k = (((M + 1 : ℕ)) : ℤ)
          · exact Or.inl hk2
          · right
            constructor <;> omega
      · rintro (rfl | rfl | ⟨h1, h2⟩)
        · constructor <;> omega
        · constructor <;> omega
        · constructor <;> omega
    have hnotin1 : -(((M + 1 : ℕ)) : ℤ) ∉
        insert (((M + 1 : ℕ)) : ℤ) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnotin2 : (((M + 1 : ℕ)) : ℤ) ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hdecomp, Finset.sum_insert hnotin1, Finset.sum_insert hnotin2, ih,
      Finset.sum_Icc_succ_top (a := 1) (b := M) (by omega) (fun k : ℕ => A (k : ℤ))]
    have hsym : A (-(((M + 1 : ℕ)) : ℤ)) = A (((M + 1 : ℕ)) : ℤ) := hA (((M + 1 : ℕ)) : ℤ)
    rw [hsym]
    ring

end Work.GM.Affine
