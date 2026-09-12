import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.ExteriorPower

namespace Commons.Analysis.InnerProductSpace

lemma wedge_replace_inner {k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : Fin k → E) (hf : Orthonormal ℝ f) {i i' : Fin k} (g h : E)
    (hg : ∀ j : Fin k, inner ℝ g (f j) = 0)
    (hh : ∀ j : Fin k, inner ℝ h (f j) = 0) :
    inner ℝ (exteriorPower.ιMulti ℝ k (fun j : Fin k => if j = i then g else f j))
           (exteriorPower.ιMulti ℝ k (fun j : Fin k => if j = i' then h else f j)) =
      if i = i' then inner ℝ g h else 0 := by
  classical
  rw [exteriorPower.inner_ιMulti_ιMulti]
  by_cases hii : i = i'
  · subst i'
    have hff : ∀ r : Fin k, inner ℝ (f r) (f r) = 1 := by
      intro r
      simpa using (orthonormal_iff_ite.mp hf) r r
    let d : Fin k → ℝ := fun r => if r = i then inner ℝ g h else 1
    have hA :
        (Matrix.of fun (r c : Fin k) =>
            inner ℝ (if c = i then g else f c) (if r = i then h else f r)) =
          Matrix.diagonal d := by
      ext r c
      change inner ℝ (if c = i then g else f c) (if r = i then h else f r) =
        if r = c then d r else 0
      by_cases hrc : r = c
      · subst c
        by_cases hri : r = i
        · subst r
          simp [d]
        · rw [if_neg hri]
          rw [if_neg hri]
          rw [hff r]
          simp [d, hri]
      · rw [if_neg hrc]
        by_cases hri : r = i
        · have hci : c ≠ i := by
            intro hci
            exact hrc (hri.trans hci.symm)
          have hfc : inner ℝ (f c) h = 0 := by
            calc
              inner ℝ (f c) h = inner ℝ h (f c) := (real_inner_comm (f c) h).symm
              _ = 0 := hh c
          simp [hri, hci, hfc]
        · by_cases hci : c = i
          · subst c
            simp [hri, hg r]
          · have hcr : inner ℝ (f c) (f r) = 0 := by
              calc
                inner ℝ (f c) (f r) = inner ℝ (f r) (f c) := real_inner_comm (f r) (f c)
                _ = 0 := hf.inner_eq_zero hrc
            simp [hri, hci, hcr]
    rw [hA, Matrix.det_diagonal]
    simp [d]
  · have hrow : ∀ c : Fin k,
        (Matrix.of fun (r : Fin k) (c' : Fin k) =>
            inner ℝ (if c' = i then g else f c') (if r = i' then h else f r)) i c = 0 := by
      intro c
      change inner ℝ (if c = i then g else f c) (if i = i' then h else f i) = 0
      by_cases hci : c = i
      · subst c
        simp [hii, hg i]
      · have hinner : inner ℝ (f i) (f c) = 0 := hf.inner_eq_zero (Ne.symm hci)
        rw [if_neg hii, if_neg hci]
        rw [real_inner_comm (f i) (f c)]
        exact hinner
    rw [Matrix.det_eq_zero_of_row_eq_zero i hrow]
    exact (if_neg hii).symm

end Commons.Analysis.InnerProductSpace