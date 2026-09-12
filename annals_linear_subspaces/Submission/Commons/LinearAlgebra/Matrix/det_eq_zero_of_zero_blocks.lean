import Mathlib.Analysis.RCLike.Lemmas

noncomputable section

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix

/-- If `m < a` (the row-block `S` is smaller than the column-block `T`), then the
zero-block hypotheses force a nonzero vector `x` supported on `T` with `M.mulVec x = 0`,
hence `M.det = 0`.  (The case `a < m` is obtained by transposing, see
`det_eq_zero_of_zero_blocks`.) -/
private lemma det_eq_zero_of_card_lt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    {S T : Finset (Fin n)} (m a : ℕ) (hm : S.card = m) (ha : T.card = a) (hlt : m < a)
    (_h01 : ∀ i ∈ S, ∀ j, j ∉ T → M i j = 0)
    (h02 : ∀ i, i ∉ S → ∀ j ∈ T, M i j = 0) :
    M.det = 0 := by
  classical
  let σ := {x : Fin n // x ∈ S}
  let τ := {x : Fin n // x ∈ T}
  let A : Matrix σ τ ℝ := fun s t => M s.1 t.1
  have hdimσ : Module.finrank ℝ (σ → ℝ) = m := by
    dsimp [σ]
    rw [Module.finrank_pi, Fintype.card_coe S, hm]
  have hdimτ : Module.finrank ℝ (τ → ℝ) = a := by
    dsimp [τ]
    rw [Module.finrank_pi, Fintype.card_coe T, ha]
  have hker : A.mulVecLin.ker ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt (K := ℝ) (V := τ → ℝ) (V₂ := σ → ℝ)
      (f := A.mulVecLin)
    rw [hdimσ, hdimτ]
    exact hlt
  rcases (Submodule.ne_bot_iff _).mp hker with ⟨g, hgker, hgne⟩
  have hg : A.mulVec g = 0 := by
    simpa using (LinearMap.mem_ker.mp hgker)
  let x : Fin n → ℝ := fun j => if hj : j ∈ T then g ⟨j, hj⟩ else 0
  have hxne : x ≠ 0 := by
    intro hx0
    apply hgne
    funext t
    have ht : x t.1 = 0 := congrFun hx0 t.1
    simpa [x, t.2] using ht
  have hxker : M.mulVec x = 0 := by
    funext i
    by_cases hiS : i ∈ S
    · have hblock : M.mulVec x i = (A.mulVec g) ⟨i, hiS⟩ := by
        calc
          M.mulVec x i = ∑ j : Fin n, M i j * x j := by
            simp [Matrix.mulVec, dotProduct]
          _ = ∑ j ∈ T, M i j * x j := by
            symm
            refine Finset.sum_subset ?_ ?_
            · intro j hjT
              simp
            · intro j _ hjnotT
              simp [x, hjnotT]
          _ = ∑ t : τ, M i t.1 * g t := by
            rw [Finset.sum_subtype T (fun j => Iff.rfl)
              (fun j => M i j * (if hj : j ∈ T then g ⟨j, hj⟩ else 0))]
            apply Finset.sum_congr rfl
            intro t ht
            rw [dif_pos t.2]
      rw [hblock]
      simpa using congrFun hg ⟨i, hiS⟩
    · have hzero : (∑ j : Fin n, M i j * x j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        by_cases hjT : j ∈ T
        · simp [h02 i hiS j hjT]
        · simp [x, hjT]
      simpa [Matrix.mulVec, dotProduct] using hzero
  exact (Matrix.exists_mulVec_eq_zero_iff).mp ⟨x, hxne, hxker⟩

/-- A square matrix with a zero-block pattern whose row and column blocks have
different sizes has zero determinant. -/
lemma det_eq_zero_of_zero_blocks {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    {S T : Finset (Fin n)} (m a : ℕ) (hm : S.card = m) (ha : T.card = a) (hne : m ≠ a)
    (h01 : ∀ i ∈ S, ∀ j, j ∉ T → M i j = 0)
    (h02 : ∀ i, i ∉ S → ∀ j ∈ T, M i j = 0) :
    M.det = 0 := by
  classical
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact det_eq_zero_of_card_lt M m a hm ha hlt h01 h02
  · have hdetT : M.transpose.det = 0 := by
      apply det_eq_zero_of_card_lt M.transpose a m ha hm hgt
      · intro i hiT j hjS
        simpa [Matrix.transpose_apply] using h02 j hjS i hiT
      · intro i hiT j hjS
        simpa [Matrix.transpose_apply] using h01 j hjS i hiT
    simpa [Matrix.det_transpose] using hdetT

end Commons.LinearAlgebra.Matrix