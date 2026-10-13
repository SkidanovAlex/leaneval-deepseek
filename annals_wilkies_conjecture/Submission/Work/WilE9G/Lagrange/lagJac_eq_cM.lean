import Mathlib
import Submission.Work.WilE9G.Lagrange.LagBlocks

namespace Work.WilE9G.Lagrange

/-! ## Index bookkeeping for `cMEquiv`

`cMEquiv r j` sends the `Fin (r + (j+1))`-index of `lagJac` to the fully split block index
`(Fin r ⊕ Fin j) ⊕ Fin 1`.  The three lemmas below compute it on the three canonical blocks
(`L`-rows/`yt`-columns, `h`-rows/`μ`-columns, and the `N`-row/`μ₀`-column). -/

/-- `cMEquiv` on the `L`/`yt` block. -/
lemma cMEquiv_castAdd {r j : ℕ} (i : Fin r) :
    cMEquiv r j (Fin.castAdd (j + 1) i) = Sum.inl (Sum.inl i) := by
  simp [cMEquiv]

/-- `cMEquiv` on the `h`/`μ` block. -/
lemma cMEquiv_natAdd_castAdd {r j : ℕ} (a : Fin j) :
    cMEquiv r j (Fin.natAdd r (Fin.castAdd 1 a)) = Sum.inl (Sum.inr a) := by
  simp [cMEquiv]

/-- `cMEquiv` on the `N`/`μ₀` block. -/
lemma cMEquiv_natAdd_natAdd {r j : ℕ} (u : Fin 1) :
    cMEquiv r j (Fin.natAdd r (Fin.natAdd j u)) = Sum.inr u := by
  have h1 : finSumFinEquiv.symm (Fin.natAdd r (Fin.natAdd j u)) = Sum.inr (Fin.natAdd j u) := by
    rw [Equiv.symm_apply_eq]; simp [finSumFinEquiv_apply_right]
  have h2 : finSumFinEquiv.symm (Fin.natAdd j u) = Sum.inr u := by
    rw [Equiv.symm_apply_eq]; simp [finSumFinEquiv_apply_right]
  simp only [cMEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, h1, h2]
  simp

/-- `lagJac` is the block matrix `cM` built from `lagA1`, `lagW`, `lagG`, `mu`, `mu0` after the
index equivalence `cMEquiv`. -/
theorem lagJac_eq_cM {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    Work.WilE9G.lagJac S Phi c z mu mu0
      = (Work.WilE9G.Lagrange.cM (Work.WilE9G.Lagrange.lagA1 S Phi c z mu mu0)
          (Work.WilE9G.Lagrange.lagW S z) (Work.WilE9G.Lagrange.lagG S Phi c z) mu mu0).submatrix
          (Work.WilE9G.Lagrange.cMEquiv (1 + m) S.j)
          (Work.WilE9G.Lagrange.cMEquiv (1 + m) S.j) := by
  ext a l
  simp only [Matrix.submatrix_apply]
  revert a
  refine Fin.addCases ?_ ?_
  · intro l'
    revert l
    refine Fin.addCases ?_ ?_
    · intro l0
      rw [cMEquiv_castAdd, cMEquiv_castAdd]
      simp [Work.WilE9G.lagJac, lagA1, Fin.addCases_left]
    · intro s
      revert s
      refine Fin.addCases ?_ ?_
      · intro b
        rw [cMEquiv_castAdd, cMEquiv_natAdd_castAdd]
        simp [Work.WilE9G.lagJac, lagW, Fin.addCases_left, Fin.addCases_right]
      · intro u
        rw [cMEquiv_castAdd, cMEquiv_natAdd_natAdd]
        simp [Work.WilE9G.lagJac, lagG, Fin.addCases_left, Fin.addCases_right]
  · intro s
    revert s
    refine Fin.addCases ?_ ?_
    · intro a'
      revert l
      refine Fin.addCases ?_ ?_
      · intro l0
        rw [cMEquiv_natAdd_castAdd, cMEquiv_castAdd]
        simp [Work.WilE9G.lagJac, lagW, Fin.addCases_left, Fin.addCases_right]
      · intro s2
        revert s2
        refine Fin.addCases ?_ ?_
        · intro b
          rw [cMEquiv_natAdd_castAdd, cMEquiv_natAdd_castAdd]
          simp [Work.WilE9G.lagJac, Fin.addCases_left, Fin.addCases_right]
        · intro u
          rw [cMEquiv_natAdd_castAdd, cMEquiv_natAdd_natAdd]
          simp [Work.WilE9G.lagJac, Fin.addCases_left, Fin.addCases_right]
    · intro u
      revert l
      refine Fin.addCases ?_ ?_
      · intro l0
        rw [cMEquiv_natAdd_natAdd, cMEquiv_castAdd]
        simp [Work.WilE9G.lagJac, Fin.addCases_left, Fin.addCases_right]
      · intro s2
        revert s2
        refine Fin.addCases ?_ ?_
        · intro b
          rw [cMEquiv_natAdd_natAdd, cMEquiv_natAdd_castAdd]
          simp [Work.WilE9G.lagJac, Fin.addCases_left, Fin.addCases_right]
        · intro u2
          rw [cMEquiv_natAdd_natAdd, cMEquiv_natAdd_natAdd]
          simp [Work.WilE9G.lagJac, Fin.addCases_left, Fin.addCases_right]

end Work.WilE9G.Lagrange
