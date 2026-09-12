import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.Analysis.InnerProductSpace.sq_norm_iMulti_eq_det_transpose_mul
import Submission.Commons.LinearAlgebra.Matrix.det_transpose_mul_le_of_kernel
import Submission.Commons.LinearAlgebra.Matrix.det_ne_zero_of_cols_linearIndependent
import Submission.Commons.Lattice.Module.exists_basis_subtype_kernel

namespace Commons.Lattice.Minkowski

open Matrix

variable {n N : ℕ}

noncomputable def kernelSplitEquiv (hn : n ≤ N) : Fin (N - n) ⊕ Fin n ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hn))

lemma kernelSplitEquiv_inl (hn : n ≤ N) (i : Fin (N - n)) :
    kernelSplitEquiv hn (Sum.inl i) = Fin.castLE (Nat.sub_le N n) i := by
  ext
  simp [kernelSplitEquiv]

lemma kernelSplitEquiv_inr (hn : n ≤ N) (j : Fin n) :
    kernelSplitEquiv hn (Sum.inr j) = ⟨N - n + j.val, by omega⟩ := by
  ext
  simp [kernelSplitEquiv]

lemma kernelSplitEquiv_symm_inl (hn : n ≤ N) (i : Fin (N - n)) :
    (kernelSplitEquiv hn).symm (Fin.castLE (Nat.sub_le N n) i) = Sum.inl i := by
  rw [Equiv.symm_apply_eq]
  exact (kernelSplitEquiv_inl hn i).symm

lemma kernelSplitEquiv_symm_inr (hn : n ≤ N) (j : Fin n) :
    (kernelSplitEquiv hn).symm ⟨N - n + j.val, by omega⟩ = Sum.inr j := by
  rw [Equiv.symm_apply_eq]
  exact (kernelSplitEquiv_inr hn j).symm

lemma det_toMatrix_basisFun_eq_one_or_neg_one {N : ℕ} (e : Module.Basis (Fin N) ℤ (Fin N → ℤ)) :
    ((Pi.basisFun ℤ (Fin N)).toMatrix e).det = 1 ∨
      ((Pi.basisFun ℤ (Fin N)).toMatrix e).det = -1 := by
  set u := Pi.basisFun ℤ (Fin N) with hu
  have hflip : u.toMatrix e * e.toMatrix u = 1 := Module.Basis.toMatrix_mul_toMatrix_flip u e
  have hdet := congrArg Matrix.det hflip
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  exact Int.eq_one_or_neg_one_of_mul_eq_one hdet

/-- The norm of the `L2`-indexed vector with coordinates `x` is the square root of the sum
of the squares. -/
lemma norm_withLpEquiv_symm_eq_sqrt {N : ℕ} (x : Fin N → ℝ) :
    ‖(WithLp.equiv 2 (Fin N → ℝ)).symm x‖ = Real.sqrt (∑ k, (x k) ^ 2) := by
  rw [PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hx : ((WithLp.equiv 2 (Fin N → ℝ)).symm x) k = x k := by
    rw [WithLp.equiv_symm_apply]
  rw [hx, Real.norm_eq_abs, sq_abs]

lemma basis_wedge_le {n N : ℕ} (hn : n < N) (b : Fin n → Fin N → ℤ)
    (e : Module.Basis (Fin N) ℤ (Fin N → ℤ))
    (he : ∀ x : Fin N → ℤ, (∀ l, ∑ k, b l k * x k = 0) ↔
        ∃ a : Fin (N - n) → ℤ, x = ∑ j, a j • e (Fin.castLE (Nat.sub_le N n) j)) :
    ‖exteriorPower.ιMulti ℝ (N - n) (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm
        (fun k => ((e (Fin.castLE (Nat.sub_le N n) j) k : ℤ) : ℝ)))‖
      ≤ ∏ l : Fin n, Real.sqrt (∑ k, (((b l k : ℤ) : ℝ)) ^ 2) := by
  classical
  set hk : N - n ≤ N := Nat.sub_le N n with hkdef
  set v : Fin (N - n) → (Fin N → ℤ) := fun j => e (Fin.castLE hk j) with hvdef
  have hvker : ∀ j : Fin (N - n), ∀ l : Fin n, ∑ k, b l k * v j k = 0 := by
    intro j l
    have hsum : (∑ j' : Fin (N - n), (if j' = j then (1 : ℤ) else 0) • v j') = v j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hj'
        simp [hj']
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    exact (he (v j)).mpr ⟨fun j' => if j' = j then (1 : ℤ) else 0, hsum.symm⟩ l
  -- the standard basis and the coordinate matrix of `e`
  set E : Matrix (Fin N) (Fin N) ℤ := (Pi.basisFun ℤ (Fin N)).toMatrix e with hEdef
  have hEapply : ∀ i j : Fin N, E i j = e j i := by
    intro i j
    rw [hEdef, Module.Basis.toMatrix_apply]
    simp
  have hEdet : E.det = 1 ∨ E.det = -1 := det_toMatrix_basisFun_eq_one_or_neg_one e
  -- the split
  set fe : Fin (N - n) ⊕ Fin n ≃ Fin N := kernelSplitEquiv (le_of_lt hn) with hfedef
  have hfe_inl : ∀ i : Fin (N - n), fe (Sum.inl i) = Fin.castLE hk i :=
    fun i => kernelSplitEquiv_inl (le_of_lt hn) i
  have hfe_symm_inl : ∀ i : Fin (N - n), fe.symm (Fin.castLE hk i) = Sum.inl i :=
    fun i => kernelSplitEquiv_symm_inl (le_of_lt hn) i
  set B : Matrix (Fin n) (Fin N) ℤ := Matrix.of b with hBdef
  have hBapply : ∀ l k, B l k = b l k := fun l k => rfl
  set E' : Matrix (Fin (N - n) ⊕ Fin n) (Fin (N - n) ⊕ Fin n) ℤ := E.submatrix fe fe with hE'def
  set B' : Matrix (Fin n) (Fin (N - n) ⊕ Fin n) ℤ := B.submatrix id fe with hB'def
  set S : Matrix (Fin n) (Fin n) ℤ := (B' * E').submatrix id Sum.inr with hSdef
  have hE'apply : ∀ (a c : Fin (N - n) ⊕ Fin n), E' a c = E (fe a) (fe c) := by
    intro a c; rw [hE'def]; rfl
  have hB'apply : ∀ (l : Fin n) (a : Fin (N-n) ⊕ Fin n), B' l a = B l (fe a) := by
    intro l a; rw [hB'def]; rfl
  have hSapply : ∀ (l : Fin n) (j : Fin n), S l j = (B' * E') l (Sum.inr j) := by
    intro l j; rw [hSdef]; rfl
  -- (0) the block relation `B' * E' = [0 | S]`
  have hBE_inl : ∀ (l : Fin n) (i : Fin (N - n)), (B' * E') l (Sum.inl i) = 0 := by
    intro l i
    have h1 : (B' * E') l (Sum.inl i) = ∑ k : Fin N, b l k * v i k := by
      rw [Matrix.mul_apply, ← Equiv.sum_comp fe.symm (fun a => B' l a * E' a (Sum.inl i))]
      apply Finset.sum_congr rfl
      intro k _
      rw [hB'apply, hE'apply, hBapply, hfe_inl, hEapply, Equiv.apply_symm_apply]
    rw [h1]
    exact hvker i l
  have hBE' : ∀ (l : Fin n) (a : Fin (N - n) ⊕ Fin n),
      (B' * E') l a = Sum.elim (fun _ : Fin (N - n) => (0 : ℤ)) (fun j : Fin n => S l j) a := by
    intro l a
    cases a with
    | inl i => simpa using hBE_inl l i
    | inr j => simp [hSapply l j]
  -- (1) det S ≠ 0
  have hvS : ∀ (l : Fin n) (j : Fin n), S l j = ∑ k : Fin N, b l k * (e (fe (Sum.inr j))) k := by
    intro l j
    rw [hSapply, Matrix.mul_apply, ← Equiv.sum_comp fe.symm (fun a => B' l a * E' a (Sum.inr j))]
    apply Finset.sum_congr rfl
    intro k _
    rw [hB'apply, hE'apply, hBapply, hEapply, Equiv.apply_symm_apply]
  have hSdet : S.det ≠ 0 := by
    apply Commons.LinearAlgebra.Matrix.det_ne_zero_of_cols_linearIndependent
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set z : Fin N → ℤ := ∑ j : Fin n, c j • (e (fe (Sum.inr j))) with hzdef
    have hzker : ∀ l : Fin n, ∑ k, b l k * z k = 0 := by
      intro l
      have hl : (∑ j : Fin n, c j * S l j) = 0 := by
        have h := congrFun hc l
        simpa [Finset.sum_apply, Pi.smul_apply, Matrix.col_apply, Pi.zero_apply] using h
      have hl' : (∑ j : Fin n, c j * (∑ k : Fin N, b l k * (e (fe (Sum.inr j))) k)) = 0 := by
        simpa [hvS] using hl
      have hexp : (∑ k, b l k * z k)
          = ∑ j : Fin n, c j * (∑ k : Fin N, b l k * (e (fe (Sum.inr j))) k) := by
        rw [hzdef]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        conv_lhs => enter [2, k]; rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hexp]
      exact hl'
    obtain ⟨d, hd⟩ := (he z).mp hzker
    set g : Fin N → ℤ :=
      fun k => Sum.elim (fun i : Fin (N - n) => - d i) (fun j : Fin n => c j) (fe.symm k) with hgdef
    have hgsum : (∑ k : Fin N, g k • e k) = 0 := by
      rw [← Equiv.sum_comp fe (fun k => g k • e k), Fintype.sum_sum_type]
      have h1 : (∑ i : Fin (N - n), g (fe (Sum.inl i)) • e (fe (Sum.inl i)))
          = - (∑ i : Fin (N - n), d i • e (Fin.castLE hk i)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [hfe_inl, hgdef]
        simp only [hfe_symm_inl, Sum.elim_inl, neg_smul]
      have h2 : (∑ j : Fin n, g (fe (Sum.inr j)) • e (fe (Sum.inr j)))
          = ∑ j : Fin n, c j • e (fe (Sum.inr j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hgdef]
        simp only [Equiv.symm_apply_apply, Sum.elim_inr]
      rw [h1, h2, ← hd, hzdef]
      abel
    have hg0 : ∀ k : Fin N, g k = 0 := Fintype.linearIndependent_iff.mp e.linearIndependent g hgsum
    intro j
    have := hg0 (fe (Sum.inr j))
    rw [hgdef] at this
    simpa [Equiv.symm_apply_apply] using this
  -- (2) the real matrix inequality
  have hEdet' : E'.det = 1 ∨ E'.det = -1 := by
    rw [hE'def, Matrix.det_submatrix_equiv_self fe E]
    exact hEdet
  have hdetCast : ∀ (M : Matrix (Fin n) (Fin n) ℤ),
      (M.map (fun z : ℤ => (z : ℝ))).det = ((M.det : ℤ) : ℝ) :=
    fun M => (Int.cast_det M).symm
  have hSabs : (1 : ℝ) ≤ |(S.map (fun z : ℤ => (z : ℝ))).det| := by
    rw [hdetCast S]
    have h : (1 : ℤ) ≤ |S.det| := Int.one_le_abs hSdet
    exact_mod_cast h
  have key : (Matrix.transpose ((E'.map (fun z : ℤ => (z : ℝ))).submatrix id Sum.inl)
        * ((E'.map (fun z : ℤ => (z : ℝ))).submatrix id Sum.inl)).det
      ≤ ((B'.map (fun z : ℤ => (z : ℝ)))
        * Matrix.transpose (B'.map (fun z : ℤ => (z : ℝ)))).det := by
    refine Commons.LinearAlgebra.Matrix.det_transpose_mul_le_of_kernel _ _ _ ?_ ?_ hSabs
    · have hcast : (E'.map (fun z : ℤ => (z : ℝ))).det = ((E'.det : ℤ) : ℝ) :=
        (Int.cast_det E').symm
      rcases hEdet' with h | h
      · left
        rw [hcast, h]; norm_num
      · right
        rw [hcast, h]; norm_num
    · intro l a
      have hmul : ((B'.map (fun z : ℤ => (z : ℝ)))
          * (E'.map (fun z : ℤ => (z : ℝ)))) l a = (((B' * E') l a : ℤ) : ℝ) := by
        simp only [Matrix.mul_apply, Matrix.map_apply, Int.cast_sum, Int.cast_mul]
      rw [hmul, hBE' l a]
      cases a with
      | inl i => simp
      | inr j => simp
  -- (3) the two wedge norms
  set C : Matrix (Fin N) (Fin (N - n)) ℤ := E.submatrix id (Fin.castLE hk) with hCdef
  have hCapply : ∀ (k : Fin N) (i : Fin (N - n)), C k i = v i k := by
    intro k i
    rw [hCdef]
    simp only [Matrix.submatrix_apply, id_eq, hEapply]
    rfl
  have hLHS : (Matrix.transpose ((E'.map (fun z : ℤ => (z : ℝ))).submatrix id Sum.inl)
        * ((E'.map (fun z : ℤ => (z : ℝ))).submatrix id Sum.inl)).det
      = ((Matrix.transpose C * C).map (fun z : ℤ => (z : ℝ))).det := by
    congr 1
    ext i i'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq,
      Matrix.map_apply, Int.cast_sum, Int.cast_mul]
    rw [← Equiv.sum_comp fe.symm
      (fun a => ((E' a (Sum.inl i) : ℤ) : ℝ) * ((E' a (Sum.inl i') : ℤ) : ℝ))]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hE'apply, Equiv.apply_symm_apply, hfe_inl, hEapply, hCapply, hvdef]
  have hRHS : ((B'.map (fun z : ℤ => (z : ℝ)))
        * Matrix.transpose (B'.map (fun z : ℤ => (z : ℝ)))).det
      = ((B * Matrix.transpose B).map (fun z : ℤ => (z : ℝ))).det := by
    congr 1
    ext l l'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Int.cast_sum,
      Int.cast_mul]
    rw [← Equiv.sum_comp fe.symm
      (fun a => ((B' l a : ℤ) : ℝ) * ((B' l' a : ℤ) : ℝ))]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hB'apply, Equiv.apply_symm_apply, hBapply]
  have hW : ‖exteriorPower.ιMulti ℝ (N - n) (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm
        (fun k => ((v j k : ℤ) : ℝ)))‖ ^ 2 = ((Matrix.transpose C * C).map
          (fun z : ℤ => (z : ℝ))).det := by
    have hfam : (fun j : Fin (N - n) => (WithLp.equiv 2 (Fin N → ℝ)).symm
        (fun k => ((v j k : ℤ) : ℝ)))
        = (fun j : Fin (N - n) => (WithLp.equiv 2 (Fin N → ℝ)).symm
            (fun i => (C i j : ℝ))) := by
      funext j
      apply congrArg (WithLp.equiv 2 (Fin N → ℝ)).symm
      funext k
      exact_mod_cast (hCapply k j).symm
    rw [hfam]
    exact Commons.Analysis.InnerProductSpace.sq_norm_iMulti_eq_det_transpose_mul C
  have hG : ‖exteriorPower.ιMulti ℝ n (fun l => (WithLp.equiv 2 (Fin N → ℝ)).symm
        (fun k => ((b l k : ℤ) : ℝ)))‖ ^ 2 = ((B * Matrix.transpose B).map
          (fun z : ℤ => (z : ℝ))).det := by
    have hfam : (fun l : Fin n => (WithLp.equiv 2 (Fin N → ℝ)).symm
          (fun k => ((b l k : ℤ) : ℝ)))
        = (fun j : Fin n => (WithLp.equiv 2 (Fin N → ℝ)).symm
            (fun i => ((Matrix.transpose B) i j : ℝ))) := by
      funext j
      apply congrArg (WithLp.equiv 2 (Fin N → ℝ)).symm
      funext i
      rw [Matrix.transpose_apply, hBapply]
    rw [hfam]
    exact (Commons.Analysis.InnerProductSpace.sq_norm_iMulti_eq_det_transpose_mul
      (Matrix.transpose B)).trans (by rw [Matrix.transpose_transpose])
  have hsq_le : ‖exteriorPower.ιMulti ℝ (N - n) (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm
        (fun k => ((v j k : ℤ) : ℝ)))‖ ^ 2
      ≤ ‖exteriorPower.ιMulti ℝ n (fun l => (WithLp.equiv 2 (Fin N → ℝ)).symm
        (fun k => ((b l k : ℤ) : ℝ)))‖ ^ 2 := by
    rw [hW, hG, ← hLHS, ← hRHS]
    exact key
  have hnorm_le : ‖exteriorPower.ιMulti ℝ (N - n) (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm
        (fun k => ((v j k : ℤ) : ℝ)))‖
      ≤ ‖exteriorPower.ιMulti ℝ n (fun l => (WithLp.equiv 2 (Fin N → ℝ)).symm
        (fun k => ((b l k : ℤ) : ℝ)))‖ := by
    have h1 := norm_nonneg (exteriorPower.ιMulti ℝ (N - n)
      (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => ((v j k : ℤ) : ℝ))))
    have h2 := norm_nonneg (exteriorPower.ιMulti ℝ n
      (fun l => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => ((b l k : ℤ) : ℝ))))
    nlinarith [hsq_le]
  calc ‖exteriorPower.ιMulti ℝ (N - n) (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm
        (fun k => ((v j k : ℤ) : ℝ)))‖
      ≤ ‖exteriorPower.ιMulti ℝ n (fun l => (WithLp.equiv 2 (Fin N → ℝ)).symm
        (fun k => ((b l k : ℤ) : ℝ)))‖ := hnorm_le
    _ ≤ ∏ l : Fin n, ‖(WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => ((b l k : ℤ) : ℝ))‖ :=
        Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod _
    _ = ∏ l : Fin n, Real.sqrt (∑ k, (((b l k : ℤ) : ℝ)) ^ 2) := by
        apply Finset.prod_congr rfl
        intro l _
        exact norm_withLpEquiv_symm_eq_sqrt _


/-- **Covolume of the relation lattice of an integer matrix.** Let `b : Fin n → (Fin N → ℤ)` be the rows of an `n × N` integer matrix of rank `n`, and let `Λ = {x : Fin N → ℤ | ∀ l, ∑ k, b l k * x k = 0}` be its lattice of integer relations (of `ℤ`-rank `N - n`). Then `Λ` admits a `ℤ`-basis whose exterior product has norm at most the product of the Euclidean norms of the rows of `b` (equivalently `covolume Λ ≤ ∏ l, ‖row l‖`). This is the classical bound `covolume(ker B) = ‖wedge of rows‖ / covolume(image lattice) ≤ ‖wedge of rows‖ ≤ ∏ ‖rowᵢ‖`, since the wedge of a kernel basis is the Hodge dual of the wedge of the rows up to an integer factor of absolute value `≥ 1`. Proof ingredients: exterior powers, Hadamard's inequality for positive semi-definite matrices (`Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod`), the covolume API (`ZLattice.covolume`, `ZLattice.covolume_eq_det`, `ZLattice.covolume_div_covolume_eq_relIndex`, `Commons.Lattice.Minkowski.covol_span_wedge`), and the description of the integer kernel by Laplace/Cramer expansion. -/
theorem kerLattice_basis_wedge_le {n N : ℕ} (hn : n < N) (b : Fin n → Fin N → ℤ) (hli : LinearIndependent ℚ (fun l : Fin n => fun k : Fin N => ((b l k : ℤ) : ℚ))) : ∃ v : Fin (N - n) → (Fin N → ℤ), LinearIndependent ℤ v ∧ (∀ x : Fin N → ℤ, (∀ l, ∑ k, b l k * x k = 0) → ∃ a : Fin (N - n) → ℤ, x = ∑ j, a j • v j) ∧ ‖exteriorPower.ιMulti ℝ (N - n) (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => ((v j k : ℤ) : ℝ)))‖ ≤ ∏ l : Fin n, Real.sqrt (∑ k, (((b l k : ℤ) : ℝ)) ^ 2) := by
  classical
  obtain ⟨e, he⟩ := Commons.Lattice.Module.exists_basis_subtype_kernel hn b hli
  refine ⟨fun j => e (Fin.castLE (Nat.sub_le N n) j), ?_, ?_, ?_⟩
  · exact e.linearIndependent.comp _ (Fin.castLE_injective _)
  · intro x hx
    exact (he x).mp hx
  · exact basis_wedge_le hn b e he

end Commons.Lattice.Minkowski
