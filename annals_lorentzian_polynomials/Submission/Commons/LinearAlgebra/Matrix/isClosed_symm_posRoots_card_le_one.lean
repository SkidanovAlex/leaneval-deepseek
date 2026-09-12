import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one
import Submission.Commons.Topology.QuadraticForm.isOpen_setOf_posDef_restrict

open Matrix Polynomial Set Topology
open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix

noncomputable section

private lemma associated_toQuadraticForm_eq_toBilin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) :
    QuadraticMap.associated A.toQuadraticForm' = Matrix.toBilin' A := by
  apply QuadraticMap.associated_left_inverse
  intro x y
  have hB : (Matrix.toBilin' A).IsSymm := (Matrix.isSymm_toBilin'_iff_isSymm).2 hA
  exact hB.eq x y

private lemma quadReal_eq_toBilin {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) :
    quadReal B x y = Matrix.toBilin' B x y := by
  rw [quadReal_mulVec, Matrix.toBilin'_apply']

@[simp] private lemma eigenvector_toLp {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (i : Fin n) :
    WithLp.toLp 2 ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)) (b i)) = b i := by
  simp [WithLp.linearEquiv]

@[simp] private lemma basis_map_apply {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (i : Fin n) :
    (b.toBasis.map (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))) i =
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)) (b i) := rfl

private lemma repr_self_ofLp {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (i k : Fin n) :
    (b.repr (b i)).ofLp k = if i = k then 1 else 0 := by
  by_cases h : i = k <;> simp [OrthonormalBasis.repr_self, h]

private lemma ortho_basis {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    (QuadraticMap.associated A.toQuadraticForm').IsOrthoᵢ
      ((symmBasis A hA).toBasis.map (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))) := by
  classical
  rw [LinearMap.isOrthoᵢ_def]
  intro i j hij
  let b := symmBasis A hA
  let v : Module.Basis (Fin n) ℝ (Fin n → ℝ) := b.toBasis.map (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))
  change (QuadraticMap.associated A.toQuadraticForm') (v i) (v j) = 0
  rw [associated_toQuadraticForm_eq_toBilin A hA]
  rw [← quadReal_eq_toBilin A (v i) (v j)]
  rw [quadReal_eq_eigen_sum' A hA]
  simp [b, v]
  intro h
  exact False.elim (hij h.symm)

private lemma Q_basis_val {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (i : Fin n) :
    A.toQuadraticForm' (((symmBasis A hA).toBasis.map
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))) i) =
      symmEigenvalues A hA i := by
  classical
  let b := symmBasis A hA
  let lam := symmEigenvalues A hA
  let v : Module.Basis (Fin n) ℝ (Fin n → ℝ) := b.toBasis.map (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))
  change A.toQuadraticForm' (v i) = lam i
  rw [← QuadraticMap.associated_eq_self_apply (S := ℝ) (Q := A.toQuadraticForm') (x := v i)]
  rw [associated_toQuadraticForm_eq_toBilin A hA]
  rw [← quadReal_eq_toBilin A (v i) (v i)]
  rw [quadReal_eq_eigen_sum' A hA]
  simp [b, lam, v]

private lemma sigPos_toQuadraticForm_eq_card_pos_roots {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    sigPos A.toQuadraticForm' =
      (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card := by
  classical
  let b := symmBasis A hA
  let lam := symmEigenvalues A hA
  let v : Module.Basis (Fin n) ℝ (Fin n → ℝ) := b.toBasis.map (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))
  have hv_ortho : (QuadraticMap.associated A.toQuadraticForm').IsOrthoᵢ v := by
    dsimp [v]
    exact ortho_basis A hA
  have hQv : ∀ i : Fin n, A.toQuadraticForm' (v i) = lam i := by
    intro i
    simpa [v] using Q_basis_val A hA i
  let e0 := QuadraticMap.isometryEquivBasisRepr A.toQuadraticForm' v
  have hbas : A.toQuadraticForm'.basisRepr v =
      QuadraticMap.weightedSumSquares ℝ (fun i : Fin n => A.toQuadraticForm' (v i)) :=
    QuadraticMap.basisRepr_eq_of_iIsOrtho A.toQuadraticForm' v hv_ortho
  let e : QuadraticMap.IsometryEquiv A.toQuadraticForm'
      (QuadraticMap.weightedSumSquares ℝ (fun i : Fin n => A.toQuadraticForm' (v i))) := by
    simpa [hbas] using e0
  have hsig := QuadraticForm.sigPos_of_equiv_weightedSumSquares
      (Q := A.toQuadraticForm') (w := fun i : Fin n => A.toQuadraticForm' (v i)) ⟨e⟩
  rw [hsig]
  have hset : {i : Fin n | 0 < A.toQuadraticForm' (v i)}.ncard =
      {i : Fin n | 0 < lam i}.ncard := by
    congr 1
    ext i
    simp [hQv]
  rw [hset]
  have hroot' : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card =
      (Finset.univ.filter (fun i : Fin n => 0 < lam i)).card := by
    simpa [lam, symmEigenvalues] using
      (charpoly_positive_roots_card_eq A hA)
  rw [hroot']
  simpa using (Set.ncard_coe_finset (Finset.univ.filter (fun i : Fin n => 0 < lam i)))

private lemma isClosed_symm (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.IsSymm} := by
  classical
  simp only [Matrix.IsSymm.ext_iff, Set.ofPred_forall]
  refine isClosed_iInter (fun i => ?_)
  refine isClosed_iInter (fun j => ?_)
  exact isClosed_eq
    ((continuous_apply (ι := Fin n) (A := fun _ : Fin n => ℝ) i).comp
      (continuous_apply (ι := Fin n) (A := fun _ : Fin n => Fin n → ℝ) j))
    ((continuous_apply (ι := Fin n) (A := fun _ : Fin n => ℝ) j).comp
      (continuous_apply (ι := Fin n) (A := fun _ : Fin n => Fin n → ℝ) i))

private lemma exists_posDef_subspace_of_two_le_sigPos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (h : 2 ≤ sigPos A.toQuadraticForm') :
    ∃ V : Submodule ℝ (Fin n → ℝ), 2 ≤ Module.finrank ℝ V ∧
      (A.toQuadraticForm'.restrict V).PosDef := by
  obtain ⟨V, hVdim, hVpos⟩ := exists_finrank_eq_sigPos_and_posDef A.toQuadraticForm'
  exact ⟨V, by omega, hVpos⟩

private lemma two_le_sigPos_of_posDef_restrict {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {V : Submodule ℝ (Fin n → ℝ)}
    (hV : (A.toQuadraticForm'.restrict V).PosDef)
    (hdim : 2 ≤ Module.finrank ℝ V) :
    2 ≤ sigPos A.toQuadraticForm' := by
  exact hdim.trans (le_sigPos_of_posDef A.toQuadraticForm' hV)

private lemma isClosed_sigPos_le_one (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | sigPos A.toQuadraticForm' ≤ 1} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro A hA
  have hA' : ¬ sigPos A.toQuadraticForm' ≤ 1 := by simpa using hA
  have hsig : 2 ≤ sigPos A.toQuadraticForm' := by omega
  obtain ⟨V, hdim, hpos⟩ := exists_posDef_subspace_of_two_le_sigPos A hsig
  let U : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {B | (B.toQuadraticForm'.restrict V).PosDef}
  have hU_open : IsOpen U := Commons.Topology.QuadraticForm.isOpen_setOf_posDef_restrict V
  have hA_mem : A ∈ U := hpos
  have hU_sub : U ⊆ {A : Matrix (Fin n) (Fin n) ℝ | sigPos A.toQuadraticForm' ≤ 1}ᶜ := by
    intro B hBpos hBle
    have hBle' : sigPos B.toQuadraticForm' ≤ 1 := by simpa using hBle
    have hBtwo : 2 ≤ sigPos B.toQuadraticForm' :=
      two_le_sigPos_of_posDef_restrict B hBpos hdim
    omega
  exact ⟨U, hU_sub, hU_open, hA_mem⟩

theorem isClosed_symm_posRoots_card_le_one (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ |
      A.IsSymm ∧ (A.charpoly.roots.filter (fun r => 0 < r)).card ≤ 1} := by
  classical
  have hset : {A : Matrix (Fin n) (Fin n) ℝ |
      A.IsSymm ∧ (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1} =
      {A : Matrix (Fin n) (Fin n) ℝ | A.IsSymm} ∩
        {A : Matrix (Fin n) (Fin n) ℝ | sigPos A.toQuadraticForm' ≤ 1} := by
    ext A
    constructor
    · rintro ⟨hA, hroot⟩
      refine ⟨hA, ?_⟩
      have hsig : sigPos A.toQuadraticForm' ≤ 1 := by
        rw [sigPos_toQuadraticForm_eq_card_pos_roots A hA]
        exact hroot
      simpa using hsig
    · rintro ⟨hA, hsig⟩
      refine ⟨hA, ?_⟩
      have hsig' : sigPos A.toQuadraticForm' ≤ 1 := by simpa using hsig
      rw [← sigPos_toQuadraticForm_eq_card_pos_roots A hA]
      exact hsig'
  rw [hset]
  exact (isClosed_symm n).inter (isClosed_sigPos_le_one n)

end
end Commons.LinearAlgebra.Matrix