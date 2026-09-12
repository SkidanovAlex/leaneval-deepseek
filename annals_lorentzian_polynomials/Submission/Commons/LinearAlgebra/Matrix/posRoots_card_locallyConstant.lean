import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Submission.Commons.LinearAlgebra.Matrix.sigPos_toQuadraticForm_eq_card_pos_roots
import Submission.Commons.Topology.QuadraticForm.isOpen_setOf_posDef_restrict

open Matrix Polynomial Set Topology
open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix

noncomputable section

private lemma toQuadraticForm'_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (-A).toQuadraticForm' = -(A.toQuadraticForm') := by
  ext x
  simp [Matrix.toQuadraticForm']

private lemma associated_toQuadraticForm_eq_toBilin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) :
    QuadraticMap.associated A.toQuadraticForm' = Matrix.toBilin' A := by
  apply QuadraticMap.associated_left_inverse ℝ
  intro x y
  have hB : (Matrix.toBilin' A).IsSymm := (Matrix.isSymm_toBilin'_iff_isSymm).2 hA
  exact hB.eq x y

private lemma radical_eq_bot_of_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hreg : A.det ≠ 0) :
    (A.toQuadraticForm').radical = ⊥ := by
  classical
  rw [QuadraticMap.radical_eq_ker_associated]
  have hassoc : QuadraticMap.associated (A.toQuadraticForm') = Matrix.toBilin' A :=
    associated_toQuadraticForm_eq_toBilin A hA
  rw [hassoc]
  apply le_antisymm
  · intro x hx
    have hxlin : ((Matrix.toBilin' A) : (Fin n → ℝ) →ₗ[ℝ] ((Fin n → ℝ) →ₗ[ℝ] ℝ)) x = 0 := by
      exact LinearMap.mem_ker.mp hx
    have hortho : ∀ w : Fin n → ℝ, x ⬝ᵥ A *ᵥ w = 0 := by
      intro w
      have hw := DFunLike.congr_fun hxlin w
      simpa [Matrix.toBilin'_apply'] using hw
    have hx0 : x = 0 :=
      Matrix.Nondegenerate.eq_zero_of_ortho (Matrix.nondegenerate_of_det_ne_zero hreg) hortho
    simpa using hx0
  · exact bot_le

/-- The number of strictly positive roots of the characteristic polynomial of a real symmetric
matrix is locally constant on the (symmetric matrices in a) neighborhood of any nonsingular
symmetric matrix. -/
theorem posRoots_card_locallyConstant (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hreg : A.det ≠ 0) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℝ), U ∈ nhds A ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B ∈ U → B.IsSymm →
        (B.charpoly.roots.filter (fun r : ℝ => 0 < r)).card =
          (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card := by
  classical
  let k : ℕ := sigPos (A.toQuadraticForm')
  have hrad : (A.toQuadraticForm').radical = ⊥ := radical_eq_bot_of_det_ne_zero A hA hreg
  have hrad0 : Module.finrank ℝ (A.toQuadraticForm').radical = 0 := by
    rw [hrad]
    simp
  have hn : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  have hsum : sigPos (A.toQuadraticForm') + sigNeg (A.toQuadraticForm') = n := by
    have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := (A.toQuadraticForm'))
    omega
  have hk_le_n : k ≤ n := by
    dsimp [k]
    omega
  have hsigNeg : sigNeg (A.toQuadraticForm') = n - k := by
    dsimp [k]
    omega
  obtain ⟨Vpos, hdimpos, hpos⟩ := exists_finrank_eq_sigPos_and_posDef (A.toQuadraticForm')
  obtain ⟨Vneg, hdimneg, hneg⟩ := exists_finrank_eq_sigNeg_and_negDef (A.toQuadraticForm')
  have hdimneg' : Module.finrank ℝ Vneg = n - k := by
    rw [hdimneg, hsigNeg]
  let Upos : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {B | (B.toQuadraticForm'.restrict Vpos).PosDef}
  let Uneg : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {B | ((-B).toQuadraticForm'.restrict Vneg).PosDef}
  have hUpos_open : IsOpen Upos := by
    simpa [Upos] using Commons.Topology.QuadraticForm.isOpen_setOf_posDef_restrict Vpos
  have hUneg_open : IsOpen Uneg := by
    have hS : IsOpen {C : Matrix (Fin n) (Fin n) ℝ | (C.toQuadraticForm'.restrict Vneg).PosDef} :=
      Commons.Topology.QuadraticForm.isOpen_setOf_posDef_restrict Vneg
    have hcont : Continuous fun B : Matrix (Fin n) (Fin n) ℝ => -B := continuous_neg
    simpa [Uneg] using hS.preimage hcont
  have hUposA : A ∈ Upos := by
    simpa [Upos] using hpos
  have hUnegA : A ∈ Uneg := by
    dsimp [Uneg]
    rw [toQuadraticForm'_neg A]
    simpa using hneg
  let U : Set (Matrix (Fin n) (Fin n) ℝ) := Upos ∩ Uneg
  have hU_open : IsOpen U := hUpos_open.inter hUneg_open
  have hU_mem : U ∈ nhds A := hU_open.mem_nhds ⟨hUposA, hUnegA⟩
  refine ⟨U, hU_mem, ?_⟩
  intro B hBU hBsym
  have hBpos : B ∈ Upos := hBU.1
  have hBneg : B ∈ Uneg := hBU.2
  have hsig_ge : k ≤ sigPos (B.toQuadraticForm') := by
    have hge := le_sigPos_of_posDef (Q := B.toQuadraticForm') hBpos
    simpa [k, hdimpos] using hge
  have hneg_le : ∀ x : Vneg, (B.toQuadraticForm') (x : Fin n → ℝ) ≤ 0 := by
    intro x
    by_cases hx0 : (x : Fin n → ℝ) = 0
    · simp [hx0]
    · have hx0' : x ≠ 0 := by
        intro hx
        exact hx0 (by simp [hx])
      have hposx : 0 < ((-B).toQuadraticForm'.restrict Vneg) x := hBneg x hx0'
      have hposx' : 0 < ((-B).toQuadraticForm') (x : Fin n → ℝ) := by
        simpa using hposx
      rw [toQuadraticForm'_neg B] at hposx'
      have hnegx : 0 < -(B.toQuadraticForm') (x : Fin n → ℝ) := by
        simpa using hposx'
      linarith
  have hle_nonpos : ∀ x ∈ Vneg, (B.toQuadraticForm') x ≤ 0 := by
    intro x hx
    exact hneg_le ⟨x, hx⟩
  have hsumle := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := B.toQuadraticForm') hle_nonpos
  have hsumle' : sigPos (B.toQuadraticForm') + (n - k) ≤ n := by
    simpa [hdimneg', hn] using hsumle
  have hsig_le : sigPos (B.toQuadraticForm') ≤ k := by
    omega
  have hsigeq : sigPos (B.toQuadraticForm') = k := le_antisymm hsig_le hsig_ge
  have hAeq : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card =
      sigPos (A.toQuadraticForm') := by
    exact (Commons.LinearAlgebra.Matrix.sigPos_toQuadraticForm_eq_card_pos_roots A hA).symm
  have hBeq : (B.charpoly.roots.filter (fun r : ℝ => 0 < r)).card =
      sigPos (B.toQuadraticForm') := by
    exact (Commons.LinearAlgebra.Matrix.sigPos_toQuadraticForm_eq_card_pos_roots B hBsym).symm
  rw [hBeq, hsigeq]
  dsimp [k]
  exact hAeq.symm

end

end Commons.LinearAlgebra.Matrix