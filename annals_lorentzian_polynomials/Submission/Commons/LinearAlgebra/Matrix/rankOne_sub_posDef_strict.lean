import Mathlib
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one
import Submission.Commons.LinearAlgebra.Matrix.sigPos_toQuadraticForm_eq_card_pos_roots
import Submission.Commons.LinearAlgebra.Matrix.posDef_dotProduct_le_trace_mul_inv_dot

open Matrix Polynomial Set
open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix

noncomputable section

lemma toQuadraticForm'_apply_eq_dotProduct {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    B.toQuadraticForm' x = x ⬝ᵥ (B *ᵥ x) := by
  rw [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply]
  exact Matrix.toLinearMap₂'_apply' B x x

lemma toQuadraticForm'_single {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    B.toQuadraticForm' (Pi.single i (1 : ℝ)) = B i i := by
  classical
  rw [toQuadraticForm'_apply_eq_dotProduct]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

lemma det_fin_one_eq (M : Matrix (Fin 1) (Fin 1) ℝ) : M.det = M 0 0 := by
  simp [Matrix.det_fin_one]

lemma det_rankOne_sub_posDef {n : ℕ}
    (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.PosDef)
    (w : Fin n → ℝ) (c : ℝ) :
    (c • Matrix.vecMulVec w w - E).det = (-E).det * (1 - c * (w ⬝ᵥ E⁻¹ *ᵥ w)) := by
  classical
  have hEunit : IsUnit E := hE.isUnit
  have hEdet : IsUnit E.det := Matrix.isUnit_iff_isUnit_det E |>.mp hEunit
  have hnegEdet : IsUnit (-E).det := by
    rw [Matrix.det_neg]
    have hunit_pow : IsUnit ((-1 : ℝ) ^ Fintype.card (Fin n)) := by
      exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    exact hunit_pow.mul hEdet
  let u : Fin n → ℝ := c • w
  let U : Matrix (Fin n) (Fin 1) ℝ := Matrix.vecMulVec u (fun _ : Fin 1 => (1 : ℝ))
  let V : Matrix (Fin 1) (Fin n) ℝ := Matrix.vecMulVec (fun _ : Fin 1 => (1 : ℝ)) w
  have hUV : U * V = Matrix.vecMulVec u w := by
    ext i j
    simp [U, V, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hB : c • Matrix.vecMulVec w w - E = -E + Matrix.vecMulVec u w := by
    dsimp [u]
    rw [sub_eq_add_neg]
    rw [← Matrix.smul_vecMulVec]
    rw [add_comm]
  have hdet := Matrix.det_add_mul (A := -E) U V hnegEdet
  rw [hB]
  rw [← hUV]
  rw [hdet]
  congr 1
  have hsmall : (1 + V * (-E)⁻¹ * U).det = 1 + w ⬝ᵥ ((-E)⁻¹ *ᵥ u) := by
    rw [det_fin_one_eq]
    simp [U, V, Matrix.mul_apply, Matrix.vecMulVec_apply]
    rw [dotProduct]
    simp_rw [Matrix.mulVec_apply_eq_sum]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsmall]
  have hEinvneg : (-E)⁻¹ = -E⁻¹ := by
    letI : Invertible (1 : ℝ) := invertibleOne
    letI : Invertible (-1 : ℝ) := invertibleNeg (1 : ℝ)
    have h' := Matrix.inv_smul (k := (-1 : ℝ)) (A := E) hEdet
    rw [show (-1 : ℝ) • E = -E by simp] at h'
    rw [h']
    simp
  have hmul : (-E)⁻¹ *ᵥ u = -(E⁻¹ *ᵥ u) := by
    rw [hEinvneg]
    simp [Matrix.neg_mulVec]
  rw [hmul]
  dsimp [u]
  rw [dotProduct_neg, Matrix.mulVec_smul, dotProduct_smul]
  ring

lemma isUnit_rankOne_sub_posDef {n : ℕ} (hn : 0 < n)
    (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.PosDef)
    (w : Fin n → ℝ) (c : ℝ) (hc : 0 < c)
    (hTrace : 0 < (c • Matrix.vecMulVec w w - E).trace) :
    IsUnit (c • Matrix.vecMulVec w w - E) := by
  classical
  let B := c • Matrix.vecMulVec w w - E
  have hEunit : IsUnit E := hE.isUnit
  have hEdet : IsUnit E.det := Matrix.isUnit_iff_isUnit_det E |>.mp hEunit
  have hdetB := det_rankOne_sub_posDef E hE w c
  have htraceB : B.trace = c * (w ⬝ᵥ w) - E.trace := by
    dsimp [B]
    simp [Matrix.trace_vecMulVec]
  have hEtr_pos : 0 < E.trace := by
    haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    exact hE.trace_pos
  have htrace : E.trace < c * (w ⬝ᵥ w) := by
    rw [htraceB] at hTrace
    linarith
  have hineq := posDef_dotProduct_le_trace_mul_inv_dot E hE w
  have hS_ne : c * (w ⬝ᵥ E⁻¹ *ᵥ w) ≠ 1 := by
    intro hS
    have hmul : c * (w ⬝ᵥ w) ≤ E.trace := by
      have hle := mul_le_mul_of_nonneg_left hineq hc.le
      nlinarith
    linarith
  have hdetB_ne : B.det ≠ 0 := by
    rw [hdetB]
    have hbase_ne : (-E).det ≠ 0 := by
      rw [Matrix.det_neg]
      have hunit_pow : IsUnit ((-1 : ℝ) ^ Fintype.card (Fin n)) := by
        exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
      exact (hunit_pow.mul hEdet).ne_zero
    have hfactor_ne : 1 - c * (w ⬝ᵥ E⁻¹ *ᵥ w) ≠ 0 := by
      intro h
      apply hS_ne
      linarith
    exact mul_ne_zero hbase_ne hfactor_ne
  exact Matrix.isUnit_iff_isUnit_det B |>.mpr (isUnit_iff_ne_zero.mpr hdetB_ne)

lemma sigPos_eq_one_rankOne_sub_posDef {n : ℕ} (hn : 0 < n)
    (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.PosDef)
    (w : Fin n → ℝ) (c : ℝ) (hc : 0 < c)
    (hTrace : 0 < (c • Matrix.vecMulVec w w - E).trace) :
    sigPos (c • Matrix.vecMulVec w w - E).toQuadraticForm' = 1 := by
  classical
  let B := c • Matrix.vecMulVec w w - E
  have hw_ne : w ≠ 0 := by
    intro hw
    haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    have hEtr : 0 < E.trace := hE.trace_pos
    have htr : (c • Matrix.vecMulVec w w - E).trace = -E.trace := by
      simp [hw, Matrix.trace_vecMulVec]
    rw [htr] at hTrace
    linarith
  have hsig_le : sigPos B.toQuadraticForm' ≤ 1 := by
    let f : Module.Dual ℝ (Fin n → ℝ) :=
      { toFun := fun x => x ⬝ᵥ w
        map_add' := by intro x y; simp [dotProduct, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro a x
          simp [dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] }
    have hf_ne : f ≠ 0 := by
      intro hf
      have hwdot : f w = 0 := by rw [hf]; rfl
      have hself : 0 < f w := by
        dsimp [f]
        simp [dotProduct]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hw_ne
        refine Finset.sum_pos' (fun i hi => mul_self_nonneg _) ?_
        exact ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
      linarith
    have hfinrank_ker : Module.finrank ℝ (LinearMap.ker f) = n - 1 := by
      have hfin := Module.Dual.finrank_ker_add_one_of_ne_zero (f := f) hf_ne
      have hfinrank : Module.finrank ℝ (Fin n → ℝ) = n := by simp
      rw [hfinrank] at hfin
      omega
    have hnonpos : ∀ x ∈ (LinearMap.ker f), B.toQuadraticForm' x ≤ 0 := by
      intro x hx
      have hxw : x ⬝ᵥ w = 0 := by
        have := (LinearMap.mem_ker).mp hx
        dsimp [f] at this
        exact this
      have hQ_E_nonneg : 0 ≤ E.toQuadraticForm' x := (hE.toQuadraticForm').nonneg x
      have hQ_E : 0 ≤ x ⬝ᵥ (E *ᵥ x) := by
        simpa [toQuadraticForm'_apply_eq_dotProduct] using hQ_E_nonneg
      calc
        B.toQuadraticForm' x = x ⬝ᵥ (B *ᵥ x) := toQuadraticForm'_apply_eq_dotProduct B x
        _ = - (x ⬝ᵥ (E *ᵥ x)) := by
          dsimp [B]
          simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hxw]
        _ ≤ 0 := by linarith
    have hsig_le' := QuadraticForm.sigPos_add_finrank_le_of_nonpos
      (Q := B.toQuadraticForm') (V := LinearMap.ker f) hnonpos
    have hfinrank_total : Module.finrank ℝ (Fin n → ℝ) = n := by simp
    rw [hfinrank_ker, hfinrank_total] at hsig_le'
    omega
  have hsig_ge : 1 ≤ sigPos B.toQuadraticForm' := by
    have hsum : B.trace = ∑ i : Fin n, B.toQuadraticForm' (Pi.single i (1 : ℝ)) := by
      rw [Matrix.trace]
      simp [Matrix.diag]
      apply Finset.sum_congr rfl
      intro i hi
      rw [toQuadraticForm'_single]
    have hsum_pos : 0 < ∑ i : Fin n, B.toQuadraticForm' (Pi.single i (1 : ℝ)) := by
      rwa [← hsum]
    obtain ⟨i, hi_pos⟩ : ∃ i : Fin n, 0 < B.toQuadraticForm' (Pi.single i (1 : ℝ)) := by
      by_contra h
      have hle : ∀ i : Fin n, B.toQuadraticForm' (Pi.single i (1 : ℝ)) ≤ 0 := by
        intro i
        exact le_of_not_gt (fun hpos => h ⟨i, hpos⟩)
      have hnonpos : (∑ i : Fin n, B.toQuadraticForm' (Pi.single i (1 : ℝ))) ≤ 0 := by
        exact Finset.sum_nonpos (fun i hi => hle i)
      linarith
    have hii_pos : 0 < B i i := by
      simpa [toQuadraticForm'_single] using hi_pos
    let v : Fin n → ℝ := Pi.single i (1 : ℝ)
    let V : Submodule ℝ (Fin n → ℝ) := ℝ ∙ v
    have hv_ne : v ≠ 0 := by
      dsimp [v]
      intro h
      have := congrFun h i
      classical
      simp at this
    have hfinrank_V : Module.finrank ℝ V = 1 := by
      dsimp [V]
      exact finrank_span_singleton hv_ne
    have hVpos : (B.toQuadraticForm'.restrict V).PosDef := by
      intro x hx
      have hxmem : (x : Fin n → ℝ) ∈ V := x.2
      obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton).mp hxmem
      have hx_eq : (x : Fin n → ℝ) = a • v := ha.symm
      have ha_ne : a ≠ 0 := by
        intro ha0
        apply hx
        apply Subtype.ext
        change (x : Fin n → ℝ) = 0
        rw [hx_eq, ha0, zero_smul]
      have hQv : B.toQuadraticForm' v = B i i := by
        dsimp [v]
        exact toQuadraticForm'_single B i
      have hQ : B.toQuadraticForm' (x : Fin n → ℝ) = a * a * (B i i) := by
        rw [hx_eq]
        rw [QuadraticMap.map_smul]
        rw [hQv]
        simp
      rw [QuadraticMap.restrict_apply]
      rw [hQ]
      exact mul_pos (mul_self_pos.mpr ha_ne) hii_pos
    have hle := le_sigPos_of_posDef (Q := B.toQuadraticForm') (V := V) hVpos
    rwa [hfinrank_V] at hle
  change sigPos B.toQuadraticForm' = 1
  omega

theorem rankOne_sub_posDef_strict
    {n : ℕ} (hn : 0 < n)
    (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.PosDef)
    (w : Fin n → ℝ) (c : ℝ) (hc : 0 < c)
    (hTrace : 0 < (c • Matrix.vecMulVec w w - E).trace) :
    let B := c • Matrix.vecMulVec w w - E
    B.IsSymm ∧ IsUnit B ∧
      (B.charpoly.roots.filter (fun r => 0 < r)).card = 1 := by
  classical
  intro B
  have hB_symm : B.IsSymm := by
    dsimp [B]
    have hE_symm : E.IsSymm := (Matrix.isHermitian_iff_isSymm).1 hE.1
    rw [Matrix.IsSymm]
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_vecMulVec]
    rw [hE_symm]
  have hB_unit : IsUnit B := by
    dsimp [B]
    exact isUnit_rankOne_sub_posDef hn E hE w c hc hTrace
  have hroots : (B.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1 := by
    have hsig := sigPos_toQuadraticForm_eq_card_pos_roots B hB_symm
    have hsig_one : B.toQuadraticForm'.sigPos = 1 := by
      change sigPos B.toQuadraticForm' = 1
      dsimp [B]
      exact sigPos_eq_one_rankOne_sub_posDef hn E hE w c hc hTrace
    rw [← hsig, hsig_one]
  exact ⟨hB_symm, hB_unit, hroots⟩

end
end Commons.LinearAlgebra.Matrix
