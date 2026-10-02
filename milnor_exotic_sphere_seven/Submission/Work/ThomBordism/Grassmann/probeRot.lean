import Mathlib
import Submission.Work.ThomBordism.Grassmann.probeFrame

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {k m : ℕ}

/-! ## The complex action in real terms -/

/-- The complex scalar multiplication written with real scalars: `μ • u = μ.re • u + μ.im • (I • u)`. -/
theorem complex_smul_eq (μ : ℂ) (u : E3) :
    μ • u = μ.re • u + μ.im • (Complex.I • u) := by
  conv_lhs => rw [← Complex.re_add_im μ]
  rw [add_smul, mul_smul]
  rfl

/-- `cxE` on a complex multiple. -/
theorem cxE_complex_smul (μ : ℂ) (u : E3) :
    cxE (μ • u) = μ.re • cxE u + μ.im • cxE (Complex.I • u) := by
  rw [complex_smul_eq μ u, map_add, map_smul, map_smul]

theorem I_smul_I_smul (u : E3) : Complex.I • (Complex.I • u) = -u := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

/-! ## The scaling of the unit vector -/

theorem cxOf_smul (c : ℂ) (v : Fin 3 → ℂ) : cxOf (c • v) = c • cxOf v :=
  WithLp.toLp_smul 2 c v

theorem cxOf_smul_real (a : ℝ) (v : Fin 3 → ℂ) : cxOf (a • v) = a • cxOf v :=
  WithLp.toLp_smul 2 a v

/-- Scaling by a positive real does not change the unit vector of the line. -/
theorem cxUnit_smul_pos {v : Fin 3 → ℂ} (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    cxUnit (a • v) = cxUnit v := by
  have hne : ‖cxOf v‖ ≠ 0 := norm_ne_zero_iff.mpr (cxOf_ne_zero hv)
  have hcoe : cxOf (a • v) = a • cxOf v := cxOf_smul_real a v
  have hnorm : ‖a • cxOf v‖ = a * ‖cxOf v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  rw [cxUnit, cxUnit, hcoe, hnorm, smul_smul]
  have hscal : (a * ‖cxOf v‖)⁻¹ * a = ‖cxOf v‖⁻¹ := by
    rw [mul_inv, mul_assoc, mul_comm (‖cxOf v‖)⁻¹ a, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt ha), one_mul]
  rw [hscal]

/-- Scaling by a unit complex number rotates the unit vector. -/
theorem cxUnit_smul_unit {v : Fin 3 → ℂ} (hv : v ≠ 0) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    cxUnit (μ • v) = μ • cxUnit v := by
  have hne : ‖cxOf v‖ ≠ 0 := norm_ne_zero_iff.mpr (cxOf_ne_zero hv)
  have hcoe : cxOf (μ • v) = μ • cxOf v := cxOf_smul μ v
  have hnorm : ‖μ • cxOf v‖ = ‖cxOf v‖ := by rw [norm_smul, hμ, one_mul]
  rw [cxUnit, cxUnit, hcoe, hnorm, smul_comm]

-- **Scaling by a general complex number**: the unit vector picks up the phase `c/‖c‖`. -/
theorem cxUnit_smul {v : Fin 3 → ℂ} (hv : v ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    cxUnit (c • v) = (c / ((‖c‖ : ℝ) : ℂ)) • cxUnit v := by
  have hc0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hcn : (((‖c‖ : ℝ) : ℂ)) ≠ 0 := by simpa using hc0
  have hμ : ‖c / ((‖c‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div]
    have h2 : ‖((‖c‖ : ℝ) : ℂ)‖ = ‖c‖ := by simp
    rw [h2, div_self hc0]
  have hμ0 : c / ((‖c‖ : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hμ; simp at hμ
  have hsplit : c • v = ((‖c‖ : ℝ)) • ((c / ((‖c‖ : ℝ) : ℂ)) • v) := by
    rw [← smul_assoc, Complex.real_smul]
    congr 1
    exact (mul_div_cancel₀ c hcn).symm
  rw [hsplit, cxUnit_smul_pos (v := (c / ((‖c‖ : ℝ) : ℂ)) • v) (smul_ne_zero hμ0 hv)
    (norm_pos_iff.mpr hc), cxUnit_smul_unit hv hμ]

/-! ## The `2 × 2` rotation matrix -/

/-- The `2 × 2` rotation matrix of a complex number `μ`. -/
def probeRotMat (μ : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![μ.re, μ.im; -μ.im, μ.re]

@[simp] theorem probeRotMat_zero_zero (μ : ℂ) : probeRotMat μ 0 0 = μ.re := rfl
@[simp] theorem probeRotMat_zero_one (μ : ℂ) : probeRotMat μ 0 1 = μ.im := rfl
@[simp] theorem probeRotMat_one_zero (μ : ℂ) : probeRotMat μ 1 0 = -μ.im := rfl
@[simp] theorem probeRotMat_one_one (μ : ℂ) : probeRotMat μ 1 1 = μ.re := rfl

theorem probeRotMat_normSq_eq_one {μ : ℂ} (hμ : ‖μ‖ = 1) :
    μ.re * μ.re + μ.im * μ.im = 1 := by
  rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hμ]
  norm_num

/-- The phase `c/‖c‖` of a nonzero complex number has norm one. -/
theorem norm_div_norm_eq_one {c : ℂ} (hc : c ≠ 0) : ‖c / ((‖c‖ : ℝ) : ℂ)‖ = 1 := by
  have hc0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [norm_div]
  have h2 : ‖((‖c‖ : ℝ) : ℂ)‖ = ‖c‖ := by simp
  rw [h2, div_self hc0]

theorem probeRotMat_det {μ : ℂ} (hμ : ‖μ‖ = 1) : (probeRotMat μ).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [probeRotMat_zero_zero, probeRotMat_zero_one, probeRotMat_one_zero,
    probeRotMat_one_one]
  nlinarith [probeRotMat_normSq_eq_one hμ]

theorem probeRotMat_transpose_mul {μ : ℂ} (hμ : ‖μ‖ = 1) :
    (probeRotMat μ).transpose * probeRotMat μ = 1 := by
  have h2 := probeRotMat_normSq_eq_one hμ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_two,
      probeRotMat_zero_zero, probeRotMat_zero_one, probeRotMat_one_zero, probeRotMat_one_one] <;>
    norm_num <;> nlinarith [h2]

/-! ## The block matrix `diag(rotMat μ, 1)` -/

/-- The block matrix `diag(probeRotMat μ, 1)` on `Fin 2 ⊕ Fin (k-2)`. -/
def probeRot (k : ℕ) (μ : ℂ) :
    Matrix (Fin 2 ⊕ Fin (k - 2)) (Fin 2 ⊕ Fin (k - 2)) ℝ :=
  Matrix.fromBlocks (probeRotMat μ) 0 0 1

@[simp] theorem probeRot_inl_inl (k : ℕ) (μ : ℂ) (a b : Fin 2) :
    probeRot k μ (Sum.inl a) (Sum.inl b) = probeRotMat μ a b :=
  Matrix.fromBlocks_apply₁₁ _ _ _ _ _ _

@[simp] theorem probeRot_inl_inr (k : ℕ) (μ : ℂ) (a : Fin 2) (l : Fin (k - 2)) :
    probeRot k μ (Sum.inl a) (Sum.inr l) = 0 :=
  Matrix.fromBlocks_apply₁₂ _ _ _ _ _ _

@[simp] theorem probeRot_inr_inl (k : ℕ) (μ : ℂ) (l : Fin (k - 2)) (a : Fin 2) :
    probeRot k μ (Sum.inr l) (Sum.inl a) = 0 :=
  Matrix.fromBlocks_apply₂₁ _ _ _ _ _ _

@[simp] theorem probeRot_inr_inr (k : ℕ) (μ : ℂ) (l l' : Fin (k - 2)) :
    probeRot k μ (Sum.inr l) (Sum.inr l') = if l = l' then 1 else 0 :=
  Matrix.fromBlocks_apply₂₂ _ _ _ _ _ _

theorem probeRot_det (k : ℕ) (μ : ℂ) (hμ : ‖μ‖ = 1) : (probeRot k μ).det = 1 := by
  rw [probeRot, Matrix.det_fromBlocks_zero₁₂, probeRotMat_det hμ, Matrix.det_one, mul_one]

theorem probeRot_transpose_mul (k : ℕ) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    (probeRot k μ).transpose * probeRot k μ = 1 := by
  rw [probeRot, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    probeRotMat_transpose_mul hμ]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul]
  simpa using (Matrix.fromBlocks_one (l := Fin 2) (m := Fin (k - 2)) (α := ℝ))

theorem isSO_reindex_probeRot (k : ℕ) (hk : 2 ≤ k) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    IsSO (Matrix.reindex (probeSplit k hk) (probeSplit k hk) (probeRot k μ)) := by
  constructor
  · rw [Matrix.reindex_apply, Matrix.transpose_submatrix,
      Matrix.submatrix_mul_equiv (probeRot k μ).transpose (probeRot k μ)
        (probeSplit k hk).symm (probeSplit k hk).symm (probeSplit k hk).symm,
      probeRot_transpose_mul k hμ,
      Matrix.submatrix_one_equiv (probeSplit k hk).symm]
  · rw [Matrix.reindex_apply,
      Matrix.det_submatrix_equiv_self ((probeSplit k hk).symm) (probeRot k μ),
      probeRot_det k μ hμ]

/-- **The rotation matrix of a unit complex number, as an element of `SO(k)`**: it rotates the
first two coordinates and fixes the `k - 2` complement coordinates. -/
noncomputable def probeSO (k : ℕ) (hk : 2 ≤ k) (μ : ℂ) (hμ : ‖μ‖ = 1) : SOk k :=
  ⟨Matrix.reindex (probeSplit k hk) (probeSplit k hk) (probeRot k μ),
    isSO_reindex_probeRot k hk hμ⟩

@[simp] theorem probeSO_val (k : ℕ) (hk : 2 ≤ k) (μ : ℂ) (hμ : ‖μ‖ = 1) :
    (probeSO k hk μ hμ).1 = Matrix.reindex (probeSplit k hk) (probeSplit k hk) (probeRot k μ) :=
  rfl

/-! ## The frame equivariance -/

/-- The linearity of `probeEmb` in the form used below (it avoids the `I •`-subterms). -/
theorem probeEmb_add_smul (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (a b : ℝ) (x y : Amb 6) :
    probeEmb k m hk hm (a • x + b • y)
      = a • probeEmb k m hk hm x + b • probeEmb k m hk hm y := by
  rw [map_add, map_smul, map_smul]

theorem probePairVec_smul_zero_of (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    {μ ν : ℂ} (hcx : cxUnit (μ • v) = ν • cxUnit v) :
    probePairVec k m hk hm (μ • v) 0
      = probeRotMat ν 0 0 • probePairVec k m hk hm v 0
        + probeRotMat ν 1 0 • probePairVec k m hk hm v 1 := by
  rw [probePairVec_zero, probePairVec_zero, probePairVec_one,
    probeRotMat_zero_zero, probeRotMat_one_zero, neg_smul, smul_neg, neg_neg, hcx,
    cxE_complex_smul, probeEmb_add_smul]

theorem probePairVec_smul_one_of (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    {μ ν : ℂ} (hcx : cxUnit (μ • v) = ν • cxUnit v) :
    probePairVec k m hk hm (μ • v) 1
      = probeRotMat ν 0 1 • probePairVec k m hk hm v 0
        + probeRotMat ν 1 1 • probePairVec k m hk hm v 1 := by
  rw [probePairVec_zero, probePairVec_one, probePairVec_one,
    probeRotMat_zero_one, probeRotMat_one_one]
  have h2 : Complex.I • cxUnit (μ • v) = ν • (Complex.I • cxUnit v) := by
    rw [hcx, smul_comm]
  have harg : cxE (Complex.I • cxUnit (μ • v))
      = ν.re • cxE (Complex.I • cxUnit v) + ν.im • (-(cxE (cxUnit v))) := by
    rw [h2, cxE_complex_smul, I_smul_I_smul, map_neg]
  rw [harg, probeEmb_add_smul, map_neg]
  simp only [smul_neg, neg_smul, neg_neg]
  abel

theorem probePairVec_smul_zero (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    {μ : ℂ} (hμ : ‖μ‖ = 1) :
    probePairVec k m hk hm (μ • v) 0
      = probeRotMat μ 0 0 • probePairVec k m hk hm v 0
        + probeRotMat μ 1 0 • probePairVec k m hk hm v 1 :=
  probePairVec_smul_zero_of k m hk hm v (cxUnit_smul_unit hv hμ)

theorem probePairVec_smul_one (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    {μ : ℂ} (hμ : ‖μ‖ = 1) :
    probePairVec k m hk hm (μ • v) 1
      = probeRotMat μ 0 1 • probePairVec k m hk hm v 0
        + probeRotMat μ 1 1 • probePairVec k m hk hm v 1 :=
  probePairVec_smul_one_of k m hk hm v (cxUnit_smul_unit hv hμ)

/-- The Stiefel point of the probe frame. -/
noncomputable def probeStiefelRep (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    (hv : v ≠ 0) : Stiefel k m :=
  ⟨probeFrameRep k m hk hm v, probeFrameRep_orthonormal k m hk hm v hv⟩

@[simp] theorem probeStiefelRep_val (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    (hv : v ≠ 0) : (probeStiefelRep k m hk hm v hv).1 = probeFrameRep k m hk hm v := rfl

theorem smul_ne_zero_of_norm_eq_one {μ : ℂ} (hμ : ‖μ‖ = 1) {v : Fin 3 → ℂ} (hv : v ≠ 0) :
    μ • v ≠ 0 :=
  smul_ne_zero (norm_ne_zero_iff.mp (by rw [hμ]; exact one_ne_zero)) hv

/-- **Frame equivariance, general form**: scaling the representative by `μ` with unit phase `ν`
rotates the probe frame by the block rotation `probeSO k ν`. -/
theorem probeStiefelRep_smul_of (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    (hv : v ≠ 0) {μ ν : ℂ} (hcx : cxUnit (μ • v) = ν • cxUnit v) (hν : ‖ν‖ = 1)
    (hp : μ • v ≠ 0) :
    probeStiefelRep k m hk hm (μ • v) hp
      = (probeSO k hk ν hν).act (probeStiefelRep k m hk hm v hv) := by
  refine Subtype.ext ?_
  show probeFrameRep k m hk hm (μ • v)
    = soActFun (Matrix.reindex (probeSplit k hk) (probeSplit k hk) (probeRot k ν))
        (probeFrameRep k m hk hm v)
  funext j
  obtain ⟨p, rfl⟩ := (probeSplit k hk).surjective j
  have hstep : soActFun (Matrix.reindex (probeSplit k hk) (probeSplit k hk) (probeRot k ν))
        (probeFrameRep k m hk hm v) (probeSplit k hk p)
      = ∑ p' : Fin 2 ⊕ Fin (k - 2), probeRot k ν p' p •
          probeFrameRep k m hk hm v (probeSplit k hk p') := by
    rw [soActFun, ← Equiv.sum_comp (probeSplit k hk)
      (fun j => Matrix.reindex (probeSplit k hk) (probeSplit k hk) (probeRot k ν) j
        (probeSplit k hk p) • probeFrameRep k m hk hm v j)]
    refine Finset.sum_congr rfl (fun p' _ => ?_)
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
  rw [hstep, Fintype.sum_sum_type]
  rcases p with a | l
  · have h0 : (∑ b : Fin 2, probeRot k ν (Sum.inl b) (Sum.inl a) •
        probeFrameRep k m hk hm v (probeSplit k hk (Sum.inl b)))
        = ∑ b : Fin 2, probeRotMat ν b a • probePairVec k m hk hm v b := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [probeRot_inl_inl, probeFrameRep_inl]
    have h1 : (∑ l' : Fin (k - 2), probeRot k ν (Sum.inr l') (Sum.inl a) •
        probeFrameRep k m hk hm v (probeSplit k hk (Sum.inr l'))) = 0 := by
      refine Finset.sum_eq_zero (fun l' _ => ?_)
      rw [probeRot_inr_inl, zero_smul]
    rw [h0, h1, add_zero, probeFrameRep_inl, Fin.sum_univ_two]
    fin_cases a
    · exact probePairVec_smul_zero_of k m hk hm v hcx
    · exact probePairVec_smul_one_of k m hk hm v hcx
  · have h0 : (∑ b : Fin 2, probeRot k ν (Sum.inl b) (Sum.inr l) •
        probeFrameRep k m hk hm v (probeSplit k hk (Sum.inl b))) = 0 := by
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [probeRot_inl_inr, zero_smul]
    have h1 : (∑ l' : Fin (k - 2), probeRot k ν (Sum.inr l') (Sum.inr l) •
        probeFrameRep k m hk hm v (probeSplit k hk (Sum.inr l')))
        = probeTailVec k m hk l := by
      rw [Finset.sum_eq_single l]
      · rw [probeRot_inr_inr, if_pos rfl, one_smul, probeFrameRep_inr]
      · intro l' _ hl'
        rw [probeRot_inr_inr, if_neg hl', zero_smul]
      · intro h; exact absurd (Finset.mem_univ l) h
    rw [h0, h1, zero_add, probeFrameRep_inr]

/-- **Frame equivariance** (unit scalar form). -/
theorem probeStiefelRep_smul (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    {μ : ℂ} (hμ : ‖μ‖ = 1) :
    probeStiefelRep k m hk hm (μ • v) (smul_ne_zero_of_norm_eq_one hμ hv)
      = (probeSO k hk μ hμ).act (probeStiefelRep k m hk hm v hv) :=
  probeStiefelRep_smul_of k m hk hm v hv (cxUnit_smul_unit hv hμ) hμ
    (smul_ne_zero_of_norm_eq_one hμ hv)

/-- **Frame equivariance** for an arbitrary nonzero scalar: the rotation is by the phase `c/‖c‖`. -/
theorem probeStiefelRep_smul_lambda (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    (hv : v ≠ 0) {c : ℂ} (hc : c ≠ 0) (hp : c • v ≠ 0) :
    probeStiefelRep k m hk hm (c • v) hp
      = (probeSO k hk (c / ((‖c‖ : ℝ) : ℂ)) (norm_div_norm_eq_one hc)).act
          (probeStiefelRep k m hk hm v hv) :=
  probeStiefelRep_smul_of k m hk hm v hv (cxUnit_smul hv hc) (norm_div_norm_eq_one hc) hp

/-- **The image in the Grassmannian is invariant under scaling** (general form). -/
theorem ogMk_probeStiefelRep_smul_of (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    (hv : v ≠ 0) {μ ν : ℂ} (hcx : cxUnit (μ • v) = ν • cxUnit v) (hν : ‖ν‖ = 1)
    (hp : μ • v ≠ 0) :
    ogMk k m (probeStiefelRep k m hk hm (μ • v) hp) = ogMk k m (probeStiefelRep k m hk hm v hv) := by
  rw [probeStiefelRep_smul_of k m hk hm v hv hcx hν hp]
  exact Quotient.sound ⟨(probeSO k hk ν hν).transpose,
    (SOk.act_transpose_act (probeSO k hk ν hν) (probeStiefelRep k m hk hm v hv)).symm⟩

/-- **The image in the Grassmannian is invariant under scaling** (unit scalar form). -/
theorem ogMk_probeStiefelRep_smul (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    (hv : v ≠ 0) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    ogMk k m (probeStiefelRep k m hk hm (μ • v) (smul_ne_zero_of_norm_eq_one hμ hv))
      = ogMk k m (probeStiefelRep k m hk hm v hv) :=
  ogMk_probeStiefelRep_smul_of k m hk hm v hv (cxUnit_smul_unit hv hμ) hμ
    (smul_ne_zero_of_norm_eq_one hμ hv)

/-- **The image in the Grassmannian is invariant under scaling** by any nonzero scalar. -/
theorem ogMk_probeStiefelRep_smul_lambda (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    (hv : v ≠ 0) {c : ℂ} (hc : c ≠ 0) (hp : c • v ≠ 0) :
    ogMk k m (probeStiefelRep k m hk hm (c • v) hp) = ogMk k m (probeStiefelRep k m hk hm v hv) :=
  ogMk_probeStiefelRep_smul_of k m hk hm v hv (cxUnit_smul hv hc) (norm_div_norm_eq_one hc) hp

end

end Work.ThomBordism.Grassmann
