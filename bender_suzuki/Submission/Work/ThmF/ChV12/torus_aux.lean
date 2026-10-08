import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 800000

namespace Work.ThmF.ChV12

/-- In a finite field `F` of characteristic `2` with `3 ∣ Nat.card F + 1`, the polynomial
`X² + X + 1` has no root. -/
theorem torus_no_root {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (h3 : 3 ∣ Nat.card F + 1) (t : F) (h : t ^ 2 + t + 1 = 0) : False := by
  have ht3 : t ^ 3 = 1 := by
    have h4 : t ^ 3 - 1 = 0 := by
      rw [show t ^ 3 - 1 = (t - 1) * (t ^ 2 + t + 1) from by ring, h, mul_zero]
    exact sub_eq_zero.mp h4
  have ht0 : t ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1] at h
    have h3' : (3 : F) = 0 := by linear_combination h
    rw [show (3 : F) = ((3 : ℕ) : F) from by norm_num, CharP.cast_eq_zero_iff] at h3'
    omega
  have hord : orderOf t = 3 := by
    have hdvd : orderOf t ∣ 3 := orderOf_dvd_of_pow_eq_one ht3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ht1
    · exact h1
  have hu : orderOf (Units.mk0 t ht0) = 3 := by
    have h2 : orderOf ((Units.mk0 t ht0 : Fˣ) : F) = 3 := by simpa using hord
    rwa [orderOf_units] at h2
  have hdvd2 : 3 ∣ Nat.card Fˣ := by rw [← hu]; exact orderOf_dvd_natCard _
  rw [Nat.card_units] at hdvd2
  have : 3 ∣ Nat.card F := by omega
  omega

/-- For a field `F` of characteristic `2` and `c ∈ SL(2,F)` of order `3`, one has
`c * c + c + 1 = 0` (as matrices). -/
theorem sl2_order_three_sq {F : Type*} [Field F] [CharP F 2]
    (c : Matrix.SpecialLinearGroup (Fin 2) F) (hc : orderOf c = 3) :
    (c : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F)
      + (c : Matrix (Fin 2) (Fin 2) F) + 1 = 0 := by
  set cm : Matrix (Fin 2) (Fin 2) F := (c : Matrix (Fin 2) (Fin 2) F) with hcm
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have h3 : cm ^ 3 = 1 := by
    have h : ((c ^ 3 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [hc3, Matrix.SpecialLinearGroup.coe_one]
    rw [Matrix.SpecialLinearGroup.coe_pow] at h
    rwa [← hcm] at h
  have hne : c ≠ 1 := by intro h; rw [h, orderOf_one] at hc; omega
  have hCH : cm * cm + cm.trace • cm + 1 = 0 := by
    have h := Matrix.aeval_self_charpoly cm
    rw [Matrix.charpoly_fin_two cm] at h
    have h' : cm * cm - cm.trace • cm + cm.det • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
      simpa [pow_two, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_one] using h
    have hdet : cm.det = 1 := by rw [hcm]; exact Matrix.SpecialLinearGroup.det_coe c
    rw [hdet, one_smul, sub_eq_add_neg, CharTwo.neg_eq] at h'
    exact h'
  have hsq : cm * cm = cm.trace • cm + 1 := by
    have h : cm * cm + (cm.trace • cm + 1) = 0 := by rw [← add_assoc]; exact hCH
    rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]
  have htr2 : (cm * cm).trace = cm.trace ^ 2 := by
    rw [hsq, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      CharP.cast_eq_zero F 2, smul_eq_mul, pow_two, add_zero]
  have htr3 : (cm ^ 3).trace = cm.trace ^ 3 + cm.trace := by
    have e : cm ^ 3 = cm * (cm * cm) := by rw [pow_succ', pow_two]
    have hexp : cm ^ 3 = (cm.trace * cm.trace) • cm
        + cm.trace • (1 : Matrix (Fin 2) (Fin 2) F) + cm := by
      rw [e, hsq, mul_add, mul_one, mul_smul_comm, hsq, smul_add, smul_smul]
    rw [hexp, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_one, Fintype.card_fin, CharP.cast_eq_zero F 2]
    simp only [smul_eq_mul, mul_zero, add_zero, pow_succ, pow_two]
    ring
  have ht : cm.trace = 1 := by
    have h0 : (cm ^ 3).trace = 0 := by
      rw [h3, Matrix.trace_one, Fintype.card_fin, CharP.cast_eq_zero F 2]
    rw [htr3] at h0
    have hfact : cm.trace * (cm.trace ^ 2 + 1) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp hfact with hz | hz
    · exfalso
      have hcm2 : cm * cm = 1 := by rw [hsq, hz, zero_smul, zero_add]
      have hcm1 : cm = 1 := by
        have he : cm ^ 3 = cm := by rw [pow_succ', pow_two, hcm2, mul_one]
        rw [h3] at he; exact he.symm
      exact hne (Subtype.ext (by rw [← hcm, hcm1, Matrix.SpecialLinearGroup.coe_one]))
    · have h2 : cm.trace ^ 2 = 1 := by
        have hh : cm.trace ^ 2 = -1 := add_eq_zero_iff_eq_neg.mp hz
        rw [hh, CharTwo.neg_eq]
      have : cm.trace = 1 := by
        rw [← one_pow 2] at h2
        exact CharTwo.sq_inj.mp h2
      exact this
  rw [ht, one_smul] at hCH
  exact hCH

/-- For a field `F` of characteristic `2` and a `2 × 2` matrix `c` with `c * c + c + 1 = 0`
such that `X² + X + 1` has no root in `F`, the centralizer of `c` in `M₂(F)` is the span of
`1` and `c`. -/
theorem matrix_centralizer_eq_span {F : Type*} [Field F] [CharP F 2]
    {c : Matrix (Fin 2) (Fin 2) F} (hc : c * c + c + 1 = 0)
    (hroot : ∀ t : F, t ^ 2 + t + 1 ≠ 0) (M : Matrix (Fin 2) (Fin 2) F) :
    M * c = c * M ↔ ∃ p q : F, M = p • (1 : Matrix (Fin 2) (Fin 2) F) + q • c := by
  constructor
  · intro hM
    have hc00 : c 0 0 * c 0 0 + c 0 1 * c 1 0 + c 0 0 + 1 = 0 := by
      have h := congrFun (congrFun hc 0) 0
      simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] using h
    have hy : c 0 1 ≠ 0 := by
      intro h0
      rw [h0, zero_mul, add_zero] at hc00
      exact hroot (c 0 0) (by rw [pow_two]; exact hc00)
    have hM10 : M 0 1 * c 1 0 = c 0 1 * M 1 0 := by
      have h := congrFun (congrFun hM 0) 0
      have h' : M 0 0 * c 0 0 + M 0 1 * c 1 0 = c 0 0 * M 0 0 + c 0 1 * M 1 0 := by
        simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] using h
      linear_combination h'
    have hM01 : M 0 0 * c 0 1 + M 0 1 * c 1 1 = c 0 0 * M 0 1 + c 0 1 * M 1 1 := by
      have h := congrFun (congrFun hM 0) 1
      simpa [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] using h
    refine ⟨M 0 0 + (M 0 1 / c 0 1) * c 0 0, M 0 1 / c 0 1, ?_⟩
    have hq : M 0 1 / c 0 1 * c 0 1 = M 0 1 := div_mul_cancel₀ _ hy
    have hqc : M 0 1 / c 0 1 * c 1 0 = M 1 0 := by
      rw [div_mul_eq_mul_div, div_eq_iff hy]
      linear_combination hM10
    have hq1 : M 0 0 + (M 0 1 / c 0 1) * c 1 1 = c 0 0 * (M 0 1 / c 0 1) + M 1 1 := by
      field_simp
      linear_combination hM01
    have hM11 : M 1 1
        = M 0 0 + (M 0 1 / c 0 1) * c 1 1 + c 0 0 * (M 0 1 / c 0 1) := by
      rw [hq1]
      rw [show c 0 0 * (M 0 1 / c 0 1) + M 1 1 + c 0 0 * (M 0 1 / c 0 1) = M 1 1 from by
        rw [show c 0 0 * (M 0 1 / c 0 1) + M 1 1 + c 0 0 * (M 0 1 / c 0 1)
            = M 1 1 + (c 0 0 * (M 0 1 / c 0 1) + c 0 0 * (M 0 1 / c 0 1)) from by abel,
          CharTwo.add_self_eq_zero, add_zero]]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    · -- (0,0)
      rw [show M 0 0 + M 0 1 / c 0 1 * c 0 0 + M 0 1 / c 0 1 * c 0 0
          = M 0 0 + (M 0 1 / c 0 1 * c 0 0 + M 0 1 / c 0 1 * c 0 0) from add_assoc ..,
        show M 0 1 / c 0 1 * c 0 0 + M 0 1 / c 0 1 * c 0 0 = 0 from
          CharTwo.add_self_eq_zero _, add_zero]
    · -- (0,1)
      exact hq.symm
    · -- (1,0)
      exact hqc.symm
    · -- (1,1)
      rw [hM11, mul_comm (c 0 0) (M 0 1 / c 0 1)]
      abel
  · rintro ⟨p, q, rfl⟩
    rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one]

/-- Cayley–Hamilton in the form used below: for a `2 × 2` matrix over a field of
characteristic `2`, `M * M = trace M • M + det M • 1`. -/
theorem mul_self_eq {F : Type*} [Field F] [CharP F 2] (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h := Matrix.aeval_self_charpoly M
  rw [Matrix.charpoly_fin_two M] at h
  have h' : M * M - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
    simpa [pow_two, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_one] using h
  rw [sub_eq_add_neg, CharTwo.neg_eq] at h'
  have h2 : M * M + (M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) F)) = 0 := by
    rw [← add_assoc]; exact h'
  rw [eq_neg_of_add_eq_zero_left h2, CharTwo.neg_eq]

/-- The trace of the square of a `2 × 2` matrix over a field of characteristic `2` is the
square of its trace. -/
theorem trace_mul_self {F : Type*} [Field F] [CharP F 2] (M : Matrix (Fin 2) (Fin 2) F) :
    (M * M).trace = M.trace ^ 2 := by
  rw [mul_self_eq M, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, CharP.cast_eq_zero F 2, smul_zero, add_zero, smul_eq_mul, pow_two]

/-- For a `2 × 2` matrix over a field of characteristic `2` with `M * M + M + 1 = 0` and
`det M = 1`, the trace of `M` is `1`. -/
theorem sl2_trace_eq_one {F : Type*} [Field F] [CharP F 2]
    {c : Matrix (Fin 2) (Fin 2) F} (hd : c.det = 1) (hc : c * c + c + 1 = 0) :
    c.trace = 1 := by
  have htr : c.trace ^ 2 + c.trace = 0 := by
    have h := congrArg Matrix.trace hc
    rw [Matrix.trace_add, Matrix.trace_add, trace_mul_self, Matrix.trace_one,
      Fintype.card_fin, CharP.cast_eq_zero F 2, add_zero] at h
    simpa using h
  have hfac : c.trace * (c.trace + 1) = 0 := by linear_combination htr
  rcases mul_eq_zero.mp hfac with hz | hz
  · exfalso
    have hcm : c * c = 1 := by
      rw [mul_self_eq c, hz, zero_smul, hd, one_smul, zero_add]
    have hzero : c = 0 := by
      have h := hc
      rw [hcm] at h
      have hcc : (1 : Matrix (Fin 2) (Fin 2) F) + c + 1 = c := by
        rw [show (1 : Matrix (Fin 2) (Fin 2) F) + c + 1 = (1 + 1) + c from by abel,
          CharTwo.add_self_eq_zero, zero_add]
      rw [hcc] at h
      exact h
    rw [hzero] at hd
    simp at hd
  · have : c.trace = -1 := add_eq_zero_iff_eq_neg.mp hz
    rw [this, CharTwo.neg_eq]

/-- The determinant of `a • 1 + b • c` for a `2 × 2` matrix `c`. -/
theorem det_smul_one_add_smul {F : Type*} [Field F] (a b : F)
    (c : Matrix (Fin 2) (Fin 2) F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • c).det
      = a ^ 2 + a * b * c.trace + b ^ 2 * c.det := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply]
  simp
  ring

end Work.ThmF.ChV12
