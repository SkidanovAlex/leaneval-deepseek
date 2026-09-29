import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.RedProj.so2_tools

/-!
# The right polar factor `K = O (OᵀO)^{-1/2}` of a `2 × 2` matrix of determinant `1`

For `O` with `det O = 1`, `N = OᵀO` is symmetric with determinant `1` and `N + 1` is positive
definite; with `S = √(tr N + 2)` and `P = S⁻¹ • (N + 1)` one has `P² = N`, `Pᵀ = P`, `det P = 1`,
so `P` is the positive square root of `N`.  The polar factor is
`K = O P⁻¹ = S⁻¹ • (O * (N + 1).adjugate)` and satisfies `K Kᵀ = 1`, `det K = 1`.

We also prove the equivariance `K (R O R') = R K O R'` for orthogonal `R, R'` with `det R' = 1`
and the analyticity of the entries `x ↦ K (O x) i j` for an analytic `O`.
-/

namespace Work.TMComp.RedProj

open Work.TMContract

noncomputable section

/-- Cayley–Hamilton for `2 × 2` matrices: `A² = (tr A) A - (det A) 1`. -/
theorem cob_two_CH (A : Matrix (Fin 2) (Fin 2) ℝ) : A * A = A.trace • A - A.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.smul_apply, Matrix.one_apply] <;> ring

theorem cob_det_add_one (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (A + 1).det = A.det + A.trace + 1 := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.one_apply,
    Fin.isValue, Fin.reduceEq, ↓reduceIte]
  ring

/-- `N O = Oᵀ O`. -/
def cobN (O : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.transpose O * O

/-- `√(tr (OᵀO) + 2)`. -/
def cobS (O : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := Real.sqrt ((cobN O).trace + 2)

/-- `P = (OᵀO)^{1/2} = S⁻¹ • (OᵀO + 1)`. -/
def cobP (O : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (cobS O)⁻¹ • (cobN O + 1)

/-- The polar factor `K = O P⁻¹ = S⁻¹ • (O * (OᵀO + 1).adjugate)`. -/
def cobK (O : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (cobS O)⁻¹ • (O * (cobN O + 1).adjugate)

theorem cobN_transpose (O : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.transpose (cobN O) = cobN O := by
  simp only [cobN, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem cobN_trace_nonneg (O : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ (cobN O).trace := by
  simp only [cobN, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply]
  nlinarith [sq_nonneg (O 0 0), sq_nonneg (O 1 0), sq_nonneg (O 0 1), sq_nonneg (O 1 1)]

theorem cobN_trace_add_two_pos (O : Matrix (Fin 2) (Fin 2) ℝ) : 0 < (cobN O).trace + 2 := by
  have := cobN_trace_nonneg O; linarith

theorem cobN_det (O : Matrix (Fin 2) (Fin 2) ℝ) : (cobN O).det = O.det * O.det := by
  rw [cobN, Matrix.det_mul, Matrix.det_transpose]

theorem cobS_pos (O : Matrix (Fin 2) (Fin 2) ℝ) : 0 < cobS O :=
  Real.sqrt_pos.2 (cobN_trace_add_two_pos O)

theorem cobS_sq (O : Matrix (Fin 2) (Fin 2) ℝ) : cobS O ^ 2 = (cobN O).trace + 2 :=
  Real.sq_sqrt (le_of_lt (cobN_trace_add_two_pos O))

theorem cobS_ne_zero (O : Matrix (Fin 2) (Fin 2) ℝ) : cobS O ≠ 0 := ne_of_gt (cobS_pos O)

theorem cobS_mul_self (O : Matrix (Fin 2) (Fin 2) ℝ) :
    cobS O * cobS O = (cobN O).trace + 2 := by
  rw [← pow_two, cobS_sq]

theorem cobP_transpose (O : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.transpose (cobP O) = cobP O := by
  simp only [cobP, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one,
    cobN_transpose]

theorem cobP_mul_self (O : Matrix (Fin 2) (Fin 2) ℝ) (hdet : O.det = 1) :
    cobP O * cobP O = cobN O := by
  have hdetN : (cobN O).det = 1 := by rw [cobN_det, hdet]; norm_num
  have h1 : (cobN O + 1) * (cobN O + 1) = ((cobN O).trace + 2) • cobN O := by
    calc (cobN O + 1) * (cobN O + 1)
        = cobN O * cobN O + cobN O + cobN O + 1 := by noncomm_ring
      _ = ((cobN O).trace • cobN O - (cobN O).det • 1) + cobN O + cobN O + 1 := by
          rw [cob_two_CH]
      _ = ((cobN O).trace + 2) • cobN O := by rw [hdetN]; module
  have hS0 : cobS O ≠ 0 := cobS_ne_zero O
  have hcoef : (cobS O)⁻¹ * (cobS O)⁻¹ * ((cobN O).trace + 2) = 1 := by
    rw [← cobS_mul_self O]; field_simp
  rw [cobP, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1, smul_smul, hcoef, one_smul]

theorem cobP_det (O : Matrix (Fin 2) (Fin 2) ℝ) (hdet : O.det = 1) : (cobP O).det = 1 := by
  have hdetN : (cobN O).det = 1 := by rw [cobN_det, hdet]; norm_num
  rw [cobP, Matrix.det_smul, cob_det_add_one, hdetN, Fintype.card_fin, pow_two]
  rw [show (1 : ℝ) + (cobN O).trace + 1 = (cobN O).trace + 2 by ring]
  rw [← cobS_mul_self O]
  have hS0 : cobS O ≠ 0 := cobS_ne_zero O
  field_simp

theorem cobK_of_O (O : Matrix (Fin 2) (Fin 2) ℝ) : cobK O = O * (cobP O).adjugate := by
  rw [cobK, cobP, Matrix.adjugate_smul, Fintype.card_fin]
  rw [Matrix.mul_smul]
  norm_num

theorem cobP_inv_eq_adjugate (O : Matrix (Fin 2) (Fin 2) ℝ) (hdet : O.det = 1) :
    (cobP O)⁻¹ = (cobP O).adjugate := by
  rw [Matrix.inv_eq_right_inv]
  rw [Matrix.mul_adjugate, cobP_det O hdet, one_smul]

theorem cobK_det (O : Matrix (Fin 2) (Fin 2) ℝ) (hdet : O.det = 1) : (cobK O).det = 1 := by
  have hdetN : (cobN O).det = 1 := by rw [cobN_det, hdet]; norm_num
  have hS0 : cobS O ≠ 0 := cobS_ne_zero O
  rw [cobK, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_adjugate,
    Fintype.card_fin, cob_det_add_one, hdetN, hdet]
  norm_num
  rw [show (1 : ℝ) + (cobN O).trace + 1 = (cobN O).trace + 2 by ring, ← cobS_mul_self O]
  field_simp

theorem cobK_orth (O : Matrix (Fin 2) (Fin 2) ℝ) (hdet : O.det = 1) :
    cobK O * Matrix.transpose (cobK O) = 1 := by
  have hOunit : IsUnit O.det := by rw [hdet]; exact isUnit_one
  have hOtunit : IsUnit (Matrix.transpose O).det := by
    rw [Matrix.det_transpose]; exact hOunit
  have hK : cobK O = O * (cobP O)⁻¹ := by
    rw [cobK_of_O O, cobP_inv_eq_adjugate O hdet]
  have hPP : (cobP O)⁻¹ * (cobP O)⁻¹ = (cobN O)⁻¹ := by
    rw [← Matrix.mul_inv_rev, cobP_mul_self O hdet]
  have hNN : (cobN O)⁻¹ = O⁻¹ * (Matrix.transpose O)⁻¹ := by
    rw [cobN, Matrix.mul_inv_rev]
  rw [hK, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, cobP_transpose]
  calc O * (cobP O)⁻¹ * ((cobP O)⁻¹ * Matrix.transpose O)
      = O * ((cobP O)⁻¹ * (cobP O)⁻¹) * Matrix.transpose O := by noncomm_ring
    _ = O * (cobN O)⁻¹ * Matrix.transpose O := by rw [hPP]
    _ = O * (O⁻¹ * (Matrix.transpose O)⁻¹) * Matrix.transpose O := by rw [hNN]
    _ = 1 := by
        rw [← mul_assoc, Matrix.mul_nonsing_inv O hOunit, one_mul,
          Matrix.nonsing_inv_mul (Matrix.transpose O) hOtunit]

/-- The equivariance of the polar factor under conjugation by orthogonal matrices. -/
theorem cobK_conj (R O R' : Matrix (Fin 2) (Fin 2) ℝ)
    (hRt : Matrix.transpose R * R = 1) (hR't : Matrix.transpose R' * R' = 1)
    (hR' : R' * Matrix.transpose R' = 1) (hdR' : R'.det = 1) :
    cobK (R * O * R') = R * cobK O * R' := by
  have hN : cobN (R * O * R') = Matrix.transpose R' * cobN O * R' := by
    calc cobN (R * O * R')
        = (Matrix.transpose R' * Matrix.transpose O * Matrix.transpose R) * (R * O * R') := by
          rw [cobN, Matrix.transpose_mul, Matrix.transpose_mul]
          noncomm_ring
      _ = Matrix.transpose R' * Matrix.transpose O * (Matrix.transpose R * R) * O * R' := by
          noncomm_ring
      _ = Matrix.transpose R' * cobN O * R' := by rw [hRt, cobN]; noncomm_ring
  have htr : (cobN (R * O * R')).trace = (cobN O).trace := by
    rw [hN, Matrix.trace_mul_comm (Matrix.transpose R' * cobN O) R']
    rw [show R' * (Matrix.transpose R' * cobN O) = (R' * Matrix.transpose R') * cobN O by
      noncomm_ring, hR', one_mul]
  have hadjR' : (R').adjugate = Matrix.transpose R' := by
    have h1 : R' * R'.adjugate = 1 := by rw [Matrix.mul_adjugate, hdR', one_smul]
    rw [← Matrix.inv_eq_right_inv h1, Matrix.inv_eq_right_inv hR']
  have hadjR't : (Matrix.transpose R').adjugate = R' := by
    have h1 : Matrix.transpose R' * (Matrix.transpose R').adjugate = 1 := by
      rw [Matrix.mul_adjugate, Matrix.det_transpose, hdR', one_smul]
    rw [← Matrix.inv_eq_right_inv h1, Matrix.inv_eq_right_inv hR't]
  have hadj : (cobN (R * O * R') + 1).adjugate
      = Matrix.transpose R' * (cobN O + 1).adjugate * R' := by
    rw [hN]
    rw [show Matrix.transpose R' * cobN O * R' + 1
        = Matrix.transpose R' * (cobN O + 1) * R' by
      rw [mul_add, add_mul, mul_one, hR't]]
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadjR', hadjR't]
    noncomm_ring
  have hS : cobS (R * O * R') = cobS O := by simp only [cobS, htr]
  rw [cobK, cobK, hS, hadj]
  rw [show R * O * R' * (Matrix.transpose R' * (cobN O + 1).adjugate * R')
      = R * O * (R' * Matrix.transpose R') * (cobN O + 1).adjugate * R' by noncomm_ring, hR']
  noncomm_ring

theorem cobK_analytic {O : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hO : ∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ) (i j : Fin 2) :
    AnalyticOnNhd ℝ (fun x => cobK (O x) i j) Set.univ := by
  have hN : ∀ a b : Fin 2, AnalyticOnNhd ℝ (fun x => cobN (O x) a b) Set.univ := by
    intro a b x _
    simp only [cobN, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    exact ((hO 0 a x trivial).mul (hO 0 b x trivial)).add
      ((hO 1 a x trivial).mul (hO 1 b x trivial))
  have hT : AnalyticOnNhd ℝ (fun x => (cobN (O x)).trace + 2) Set.univ := by
    intro x _
    simp only [Matrix.trace_fin_two]
    exact ((hN 0 0 x trivial).add (hN 1 1 x trivial)).add analyticAt_const
  have hS : AnalyticOnNhd ℝ (fun x => cobS (O x)) Set.univ :=
    analyticOnNhd_sqrt hT fun x _ => cobN_trace_add_two_pos (O x)
  have hSi : AnalyticOnNhd ℝ (fun x => (cobS (O x))⁻¹) Set.univ := by
    intro x _
    exact (hS x trivial).inv (cobS_ne_zero (O x))
  have hone : AnalyticOnNhd ℝ (fun _ : ℝ => (1 : ℝ)) Set.univ := analyticOnNhd_const
  have hAdj : ∀ a b : Fin 2,
      AnalyticOnNhd ℝ (fun x => ((cobN (O x) + 1).adjugate) a b) Set.univ := by
    intro a b
    fin_cases a <;> fin_cases b
    · refine AnalyticOnNhd.congr isOpen_univ ((hN 1 1).add hone) ?_
      intro y _
      show cobN (O y) 1 1 + 1 = ((cobN (O y) + 1).adjugate) 0 0
      rw [Matrix.adjugate_fin_two]; simp
    · refine AnalyticOnNhd.congr isOpen_univ ((hN 0 1).neg) ?_
      intro y _
      show -(cobN (O y) 0 1) = ((cobN (O y) + 1).adjugate) 0 1
      rw [Matrix.adjugate_fin_two]; simp
    · refine AnalyticOnNhd.congr isOpen_univ ((hN 1 0).neg) ?_
      intro y _
      show -(cobN (O y) 1 0) = ((cobN (O y) + 1).adjugate) 1 0
      rw [Matrix.adjugate_fin_two]; simp
    · refine AnalyticOnNhd.congr isOpen_univ ((hN 0 0).add hone) ?_
      intro y _
      show cobN (O y) 0 0 + 1 = ((cobN (O y) + 1).adjugate) 1 1
      rw [Matrix.adjugate_fin_two]; simp
  have hM : ∀ a b : Fin 2,
      AnalyticOnNhd ℝ (fun x => (O x * (cobN (O x) + 1).adjugate) a b) Set.univ := by
    intro a b x _
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact ((hO a 0 x trivial).mul (hAdj 0 b x trivial)).add
      ((hO a 1 x trivial).mul (hAdj 1 b x trivial))
  intro x _
  have h1 : AnalyticAt ℝ (fun y => (cobS (O y))⁻¹) x := hSi x trivial
  have h2 : AnalyticAt ℝ (fun y => (O y * (cobN (O y) + 1).adjugate) i j) x := hM i j x trivial
  refine (h1.mul h2).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [cobK, Matrix.smul_apply, smul_eq_mul, Pi.mul_apply]


/-! ## Elementary facts about the rotations `rot` -/

theorem cob_rot_mul' (a b : ℝ) : rot a * rot b = rot (a + b) := by
  have hc : 2 * Real.pi * (a + b) = 2 * Real.pi * a + 2 * Real.pi * b := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, hc, Real.cos_add, Real.sin_add] <;> ring

theorem cob_rot_zero : rot 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot]

theorem cob_rot_transpose (a : ℝ) : Matrix.transpose (rot a) = rot (-a) := by
  have h1 : 2 * Real.pi * (-a) = -(2 * Real.pi * a) := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.transpose_apply, h1, Real.cos_neg, Real.sin_neg]

theorem cob_rot_det (a : ℝ) : (rot a).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [rot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * a)]

theorem cob_rot_orth (a : ℝ) : Matrix.transpose (rot a) * rot a = 1 := by
  rw [cob_rot_transpose, cob_rot_mul', neg_add_cancel, cob_rot_zero]

theorem cob_rot_orth' (a : ℝ) : rot a * Matrix.transpose (rot a) = 1 := by
  rw [cob_rot_transpose, cob_rot_mul', add_neg_cancel, cob_rot_zero]

/-- **Polar (`SO(2)`) factor of an analytic `SL(2,ℝ)`-valued cocycle.**  See the file header. -/
theorem cob_polar_factor (α c : ℝ) (φ : ℝ → ℝ) (O : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hO : ∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ)
    (hper : ∀ x, O (x + 1) = O x) (hdet : ∀ x, (O x).det = 1)
    (hconj : ∀ x, O (x + α) * rot (φ x) = rot c * O x) :
    ∃ K : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      (∀ i j, AnalyticOnNhd ℝ (fun x => K x i j) Set.univ) ∧
      (∀ x, K (x + 1) = K x) ∧
      (∀ x, K x * Matrix.transpose (K x) = 1) ∧ (∀ x, (K x).det = 1) ∧
      (∀ x, K (x + α) = rot c * K x * rot (-(φ x))) := by
  have hA : ∀ x, O (x + α) = rot c * O x * rot (-(φ x)) := by
    intro x
    have h2 := hconj x
    calc O (x + α)
        = O (x + α) * (rot (φ x) * rot (-(φ x))) := by
          rw [cob_rot_mul', add_neg_cancel, cob_rot_zero, mul_one]
      _ = O (x + α) * rot (φ x) * rot (-(φ x)) := by noncomm_ring
      _ = rot c * O x * rot (-(φ x)) := by rw [h2]
  refine ⟨fun x => cobK (O x), fun i j => cobK_analytic hO i j, ?_, ?_, ?_, ?_⟩
  · intro x
    show cobK (O (x + 1)) = cobK (O x)
    rw [hper x]
  · intro x; exact cobK_orth (O x) (hdet x)
  · intro x; exact cobK_det (O x) (hdet x)
  · intro x
    show cobK (O (x + α)) = rot c * cobK (O x) * rot (-(φ x))
    rw [hA x]
    exact cobK_conj (rot c) (O x) (rot (-(φ x))) (cob_rot_orth c) (cob_rot_orth (-(φ x)))
      (cob_rot_orth' (-(φ x))) (cob_rot_det (-(φ x)))

end

end Work.TMComp.RedProj
