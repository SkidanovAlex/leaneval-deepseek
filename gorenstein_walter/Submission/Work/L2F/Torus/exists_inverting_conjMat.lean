import Mathlib
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Mat2.quadAlgebra
import Submission.Work.L2F.Conic.exists_sq_sub_mul_sq

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Torus

/-! ## A traceless `V` with `V * V = D • 1` (`D ≠ 0`) is conjugate to `quadT D`

Writing `V = !![a, b; c, -a]`, the matrix of the basis `(u, V *ᵥ u)` for `u = !![1; t]` is
`P t = !![1, a + b*t; t, c - a*t]`, and `V * P t = P t * quadT D` because the second column of
`V * P t` is `V *ᵥ (V *ᵥ u) = D • u`.  Since `det (P t) = c - 2*a*t - b*t^2` is not the zero
polynomial as soon as `V ≠ 0` (evaluate at `t = 0, 1, 2`), some `t` gives `det (P t) ≠ 0`. -/
theorem exists_conj_quadT_of_traceless {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (V : Matrix (Fin 2) (Fin 2) F) (D : F) (hVtr : V.trace = 0)
    (hV2 : V * V = D • (1 : Matrix (Fin 2) (Fin 2) F)) (hD : D ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, P.det ≠ 0 ∧ P⁻¹ * V * P = Work.L2F.Mat2.quadT D := by
  have hV11 : V 1 1 = - V 0 0 := by
    have h := hVtr
    rw [Matrix.trace_fin_two] at h
    exact eq_neg_of_add_eq_zero_right h
  have h00 : V 0 0 * V 0 0 + V 0 1 * V 1 0 = D := by
    have h := congrFun (congrFun hV2 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    exact h
  set a : F := V 0 0 with ha
  set b : F := V 0 1 with hb
  set c : F := V 1 0 with hc
  have hD' : a * a + b * c = D := by rw [ha, hb, hc]; exact h00
  have hVeq : V = !![a, b; c, -a] := by
    rw [Matrix.eta_fin_two V, hV11, ← ha, ← hb, ← hc]
  have habc : ¬(a = 0 ∧ b = 0 ∧ c = 0) := by
    rintro ⟨ha0, hb0, hc0⟩
    rw [ha0, hb0, hc0] at hD'
    simp at hD'
    exact hD hD'.symm
  -- Some `t` has `det (!![1, a + b*t; t, c - a*t]) ≠ 0`, i.e. `c - 2*a*t - b*t^2 ≠ 0`.
  have key : ∃ t : F, c - 2 * a * t - b * t ^ 2 ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_ne_iff] at hcon
    have hc0 : c = 0 := by simpa using hcon 0
    have h1 : c - 2 * a - b = 0 := by simpa using hcon 1
    have h2' : c - 4 * a - 4 * b = 0 := by
      have ht := hcon 2
      have h : c - 2 * a * 2 - b * 2 ^ 2 = c - 4 * a - 4 * b := by ring
      rw [h] at ht; exact ht
    have e1 : 2 * a + b = 0 := by linear_combination -h1 + hc0
    have e2 : 4 * a + 4 * b = 0 := by linear_combination -h2' + hc0
    have e3 : 2 * b = 0 := by
      have hh : (4 : F) * a + 4 * b = 2 * (2 * a + b) + 2 * b := by ring
      rw [hh, e1, mul_zero, zero_add] at e2
      exact e2
    have hb0 : b = 0 := by
      rcases mul_eq_zero.mp e3 with hh | hh
      · exact absurd hh h2
      · exact hh
    have ha0 : a = 0 := by
      rw [hb0, add_zero] at e1
      exact (mul_eq_zero.mp e1).resolve_left h2
    exact habc ⟨ha0, hb0, hc0⟩
  obtain ⟨t, ht⟩ := key
  set P : Matrix (Fin 2) (Fin 2) F := !![1, a + b * t; t, c - a * t] with hP
  have hPdetval : (!![1, a + b * t; t, c - a * t] : Matrix (Fin 2) (Fin 2) F).det
      = c - 2 * a * t - b * t ^ 2 := by
    rw [Matrix.det_fin_two]; simp; ring
  have hPdet : P.det ≠ 0 := by rw [hP, hPdetval]; exact ht
  -- The matrix `P` is the matrix of the basis `(u, V *ᵥ u)`, so `V * P = P * quadT D`.
  have hVP : V * P = P * Work.L2F.Mat2.quadT D := by
    rw [hP, hVeq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Work.L2F.Mat2.quadT]
    all_goals (try rw [← hD'])
    all_goals ring
  refine ⟨P, hPdet, ?_⟩
  calc P⁻¹ * V * P = P⁻¹ * (V * P) := by rw [Matrix.mul_assoc]
    _ = P⁻¹ * (P * Work.L2F.Mat2.quadT D) := by rw [hVP]
    _ = (P⁻¹ * P) * Work.L2F.Mat2.quadT D := by rw [Matrix.mul_assoc]
    _ = Work.L2F.Mat2.quadT D := by
          rw [Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hPdet), Matrix.one_mul]

/-- For `x ∈ SL(2,F)` with `disc F x ≠ 0` there is `w ∈ SL(2,F)` with `w * w = -1` (the
nontrivial central element) whose conjugation sends the traceless part `conjMat F x` to its
negative -- equivalently `w * x * w⁻¹ = x⁻¹`. -/
theorem exists_inverting_conjMat (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F) (hD : disc F x ≠ 0) : ∃ w : Matrix.SpecialLinearGroup (Fin 2) F, w * w = Work.L2F.negOne F ∧ conjNeg F w (conjMat F x) := by
  -- `V = conjMat F x` is traceless with `V * V = D • 1`, `D = disc F x ≠ 0`.
  set V : Matrix (Fin 2) (Fin 2) F := conjMat F x with hV
  set D : F := disc F x with hDf
  have hDne : D ≠ 0 := by rw [hDf]; exact hD
  have hVtr : V.trace = 0 := by rw [hV]; exact conjMat_trace F x
  have hV2 : V * V = D • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hV, hDf]; exact conjMat_mul_self F x
  -- Conjugate `V` to `quadT D`.
  obtain ⟨P, hPdet, hP⟩ := exists_conj_quadT_of_traceless h2 V D hVtr hV2 hDne
  -- Solve `p ^ 2 - D * q ^ 2 = -1`.
  obtain ⟨p, q, hpq⟩ := Work.L2F.Conic.exists_sq_sub_mul_sq F h2 D hDne (-1)
  set w0 : Matrix (Fin 2) (Fin 2) F := Work.L2F.Mat2.hypWMat D p q with hw0
  have hw0det : w0.det = 1 := by rw [hw0]; exact Work.L2F.Mat2.hypWMat_det D p q hpq
  have hw0ne : w0.det ≠ 0 := by rw [hw0det]; exact one_ne_zero
  have hw0sq : w0 * w0 = -(1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hw0, Work.L2F.Mat2.hypWMat_mul_self, hpq]
    simp
  have hw0T : w0 * Work.L2F.Mat2.quadT D = -(Work.L2F.Mat2.quadT D * w0) := by
    rw [hw0]; exact Work.L2F.Mat2.hypWMat_mul_quadT D p q
  have huP : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  have hPinvP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P huP
  have hPPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P huP
  have hVeq : V = P * Work.L2F.Mat2.quadT D * P⁻¹ := by
    calc V = (P * P⁻¹) * V * (P * P⁻¹) := by rw [hPPinv, Matrix.one_mul, Matrix.mul_one]
      _ = P * (P⁻¹ * V * P) * P⁻¹ := by noncomm_ring
      _ = P * Work.L2F.Mat2.quadT D * P⁻¹ := by rw [hP]
  -- The candidate inverting element `w = P * w0 * P⁻¹`.
  set w : Matrix (Fin 2) (Fin 2) F := P * w0 * P⁻¹ with hw
  have hdetPinv : P⁻¹.det = (P.det)⁻¹ :=
    eq_inv_of_mul_eq_one_left (Matrix.det_nonsing_inv_mul_det P huP)
  have hwdet : w.det = 1 := by
    rw [hw, Matrix.det_mul, Matrix.det_mul, hw0det, hdetPinv, mul_one, mul_inv_cancel₀ hPdet]
  have hwne : w.det ≠ 0 := by rw [hwdet]; exact one_ne_zero
  have hwsq : w * w = -(1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hw]
    calc (P * w0 * P⁻¹) * (P * w0 * P⁻¹)
        = P * w0 * (P⁻¹ * P) * w0 * P⁻¹ := by noncomm_ring
      _ = P * (w0 * w0) * P⁻¹ := by rw [hPinvP]; noncomm_ring
      _ = P * (-(1 : Matrix (Fin 2) (Fin 2) F)) * P⁻¹ := by rw [hw0sq]
      _ = -(P * P⁻¹) := by noncomm_ring
      _ = -(1 : Matrix (Fin 2) (Fin 2) F) := by rw [hPPinv]
  have hant : w * V = -(V * w) := by
    rw [hw, hVeq]
    calc (P * w0 * P⁻¹) * (P * Work.L2F.Mat2.quadT D * P⁻¹)
        = P * (w0 * (P⁻¹ * P) * Work.L2F.Mat2.quadT D * P⁻¹) := by noncomm_ring
      _ = P * (w0 * Work.L2F.Mat2.quadT D * P⁻¹) := by rw [hPinvP]; noncomm_ring
      _ = P * (-(Work.L2F.Mat2.quadT D * w0) * P⁻¹) := by rw [hw0T]
      _ = -(P * (Work.L2F.Mat2.quadT D * (P⁻¹ * P) * w0 * P⁻¹)) := by
            rw [hPinvP]; noncomm_ring
      _ = -((P * Work.L2F.Mat2.quadT D * P⁻¹) * (P * w0 * P⁻¹)) := by noncomm_ring
  have hconj : w * V * w⁻¹ = -V := by
    have hw1 : w * w⁻¹ = 1 := Matrix.mul_nonsing_inv w (isUnit_iff_ne_zero.mpr hwne)
    calc w * V * w⁻¹ = (w * V) * w⁻¹ := rfl
      _ = (-(V * w)) * w⁻¹ := by rw [hant]
      _ = -(V * (w * w⁻¹)) := by noncomm_ring
      _ = -(V * 1) := by rw [hw1]
      _ = -V := by rw [Matrix.mul_one]
  have hn : ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -(1 : Matrix (Fin 2) (Fin 2) F) := rfl
  refine ⟨⟨w, hwdet⟩, ?_, ?_⟩
  · apply Subtype.ext
    simp only [hn]
    show w * w = -(1 : Matrix (Fin 2) (Fin 2) F)
    exact hwsq
  · show w * conjMat F x * w⁻¹ = -(conjMat F x)
    rw [← hV]
    exact hconj

end Work.L2F.Torus
