import Mathlib
import Submission.Work.TMC14Core.RatRot

/-!
# `rotQ` is an integer iff the `q`-step monodromy has `|trace| ≥ 2`

For the rational frequency `p/q` the `q`-step Prüfer map `qMap p q lam E x` is a monotone
degree-one lift of the projective action of the `q`-step transfer matrix
`M = iterR (p/q) lam E q x` (`pruferIter_isPosLift`), and `rotQ p q lam E x` is by definition
the rotation number of this lift.  Since `M` is unimodular, its projective action fixes a
direction exactly when `M` has a real eigenvector, i.e. exactly when `|tr M| ≥ 2`; and a
(positive) lift fixes such a direction exactly when its rotation number is an integer.

The module is self-contained: it only uses the definitions and the Prüfer facts of
`Submission.Work.TMC14Core.RatRot` / `Submission.Work.TMComp.RotBasics`.
-/

open Work.TMComp.RotBasics

noncomputable section

namespace Work.TMC14Core

/-! ## The `q`-step Prüfer map as a `CircleDeg1Lift` -/

/-- The `q`-step Prüfer map of the fibre `x`, as a monotone degree-one circle lift. -/
private def qLift (p : ℤ) (q : ℕ) (lam E x : ℝ) : CircleDeg1Lift where
  toOrderHom := ⟨qMap p q lam E x, pruferIter_mono_t ((p : ℝ) / (q : ℝ)) lam E q x⟩
  map_add_one' := fun t => pruferIter_add_one ((p : ℝ) / (q : ℝ)) lam E q x t

private theorem continuous_qLift (p : ℤ) (q : ℕ) (lam E x : ℝ) :
    Continuous ⇑(qLift p q lam E x) := by
  change Continuous (fun t : ℝ => Work.TMContract.pruferIter ((p : ℝ) / (q : ℝ)) lam E q x t)
  exact (Work.TMComp.IDSPrufer.pruferIter_continuous ((p : ℝ) / (q : ℝ)) lam E q).comp
    (Continuous.prodMk continuous_const continuous_id)

/-- `rotQ` is the translation number of the `q`-step Prüfer lift. -/
private theorem rotQ_eq_translationNumber (p : ℤ) (q : ℕ) (lam E x : ℝ) :
    rotQ p q lam E x = (qLift p q lam E x).translationNumber := by
  have hseq : (fun m : ℕ => qIter p q lam E x m / (m : ℝ))
      = fun m : ℕ => ((qLift p q lam E x) ^ m) 0 / (m : ℝ) := by
    funext m
    congr 1
    simp only [qIter, CircleDeg1Lift.coe_pow]
    rfl
  rw [rotQ, hseq]
  exact (CircleDeg1Lift.tendsto_translation_number₀ _).limUnder_eq

/-! ## Unimodularity of the `q`-step transfer matrix -/

private theorem iterR_det (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    (iterR α lam E n x).det = 1 := by
  induction n with
  | zero => exact Matrix.det_one
  | succ n ih =>
    simp only [iterR]
    rw [Matrix.det_mul, ih, mul_one]
    simp [Work.TMContract.tmR, Matrix.det_fin_two]

/-! ## Real eigenvalues of a unimodular `2 × 2` matrix, and `|trace| ≥ 2` -/

private lemma exists_root_quadratic_le (t : ℝ) (ht : 2 ≤ |t|) :
    ∃ l : ℝ, l ^ 2 - t * l + 1 = 0 := by
  refine ⟨(t + Real.sqrt (t ^ 2 - 4)) / 2, ?_⟩
  have hpos : 0 ≤ t ^ 2 - 4 := by nlinarith [sq_abs t, abs_nonneg t]
  have hssq : (Real.sqrt (t ^ 2 - 4)) ^ 2 = t ^ 2 - 4 := Real.sq_sqrt hpos
  nlinarith [hssq]

/-- A unimodular real `2 × 2` matrix with `|trace| ≥ 2` has a nonzero real eigenvector with
nonzero eigenvalue. -/
private lemma exists_eigvec_of_det_one_le (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det = 1)
    (htr : 2 ≤ |M.trace|) :
    ∃ (l : ℝ) (v : Fin 2 → ℝ), l ≠ 0 ∧ v ≠ 0 ∧ M.mulVec v = l • v := by
  obtain ⟨l, hl⟩ := exists_root_quadratic_le M.trace htr
  have hlne : l ≠ 0 := by
    intro h; rw [h] at hl; norm_num at hl
  have hA : (Matrix.scalar (Fin 2) l - M).det = 0 := by
    rw [← Matrix.eval_charpoly M l, Matrix.charpoly_fin_two]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [hdet]
    linarith [hl]
  obtain ⟨v, hv_ne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
  refine ⟨l, v, hlne, hv_ne, ?_⟩
  have hscalar : Matrix.scalar (Fin 2) l = l • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
  rw [hscalar, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv.symm

/-- Conversely, a unimodular real `2 × 2` matrix with a nonzero real eigenvector has
`|trace| ≥ 2`. -/
private lemma two_le_abs_trace_of_eigvec (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det = 1)
    {l : ℝ} {v : Fin 2 → ℝ} (hv : v ≠ 0) (heig : M.mulVec v = l • v) :
    2 ≤ |M.trace| := by
  have hzero : (l • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heig, sub_self]
  have hdet0 : (l • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hzero⟩
  have hchar : l ^ 2 - M.trace * l + 1 = 0 := by
    have hscalar : Matrix.scalar (Fin 2) l = l • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j; by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
    have hcf := Matrix.eval_charpoly M l
    rw [hscalar] at hcf
    rw [← hcf] at hdet0
    rw [Matrix.charpoly_fin_two] at hdet0
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hdet0
    rw [hdet] at hdet0
    linarith
  have hlne : l ≠ 0 := by
    intro h; rw [h] at hchar; norm_num at hchar
  have htr_eq : M.trace = l + l⁻¹ := by
    have h2 : M.trace * l = l ^ 2 + 1 := by linarith
    field_simp
    linarith
  have htr2 : 4 ≤ M.trace ^ 2 := by
    rw [htr_eq]
    have heq : (l + l⁻¹) ^ 2 = 4 + (l - l⁻¹) ^ 2 := by field_simp; ring
    rw [heq]
    nlinarith [sq_nonneg (l - l⁻¹)]
  nlinarith [sq_abs M.trace, abs_nonneg M.trace]

/-! ## Directions, eigenvectors and fixed points of a positive lift -/

/-- The complex number with real coordinates `v 0, v 1`. -/
private lemma smul_complex_eq (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    smul M (⟨v 0, v 1⟩ : ℂ) = ⟨(M.mulVec v) 0, (M.mulVec v) 1⟩ := by
  refine Complex.ext ?_ ?_
  · simp only [smul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp only [smul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Every nonzero complex number is a positive multiple of some circle point `vc t0`. -/
private lemma exists_vc_eq_unit (w : ℂ) (hw : w ≠ 0) :
    ∃ t0 : ℝ, vc t0 = (‖w‖)⁻¹ • w := by
  refine ⟨w.arg / Real.pi, ?_⟩
  refine Complex.ext ?_ ?_
  · simp only [vc]
    rw [show Real.pi * (w.arg / Real.pi) = w.arg by field_simp, Complex.cos_arg hw]
    rw [Complex.smul_re, smul_eq_mul, div_eq_inv_mul]
  · simp only [vc]
    rw [show Real.pi * (w.arg / Real.pi) = w.arg by field_simp, Complex.sin_arg]
    rw [Complex.smul_im, smul_eq_mul, div_eq_inv_mul]

/-- A half-turn shift negates a circle point. -/
private lemma vc_add_one (t : ℝ) : vc (t + 1) = -vc t := by
  have h := vc_add_int (1 : ℤ) t
  simp only [Int.cast_one] at h
  rw [show (1 : ℝ) + t = t + 1 by ring] at h
  rw [h]
  norm_num

/-- A nonzero complex eigenvector of a real matrix is a real eigenvector. -/
private lemma exists_eigvec_of_smul (M : Matrix (Fin 2) (Fin 2) ℝ) {w : ℂ} (hw : w ≠ 0)
    {l : ℝ} (h : smul M w = l • w) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ M.mulVec v = l • v := by
  let v : Fin 2 → ℝ := fun i => if i = 0 then w.re else w.im
  have hv01 : (⟨v 0, v 1⟩ : ℂ) = w := by
    refine Complex.ext ?_ ?_ <;> simp [v]
  have hvne : v ≠ 0 := by
    intro hv0
    apply hw
    have h0 : w.re = 0 := by have := congrFun hv0 0; simpa [v] using this
    have h1 : w.im = 0 := by have := congrFun hv0 1; simpa [v] using this
    exact Complex.ext h0 h1
  have hbridge : smul M w = (⟨(M.mulVec v) 0, (M.mulVec v) 1⟩ : ℂ) := by
    rw [← hv01]; exact smul_complex_eq M v
  have hcomp : (l • w : ℂ) = (⟨(l • v) 0, (l • v) 1⟩ : ℂ) := by
    refine Complex.ext ?_ ?_ <;> simp [v, Pi.smul_apply, smul_eq_mul]
  have heq : (⟨(M.mulVec v) 0, (M.mulVec v) 1⟩ : ℂ) = ⟨(l • v) 0, (l • v) 1⟩ := by
    rw [← hbridge, h, hcomp]
  refine ⟨v, hvne, ?_⟩
  funext i
  rcases Complex.ext_iff.mp heq with ⟨h0, h1⟩
  fin_cases i
  · exact h0
  · exact h1

/-- A positive lift of a matrix with a real eigenvector fixes the corresponding direction, so
its translation number is an integer. -/
private lemma exists_fixed_point_of_eigvec
    (M : Matrix (Fin 2) (Fin 2) ℝ) (G : CircleDeg1Lift)
    (hG : IsPosLift M ⇑G)
    {l : ℝ} (hl : l ≠ 0) {v : Fin 2 → ℝ} (hv : v ≠ 0)
    (heig : M.mulVec v = l • v) :
    ∃ k : ℤ, G.translationNumber = (k : ℝ) := by
  set w : ℂ := ⟨v 0, v 1⟩ with hw_def
  have hw : w ≠ 0 := by
    intro h
    apply hv
    funext i
    fin_cases i
    · have : w.re = 0 := by rw [h]; simp
      simpa [hw_def] using this
    · have : w.im = 0 := by rw [h]; simp
      simpa [hw_def] using this
  have heigC : smul M w = l • w := by
    rw [hw_def, smul_complex_eq, heig]
    refine Complex.ext ?_ ?_
    · simp only [Pi.smul_apply, Complex.smul_re, smul_eq_mul]
    · simp only [Pi.smul_apply, Complex.smul_im, smul_eq_mul]
  obtain ⟨t0, hvc⟩ := exists_vc_eq_unit w hw
  have hsmul : smul M (vc t0) = l • vc t0 := by
    rw [hvc, smul_smul_real, heigC, smul_smul, smul_smul]
    congr 1
    ring
  have hnorm : ‖smul M (vc t0)‖ = |l| := by
    rw [hsmul, norm_smul_real, vc_norm, mul_one]
  have hkey : (|l| : ℝ) • vc (G t0) = l • vc t0 := by
    rw [← hnorm, ← hG t0]
    exact hsmul
  have hlabs : (0 : ℝ) < |l| := abs_pos.mpr hl
  have hvcG : vc (G t0) = (l / |l|) • vc t0 := by
    have h1 : (|l|)⁻¹ • ((|l| : ℝ) • vc (G t0)) = vc (G t0) := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hlabs), one_smul]
    calc vc (G t0) = (|l|)⁻¹ • ((|l| : ℝ) • vc (G t0)) := h1.symm
      _ = (|l|)⁻¹ • (l • vc t0) := by rw [hkey]
      _ = (l / |l|) • vc t0 := by rw [smul_smul]; congr 1; field_simp
  have hc : l / |l| = 1 ∨ l / |l| = -1 := by
    rcases lt_or_gt_of_ne (Ne.symm hl) with hpos | hneg
    · left; rw [abs_of_pos hpos]; field_simp
    · right; rw [abs_of_neg hneg]; field_simp
  obtain ⟨j, hj⟩ : ∃ j : ℤ, vc (G t0) = vc (t0 + j) := by
    rcases hc with hc1 | hc1
    · refine ⟨0, ?_⟩
      simp only [Int.cast_zero, add_zero]
      rw [hvcG, hc1, one_smul]
    · refine ⟨1, ?_⟩
      simp only [Int.cast_one]
      rw [hvcG, hc1, vc_add_one]
      simp
  obtain ⟨m, hm⟩ := vc_eq_iff hj
  refine ⟨j + m * 2, ?_⟩
  refine CircleDeg1Lift.translationNumber_of_eq_add_int G (x := t0) ?_
  push_cast
  linarith

/-! ## The main theorem -/

theorem rotQ_int_iff_trace (p : ℤ) (q : ℕ) (lam E x : ℝ) (hq : 1 ≤ q) :
    ((∃ k : ℤ, Work.TMC14Core.rotQ p q lam E x = (k : ℝ)) ↔
      2 ≤ |(Work.TMComp.RotBasics.iterR ((p : ℝ) / (q : ℝ)) lam E q x).trace|) := by
  set M : Matrix (Fin 2) (Fin 2) ℝ := iterR ((p : ℝ) / (q : ℝ)) lam E q x with hM
  have hdet : M.det = 1 := by rw [hM]; exact iterR_det _ _ _ _ _
  have hlift : IsPosLift M ⇑(qLift p q lam E x) := by
    rw [hM]
    exact pruferIter_isPosLift ((p : ℝ) / (q : ℝ)) lam E q x
  have htrans : rotQ p q lam E x = (qLift p q lam E x).translationNumber :=
    rotQ_eq_translationNumber p q lam E x
  constructor
  · rintro ⟨k, hk⟩
    have hk' : (qLift p q lam E x).translationNumber = (k : ℝ) := by
      rw [← htrans]; exact hk
    obtain ⟨t0, ht0⟩ := (CircleDeg1Lift.translationNumber_eq_int_iff (qLift p q lam E x)
      (continuous_qLift p q lam E x)).mp hk'
    have hIsPos := hlift t0
    have hvc1 : vc ((qLift p q lam E x) t0) = ((-1 : ℝ) ^ k) • vc t0 := by
      rw [show (qLift p q lam E x) t0 = t0 + (k : ℝ) from ht0,
        show t0 + (k : ℝ) = (k : ℝ) + t0 by ring, vc_add_int]
    have heig : smul M (vc t0) = (‖smul M (vc t0)‖ * ((-1 : ℝ) ^ k)) • vc t0 := by
      calc smul M (vc t0) = ‖smul M (vc t0)‖ • vc ((qLift p q lam E x) t0) := hIsPos
        _ = ‖smul M (vc t0)‖ • (((-1 : ℝ) ^ k) • vc t0) := by rw [hvc1]
        _ = (‖smul M (vc t0)‖ * ((-1 : ℝ) ^ k)) • vc t0 := by rw [smul_smul]
    have hw : vc t0 ≠ 0 := vc_ne_zero t0
    obtain ⟨v, hvne, heigv⟩ := exists_eigvec_of_smul M hw heig
    have hthis := two_le_abs_trace_of_eigvec M hdet hvne heigv
    rwa [hM] at hthis
  · intro htr
    have htrM : 2 ≤ |M.trace| := by rw [hM]; exact htr
    obtain ⟨l, v, hl, hvne, heigv⟩ := exists_eigvec_of_det_one_le M hdet htrM
    obtain ⟨k, hk⟩ := exists_fixed_point_of_eigvec M (qLift p q lam E x) hlift hl hvne heigv
    exact ⟨k, by rw [htrans, hk]⟩

end Work.TMC14Core
