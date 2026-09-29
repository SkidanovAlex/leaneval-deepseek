import Mathlib
import Submission.Work.TMComp.LocCantor.Bloch

/-!
# The determinant of the Bloch matrix is a constant multiple of `i`

(Fundamental step of AJ section 5, items (5.1)-(5.12), used to build the conjugacy between the
dual cocycle and the rotation `R_theta`.)

Let `U = fourier u` be the Fourier transform of `u`, satisfying

* the Bloch scalar identity
  `2 cos(2 pi x) U(x) + lam e^{2 pi i theta} U(x+alpha) + lam e^{-2 pi i theta} U(x-alpha) = E U(x)`,
* continuity and `1`-periodicity of `U`.

Writing `W(x) = (U(x) e^{2 pi i theta}, U(x-alpha))` for the Bloch vector, the scalar identity is
exactly the statement that `W(x+alpha) = e^{-2 pi i theta} S_{lam^-1,E/lam}(x) W(x)` with
`det S = 1`.  Hence the matrix `M(x) = [W(x), conj W(x)]` -- whose determinant is nothing but
`(blochMat alpha theta u x).det` -- satisfies `det M(x+alpha) = det M(x)`, while the periodicity
of `U` gives `det M(x+1) = det M(x)`.  As `alpha` is irrational and `x |-> det M(x)` is
continuous, it is constant; and it is always purely imaginary because `det M = F - conj F` with
`F = W_0 conj W_1`.  This is the content of `Work.TMComp.LocCantor.det_blochMat_const`.
-/

noncomputable section

open scoped ComplexConjugate

namespace Work.TMComp.LocCantor

open Work.TMComp

/-! ## Elementary facts about complex conjugation and purely imaginary numbers -/

/-- `conj (e^{-2 pi i theta}) = e^{2 pi i theta}`. -/
theorem conj_exp_neg_two_pi_theta (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-(2 * Real.pi * θ * Complex.I)))
      = Complex.exp (2 * Real.pi * θ * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/-- A complex number with vanishing real part is `c * I` for the real number `c = z.im`. -/
theorem eq_im_mul_I_of_re_eq_zero {z : ℂ} (h : z.re = 0) :
    z = ((z.im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.mul_re, Complex.I_re, Complex.I_im, h]
  · simp [Complex.mul_im, Complex.I_re, Complex.I_im]

/-! ## The determinant of `blochMat` as `F - conj F` -/

/-- `det (blochMat alpha theta u x) = W0 * conj W1 - conj W0 * W1`
where `W0 = blochVec alpha theta u x 0`, `W1 = blochVec alpha theta u x 1`, i.e. it is
`F - conj F` with `F = W0 * conj W1`. -/
theorem det_blochMat_eq_sub_conj (α θ : ℝ) (u : ℤ → ℂ) (x : ℝ) :
    (blochMat α θ u x).det
      = blochVec α θ u x 0 * (starRingEnd ℂ) (blochVec α θ u x 1)
        - (starRingEnd ℂ)
            (blochVec α θ u x 0 * (starRingEnd ℂ) (blochVec α θ u x 1)) := by
  rw [Matrix.det_fin_two]
  simp only [blochMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.isValue, map_mul, Complex.conj_conj]

/-- The determinant of `blochMat α θ u x` is purely imaginary. -/
theorem det_blochMat_re_zero (α θ : ℝ) (u : ℤ → ℂ) (x : ℝ) :
    ((blochMat α θ u x).det).re = 0 := by
  rw [det_blochMat_eq_sub_conj]
  simp only [Complex.sub_re, Complex.conj_re, sub_self]

/-! ## Continuity and the period `1` -/

/-- `x |-> det (blochMat α θ u x)` is continuous as soon as `U = fourier u` is. -/
theorem continuous_det_blochMat {α θ : ℝ} {u : ℤ → ℂ}
    (hcont : Continuous (fourier u)) :
    Continuous fun x => (blochMat α θ u x).det := by
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    · simp only [blochMat, blochVec, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue, map_mul]
      fun_prop

/-- `1`-periodicity of `U` gives `1`-periodicity of `x |-> det (blochMat α θ u x)`. -/
theorem det_blochMat_add_one {α θ : ℝ} {u : ℤ → ℂ}
    (hper : ∀ x, fourier u (x + 1) = fourier u x) (x : ℝ) :
    (blochMat α θ u (x + 1)).det = (blochMat α θ u x).det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [blochMat, blochVec, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue]
  rw [show x + 1 - α = (x - α) + 1 by ring, hper (x - α), hper x]

/-! ## The period `α` -/

/-- The Bloch relation `W(x+α) = e^{-2 pi i theta} S(x) W(x)` (componentwise form, with
`det S = 1`) implies the invariance of the determinant under `x |-> x + α`. -/
theorem det_blochMat_shift {α θ lam E : ℝ} {u : ℤ → ℂ}
    (hident : ∀ x : ℝ,
      (((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) * fourier u x
        + (lam : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u (x + α)
        + (lam : ℂ) * Complex.exp (-(2 * Real.pi * θ * Complex.I)) * fourier u (x - α)
      = (E : ℂ) * fourier u x)
    (hlam : lam ≠ 0) (x : ℝ) :
    (blochMat α θ u (x + α)).det = (blochMat α θ u x).det := by
  have h0 := bloch_component0 hident hlam x
  have h1 := bloch_component1 (α := α) (θ := θ) (u := u) x
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [blochMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.isValue]
  rw [h0, h1]
  rw [map_mul, map_mul, map_sub, map_mul, conj_exp_neg_two_pi_theta]
  simp only [Complex.conj_ofReal]
  linear_combination
    (blochVec α θ u x 0 * (starRingEnd ℂ) (blochVec α θ u x 1)
      - (starRingEnd ℂ) (blochVec α θ u x 0) * blochVec α θ u x 1)
    * (exp_neg_mul_exp (2 * Real.pi * θ * Complex.I))

/-! ## A continuous function with periods `1` and an irrational `α` is constant -/

/-- A continuous `ℂ`-valued function with periods `1` and an irrational `α` is constant:
the stabilizer `{y | forall x, f (x+y) = f x}` is an additive subgroup containing `1` and `α`,
hence contains the dense subgroup `closure {α, 1} = ℤ + αℤ`. -/
theorem cont_eq_const_of_period (f : ℝ → ℂ) (hf : Continuous f) {α : ℝ} (hα : Irrational α)
    (h1 : ∀ x, f (x + 1) = f x) (ha : ∀ x, f (x + α) = f x) :
    ∃ c : ℂ, ∀ x, f x = c := by
  let G : AddSubgroup ℝ :=
    { carrier := {y | ∀ x, f (x + y) = f x}
      zero_mem' := by intro x; simp
      add_mem' := by
        intro a b ha' hb' x
        rw [← add_assoc, hb' (x + a), ha' x]
      neg_mem' := by
        intro a ha' x
        have h := ha' (x + (-a))
        have h' : x + -a + a = x := by ring
        rw [h'] at h
        exact h.symm }
  have hone : (1 : ℝ) ∈ G := by intro x; simpa using h1 x
  have halpha : α ∈ G := by intro x; simpa using ha x
  have hsub : (AddSubgroup.closure ({α, 1} : Set ℝ) : Set ℝ) ⊆ (G : Set ℝ) := by
    rw [SetLike.coe_subset_coe, AddSubgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact halpha
    · exact hone
  have hdense : Dense (AddSubgroup.closure ({α, 1} : Set ℝ) : Set ℝ) := by
    rw [dense_addSubgroupClosure_pair_iff]
    simpa using hα
  have hSclosed : IsClosed {y : ℝ | f y = f 0} := isClosed_eq hf continuous_const
  have hsubS : (AddSubgroup.closure ({α, 1} : Set ℝ) : Set ℝ) ⊆ {y : ℝ | f y = f 0} := by
    intro y hy
    have hyG : y ∈ G := hsub hy
    have := hyG 0
    simpa using this
  have hdenseS : Dense {y : ℝ | f y = f 0} := hdense.mono hsubS
  refine ⟨f 0, fun x => ?_⟩
  have huniv : closure {y : ℝ | f y = f 0} = Set.univ := hdenseS.closure_eq
  rw [hSclosed.closure_eq] at huniv
  have : x ∈ {y : ℝ | f y = f 0} := by rw [huniv]; trivial
  exact this

/-! ## The main statement -/

theorem det_blochMat_const {α θ lam E : ℝ} {u : ℤ → ℂ} (hα : Irrational α) (hlam : lam ≠ 0)
    (hcont : Continuous (Work.TMComp.fourier u))
    (hper : ∀ x, Work.TMComp.fourier u (x + 1) = Work.TMComp.fourier u x)
    (hident : ∀ x : ℝ,
      (((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) * Work.TMComp.fourier u x
        + (lam : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I) * Work.TMComp.fourier u (x + α)
        + (lam : ℂ) * Complex.exp (-(2 * Real.pi * θ * Complex.I)) * Work.TMComp.fourier u (x - α)
      = (E : ℂ) * Work.TMComp.fourier u x) :
    ∃ c : ℝ, ∀ x, (Work.TMComp.blochMat α θ u x).det = (c : ℂ) * Complex.I := by
  have hcont_det : Continuous fun x => (Work.TMComp.blochMat α θ u x).det :=
    continuous_det_blochMat hcont
  obtain ⟨c, hc⟩ :=
    cont_eq_const_of_period (fun x => (Work.TMComp.blochMat α θ u x).det) hcont_det hα
      (fun x => det_blochMat_add_one hper x)
      (fun x => det_blochMat_shift hident hlam x)
  have hcim : c = ((c.im : ℝ) : ℂ) * Complex.I := by
    rw [show c = (Work.TMComp.blochMat α θ u 0).det from (hc 0).symm]
    exact eq_im_mul_I_of_re_eq_zero (det_blochMat_re_zero α θ u 0)
  exact ⟨c.im, fun x => by rw [hc x]; exact hcim⟩

end Work.TMComp.LocCantor
