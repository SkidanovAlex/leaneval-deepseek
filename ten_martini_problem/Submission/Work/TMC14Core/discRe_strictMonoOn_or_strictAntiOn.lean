import Mathlib
import Submission.Work.TMC14Core.RatRot
import Submission.Work.TMC14Core.disc_im_eq_zero
import Submission.Work.TMC14Core.strictMonoOn_or_strictAntiOn_of_deriv_ne_zero
import Submission.Work.TMC14Core.ceyTraceOdd
import Submission.Work.TMC14Core.traceUnitaryLe
import Submission.Work.TMC14Core.adjugateHermitianRankOne
import Submission.Work.TMC14Core.ceyDerivBound
import Submission.Work.TMC14Core.adjugateTraceCharpolyDeriv
import Submission.Work.TMC14Core.existsBlochMatCharpolyRoot
import Submission.Work.TMC14Core.discDerivNeZeroEven

namespace Work.TMC14Core

open Polynomial

/-- The real polynomial whose coefficients are the real parts of the coefficients of `p`. -/
noncomputable def rePoly (p : Polynomial ℂ) : Polynomial ℝ :=
  p.sum fun k a => Polynomial.C a.re * Polynomial.X ^ k

lemma rePoly_eval (p : Polynomial ℂ) (x : ℝ) :
    (rePoly p).eval x = (p.eval (x:ℂ)).re := by
  have hR : (p.eval (x:ℂ)).re = p.sum (fun n a => a.re * x ^ n) := by
    rw [← Polynomial.eval₂_id, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
    rw [show (∑ n ∈ p.support, (RingHom.id ℂ) (p.coeff n) * (x:ℂ) ^ n).re
          = ∑ n ∈ p.support, ((RingHom.id ℂ) (p.coeff n) * (x:ℂ) ^ n).re from
        map_sum Complex.reAddGroupHom _ _]
    apply Finset.sum_congr rfl
    intro n _
    rw [RingHom.id_apply, Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have hL : (rePoly p).eval x = p.sum (fun n a => a.re * x ^ n) := by
    rw [rePoly, ← Polynomial.eval₂_id, Polynomial.eval₂_sum, Polynomial.sum_def,
      Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro n _
    simp [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rw [hL, hR]

lemma rePoly_coeff (p : Polynomial ℂ) (k : ℕ) : (rePoly p).coeff k = (p.coeff k).re := by
  rw [rePoly, Polynomial.coeff_sum, Polynomial.sum_def]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hbk
    rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
    simp [hbk]
  · intro hk
    have hpk : p.coeff k = 0 := Polynomial.notMem_support_iff.mp hk
    rw [hpk]
    simp

lemma deriv_rePoly (p : Polynomial ℂ) :
    Polynomial.derivative (rePoly p) = rePoly (Polynomial.derivative p) := by
  ext k
  simp only [Polynomial.coeff_derivative, rePoly_coeff]
  simp [Complex.mul_re]

lemma polyC_eq_zero_of_forall_real_eval (p : Polynomial ℂ)
    (h : ∀ x : ℝ, p.eval (x:ℂ) = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun i : Fin (p.natDegree + 1) => ((i:ℝ):ℂ))
  · intro i j hij
    simp only [Complex.ofReal_inj] at hij
    exact Fin.ext (Nat.cast_injective hij)
  · intro i; exact h _
  · simp

lemma eval_map_star (p : Polynomial ℂ) (x : ℝ) :
    (p.map (starRingEnd ℂ)).eval (x:ℂ) = star (p.eval (x:ℂ)) := by
  have hx : starRingEnd ℂ (x:ℂ) = (x:ℂ) := by simp
  have h := Polynomial.eval₂_at_apply (f := starRingEnd ℂ) (p := p) (x:ℂ)
  rw [hx] at h
  rw [Polynomial.eval_map]
  exact h

lemma star_eval_eq_self (p : Polynomial ℂ) (x : ℝ) (h : (p.eval (x:ℂ)).im = 0) :
    star (p.eval (x:ℂ)) = p.eval (x:ℂ) := by
  rw [Complex.star_def]
  exact Complex.conj_eq_iff_im.mpr h

lemma map_star_eq_self_of_im_eval_eq_zero (p : Polynomial ℂ)
    (h : ∀ x : ℝ, (p.eval (x:ℂ)).im = 0) : p.map (starRingEnd ℂ) = p := by
  have hzero : p.map (starRingEnd ℂ) - p = 0 := by
    apply polyC_eq_zero_of_forall_real_eval
    intro x
    rw [Polynomial.eval_sub, sub_eq_zero, eval_map_star, star_eval_eq_self p x (h x)]
  exact sub_eq_zero.mp hzero

lemma im_derivative_eval_eq_zero (p : Polynomial ℂ)
    (h : ∀ x : ℝ, (p.eval (x:ℂ)).im = 0) (x : ℝ) :
    ((Polynomial.derivative p).eval (x:ℂ)).im = 0 := by
  have hmap : Polynomial.derivative p = (Polynomial.derivative p).map (starRingEnd ℂ) := by
    have := Polynomial.derivative_map p (starRingEnd ℂ)
    rwa [map_star_eq_self_of_im_eval_eq_zero p h] at this
  have h2 : star ((Polynomial.derivative p).eval (x:ℂ))
      = (Polynomial.derivative p).eval (x:ℂ) := by
    rw [← eval_map_star (Polynomial.derivative p) x, ← hmap]
  rw [Complex.star_def] at h2
  exact Complex.conj_eq_iff_im.mp h2

/-- A scalar matrix is a scalar multiple of the identity. -/
lemma scalar_eq_smul_one {n : ℕ} (z : ℂ) :
    Matrix.scalar (Fin n) z = z • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  rw [Matrix.scalar_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

/-- `Δ'(E) ≠ 0` on the spectral range, odd `q` (assembly from the CEY story). -/
theorem disc_deriv_ne_zero_odd_self (p : ℤ) (q m : ℕ) (lam : ℝ) (hm : q = 2 * m + 1)
    (hq : 1 ≤ q) (hpq : Nat.Coprime p.natAbs q) (hlam : 0 < lam) (E : ℝ)
    (hU : ‖(disc p q lam).eval (E : ℂ)‖ ≤ 2 + 2 * lam ^ q) :
    (Polynomial.derivative (disc p q lam)).eval (E : ℂ) ≠ 0 := by
  obtain ⟨θ, k, hroot⟩ : ∃ θ k : ℝ, (blochMat p q lam θ k).charpoly.eval (E : ℂ) = 0 :=
    existsBlochMatCharpolyRoot p q lam hq hpq hlam E hU
  set z : ℂ := (E : ℂ) with hzdef
  set M : Matrix (Fin q) (Fin q) ℂ := blochMat p q lam θ k with hMdef
  have hroot' : M.charpoly.eval z = 0 := hroot
  have hdet : (Matrix.scalar (Fin q) z - M).det = 0 := by
    rw [← Matrix.eval_charpoly M z]; exact hroot'
  obtain ⟨v, hv, hNv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hzs : IsSelfAdjoint z := by
    rw [hzdef]; exact (Complex.im_eq_zero_iff_isSelfAdjoint (E : ℂ)).mp (Complex.ofReal_im E)
  have hHerm : (Matrix.scalar (Fin q) z - M).IsHermitian := by
    rw [hMdef, scalar_eq_smul_one]
    exact (Matrix.isHermitian_one (n := Fin q)).smul hzs |>.sub (blochMat_isHermitian p q lam θ k)
  obtain ⟨c, hc⟩ := adjugateHermitianRankOne (Matrix.scalar (Fin q) z - M) hHerm v hv hNv
  obtain ⟨W, hW, hWtr⟩ := ceyTraceOdd p q m hm hpq lam θ k z
  have hkey : ‖(Matrix.adjugate (Matrix.scalar (Fin q) z - M) * W).trace‖ = (q : ℝ) * |lam| ^ m := by
    rw [hMdef, scalar_eq_smul_one]
    exact hWtr
  have hle : ‖(Matrix.adjugate (Matrix.scalar (Fin q) z - M) * W).trace‖ ≤
      ‖(Matrix.adjugate (Matrix.scalar (Fin q) z - M)).trace‖ := by
    rw [hc]; exact traceUnitaryLe c v W hW
  have htr : ‖(Matrix.adjugate (Matrix.scalar (Fin q) z - M)).trace‖ =
      ‖(M.charpoly).derivative.eval z‖ := by
    rw [show (M.charpoly).derivative.eval z =
      (Matrix.adjugate (z • (1 : Matrix (Fin q) (Fin q) ℂ) - M)).trace from
        adjugateTraceCharpolyDeriv M z]
    congr 1
    rw [scalar_eq_smul_one]
  have hdisc : ‖(M.charpoly).derivative.eval z‖ = ‖(disc p q lam).derivative.eval z‖ := by
    rw [disc_derivative_eq p q m hm hpq lam θ k, hMdef]
  have hfinal : (q : ℝ) * |lam| ^ m ≤ ‖(disc p q lam).derivative.eval z‖ := by
    rw [← hkey]
    exact le_trans hle (le_of_eq (htr.trans hdisc))
  have hpos : 0 < (q : ℝ) * |lam| ^ m := by
    have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    exact mul_pos hq' (pow_pos (abs_pos.mpr (ne_of_gt hlam)) m)
  have hne : (disc p q lam).derivative.eval z ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hpos hfinal))
  rw [hzdef] at hne
  exact hne

theorem discRe_strictMonoOn_or_strictAntiOn (p : ℤ) (q : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (hq : 1 ≤ q) (hpq : Nat.Coprime p.natAbs q) (a c : ℝ)
    (h0 : Even q → ∀ E ∈ Set.Ioo a c, E ≠ 0)
    (hkey : ∀ E ∈ Set.Ioo a c, ‖(Work.TMC14Core.disc p q lam).eval (E : ℂ)‖ ≤ 2 + 2 * lam ^ q) :
    (StrictMonoOn (fun E : ℝ => ((Work.TMC14Core.disc p q lam).eval (E : ℂ)).re) (Set.Ioo a c) ∨
      StrictAntiOn (fun E : ℝ => ((Work.TMC14Core.disc p q lam).eval (E : ℂ)).re)
        (Set.Ioo a c)) := by
  have him : ∀ x : ℝ, ((disc p q lam).eval (x : ℂ)).im = 0 := fun x => disc_im_eq_zero p q lam x
  have hderiv : ∀ E ∈ Set.Ioo a c,
      (Polynomial.derivative (rePoly (disc p q lam))).eval E ≠ 0 := by
    intro E hE
    have hne : (Polynomial.derivative (disc p q lam)).eval (E:ℂ) ≠ 0 := by
      rcases Nat.even_or_odd q with hev | hod
      · have hEven : Even q := hev
        obtain ⟨m, hm⟩ := hev
        have hm2 : q = 2 * (m - 1) + 2 := by omega
        exact discDerivNeZeroEven p q (m - 1) lam hm2 hq hpq hlam E
          (h0 hEven E hE) (hkey E hE)
      · obtain ⟨m, hm⟩ := hod
        exact disc_deriv_ne_zero_odd_self p q m lam hm hq hpq hlam E (hkey E hE)
    rw [deriv_rePoly, rePoly_eval]
    intro hre
    apply hne
    rw [Complex.ext_iff]
    exact ⟨by simpa using hre, by simpa using im_derivative_eval_eq_zero _ him E⟩
  have h := strictMonoOn_or_strictAntiOn_of_deriv_ne_zero
    (rePoly (disc p q lam)) a c hderiv
  simpa only [rePoly_eval] using h

end Work.TMC14Core
