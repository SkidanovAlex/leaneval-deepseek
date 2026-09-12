import Mathlib
import Submission.Commons.Analysis.MvPolynomial.garding_cone_hyperbolic

noncomputable section

open MvPolynomial Polynomial
open scoped BigOperators

set_option autoImplicit false

namespace Commons.Analysis.MvPolynomial

/-- The univariate real polynomial obtained by restricting `H` to the affine line
`a + ℝe`, i.e. `t ↦ H (a + t • e)`. -/
def LinePoly {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a e : Fin m → ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval (R := ℝ)
    (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H

/-- A real polynomial is `RealRooted` if it is zero or all its complex roots are real. -/
def RealRooted {m : ℕ} (p : Polynomial ℝ) : Prop :=
  p = 0 ∨ ∀ r : ℂ, Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) p) = 0 →
    ∃ s : ℝ, r = (s : ℂ)

/-- Evaluating the ℂ-line restriction of `H` at `b` equals evaluating `H` at the
complex point `z + b • v`. -/
lemma line_eval_complex {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (z v : Fin m → ℂ) (b : ℂ) :
    Polynomial.eval b (MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) H) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => z i + b * v i) H := by
  classical
  let f : Fin m → Polynomial ℂ := fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  let φ : Polynomial ℂ →ₐ[ℝ] ℂ := (Polynomial.aeval (R := ℂ) b).restrictScalars ℝ
  have h := MvPolynomial.comp_aeval_apply (R := ℝ) (S₁ := Polynomial ℂ) (f := f) (φ := φ) (p := H)
  change φ ((MvPolynomial.aeval f) H) = MvPolynomial.aeval (R := ℝ) (fun i => z i + b * v i) H
  rw [h]
  have hfun : (fun i : Fin m => φ (f i)) = (fun i : Fin m => z i + b * v i) := by
    funext i
    dsimp [f, φ]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [hfun]

/-- Mapping the real line restriction to ℂ gives the ℂ-line restriction. -/
lemma map_aeval_real {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a e : Fin m → ℝ) :
    Polynomial.map (algebraMap ℝ ℂ) (LinePoly H a e) =
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C ((a i : ℝ) : ℂ) + Polynomial.C ((e i : ℝ) : ℂ) * Polynomial.X) H := by
  classical
  unfold LinePoly
  let f : Fin m → Polynomial ℝ := fun i => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X
  let φ : Polynomial ℝ →ₐ[ℝ] Polynomial ℂ := Polynomial.mapAlgHom (Algebra.ofId ℝ ℂ)
  have h := MvPolynomial.comp_aeval_apply (R := ℝ) (S₁ := Polynomial ℝ) (f := f) (φ := φ) (p := H)
  change φ ((MvPolynomial.aeval f) H) = MvPolynomial.aeval (R := ℝ)
    (fun i : Fin m => Polynomial.C ((a i : ℝ) : ℂ) + Polynomial.C ((e i : ℝ) : ℂ) * Polynomial.X) H
  rw [h]
  have hfun : (fun i : Fin m => φ (f i)) = (fun i : Fin m =>
      Polynomial.C ((a i : ℝ) : ℂ) + Polynomial.C ((e i : ℝ) : ℂ) * Polynomial.X) := by
    funext i
    dsimp [f, φ]
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  rw [hfun]

/-- Complex evaluation of the real line polynomial equals complex evaluation of `H`. -/
lemma LinePoly_eval_eq {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a e : Fin m → ℝ) (t : ℂ) :
    Polynomial.eval t (Polynomial.map (algebraMap ℝ ℂ) (LinePoly H a e)) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => (a i : ℂ) + t * (e i : ℂ)) H := by
  rw [map_aeval_real]
  simpa [LinePoly] using (line_eval_complex H (fun i : Fin m => ((a i : ℝ) : ℂ))
    (fun i : Fin m => ((e i : ℝ) : ℂ)) t)

/-- Complex evaluation of `H` at a real vector equals the coerced real evaluation. -/
lemma aeval_real_complex {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    MvPolynomial.aeval (R := ℝ) (fun i : Fin m => (x i : ℂ)) H =
      (MvPolynomial.eval x H : ℂ) := by
  classical
  induction H using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq]; norm_num
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.aeval_X, hp]
      simp

/-- A nonzero real-rooted real polynomial does not vanish at `i`. -/
lemma realRooted_i_ne_zero (p : Polynomial ℝ) (hp : p ≠ 0)
    (hrr : ∀ r : ℂ, Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) p) = 0 →
      ∃ s : ℝ, r = (s : ℂ)) :
    Polynomial.eval (Complex.I) (Polynomial.map (algebraMap ℝ ℂ) p) ≠ 0 := by
  intro hz
  rcases hrr Complex.I hz with ⟨s, hs⟩
  have him : (Complex.I : ℂ).im = 1 := by norm_num
  have hsi : ((s : ℝ) : ℂ).im = 0 := by norm_num
  rw [hs] at him
  rw [hsi] at him
  norm_num at him

/-- A nonzero polynomial with nonnegative coefficients is strictly positive on the
strictly positive orthant. -/
lemma eval_pos_of_pos {m : ℕ} {H : MvPolynomial (Fin m) ℝ}
    (hH0 : H ≠ 0)
    (hnonneg : ∀ M : Fin m →₀ ℕ, 0 ≤ H.coeff M)
    (u : Fin m → ℝ) (hu : ∀ i : Fin m, 0 < u i) :
    0 < MvPolynomial.eval u H := by
  classical
  have hsupp : H.support.Nonempty := by
    by_contra hnone
    have h0 : H.support = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp hnone
    apply hH0
    exact MvPolynomial.support_eq_empty.mp h0
  obtain ⟨M, hM⟩ := hsupp
  have hc_ne : H.coeff M ≠ 0 := (MvPolynomial.mem_support_iff.mp hM)
  have hc : 0 < H.coeff M := lt_of_le_of_ne (hnonneg M) (Ne.symm hc_ne)
  have hprod : 0 < M.prod (fun i k => u i ^ k) := by
    have hprod' : 0 < ∏ i ∈ M.support, u i ^ M i := by
      apply Finset.prod_pos
      intro i hi
      have hui : 0 < u i := hu i
      positivity
    simpa [Finsupp.prod] using hprod'
  have hterm : 0 < H.coeff M * M.prod (fun i k => u i ^ k) := mul_pos hc hprod
  have hnonneg_term : ∀ d ∈ H.support,
      0 ≤ H.coeff d * (∏ i ∈ d.support, u i ^ d i) := by
    intro d hd
    have h1 : 0 ≤ H.coeff d := hnonneg d
    have h2 : 0 ≤ ∏ i ∈ d.support, u i ^ d i := by
      apply Finset.prod_nonneg
      intro i hi
      have hui : 0 ≤ u i := le_of_lt (hu i)
      positivity
    exact mul_nonneg h1 h2
  have hterm_le : H.coeff M * (∏ i ∈ M.support, u i ^ M i) ≤
      ∑ d ∈ H.support, H.coeff d * ∏ i ∈ d.support, u i ^ d i := by
    simpa using (Finset.single_le_sum hnonneg_term hM : H.coeff M * (∏ i ∈ M.support, u i ^ M i) ≤
      ∑ d ∈ H.support, H.coeff d * ∏ i ∈ d.support, u i ^ d i)
  have hsum : MvPolynomial.eval u H =
      ∑ d ∈ H.support, H.coeff d * ∏ i ∈ d.support, u i ^ d i := by
    simpa using (MvPolynomial.eval_eq u H)
  rw [hsum]
  exact lt_of_lt_of_le hterm hterm_le


theorem garding_stable_of_hyperbolic_and_cone {m d : ℕ} (H : MvPolynomial (Fin m) ℝ)
    (e : Fin m → ℝ) (hdpos : 0 < d)
    (hhom : H.IsHomogeneous d)
    (hH0 : H ≠ 0)
    (hnonneg : ∀ M : Fin m →₀ ℕ, 0 ≤ H.coeff M)
    (he_ne : MvPolynomial.eval e H ≠ 0)
    (hhyp : ∀ a : Fin m → ℝ,
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H = 0 ∨
        ∀ r : Complex, Polynomial.eval r (Polynomial.map (algebraMap ℝ Complex)
          (MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H)) = 0 →
          ∃ s : ℝ, r = (s : Complex))
    (hcone : ∀ u : Fin m → ℝ, (∀ i : Fin m, 0 < u i) →
      ∀ t : ℝ, 0 ≤ t → MvPolynomial.eval (fun i : Fin m => u i + t * e i) H ≠ 0) :
    ∀ z : Fin m → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ)) H ≠ 0 := by
  classical
  intro z
  let x : Fin m → ℝ := fun i => (z i : ℂ).re
  let y : Fin m → ℝ := fun i => (z i : ℂ).im
  have hy : ∀ i : Fin m, 0 < y i := by
    intro i
    exact UpperHalfPlane.im_pos (z i)
  have hu_y : ∀ s : ℝ, 0 ≤ s → MvPolynomial.eval (fun i : Fin m => y i + s * e i) H ≠ 0 := by
    intro s hs
    exact hcone y hy s hs
  -- a real parameter making x + t₀•y strictly positive (y > 0)
  let t0 : ℝ := 1 + ∑ i : Fin m, |x i| / y i
  have hpos_t0 : ∀ i : Fin m, 0 < x i + t0 * y i := by
    intro i
    have hyi : 0 < y i := hy i
    let S : ℝ := ∑ j : Fin m, |x j| / y j
    have hbig : |x i| / y i ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum (s := Finset.univ)
        (by intro j hj; exact div_nonneg (abs_nonneg (x j)) (le_of_lt (hy j))) (Finset.mem_univ i)
    have hSy : |x i| ≤ S * y i := by
      calc
        |x i| = (|x i| / y i) * y i := by field_simp [ne_of_gt hyi]
        _ ≤ S * y i := mul_le_mul_of_nonneg_right hbig (le_of_lt hyi)
    have hxS : 0 ≤ x i + S * y i := by linarith [hSy, (neg_le_abs (x i))]
    have hsum : x i + t0 * y i = (x i + S * y i) + y i := by
      dsimp [t0, S]
      ring
    rw [hsum]
    linarith

  have hval_pos : 0 < MvPolynomial.eval (fun i : Fin m => x i + t0 * y i) H :=
    eval_pos_of_pos hH0 hnonneg (fun i : Fin m => x i + t0 * y i) hpos_t0
  have hline_ne : LinePoly H x y ≠ 0 := by
    intro hz
    have hev : Polynomial.eval (t0 : ℂ) (Polynomial.map (algebraMap ℝ ℂ) (LinePoly H x y)) = 0 := by
      simp [hz]
    have hev' : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => (x i : ℂ) + (t0 : ℂ) * (y i : ℂ)) H = 0 := by
      exact (LinePoly_eval_eq H x y (t0 : ℂ)).symm.trans hev
    have hpi (i : Fin m) : ((x i + t0 * y i : ℝ) : ℂ) = (x i : ℂ) + (t0 : ℂ) * (y i : ℂ) := by
      rw [Complex.ofReal_add, Complex.ofReal_mul]
    have hfun2 : (fun i : Fin m => ((x i + t0 * y i : ℝ) : ℂ)) =
        (fun i : Fin m => (x i : ℂ) + (t0 : ℂ) * (y i : ℂ)) := by
      funext i
      exact hpi i
    have hre : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => ((x i + t0 * y i : ℝ) : ℂ)) H = 0 := by
      rw [hfun2]
      exact hev'
    have hreal : (MvPolynomial.eval (fun i : Fin m => x i + t0 * y i) H : ℂ) = 0 := by
      exact ((aeval_real_complex H (fun i : Fin m => x i + t0 * y i)).symm.trans hre)
    have hne : (MvPolynomial.eval (fun i : Fin m => x i + t0 * y i) H : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hval_pos)
    exact hne hreal

  -- apply the Gårding core lemma to direction y
  have hcore := garding_cone_hyperbolic H e y hhom hH0 he_ne hhyp hu_y
  rcases hcore x with hzero | hrr
  · exact False.elim (hline_ne hzero)
  · have hri : Polynomial.eval (Complex.I) (Polynomial.map (algebraMap ℝ ℂ) (LinePoly H x y)) ≠ 0 :=
      realRooted_i_ne_zero (LinePoly H x y) hline_ne hrr
    have hev_i : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => (x i : ℂ) + Complex.I * (y i : ℂ)) H ≠ 0 := by
      intro h0
      apply hri
      exact (LinePoly_eval_eq H x y Complex.I).trans h0
    have hfun : (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ)) =
        (fun i : Fin m => (x i : ℂ) + Complex.I * (y i : ℂ)) := by
      funext i
      apply Complex.ext
      · simp [x]
      · simp [y]
    rw [hfun]
    exact hev_i

end Commons.Analysis.MvPolynomial
