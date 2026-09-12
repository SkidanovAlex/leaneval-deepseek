import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

noncomputable section

/-- The `m`-th coefficient of a scalar multiple: `(c • f).coeff m = c * f.coeff m`. -/
private lemma coeff_smul_H' (n d : ℕ) (c : ℝ) (f : H n d) (m : Fin n →₀ ℕ) :
    (c • f).1.coeff m = c * f.1.coeff m := by
  rw [show (c • f).1 = c • f.1 by rfl]
  simp [MvPolynomial.coeff_smul, smul_eq_mul]

/-- The characteristic polynomial of a non-zero scalar multiple of a matrix is the
`scaleRoots`-transform of the characteristic polynomial. -/
private lemma charpoly_smul_scaleRoots (n : ℕ) {c : ℝ} (hc : c ≠ 0)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (c • A).charpoly = A.charpoly.scaleRoots c := by
  classical
  apply Polynomial.funext
  intro x
  let y : ℝ := c⁻¹ * x
  have hcy : c * y = x := by
    dsimp [y]
    field_simp [hc]
  have hsmul_scalar : c • Matrix.scalar (Fin n) y = Matrix.scalar (Fin n) (c * y) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar_apply, Matrix.smul_apply, smul_eq_mul]
    · simp [Matrix.scalar_apply, Matrix.smul_apply, smul_eq_mul, hij]
  have hscalar : Matrix.scalar (Fin n) (c * y) - c • A = c • (Matrix.scalar (Fin n) y - A) := by
    rw [hsmul_scalar.symm]
    rw [smul_sub]
  have hL : eval (c * y) (charpoly (c • A)) =
      c ^ n * eval y (charpoly A) := by
    rw [Matrix.eval_charpoly, Matrix.eval_charpoly, hscalar, Matrix.det_smul]
    simp
  have hnd : (A.charpoly).natDegree = n := by simp
  have hR : eval (c * y) (A.charpoly.scaleRoots c) =
      c ^ n * eval y (charpoly A) := by
    rw [Polynomial.scaleRoots_eval_mul]
    rw [hnd]
  have hmain : eval x (charpoly (c • A)) = eval x (A.charpoly.scaleRoots c) := by
    calc
      eval x (charpoly (c • A)) = eval (c * y) (charpoly (c • A)) := by rw [← hcy]
      _ = c ^ n * eval y (charpoly A) := hL
      _ = eval (c * y) (A.charpoly.scaleRoots c) := hR.symm
      _ = eval x (A.charpoly.scaleRoots c) := by rw [hcy]
  exact hmain

/-- Multiplying the roots of a multiset of reals by a positive scalar preserves the
number of positive elements. -/
private lemma card_filter_pos_map_mul (c : ℝ) (hc : 0 < c) (s : Multiset ℝ) :
    ((s.map (fun r : ℝ => c * r)).filter (0 < ·)).card =
      (s.filter (0 < ·)).card := by
  classical
  have hf := Multiset.filter_map (p := fun r : ℝ => 0 < r) (f := fun r : ℝ => c * r) s
  rw [hf]
  rw [Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro r hr
  constructor
  · intro hpos
    dsimp at hpos
    exact (mul_pos_iff_of_pos_left hc).mp hpos
  · intro hpos
    exact mul_pos hc hpos

/-- A positive scalar multiple of a matrix has the same number of positive characteristic
roots as the original matrix. -/
private lemma charpoly_smul_pos_roots_card (n : ℕ) {c : ℝ} (hc : 0 < c)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ((c • A).charpoly.roots.filter (0 < ·)).card = (A.charpoly.roots.filter (0 < ·)).card := by
  classical
  have hc0 : c ≠ 0 := ne_of_gt hc
  rw [charpoly_smul_scaleRoots n hc0 A]
  have hIsUnit : IsUnit c := isUnit_iff_ne_zero.mpr hc0
  rw [Polynomial.roots_scaleRoots (A.charpoly) hIsUnit]
  exact card_filter_pos_map_mul c hc A.charpoly.roots

/-- A non-zero scalar multiple of an invertible matrix is invertible. -/
private lemma isUnit_smul_matrix (n : ℕ) {c : ℝ} (hc : c ≠ 0)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) : IsUnit (c • A) := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det] at hA
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [Matrix.det_smul]
  rw [isUnit_iff_ne_zero] at hA ⊢
  exact mul_ne_zero (pow_ne_zero (Fintype.card (Fin n)) hc) hA

/-- The Hessian of `c • f` is `c` times the Hessian of `f`. -/
private lemma hessian_smul (n : ℕ) (c : ℝ) (f : H n 2) : (c • f).hessian = c • f.hessian := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    rw [hessian_apply_sq n (c • f) i]
    rw [Matrix.smul_apply, smul_eq_mul]
    rw [hessian_apply_sq n f i]
    rw [coeff_smul_H' n 2 c f (Finsupp.single i 2)]
    ring
  · rw [hessian_apply_cross n (c • f) hij]
    rw [Matrix.smul_apply, smul_eq_mul]
    rw [hessian_apply_cross n f hij]
    rw [coeff_smul_H' n 2 c f (Finsupp.single i 1 + Finsupp.single j 1)]

/-- Multiplying a polynomial in `P n d` by a positive scalar keeps it in `P n d`. -/
private lemma smul_mem_P' (n d : ℕ) {c : ℝ} (hc : 0 < c) (f : H n d) (hf : f ∈ P n d) :
    c • f ∈ P n d := by
  intro m hm
  rw [coeff_smul_H' n d c f m]
  exact mul_pos hc (hf m hm)

/-- Positive scalar multiples of strictly Lorentzian quadratics are strictly Lorentzian. -/
private lemma smul_mem_Ŀ_two (n : ℕ) {c : ℝ} (hc : 0 < c) (f : H n 2) (hf : f ∈ Ŀ n 2) :
    c • f ∈ Ŀ n 2 := by
  classical
  simp [Ŀ] at hf ⊢
  rcases hf with ⟨hP, hUnit, hcard⟩
  constructor
  · exact smul_mem_P' n 2 hc f hP
  · constructor
    · rw [hessian_smul n c f]
      exact isUnit_smul_matrix n (ne_of_gt hc) hUnit
    · rw [hessian_smul n c f]
      rw [charpoly_smul_pos_roots_card n hc f.hessian]
      exact hcard

theorem smul_mem_strict (n d : ℕ) (hn : 0 < n) {c : ℝ} (hc : 0 < c)
    (f : Commons.LorentzianPolynomials.H n d) (hf : f ∈ Commons.LorentzianPolynomials.Ŀ n d) :
    c • f ∈ Commons.LorentzianPolynomials.Ŀ n d := by
  classical
  revert f hf
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro f hf
    cases d with
    | zero =>
      change c • f ∈ P n 0
      exact smul_mem_P' n 0 hc f (by simpa [Ŀ] using hf)
    | succ d1 =>
      cases d1 with
      | zero =>
        change c • f ∈ P n 1
        exact smul_mem_P' n 1 hc f (by simpa [Ŀ] using hf)
      | succ d2 =>
        cases d2 with
        | zero =>
          exact smul_mem_Ŀ_two n hc f hf
        | succ k =>
          change f ∈ P n (k + 3) ∧
            (∀ i : Fin n, (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (k + 2)) ∈ Ŀ n (k + 2)) at hf
          change c • f ∈ P n (k + 3) ∧
            (∀ i : Fin n, (⟨(c • f).1.pderiv i, (c • f).2.pderiv⟩ : H n (k + 2)) ∈ Ŀ n (k + 2))
          constructor
          · exact smul_mem_P' n (k + 3) hc f hf.1
          · intro i
            have hder_i : (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (k + 2)) ∈ Ŀ n (k + 2) := hf.2 i
            have hder_eq : (⟨(c • f).1.pderiv i, (c • f).2.pderiv⟩ : H n (k + 2)) =
                c • (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (k + 2)) := by
              apply Subtype.ext
              change (c • f).1.pderiv i = c • (f.1.pderiv i)
              rw [show (c • f).1 = c • f.1 by rfl]
              exact (pderiv i).map_smul c f.1
            rw [hder_eq]
            exact ih (k + 2) (by omega) (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (k + 2)) hder_i

end
end Commons.LorentzianPolynomials
