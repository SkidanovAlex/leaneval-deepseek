import Mathlib
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.rayleigh_of_hessian_roots_le_one
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one
import Submission.Commons.Analysis.MvPolynomial.homogeneousComponent_stable_of_stable_nonneg
import Submission.Commons.Analysis.MvPolynomial.taylor_second_bind_add
import Submission.Commons.Analysis.MvPolynomial.isStable_bind_add
import Submission.Commons.Analysis.MvPolynomial.coeff_nonneg_bind_add
import Submission.Commons.Analysis.MvPolynomial.quadraticSum_zero_imp_matrix_zero

open Finsupp Matrix MvPolynomial UpperHalfPlane
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.LorentzianPolynomials

private lemma aeval_quadSum_eq_quadComplex (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) z
        (∑ u : Fin n, ∑ v : Fin n, C (A u v) * X u * X v) =
      Commons.LinearAlgebra.Matrix.quadComplex A z := by
  rw [map_sum]
  rw [Commons.LinearAlgebra.Matrix.quadComplex]
  apply Finset.sum_congr rfl
  intro u hu
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  simp [mul_assoc]


private lemma C2_half_mul (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.C (2 : ℝ) * (MvPolynomial.C (1 / 2 : ℝ) * p) = p := by
  rw [← mul_assoc]
  have hc1 : MvPolynomial.C (2 : ℝ) * MvPolynomial.C (1 / 2 : ℝ) =
      (1 : MvPolynomial (Fin n) ℝ) := by
    rw [← MvPolynomial.C.map_mul]
    norm_num
  rw [hc1]
  simp

noncomputable section

theorem stable_hessian_posRoots_le_one (n d : ℕ) (hd : 2 ≤ d)
    (f : H n d) (hf : f ∈ S n d) (hf0 : f.1 ≠ 0) (w : Fin n → ℝ)
    (hw : ∀ k : Fin n, 0 < w k) :
    ((Matrix.of (fun a b : Fin n => MvPolynomial.eval w
        (MvPolynomial.pderiv a (MvPolynomial.pderiv b f.1)))).charpoly.roots.filter
          (fun r : ℝ => 0 < r)).card ≤ 1 := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun a b : Fin n =>
    MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b f.1)))
  change (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1
  -- symmetric
  have hsymm : A.IsSymm := by
    ext a b
    dsimp [A]
    congr 1
    exact (rayleigh_pre.pderiv_comm b a f.1)
  -- nonnegative entries (w > 0)
  have hnn : ∀ i j : Fin n, 0 ≤ A i j := by
    intro i j
    dsimp [A]
    exact rayleigh_pre.eval_pderiv_pderiv_nonneg i j f.1 hf.2 (fun k => le_of_lt (hw k))
  -- stability & nonnegativity of the shifted polynomial
  let sh : MvPolynomial (Fin n) ℝ :=
    MvPolynomial.bind₁ (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C (w i)) f.1
  have hf_stable : ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) ((fun h : UpperHalfPlane => (h : ℂ)) ∘ z) f.1 ≠ 0 := by
    exact hf.1.resolve_left hf0
  have hsh_stab : sh = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) sh ≠ 0 := by
    dsimp [sh]
    simpa using (Commons.Analysis.MvPolynomial.isStable_bind_add n f.1 w (Or.inr hf_stable))
  have hsh_nn : ∀ m : Fin n →₀ ℕ, 0 ≤ sh.coeff m := by
    dsimp [sh]
    exact Commons.Analysis.MvPolynomial.coeff_nonneg_bind_add n f.1 w hf.2 (fun i => le_of_lt (hw i))
  -- the degree-2 homogeneous part of the shifted polynomial is stable or zero
  have hq2 := Commons.Analysis.MvPolynomial.homogeneousComponent_stable_of_stable_nonneg n 2 sh hsh_nn hsh_stab
  -- Taylor expansion connects it to the Hessian quadratic form
  let qpoly : MvPolynomial (Fin n) ℝ :=
    ∑ a : Fin n, ∑ b : Fin n, MvPolynomial.C (A a b) * MvPolynomial.X a * MvPolynomial.X b
  have htay : MvPolynomial.homogeneousComponent 2 sh = MvPolynomial.C (1 / 2 : ℝ) * qpoly := by
    dsimp [qpoly, A, sh]
    exact Commons.Analysis.MvPolynomial.taylor_second_bind_add n f.1 w
  -- build the left-hand side of the quadratic stability equivalence
  have hleft : A = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
      Commons.LinearAlgebra.Matrix.quadComplex A (fun i : Fin n => (z i : ℂ)) ≠ 0 := by
    by_cases hA0 : A = 0
    · exact Or.inl hA0
    · right
      -- A ≠ 0, so q2 ≠ 0 (else qpoly = 0 forces A = 0)
      have hq2ne : MvPolynomial.homogeneousComponent 2 sh ≠ 0 := by
        intro hz
        apply hA0
        apply Commons.Analysis.MvPolynomial.quadraticSum_zero_imp_matrix_zero n A hsymm
        -- qpoly = 0
        have hqpoly0 : qpoly = 0 := by
          -- q2 = C(1/2) * qpoly and q2 = 0
          have hc : MvPolynomial.C (1 / 2 : ℝ) * qpoly = 0 := by
            rw [← htay, hz]
          -- multiply both sides by C 2
          have h2 : MvPolynomial.C (2 : ℝ) * (MvPolynomial.C (1 / 2 : ℝ) * qpoly) = 0 := by
            rw [hc]
            simp
          -- C 2 * C (1/2) = C 1 = 1
          have hsim : MvPolynomial.C (2 : ℝ) * (MvPolynomial.C (1 / 2 : ℝ) * qpoly) = qpoly :=
            C2_half_mul n qpoly
          rwa [hsim] at h2
        simpa [qpoly] using hqpoly0
      have hq2stab : ∀ z : Fin n → UpperHalfPlane,
          MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ))
            (MvPolynomial.homogeneousComponent 2 sh) ≠ 0 := hq2.resolve_left hq2ne
      intro z
      let zc : Fin n → ℂ := fun i => (z i : ℂ)
      -- qpoly = C 2 * q2, so aeval zc qpoly = 2 * aeval zc q2 ≠ 0
      have hqpoly_eq : qpoly = MvPolynomial.C (2 : ℝ) * MvPolynomial.homogeneousComponent 2 sh := by
        rw [htay]
        exact (C2_half_mul n qpoly).symm
      have haeval_ne : MvPolynomial.aeval (R := ℝ) zc qpoly ≠ 0 := by
        rw [hqpoly_eq]
        rw [map_mul]
        rw [MvPolynomial.aeval_C]
        have hc2 : (algebraMap ℝ ℂ (2 : ℝ)) ≠ 0 := by norm_num
        exact mul_ne_zero hc2 (hq2stab z)
      -- aeval zc qpoly = quadComplex A zc
      have hident := aeval_quadSum_eq_quadComplex n A zc
      simpa [zc, qpoly, hident] using haeval_ne
  have hleft' : A = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
      (∑ i : Fin n, ∑ j : Fin n, A i j * (z i : ℂ) * (z j : ℂ)) ≠ 0 := by
    simpa [Commons.LinearAlgebra.Matrix.quadComplex] using hleft
  have hroot : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1 :=
    (Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one A hsymm hnn).mp hleft'
  simpa [A] using hroot

end

end Commons.LorentzianPolynomials
