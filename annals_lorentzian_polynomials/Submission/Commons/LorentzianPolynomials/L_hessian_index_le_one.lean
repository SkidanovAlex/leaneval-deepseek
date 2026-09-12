import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.rayleigh_of_hessian_roots_le_one
import Submission.Commons.LorentzianPolynomials.strict_L_hessian_index_le_one
import Submission.Commons.LorentzianPolynomials.L_subset_closure
import Submission.Commons.LinearAlgebra.Matrix.isClosed_symm_posRoots_card_le_one

namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

/-- the Hessian matrix `(∂a∂b g(w))` of a degree-`d` homogeneous polynomial `g` at `w` -/
def hessMat (n d : ℕ) (w : Fin n → ℝ) : H n d → Matrix (Fin n) (Fin n) ℝ :=
  fun g => Matrix.of (fun a b : Fin n => MvPolynomial.eval w (MvPolynomial.pderiv (R := ℝ) a (MvPolynomial.pderiv (R := ℝ) b g.1)))

/-- `hessMat` is continuous in the polynomial for the module topology. -/
lemma hessMat_continuous (n d : ℕ) (w : Fin n → ℝ) : Continuous (hessMat n d w) := by
  haveI : ContinuousAdd (Matrix (Fin n) (Fin n) ℝ) := by infer_instance
  haveI : ContinuousSMul ℝ (Matrix (Fin n) (Fin n) ℝ) := by infer_instance
  let L : H n d →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ := {
    toFun := hessMat n d w
    map_add' := by
      intro f g
      ext a b
      change MvPolynomial.eval w (MvPolynomial.pderiv (R := ℝ) a (MvPolynomial.pderiv (R := ℝ) b (f + g).1)) =
        MvPolynomial.eval w (MvPolynomial.pderiv (R := ℝ) a (MvPolynomial.pderiv (R := ℝ) b f.1)) +
          MvPolynomial.eval w (MvPolynomial.pderiv (R := ℝ) a (MvPolynomial.pderiv (R := ℝ) b g.1))
      rw [show (f + g).1 = f.1 + g.1 by rfl]
      simp [hessMat]
    map_smul' := by
      intro r f
      ext a b
      change MvPolynomial.eval w (MvPolynomial.pderiv (R := ℝ) a (MvPolynomial.pderiv (R := ℝ) b (r • f).1)) =
        r * MvPolynomial.eval w (MvPolynomial.pderiv (R := ℝ) a (MvPolynomial.pderiv (R := ℝ) b f.1))
      rw [show (r • f).1 = r • f.1 by rfl]
      simp [hessMat] }
  have hcont : Continuous L := IsModuleTopology.continuous_of_linearMap L
  change Continuous (hessMat n d w)
  simpa [L] using hcont

/-- second partial derivatives commute, so the Hessian matrix is symmetric -/
lemma hessMat_symm (n d : ℕ) (w : Fin n → ℝ) (g : H n d) : (hessMat n d w g).IsSymm := by
  rw [Matrix.IsSymm]
  ext a b
  change MvPolynomial.eval w (MvPolynomial.pderiv (R := ℝ) b (MvPolynomial.pderiv (R := ℝ) a g.1)) =
    MvPolynomial.eval w (MvPolynomial.pderiv (R := ℝ) a (MvPolynomial.pderiv (R := ℝ) b g.1))
  congr 1
  exact rayleigh_pre.pderiv_comm b a g.1

/-- Theorem 2.16(2) of Br&auml;nd&eacute;n--Huh: for `f ∈ L n d`, `d ≥ 2`, the Hessian matrix
`(∂a∂b f(w))` has at most one positive eigenvalue for every `w > 0`, expressed via
the number of positive roots of the characteristic polynomial being ≤ 1. -/
theorem L_hessian_index_le_one (n d : ℕ) (hd : 2 ≤ d) :
    ∀ (f : H n d), f ∈ L n d → ∀ (w : Fin n → ℝ), (∀ k : Fin n, 0 < w k) →
      ((Matrix.of (fun a b : Fin n => MvPolynomial.eval w
          (MvPolynomial.pderiv a (MvPolynomial.pderiv b f.1)))).charpoly.roots.filter
            (fun r : ℝ => 0 < r)).card ≤ 1 := by
  intro f hf w hw
  by_cases hn : 0 < n
  · -- n > 0 : L n d ⊆ closure (Ŀ n d), strict elements have index ≤ 1, and the
    -- set of symmetric matrices with at most one positive (real) root is closed.
    classical
    have hcl : f ∈ closure (Ŀ n d) := L_subset_closure n d hn hf
    have hcont : Continuous (hessMat n d w) := hessMat_continuous n d w
    have himg : hessMat n d w '' (closure (Ŀ n d)) ⊆ closure (hessMat n d w '' Ŀ n d) :=
      image_closure_subset_closure_image hcont
    have hmem : hessMat n d w f ∈ closure (hessMat n d w '' Ŀ n d) := himg ⟨f, hcl, rfl⟩
    let C : Set (Matrix (Fin n) (Fin n) ℝ) :=
      {A | A.IsSymm ∧ (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1}
    have hsub : hessMat n d w '' Ŀ n d ⊆ C := by
      rintro A ⟨g, hg, rfl⟩
      exact ⟨hessMat_symm n d w g, strict_L_hessian_index_le_one n d hn hd g hg w hw⟩
    have hclosed : IsClosed C :=
      Commons.LinearAlgebra.Matrix.isClosed_symm_posRoots_card_le_one n
    have hclsub : closure (hessMat n d w '' Ŀ n d) ⊆ C := by
      have h1 : closure (hessMat n d w '' Ŀ n d) ⊆ closure C := closure_mono hsub
      simpa [hclosed.closure_eq] using h1
    exact (hclsub hmem).2
  · -- n = 0 : the matrix is empty, so its characteristic polynomial has no roots.
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hcard : ((hessMat 0 d w f).charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1 := by
      have hA : hessMat 0 d w f = 0 := Subsingleton.elim _ 0
      rw [hA, Matrix.charpoly_zero]
      simp
    simpa [hessMat] using hcard

end
end Commons.LorentzianPolynomials
