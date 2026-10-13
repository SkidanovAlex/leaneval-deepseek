import Mathlib
import Submission.Work.WilE3.Frame.Setup

namespace Work.WilE3.Frame

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-- A multivariable polynomial over `ℝ` evaluated in `ℂ` along the complexification of a real
assignment: if `φ : σ → ℂ` is the pointwise image of `ψ : σ → ℝ`, then the `ℂ`-valued evaluation of
`Q` at `φ` is the image of the `ℝ`-valued evaluation of `Q` at `ψ`.  Both sides are the ring
homomorphisms `eval₂ (algebraMap ℝ ℂ) φ` and `(algebraMap ℝ ℂ).comp (eval ψ)`, which agree on the
generators `C r` and `X i`. -/
theorem eval₂_algebraMap_eq_coe {σ : Type*} (φ : σ → ℂ) (ψ : σ → ℝ)
    (hφ : ∀ i, φ i = (ψ i : ℂ)) (Q : MvPolynomial σ ℝ) :
    MvPolynomial.eval₂ (algebraMap ℝ ℂ) φ Q = (MvPolynomial.eval ψ Q : ℂ) := by
  have h : MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) φ
      = (algebraMap ℝ ℂ).comp (MvPolynomial.eval ψ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp
    · simp [hφ i]
  exact RingHom.congr_fun h Q

/-- At a real point (viewed as a complex point), the complexified evaluation of an EA polynomial
agrees with the real evaluation: `eaEvalC c P (toC x) = ↑(eaEval c P x)`.  This is the transfer
between the complex setting in which the multiplicity bound lives and the real hypothesis of
`E3_identity`. -/
theorem eaEvalC_toC {k r : ℕ} (c : EAChain k r) (P : EAPoly k r) (x : Fin k → ℝ) :
    Work.WilE3.eaEvalC c P (Work.WilE3.Frame.toC x) = (eaEval c P x : ℂ) := by
  -- The complex assignment is the pointwise complexification of the real one: the coordinates
  -- themselves at `Sum.inl i`, and `exp` of the (complexified) affine form at `Sum.inr j`.
  have hφ : ∀ i : Fin k ⊕ Fin r,
      (Sum.elim (Work.WilE3.Frame.toC x) fun j =>
        Complex.exp (∑ i, (c.a j i : ℂ) * Work.WilE3.Frame.toC x i + (c.b j : ℂ))) i
      = ((Sum.elim x fun j => Real.exp (c.ell j x)) i : ℂ) := by
    intro i
    rcases i with i | j
    · simp [Work.WilE3.Frame.toC]
    · simp only [Sum.elim_inr, Work.WilE3.Frame.toC]
      rw [Complex.ofReal_exp]
      congr 1
      simp only [EAChain.ell]
      push_cast
      ring
  rw [Work.WilE3.eaEvalC, eaEval]
  exact eval₂_algebraMap_eq_coe _ _ hφ P

end Work.WilE3.Frame
