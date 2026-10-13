import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3.API

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

theorem eaEvalC_ring {k r : ℕ} (c : EAChain k r) (z : Fin k → ℂ) :
    (∀ Q Q' : EAPoly k r, Work.WilE3.eaEvalC c (Q + Q') z = Work.WilE3.eaEvalC c Q z + Work.WilE3.eaEvalC c Q' z) ∧
    (∀ Q Q' : EAPoly k r, Work.WilE3.eaEvalC c (Q * Q') z = Work.WilE3.eaEvalC c Q z * Work.WilE3.eaEvalC c Q' z) ∧
    (∀ a : ℝ, Work.WilE3.eaEvalC c (MvPolynomial.C a) z = (a : ℂ)) ∧
    (∀ i : Fin k, Work.WilE3.eaEvalC c (MvPolynomial.X (Sum.inl i)) z = z i) ∧
    (∀ j : Fin r, Work.WilE3.eaEvalC c (MvPolynomial.X (Sum.inr j)) z =
      Complex.exp (∑ i, (c.a j i : ℂ) * z i + (c.b j : ℂ))) := by
  -- `eaEvalC` is `MvPolynomial.eval₂` at the complexified assignment
  -- `z ↦ (z, exp (∑ a z + b))`, i.e. the underlying map of the ring homomorphism
  -- `MvPolynomial.eval₂Hom`, so all five statements are defining properties of that homomorphism.
  let φ : Fin k ⊕ Fin r → ℂ :=
    Sum.elim z fun j => Complex.exp (∑ i, (c.a j i : ℂ) * z i + (c.b j : ℂ))
  have key : ∀ Q : EAPoly k r,
      Work.WilE3.eaEvalC c Q z = MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) φ Q :=
    fun Q => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Q Q'
    rw [key (Q + Q'), key Q, key Q']
    exact map_add (MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) φ) Q Q'
  · intro Q Q'
    rw [key (Q * Q'), key Q, key Q']
    exact map_mul (MvPolynomial.eval₂Hom (algebraMap ℝ ℂ) φ) Q Q'
  · intro a
    rw [key (MvPolynomial.C a)]
    exact MvPolynomial.eval₂Hom_C (algebraMap ℝ ℂ) φ a
  · intro i
    rw [key (MvPolynomial.X (Sum.inl i))]
    exact MvPolynomial.eval₂Hom_X' (algebraMap ℝ ℂ) φ (Sum.inl i)
  · intro j
    rw [key (MvPolynomial.X (Sum.inr j))]
    exact MvPolynomial.eval₂Hom_X' (algebraMap ℝ ℂ) φ (Sum.inr j)

end Work.WilE3.API
