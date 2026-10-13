import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE2.Degree

namespace Work.WilE3.API

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-- `eaD c i` is the derivation
`∂/∂xᵢ + ∑ⱼ aⱼᵢ ψⱼ ∂/∂ψⱼ` of the EA polynomial ring: it is additive, ℝ-homogeneous,
satisfies the Leibniz rule, and kills the constants.

The operator `eaD c i` is *definitionally* the operator `Work.WilE2.ESys.d (ofChain c) i`,
whose derivation properties are proved in `Submission.Work.WilE2.Degree`; we transfer them
along that definitional equality.  The only case not available there verbatim is the
ℝ-homogeneity, which follows from the Leibniz rule and `d_C` because `a • Q = C a * Q`. -/
theorem eaD_derivation {k r : ℕ} (c : EAChain k r) (i : Fin k) :
    (∀ Q Q' : EAPoly k r, eaD c i (Q + Q') = eaD c i Q + eaD c i Q') ∧
    (∀ (a : ℝ) (Q : EAPoly k r), eaD c i (a • Q) = a • eaD c i Q) ∧
    (∀ Q Q' : EAPoly k r, eaD c i (Q * Q') = eaD c i Q * Q' + Q * eaD c i Q') ∧
    (∀ a : ℝ, eaD c i (MvPolynomial.C a) = 0) := by
  have h : ∀ Q : EAPoly k r, (Work.WilE2.ESys.ofChain c).d i Q = eaD c i Q :=
    fun Q => Work.WilE2.ESys.ofChain_d c i Q
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Q Q'
    rw [← h (Q + Q'), ← h Q, ← h Q']
    exact Work.WilE2.ESys.d_add (Work.WilE2.ESys.ofChain c) i Q Q'
  · intro a Q
    simp only [MvPolynomial.smul_eq_C_mul]
    rw [← h (MvPolynomial.C a * Q), ← h Q, Work.WilE2.ESys.d_mul, Work.WilE2.ESys.d_C]
    ring
  · intro Q Q'
    rw [← h (Q * Q'), ← h Q, ← h Q']
    exact Work.WilE2.ESys.d_mul (Work.WilE2.ESys.ofChain c) i Q Q'
  · intro a
    rw [← h (MvPolynomial.C a)]
    exact Work.WilE2.ESys.d_C (Work.WilE2.ESys.ofChain c) i a

end Work.WilE3.API
