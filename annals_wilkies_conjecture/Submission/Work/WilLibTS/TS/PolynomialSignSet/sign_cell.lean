import Mathlib
import Submission.Work.WilLibTS.TS.PolynomialSignSetFinite

namespace Work.WilLibTS.TS.PolynomialSignSet

theorem sign_cell {X ι : Type*} {c : X → ι → ℝ} {S : Set X}
    (hS : Work.WilLibTS.TS.PolynomialSignSet c S) (s : Finset (MvPolynomial ι ℝ))
    (σ : s → SignType) :
    Work.WilLibTS.TS.PolynomialSignSet c
      (S ∩ {x | ∀ p : s, SignType.sign (MvPolynomial.eval (c x) p.val) = σ p}) := by
  classical
  exact hS.inter
    (PolynomialSignSet.forall_finite _ (fun p => PolynomialSignSet.sign p.val (σ p)))

end Work.WilLibTS.TS.PolynomialSignSet
