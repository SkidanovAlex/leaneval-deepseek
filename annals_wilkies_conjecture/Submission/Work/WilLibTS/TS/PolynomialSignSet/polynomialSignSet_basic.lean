import Mathlib
import Submission.Work.WilLibTS.TS.PolynomialSignSetFinite
import Submission.Work.WilLibTS.TS.PolynomialSignSet.forall_finset

namespace Work.WilLibTS.TS.PolynomialSignSet

open Set

variable {X ι : Type*} {c : X → ι → ℝ}

theorem polynomialSignSet_basic {X ι : Type*} {c : X → ι → ℝ}
    (E G : Finset (MvPolynomial ι ℝ)) :
    Work.WilLibTS.TS.PolynomialSignSet c
      {x | (∀ p ∈ E, MvPolynomial.eval (c x) p = 0) ∧
        (∀ q ∈ G, 0 < MvPolynomial.eval (c x) q)} := by
  have hE : PolynomialSignSet c {x | ∀ p ∈ E, MvPolynomial.eval (c x) p = 0} :=
    PolynomialSignSet.forall_finset E (fun p x => MvPolynomial.eval (c x) p = 0)
      (fun p _ => PolynomialSignSet.zero p)
  have hG : PolynomialSignSet c {x | ∀ q ∈ G, 0 < MvPolynomial.eval (c x) q} :=
    PolynomialSignSet.forall_finset G (fun q x => 0 < MvPolynomial.eval (c x) q)
      (fun q _ => PolynomialSignSet.positive q)
  convert hE.inter hG using 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]

end Work.WilLibTS.TS.PolynomialSignSet
