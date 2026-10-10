import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Submission.Work.AbsoluteGalois.exists_hom_lift_iff_pullbackCocycle_mem_B2
import Submission.Work.AbsoluteGalois.sectionCocycle_mem_Z2
import Submission.Work.AbsoluteGalois.twisted_splitting_iff_mem_B2
import Submission.Work.AbsoluteKummer.Factorisation.exists_finiteGalois_le_ker_pair
import Submission.Work.AbsoluteKummer.Functoriality
import Submission.Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective
import Submission.Work.AbsoluteKummer.H1Pi.nonempty_h1_pi_equiv
import Submission.Work.AbsoluteKummer.Kummer.kummerQuotientEquiv
import Submission.Work.AbsoluteKummer.Kummer.nonempty_h0_addUnits_equiv
import Submission.Work.AbsoluteKummer.KummerBijective
import Submission.Work.AbsoluteKummer.Rat
import Submission.Work.AbsoluteKummer.SES.exists_connecting_exact_H2
import Submission.Work.Properness.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

open scoped Classical

noncomputable section

/-- **The Kummer isomorphism** `kˣ/(kˣ)ⁿ ≃* H¹(G_k, μₙ)` for a field `k` containing a primitive
`n`-th root of unity `ζ`.  The map sends the class of `x` to the class of the crossed homomorphism
`σ ↦ σ(α)/α`, where `α` is any `n`-th root of `x` in `k̄`. -/
def kummerEquiv {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)] {n : ℕ} [NeZero n]
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) :
    (kˣ ⧸ Work.Kummer.nthPowerSubgroup n kˣ) ≃*
      Multiplicative (Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G k)
        (Additive (rootsOfUnity n (AlgebraicClosure k)))) :=
  Work.AbsoluteKummer.kummerEquiv hζ

/-- The Kummer isomorphism for `k = ℚ`, `n = 2`: **`ℚˣ/(ℚˣ)² ≃* H¹(G_ℚ, μ₂)`**. -/
def kummerEquivRatTwo :
    (ℚˣ ⧸ Work.Kummer.nthPowerSubgroup 2 ℚˣ) ≃*
      Multiplicative (Work.AbsoluteKummer.H1 (Field.absoluteGaloisGroup ℚ)
        (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ)))) :=
  Work.AbsoluteKummer.kummerEquivRatTwo

/-- **Hilbert 90 for the absolute Galois group**: every locally constant crossed homomorphism
`G_k → k̄ˣ` is principal, i.e. `H¹(G_k, k̄ˣ) = 0`. -/
theorem hilbert90_H1_eq_zero (k : Type*) [Field k] [IsGalois k (AlgebraicClosure k)]
    (x : Work.AbsoluteKummer.H1 (Field.absoluteGaloisGroup k)
      (Additive (AlgebraicClosure k)ˣ)) : x = 0 :=
  Work.AbsoluteKummer.Hilbert90.H1_eq_zero_absolute x

theorem grunwald_sqClassLocalize_surjective {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ i, Fact (q i).Prime] (hq : Function.Injective q) :
    Function.Surjective (fun x : Work.AbsoluteKummer.SqClass ℚ => fun i : ι =>
      Work.AbsoluteKummer.sqClassLocalize (q i) x) :=
  Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective q hq

end

end Submission
