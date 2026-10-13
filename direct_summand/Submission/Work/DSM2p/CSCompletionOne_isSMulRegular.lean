import Mathlib
import Submission.Work.DSM2p.One
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.adicCompletion_isSMulRegular
import Submission.Work.DSM2p.rootClosure_flat
import Submission.Work.DSM2p.CSIntegralClosurePos_isSMulRegular
import Submission.Work.DSM2p.CSIntegralClosureOne_isSMulRegular

/-!
# `p`-torsion-freeness of the one-polynomial Česnavičius–Scholze completion `B_F`

We prove `Work.DSM2p.CSCompletionOne_isSMulRegular`: for a perfectoid datum `P` on `A`, the prime
`p` is a non-zero-divisor of the one-polynomial cover `B_F = CSCompletionOne A p (P.ϖ 0) F`.

The argument is in two steps, exactly parallel to the positive-degree version
(`CSIntegralClosurePos_isSMulRegular`) and to `adicCompletion_isSMulRegular`:

* `p` is a non-zero-divisor of the localisation `Λ[1/ϖ] = Lam1Loc A p ϖ` of the flat `A`-algebra
  `Λ = Lam1 A p = rootClosure A p PUnit`; hence it is one on the subring
  `A'_F = CSIntegralClosureOne A p ϖ F = pIntClosure p (CSAlgOne A p ϖ F) ≤ Λ[1/ϖ]`
  (`natCast_isSMulRegular_Lam1Loc`, `CSIntegralClosureOne_isSMulRegular`);
* a `p`-adic completion of a ring in which `p` is a non-zero-divisor again has `p` as a
  non-zero-divisor (`adicCompletion_isSMulRegular`).
-/

namespace Work.DSM2p

universe u

/-- **`p` is a non-zero-divisor of `Λ[1/ϖ] = Lam1Loc A p ϖ`.**

`Λ = Lam1 A p = rootClosure A p PUnit` is a root-system ring, hence flat over `A`
(`rootClosure_flat`), so a non-zero-divisor of `A` stays one after base change to `Λ`
(`natCast_isSMulRegular_of_flat`); localisation preserves non-zero-divisors
(`natCast_isSMulRegular_of_isLocalization`). -/
theorem natCast_isSMulRegular_Lam1Loc (A : Type u) [CommRing A] (p : ℕ) (ϖ : A)
    (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (Lam1Loc A p ϖ) (p : Lam1Loc A p ϖ) := by
  have hflat : Module.Flat A (Lam1 A p) := rootClosure_flat A p PUnit.{u + 1}
  have hΛ : IsSMulRegular (Lam1 A p) (p : Lam1 A p) :=
    natCast_isSMulRegular_of_flat A (Lam1 A p) p hp
  exact natCast_isSMulRegular_of_isLocalization (Lam1 A p) (Lam1Loc A p ϖ)
    (Submonoid.powers (algebraMap A (Lam1 A p) ϖ)) p hΛ

-- NOTE: the `p`-torsion-freeness of `A'_F` itself,
-- `Work.DSM2p.CSIntegralClosureOne_isSMulRegular`, is the declared lemma of
-- `Submission/Work/DSM2p/CSIntegralClosureOne_isSMulRegular.lean` (imported below); it is not
-- repeated here so that both modules can be imported together.

theorem CSCompletionOne_isSMulRegular (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) :
    IsSMulRegular (CSCompletionOne A p (P.ϖ 0) F) (p : CSCompletionOne A p (P.ϖ 0) F) := by
  exact adicCompletion_isSMulRegular (p := p)
    (CSIntegralClosureOne_isSMulRegular A p (P.ϖ 0) F P.torsionFree)

end Work.DSM2p
