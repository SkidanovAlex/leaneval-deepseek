import Mathlib
import Submission.NK.BrauerHasse.Profinite
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.BrauerTwist.All
import Submission.NK.IndecomposedDeep.twistTwoComparison

/-!
# `FiniteSupportTwist`: the `μ_p`-twisted finite-support statement

**Restoration note (agent `finite_support_loc_odd_of_twist`).**  The module that used to live at
this path was deleted from the workspace after the audit recorded in
`Submission/Work/NUV2/LC/NOTES_finite_support_loc.md` concluded that its *general-`p`* statement
`finite_support_loc (p : ℕ) ...` is **FALSE** as written for `p = 0` (there `Coeff 0 = ℤ` and the
statement is the `ℤ`-coefficient statement, which fails); the corrected statement carries the
hypothesis `(hp : p.Prime)`.  The *definition* `FiniteSupportTwist` (the `μ_p`-twisted statement,
which the chapter's consumers — in particular `NK.NUV2.LC.finite_support_loc_odd_of_twist` and
`NK.NUV2.LC.finite_support_loc_twist` — import from this module) is indispensable and is restored
here verbatim, together with the proved reduction `finite_support_loc_two_of_twist`.  The
general-`p` statement is deliberately *not* restored: it is false, and its corrected (prime-`p`)
form can be added at (or beside) this path by whoever owns it.
-/

namespace NK.NUV2.LC

open IsDedekindDomain

/-- **The `μ_p`-twisted form of finite support** (the arithmetic core of `finite_support_loc`).

For a class `x` of the *cyclotomic* (`μ_p = Z/p(1)`-twisted) profinite cohomology `H²(U, μ_p)`,
the set of primes `𝔭` of `K` carrying a place `A` of `K'` with non-vanishing localisation is finite.
This is the classical "Brauer classes are ramified at only finitely many places"
(Hasse–Brauer–Noether / the fundamental theorem of class field theory); see
`Submission/Work/NUV2/LC/NOTES_finite_support_loc.md` for the route and for why no level-wise
formulation can be true. -/
def FiniteSupportTwist (p : ℕ) : Prop :=
  ∀ {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    {U : Subgroup Gal(K'/K)} (x : NK.BrauerTwist.H2Twist (K := K) (K' := K') p U),
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
      ∃ A : NK.BrauerTwist.OverFinitePrime K K',
        A.1.comap (algebraMap K K') =
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 ∧
        NK.BrauerTwist.H2Twist.loc p U x A ≠ 0}.Finite

/-- **`p = 2` reduces to the twisted statement.**  At `p = 2` the coefficient modules `Z/2` and
`μ_2` agree (characteristic `0`), so the twisted and the trivial profinite cohomology are canonically
identified (`NK.IndecomposedDeep.compareEquiv`), and a non-vanishing trivial-theory localisation
transfers to a non-vanishing twisted-theory localisation
(`NK.IndecomposedDeep.compareEquiv_loc`).  Hence the target at `p = 2` is implied by
`FiniteSupportTwist 2`. -/
theorem finite_support_loc_two_of_twist (h : FiniteSupportTwist 2)
    {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    {U : Subgroup Gal(K'/K)} (x : NK.BrauerHasse.H2Profinite (K := K) (K' := K') 2 U) :
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
      ∃ A : NK.BrauerHasse.OverFinitePrime K K',
        A.1.comap (algebraMap K K') =
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭 ∧
        NK.BrauerHasse.H2Profinite.loc 2 U x A ≠ 0}.Finite := by
  refine Set.Finite.subset
    (h (NK.IndecomposedDeep.compareInvFun (K := K) (K' := K') U x)) ?_
  intro 𝔭 hmem
  rcases hmem with ⟨A, hA, hloc⟩
  refine ⟨⟨A.1, fun htop => A.2 (by rw [htop])⟩, hA, ?_⟩
  have hx : (NK.IndecomposedDeep.compareEquiv (K := K) (K' := K') U)
      (NK.IndecomposedDeep.compareInvFun (K := K) (K' := K') U x) = x :=
    NK.IndecomposedDeep.compare_right_inv (K := K) (K' := K') U x
  have hloc' : NK.BrauerHasse.H2Profinite.loc 2 U
      ((NK.IndecomposedDeep.compareEquiv (K := K) (K' := K') U)
        (NK.IndecomposedDeep.compareInvFun (K := K) (K' := K') U x))
      ⟨A.1, fun htop => A.2 (by rw [htop])⟩ ≠ 0 := by
    rw [hx]; exact hloc
  exact NK.IndecomposedDeep.compareEquiv_loc (K := K) (K' := K') U
    ⟨A.1, fun htop => A.2 (by rw [htop])⟩
    (NK.IndecomposedDeep.compareInvFun (K := K) (K' := K') U x) hloc'

end NK.NUV2.LC
