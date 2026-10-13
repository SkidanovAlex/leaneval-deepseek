import Mathlib
import Submission.Work.DSM2p.Construction
import Submission.Work.DSM2p.rootClosure_flat

/-!
# `p`-torsion-freeness of the `p`-integral closure `A'`

If `p : ℕ` is a non-zero-divisor of `A`, then `p` is a non-zero-divisor of the `p`-integral
closure `A' = CSIntegralClosure A p ϖ = pIntClosure p (CSAlg A p ϖ) ⊆ Λ[1/ϖ]`
(`Construction.lean`).

`A'` is by definition a subring of `Λ[1/ϖ] = RootAlgLoc A p ϖ`, so it suffices to show that `p`
remains a non-zero-divisor of `Λ[1/ϖ]`.  This is the flat base change `A → Λ` followed by the
localisation `Λ → Λ[1/ϖ]`:

* `rootClosure_flat` : `Λ = RootAlg A p = rootClosure A p 𝒫` is `A`-flat, so a non-zero-divisor
  of `A` stays a non-zero-divisor after tensoring (`IsSMulRegular.of_flat`);
* `IsSMulRegular.of_isLocalization` : localising at `ϖ` again preserves non-zero-divisors.

Finally, a non-zero-divisor of a ring remains one on any subring.
-/

namespace Work.DSM2p

universe u

/-- **A non-zero-divisor of `A` is a non-zero-divisor of every flat `A`-algebra.** -/
theorem natCast_isSMulRegular_of_flat (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] [Module.Flat A B] (p : ℕ) (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular B (p : B) := by
  simpa only [map_natCast] using IsSMulRegular.of_flat (S := B) hp

/-- **A non-zero-divisor remains a non-zero-divisor after localisation at a submonoid.** -/
theorem natCast_isSMulRegular_of_isLocalization (R : Type u) [CommRing R] (S : Type u)
    [CommRing S] [Algebra R S] (m : Submonoid R) [IsLocalization m S]
    (p : ℕ) (hp : IsSMulRegular R (p : R)) : IsSMulRegular S (p : S) := by
  simpa only [map_natCast] using IsSMulRegular.of_isLocalization S m hp

/-- **A non-zero-divisor of a ring remains one on a subring.** -/
theorem natCast_isSMulRegular_of_subring (S : Type u) [CommRing S] (R : Subring S)
    (p : ℕ) (hp : IsSMulRegular S (p : S)) : IsSMulRegular R (p : R) := by
  intro x y hxy
  refine Subtype.ext (hp ?_)
  show (p : S) • (Subring.subtype R x) = (p : S) • (Subring.subtype R y)
  have h3 := congrArg (Subring.subtype R) hxy
  simpa only [smul_eq_mul, map_mul, map_natCast] using h3

/-- **`p`-torsion-freeness of the `p`-integral closure `A'`.** -/
theorem CSIntegralClosure_isSMulRegular (A : Type*) [CommRing A] (p : ℕ) (ϖ : A)
    (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (CSIntegralClosure A p ϖ) (p : CSIntegralClosure A p ϖ) := by
  -- `p` is a non-zero-divisor of `Λ = RootAlg A p`, which is a flat `A`-algebra.
  have hflat : Module.Flat A (RootAlg A p) := rootClosure_flat A p (MonicPolys A)
  have hΛ : IsSMulRegular (RootAlg A p) (p : RootAlg A p) :=
    natCast_isSMulRegular_of_flat A (RootAlg A p) p hp
  -- localising at `ϖ` preserves non-zero-divisors
  have hLoc : IsSMulRegular (RootAlgLoc A p ϖ) (p : RootAlgLoc A p ϖ) :=
    natCast_isSMulRegular_of_isLocalization (RootAlg A p) (RootAlgLoc A p ϖ)
      (Submonoid.powers (algebraMap A (RootAlg A p) ϖ)) p hΛ
  -- and so does passing to the subring `A' = CSIntegralClosure A p ϖ`
  exact natCast_isSMulRegular_of_subring (RootAlgLoc A p ϖ) (CSIntegralClosure A p ϖ) p hLoc

end Work.DSM2p
