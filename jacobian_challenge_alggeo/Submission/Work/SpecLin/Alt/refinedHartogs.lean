import Mathlib
import Submission.Work.SpecLin.Alt.conservationNumber
import Submission.Work.SpecLin.Setup.hartogsRelativeCurve

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.SpecLin.Alt

/-! ## The `N`-localised regularity (Hartogs) statement for the relative curve

`Work.SpecLin.Alt.refinedHartogs` is the "regularity" (R) half of the unit step of the
affine-chart core of specialisation of linear equivalence: a rational function on the relative
curve `B = A ⊗[K] R` which is regular at the fibre prime `P = 𝔪_R · B` and at every height-one
prime contained in `N` is regular at `N`.

It is proved by `Work.SpecLin.Setup.hartogsRelativeCurve` (which rests on
`Work.SpecLin.Setup.hartogsBridge`): a *descent along the generic fibre*.  Assuming the negation
(the denominator ideal `D` of `x` is contained in `N`), one shows that `x` lies in the
localisation `O = B[(B∖N)·ι(R∖{0})]⁻¹`; the primes of `O` are the primes `q ⊆ N` with
`q ∩ R = 0`, they inject height-preservingly into the one-dimensional generic fibre
`A ⊗[K] Frac R`, hence have height `≤ 1` and the height-one hypothesis applies to them.  Writing
`x = b/(w·ι r)` with `w ∉ N`, `r ∈ R∖{0}`, the element `x·w` is regular at the fibre prime
(`x ∈ B_P`, `w ∉ P`) and lies in the generic fibre, so the descent lemma
`Work.SpecLin.Alt.B_eq_inter_localizations` gives `x·w ∈ B`, and since `w ∉ N` this yields
`x ∈ B_N`, contradicting `D ≤ N`. -/
theorem refinedHartogs {K : Type u} [Field K] (A : Type u) [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] [Algebra.Smooth K A] [Ring.KrullDimLE 1 A]
    (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (N : Ideal (TensorProduct K A R)) [N.IsMaximal]
    (hPN : ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))) ≤ N)
    (x : FractionRing (TensorProduct K A R))
    (hxP : Work.SpecLin.Alt.InLocalization x ((IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (hxq : ∀ p : Ideal (TensorProduct K A R), p.IsPrime → p.height = 1 → p ≤ N →
      Work.SpecLin.Alt.InLocalization x p) :
    Work.SpecLin.Alt.InLocalization x N :=
  Work.SpecLin.Setup.hartogsRelativeCurve (K := K) A hA R N hPN x hxP hxq

end Work.SpecLin.Alt
