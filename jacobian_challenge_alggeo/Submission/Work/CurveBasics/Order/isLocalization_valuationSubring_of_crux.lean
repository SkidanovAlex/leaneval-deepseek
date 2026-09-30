import Mathlib
import Submission.Work.CurveBasics.Order.RamificationSetup
import Submission.Work.CurveBasics.Order.Bridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Order

/-- **From the `CruxStatement` to the localisation statement.**

The `CruxStatement` says that every element of the valuation subring `𝒪_Q` at a place `Q` where `h`
vanishes can be written as `a / s` with `a` integral over `k[h]` and `s` integral over `k[h]` with
`s ∉ kxPrimeOfPlace C h Q`.  That is precisely the statement that `𝒪_Q` is the localisation of the
integral closure `k[h]^int` at the prime `kxPrimeOfPlace C h Q`.

The algebra structure `Algebra (C.kxClosure h) ↥(Q.valuationSubring)` is not assumed to be the
canonical one, but `halg` pins it down to the inclusion `kxClosure_le_valuationSubring`. -/
theorem isLocalization_valuationSubring_of_crux {k : Type*} [Field k] (C : Curve k)
    (h : C.functionField) (Q : C.Place) (hQ : 0 < C.ordAt h Q)
    (hcrux : CruxStatement C h Q hQ)
    [Algebra (C.kxClosure h) ↥(Q.valuationSubring)]
    (halg : ∀ x : C.kxClosure h,
      algebraMap (C.kxClosure h) ↥(Q.valuationSubring) x =
        Subring.inclusion (kxClosure_le_valuationSubring C h Q hQ.le) x)
    [(kxPrimeOfPlace C h Q hQ.le).IsPrime] :
    IsLocalization (kxPrimeOfPlace C h Q hQ.le).primeCompl ↥(Q.valuationSubring) := by
  -- The given algebra structure, read in the function field, is the identity.
  have coe_eq : ∀ x : C.kxClosure h,
      ((algebraMap (C.kxClosure h) ↥(Q.valuationSubring) x : ↥(Q.valuationSubring)) :
        C.functionField) = (x : C.functionField) := by
    intro x
    rw [halg x, Subring.coe_inclusion]
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- Elements outside the prime become units: they do not lie in the maximal ideal.
    intro y
    have hy : Subring.inclusion (kxClosure_le_valuationSubring C h Q hQ.le) (y : C.kxClosure h)
        ∉ IsLocalRing.maximalIdeal ↥(Q.valuationSubring) := fun hmem =>
      (Ideal.mem_primeCompl_iff.mp y.2) (Ideal.mem_comap.mpr hmem)
    have hunit : IsUnit (Subring.inclusion (kxClosure_le_valuationSubring C h Q hQ.le)
        (y : C.kxClosure h)) :=
      (IsLocalRing.notMem_maximalIdeal (R := ↥(Q.valuationSubring))).mp hy
    rw [halg (y : C.kxClosure h)]
    exact hunit
  · -- Surjectivity: every element of the valuation subring is `a / s` with `s` invertible.
    intro z
    obtain ⟨s, a, hs, hsa⟩ := hcrux z z.2
    refine ⟨(a, ⟨s, hs⟩), ?_⟩
    apply Subtype.ext
    rw [Subring.coe_mul, coe_eq, coe_eq, mul_comm]
    exact hsa
  · -- The kernel condition is trivial: the structure map is injective.
    intro x y hxy
    have hinj : Subring.inclusion (kxClosure_le_valuationSubring C h Q hQ.le) x =
        Subring.inclusion (kxClosure_le_valuationSubring C h Q hQ.le) y := by
      rw [← halg x, ← halg y, hxy]
    have hxy' : x = y := Subring.inclusion_injective _ hinj
    refine ⟨1, ?_⟩
    simp [hxy']

end Work.CurveBasics.Order
