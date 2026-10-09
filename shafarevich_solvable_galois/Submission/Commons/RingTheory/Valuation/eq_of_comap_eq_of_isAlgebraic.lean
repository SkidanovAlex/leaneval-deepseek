import Mathlib
import Submission.Commons.RingTheory.Valuation.isIntegral_of_mem_of_henselian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Unique extension of a henselian valuation to an algebraic extension

Let `V` be a henselian valuation subring of a field `K` and let `L/K` be algebraic.  Then `V`
has at most one extension to a valuation subring of `L`: if `W₁, W₂ : ValuationSubring L` both
pull back to `V` along `algebraMap K L`, then `W₁ = W₂`.

The proof uses the fact that every element of an extension of a henselian valuation subring is
integral over `V` (`isIntegral_of_mem_of_henselian`); a valuation subring is integrally closed,
so any element of `W₁` is integral over `V ⊆ W₂` and hence lies in `W₂`, and conversely.
-/

namespace Commons.RingTheory.Valuation

/-- Any element that is integral over `V` lies in a valuation subring `W` of `L` whose
intersection with `K` is `V`. -/
private lemma mem_of_isIntegral_of_comap_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring K) (W : ValuationSubring L) (hW : W.comap (algebraMap K L) = V)
    {x : L} (hx : IsIntegral V x) : x ∈ W := by
  have hAW : (integralClosure V L).toSubring ≤ W.toSubring := by
    have : IsIntegrallyClosedIn ↥W.toSubring L :=
      Subring.isIntegrallyClosedIn_iff.mpr fun z hz =>
        LocalSubring.mem_of_isMax_of_isIntegral W.isMax_toLocalSubring hz
    exact Subring.integralClosure_le_iff.mpr fun r => by
      rw [IsScalarTower.algebraMap_apply V K L, ValuationSubring.algebraMap_apply]
      exact (ValuationSubring.mem_toSubring W _).mpr
        ((ValuationSubring.mem_comap).mp ((SetLike.ext_iff.mp hW (r : K)).mpr r.2))
  exact hAW ((mem_integralClosure_iff (R := V) (A := L)).mpr hx)

theorem eq_of_comap_eq_of_isAlgebraic {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (V : ValuationSubring K) [HenselianLocalRing V]
    (W₁ W₂ : ValuationSubring L) (h₁ : W₁.comap (algebraMap K L) = V)
    (h₂ : W₂.comap (algebraMap K L) = V) : W₁ = W₂ := by
  apply ValuationSubring.toSubring_injective
  apply le_antisymm
  · intro x hx
    exact mem_of_isIntegral_of_comap_eq V W₂ h₂
      (isIntegral_of_mem_of_henselian V W₁ h₁ hx)
  · intro x hx
    exact mem_of_isIntegral_of_comap_eq V W₁ h₁
      (isIntegral_of_mem_of_henselian V W₂ h₂ hx)

end Commons.RingTheory.Valuation
