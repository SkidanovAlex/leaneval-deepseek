import Mathlib
import Submission.NK.NUV2.RouteB.RayModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.localFactorProductFormulaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The idèle of a fractional ideal, as a product of one-place idèles

`NOTE_orthogonality_route.md` §2 (i).  `ZDataMup.fracIdele 𝔵` is `ideleOfFun` of the exponents of
`𝔵` (`NK.NUV2.RouteB.RayModulus.fracIdele`), i.e. `1` at the archimedean places and
`unifUnit 𝔮 ^ count 𝔮 𝔵` at the finite places.  This file writes it as the *finite product* of
one-place idèles over the support of `𝔵`, the form in which the Artin map can be evaluated prime by
prime (`ideleArtin_ideleOfPrime_of_unramified` gives the Frobenius value at an unramified prime).
-/

open scoped NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSGRoute.GrunwaldEscapeCore

variable {K : Type} [Field K] [NumberField K]

/-- **`ideleOfFun` as a product of one-place idèles over its support.** -/
theorem ideleOfFun_eq_prod_onePlace (f : NK.Chebotarev.PrimeIdeal K → ℤ)
    (hf : ∀ᶠ q in Filter.cofinite, f q = 0) :
    IdeleClassGroup.ideleOfFun K f hf =
      ∏ q ∈ (Filter.eventually_cofinite.mp hf).toFinset,
        NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^ (f q)) := by
  classical
  refine Idele.ext (fun v => ?_)
  have hmem : ∀ q : NK.Chebotarev.PrimeIdeal K,
      q ∈ (Filter.eventually_cofinite.mp hf).toFinset ↔ f q ≠ 0 := by
    intro q
    rw [Set.Finite.mem_toFinset]
    exact Iff.rfl
  rcases v with w | q
  · -- archimedean place: both sides are `1`
    rw [Work.SSGRoute.ZDataMup.Idele_prod_apply]
    rw [Finset.prod_eq_one (fun b _ =>
      NK.HassePrinciple.onePlace_apply_ne (v := NK.GlobalCFT.Place.ofInfinite w)
        (w := NK.GlobalCFT.Place.ofFinite b) (by simp) _)]
    rfl
  · -- finite place
    rw [Work.SSGRoute.ZDataMup.Idele_prod_apply]
    by_cases hq : q ∈ (Filter.eventually_cofinite.mp hf).toFinset
    · rw [Finset.prod_eq_single_of_mem q hq (fun b hb hbq =>
        NK.HassePrinciple.onePlace_apply_ne (v := NK.GlobalCFT.Place.ofFinite q)
          (w := NK.GlobalCFT.Place.ofFinite b)
          (fun h => hbq ((NK.GlobalCFT.Place.ofFinite_inj.mp h).symm)) _)]
      simp only [NK.HassePrinciple.onePlace_apply_self]
      rfl
    · have hfq : f q = 0 := by
        by_contra h
        exact hq ((hmem q).mpr h)
      rw [show (IdeleClassGroup.ideleOfFun K f hf) (Sum.inr q) =
          NK.GlobalCFT.IdeleClassGroup.unifUnit K q ^ (f q) from rfl, hfq, zpow_zero,
        Finset.prod_eq_one (fun b hb =>
          NK.HassePrinciple.onePlace_apply_ne (v := NK.GlobalCFT.Place.ofFinite q)
            (w := NK.GlobalCFT.Place.ofFinite b)
            (fun h => hq ((NK.GlobalCFT.Place.ofFinite_inj.mp h).symm ▸ hb)) _)]

end Work.SSGRoute.GrunwaldEscapeCore
