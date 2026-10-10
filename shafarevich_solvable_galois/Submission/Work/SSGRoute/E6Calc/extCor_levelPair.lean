import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.extCor_yoneda_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

namespace Work.SSGRoute.E6Calc

/-- **The corestriction of a level pairing.**  For a finite group `G`, a subgroup `S ≤ G`, `G`-modules
`M`, `A`, `B`, a class `x ∈ Ext^r_G(M, A)`, a coefficient map `c : A ⟶ B` and
`b ∈ H^s(S, res_S M) = Ext^s_S(unitRep S, Rep.res S.subtype M)`, corestricting the level-`S` value of
the pairing `(x, b)` — computed with the coefficient map `Rep.resMap S.subtype c` — is the level-`G`
value of the pairing of `x` with the corestricted class `cor b`, i.e. `(cor b) ∘ x ∘ c`.

Proof: apply `Work.SSGRoute.extCor_yoneda_comp` twice (once with `x` and `b`, once with `mk₀ c` and
`b.comp (extRes S.subtype x)`), using `mk₀ (Rep.resMap S.subtype c) = extRes S.subtype (mk₀ c)`
(`Abelian.Ext.mapExactFunctor_mk₀`) and `Abelian.Ext.comp_assoc`.

This is the formal heart of the Sylow descent `E6Ω`: with `c := classIncl k K L` at a level `L`,
`x := extRes (galRes k K L) x₀` and `b` a restricted class at the level `L`, the right-hand
side is `phiAt k K L x₀ (extCor S _ _ _ b)`, which vanishes by the hypothesis `PhiOneVanishesIn`, and
`ClassFormation.extCor_injective_classesK S` then gives the vanishing of the left-hand side. -/
theorem extCor_levelPair {G : Type} [Group G] [Fintype G] (S : Subgroup G)
    [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)]
    {M A B : Rep SSGRoute.PTExt.Coeff G} {r s : ℕ}
    (x : CategoryTheory.Abelian.Ext M A r)
    (b : SSGRoute.PTExt.extH (Rep.res S.subtype M) s)
    (c : A ⟶ B) :
    Work.SSGRoute.extCor S (SSGRoute.PTExt.unitRep G) B (s + r)
        (SSGRoute.PTExt.levelPair S.subtype (Rep.resMap S.subtype c) x b)
      = ((Work.SSGRoute.extCor S (SSGRoute.PTExt.unitRep G) M s b).comp x rfl).comp
          (CategoryTheory.Abelian.Ext.mk₀ c) (add_zero (s + r)) := by
  -- unfold the level-`S` pairing
  rw [SSGRoute.PTExt.levelPair]
  -- re-associate `b ∘ (res x ∘ c) = (b ∘ res x) ∘ c`
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero b (SSGRoute.PTExt.extRes S.subtype x)
        (Abelian.Ext.mk₀ (Rep.resMap S.subtype c)) rfl]
  -- second application of the projection formula, for `mk₀ c` and `b ∘ extRes x`
  have h2 := Work.SSGRoute.extCor_yoneda_comp S (Abelian.Ext.mk₀ c)
    (b.comp (SSGRoute.PTExt.extRes S.subtype x) rfl)
  have hmk : SSGRoute.PTExt.extRes S.subtype (Abelian.Ext.mk₀ c)
      = Abelian.Ext.mk₀ (Rep.resMap S.subtype c) := by
    rw [SSGRoute.PTExt.extRes, Abelian.Ext.mapExactFunctor_mk₀]
  rw [hmk] at h2
  -- first application of the projection formula, for `x` and `b`
  have hy1 := Work.SSGRoute.extCor_yoneda_comp S x b
  rw [← hy1]
  exact h2

end Work.SSGRoute.E6Calc
