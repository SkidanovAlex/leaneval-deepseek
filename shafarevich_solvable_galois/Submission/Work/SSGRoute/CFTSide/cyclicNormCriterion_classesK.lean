import Submission.Work.SSGRoute.CFTSide.cyclicNormCriterion_kills_norms
import Submission.Work.SSGRoute.CFTSide.cyclicNormCriterion_transgression
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclic norm criterion with `C_L` coefficients, assembled from its two halves

`Work.SSGRoute.CFTSide.cyclicNormCriterion_transgression` is the hard direction (the transgression
argument: the vanishing of `a ∪ δh` forces `a` to be a norm) and
`Work.SSGRoute.CFTSide.cyclicNormCriterion_kills_norms` is the easy direction (the coefficient map
`1 ↦ a` factors through the trace, so norms are killed).  Together they give the criterion
`a ∪ δh = 0 ↔ a ∈ N_{L/k}C_L` for `Gal(L/k)` cyclic of prime order `p`, which is the CFT input of
the base case `φ¹` (nodes `E3` / `E3Ω`).
-/

namespace Work.SSGRoute.CFTSide

open SSGRoute.PTExt CategoryTheory

/-- **The cyclic norm criterion** (`C_L` coefficients): for `Gal(L/k)` cyclic of prime order `p`,
an element `a` of `C_L` fixed by `Gal(L/k)` and a nonzero character `h ∈ H¹(Gal(L/k), 𝔽_p)`, the
cup product class `groupCohomology.map (id) (powHomCls a) 2 (δ h)` (with `δ` the Bockstein, the
connecting map of `SSGRoute.Phi1.coeffSES`) vanishes if and only if `a` is a norm from `L`. -/
theorem cyclicNormCriterion_classesK (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime] (hcyc : IsCyclic (L ≃ₐ[k] L)) (hcard : Nat.card (L ≃ₐ[k] L) = p)
    (a : SSGRoute.PTExt.classesK k L)
    (hafix : ∀ σ : L ≃ₐ[k] L, (SSGRoute.PTExt.classesK k L).ρ σ a = a)
    (h : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p)) 1) (hne : h ≠ 0) :
    (groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
          (SSGRoute.Phi1.powHomCls k L a hafix) 2
          ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom h)
        = 0) ↔
      a ∈ Set.range ((SSGRoute.PTExt.classesK k L).norm.hom) :=
  ⟨fun hvan => cyclicNormCriterion_transgression k L p hcyc hcard a hafix h hne hvan,
   fun hnorm => cyclicNormCriterion_kills_norms k L p a hafix hnorm h⟩

end Work.SSGRoute.CFTSide
