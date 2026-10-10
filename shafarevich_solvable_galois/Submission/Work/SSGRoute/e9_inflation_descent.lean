import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.eCoh_map
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open scoped NumberField
open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute

noncomputable section

/-! ## Generic helpers: the quotient/invariant comparison for Mathlib's `groupCohomology`

Let `f : G →* H` be a surjective group homomorphism, `S = ker f`, `M` a representation of `H`
and `A = Rep.res f M` its restriction to `G`, on which `S` acts trivially.  Mathlib's
inflation–restriction sequence reads
`H¹(G ⧸ S, A^S) --inf--> H¹(G, A) --res--> H¹(S, A)`.  The results below identify the source
`H¹(G ⧸ S, A^S)` with `H¹(H, M)` along the canonical isomorphism `G ⧸ S ≃* H`, and show that
`inf` becomes `H¹(H, M) → H¹(G, A)` composed with the restriction `Rep.res f`.
-/

section Generic

variable {k : Type} [CommRing k] {G H : Type} [Group G] [Group H]

lemma quotientKerEquiv_apply_mk (f : G →* H) (hf : Function.Surjective f) (g : G) :
    (QuotientGroup.quotientKerEquivOfSurjective f hf) (QuotientGroup.mk' f.ker g) = f g := by
  change QuotientGroup.kerLift f (QuotientGroup.mk' f.ker g) = f g
  rw [QuotientGroup.mk'_apply]
  exact QuotientGroup.kerLift_mk f g

lemma quotientKerEquiv_symm_comp (f : G →* H) (hf : Function.Surjective f) :
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom.comp f
      = QuotientGroup.mk' f.ker := by
  ext g
  change (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f g)
    = QuotientGroup.mk' f.ker g
  apply (QuotientGroup.quotientKerEquivOfSurjective f hf).injective
  rw [MulEquiv.apply_symm_apply]
  exact (quotientKerEquiv_apply_mk f hf g).symm

/-- The descent morphism `(A^S) → M` for `A = Rep.res f M` and `S = ker f`, i.e. the canonical
identification of the `S`-invariants of `M` (viewed as a `G`-module through `f`) with `M`. -/
def descentPsi (f : G →* H) (hf : Function.Surjective f) (M : Rep k H) :
    Rep.res (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
      ((Rep.res f M).quotientToInvariants f.ker) ⟶ M :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ M.ρ (Submodule.subtype _)
    (fun q x => by
      show (Submodule.subtype _) (((Rep.res f M).quotientToInvariants f.ker).ρ
            ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm q) x)
          = M.ρ q (Submodule.subtype _ x)
      obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective f.ker
        ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm q)
      have hfg : f g = q := by
        have h2 := quotientKerEquiv_apply_mk f hf g
        rw [hg, MulEquiv.apply_symm_apply] at h2
        exact h2.symm
      rw [← hg]
      have h1 : Submodule.subtype _
            (((Rep.res f M).quotientToInvariants f.ker).ρ ((QuotientGroup.mk' f.ker) g) x)
          = (Rep.res f M).ρ g (Submodule.subtype _ x) :=
        Representation.IntertwiningMap.isIntertwining
          (((Rep.res f M).ρ.quotientToInvariants f.ker).comp (QuotientGroup.mk' f.ker))
          (Rep.res f M).ρ
          ((Rep.res f M).ρ.quotientToInvariants_lift f.ker) g x
      rw [← hfg]
      exact h1))

lemma descentPsi_toLinearMap (f : G →* H) (hf : Function.Surjective f) (M : Rep k H) :
    (Rep.Hom.hom (descentPsi f hf M)).toLinearMap
      = (Representation.quotientToInvariants_lift (Rep.res f M).ρ f.ker).toLinearMap := rfl

/-- **The inflation computation.**  For `f : G →* H` surjective, `A = Rep.res f M` and
`S = ker f`, the Mathlib inflation `H¹(G ⧸ S, A^S) → H¹(G, A)` factors as the descent
identification `H¹(G ⧸ S, A^S) → H¹(H, M)` (along `G ⧸ S ≃* H`) followed by the restriction of
cohomology `H¹(H, M) → H¹(G, A)`. -/
theorem infNatTrans_eq_comp_descent (f : G →* H) (hf : Function.Surjective f) (M : Rep k H)
    (γ : groupCohomology ((Rep.res f M).quotientToInvariants f.ker) 1) :
    ((groupCohomology.infNatTrans k f.ker 1).app (Rep.res f M)).hom γ
      = (groupCohomology.map f (𝟙 (Rep.res f M)) 1).hom
          ((groupCohomology.map (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
            (descentPsi f hf M) 1).hom γ) := by
  change (groupCohomology.map (QuotientGroup.mk' f.ker)
      (Rep.ofHom ((Rep.res f M).ρ.quotientToInvariants_lift f.ker)) 1).hom γ
    = (groupCohomology.map f (𝟙 (Rep.res f M)) 1).hom
        ((groupCohomology.map (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
          (descentPsi f hf M) 1).hom γ)
  have hfg : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom.comp f
      = QuotientGroup.mk' f.ker := quotientKerEquiv_symm_comp f hf
  let φterm : Rep.res ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom.comp f)
        ((Rep.res f M).quotientToInvariants f.ker) ⟶ Rep.res f M :=
    (Rep.resFunctor f).map (descentPsi f hf M) ≫ 𝟙 (Rep.res f M)
  have hlin : (Rep.Hom.hom φterm).toLinearMap
      = (Rep.Hom.hom (Rep.ofHom ((Rep.res f M).ρ.quotientToInvariants_lift f.ker))).toLinearMap := by
    dsimp only [φterm]
    rw [Rep.hom_comp]
    simp only [Representation.IntertwiningMap.comp_toLinearMap]
    rw [Rep.resMap_hom_toLinearMap, descentPsi_toLinearMap]
    rfl
  have hmain : groupCohomology.map (QuotientGroup.mk' f.ker)
        (Rep.ofHom ((Rep.res f M).ρ.quotientToInvariants_lift f.ker)) 1
      = groupCohomology.map
          ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom.comp f) φterm 1 :=
    groupCohomology.map_congr (f := QuotientGroup.mk' f.ker)
      (g := (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom.comp f)
      hfg.symm hlin.symm 1
  rw [hmain]
  rw [groupCohomology.map_comp (k := k)
    (f := (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom) (g := f)
    (φ := descentPsi f hf M) (ψ := 𝟙 (Rep.res f M)) 1]
  rfl

end Generic

/-! ## The target -/

/-- Inflation–restriction exactness in degree `1` for the `Ext`-core cohomology: for a tower
`k ⊆ K ⊆ L` of finite Galois number fields and a finite `Gal(K/k)`-module `M`, a class
`h ∈ H¹(Gal(L/k), res M)` whose restriction to `N = ker(galRes : Gal(L/k) → Gal(K/k))` vanishes is
the inflation of a class of `H¹(Gal(K/k), M)`.  (`N` acts trivially on `M`, so `M^N = M`.)
Route: transfer along the additive equivalence `Work.SSGRoute.eCoh n G A` (`Bridge.E`) to Mathlib's
`groupCohomology`, use the commons inflation–restriction exactness
`Commons.RepresentationTheory.GroupCohomology.range_infNatTrans_eq_ker_resNatTrans_of_subsingleton`
in degree `1` (whose hypothesis is vacuous), the identification `H¹(Gal(L/k)/N, M^N) ≃ H¹(Gal(K/k),
M)` along `galRes` (surjective with kernel `N`), and `Work.SSGRoute.eCoh_map` for naturality. -/
theorem e9_inflation_descent (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M]
    (h : extH (Rep.res (galRes k K L) M) 1)
    (hh : extHRestrict (galRes k K L).ker h = 0) :
    ∃ h' : extH M 1, inflH (k := k) (K := K) (L := L) h' = h := by
  let f : (L ≃ₐ[k] L) →* (K ≃ₐ[k] K) := galRes k K L
  have hf : Function.Surjective f :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := L)
  -- (1) move to Mathlib's `groupCohomology`
  let hc : groupCohomology (Rep.res f M) 1 := (eCoh 1 (L ≃ₐ[k] L) (Rep.res f M)).symm h
  have hc_spec : eCoh 1 (L ≃ₐ[k] L) (Rep.res f M) hc = h :=
    (eCoh 1 (L ≃ₐ[k] L) (Rep.res f M)).apply_symm_apply h
  -- (2) the restriction of `hc` to the kernel vanishes
  have hres0 : (groupCohomology.map f.ker.subtype
      (𝟙 (Rep.res f.ker.subtype (Rep.res f M))) 1).hom hc = 0 := by
    apply (eCoh 1 f.ker (Rep.res f.ker.subtype (Rep.res f M))).injective
    rw [eCoh_map 1 (L ≃ₐ[k] L) f.ker f.ker.subtype (Rep.res f M)
      (Rep.res f.ker.subtype (Rep.res f M)) (𝟙 _) hc]
    rw [hc_spec]
    rw [show extHMap f.ker.subtype (𝟙 (Rep.res f.ker.subtype (Rep.res f M))) h
        = extHRestrict f.ker h from rfl]
    rw [show f.ker = (galRes k K L).ker from rfl, hh, map_zero]
  -- (3) inflation–restriction exactness in degree `1` (commons, in `LinearMap.range = ker` form)
  have hrange :=
    Commons.RepresentationTheory.GroupCohomology.range_infNatTrans_eq_ker_resNatTrans_of_subsingleton
      (k := Coeff) (G := L ≃ₐ[k] L) f.ker (Rep.res f M) (r := 1) (by norm_num)
      (fun j hj hjr => by omega)
  have hmem : hc ∈ LinearMap.range
      (((groupCohomology.infNatTrans Coeff f.ker 1).app (Rep.res f M))).hom := by
    rw [hrange]
    exact hres0
  obtain ⟨γ, hγ⟩ := hmem
  -- (4) descend `γ ∈ H¹(Gal(L/k)/N, M^N)` to `H¹(Gal(K/k), M)`
  have key := infNatTrans_eq_comp_descent f hf M γ
  rw [hγ] at key
  -- (5) assemble
  refine ⟨eCoh 1 (K ≃ₐ[k] K) M
      ((groupCohomology.map
        (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
        (descentPsi f hf M) 1).hom γ), ?_⟩
  show inflH (k := k) (K := K) (L := L)
      (eCoh 1 (K ≃ₐ[k] K) M
        ((groupCohomology.map
          (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
          (descentPsi f hf M) 1).hom γ)) = h
  rw [show inflH (k := k) (K := K) (L := L)
        (eCoh 1 (K ≃ₐ[k] K) M
          ((groupCohomology.map
            (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
            (descentPsi f hf M) 1).hom γ))
      = extHMap f (𝟙 (Rep.res f M))
          (eCoh 1 (K ≃ₐ[k] K) M
            ((groupCohomology.map
              (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
              (descentPsi f hf M) 1).hom γ)) from rfl]
  rw [← eCoh_map 1 (K ≃ₐ[k] K) (L ≃ₐ[k] L) f M (Rep.res f M) (𝟙 _)
      ((groupCohomology.map
        (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom
        (descentPsi f hf M) 1).hom γ)]
  rw [← key, hc_spec]

end

end Work.SSGRoute
