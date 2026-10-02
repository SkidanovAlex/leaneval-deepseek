import Mathlib
import Submission.Work.Thom.transgressionFleetDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Commutation of the descended cup product with the differential

`Work.Thom.cupDescendMor X A U V n p t ht` is the cup product with a cochain `t` which vanishes on
the subset `A ⊆ X`, descended to the relative small chains `C^{U,V}_*(X,A)` of the cover
`X = U ∪ V`.  It sends a functional `ψ` on the small `p`-chains of the cover to the functional
`z ↦ (ψ ⌣ t)(z)` on the relative `(p+n)`-chains.

The Alexander–Whitney Leibniz rule `δ(ψ ⌣ t) = (δψ) ⌣ t + (-1)^p ψ ⌣ (δt)` shows that for a
*cocycle* `t` (`cochainDiff t = 0`) cupping with `t` is a chain map of degree `n`, i.e. the
descended cup map commutes (up to the transport of the degree `(p+1)+n = p+n+1`) with the
differentials of the two dual complexes.  This identity is `cupDescendMor_d_comm` below; it is the
ingredient which makes `cupDescendMor` a morphism of the Mayer–Vietoris short exact sequences.

The proof is elementary.  Both sides live in the dual of `C^{U,V}_{p+n+1}(X,A)`; since the cokernel
projection `C^{U,V}_*(X) ⟶ C^{U,V}_*(X,A)` is degreewise epi, it suffices to check the identity on
the small chains of the cover, where it reduces to the Leibniz rule together with the fact that the
restriction `restrSmall` of a cocycle to the small simplices is again a cocycle.

## Main results

* `restSmall_cochainDiff`, `restrSmall_cocycle` — restriction to the small simplices commutes with
  the coboundary;
* `cup_d_cocycle` — the Leibniz rule with one of the two factors a cocycle;
* `cast_comp_XIsoOfEq` — a functional transported along an equality of degrees is the original one
  precomposed with the transport;
* `cupDescendMor_d_comm` — the main identity.
-/

namespace Work.Thom

open CategoryTheory CategoryTheory.Limits Work.Cohomology
open scoped Simplicial

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-! ## Transporting along an equality of degrees -/

/-- The transpose of `XIsoOfEq` for the dual cochain complex is precomposition with the transport:
`(XIsoOfEq (dualComplex ℤ C) h).inv` sends a functional `x` on the chains in degree `b` to
`x ∘ ξ`, where `ξ : C.X a ⟶ C.X b` is the transport along `h : a = b`. -/
lemma XIsoOfEq_dual_inv_apply (C : ChainComplex (ModuleCat ℤ) ℕ) {a b : ℕ} (h : a = b)
    (x : (dualComplex ℤ C).X b) :
    ModuleCat.Hom.hom (HomologicalComplex.XIsoOfEq (dualComplex ℤ C) h).inv x
      = x ∘ₗ (ModuleCat.Hom.hom (HomologicalComplex.XIsoOfEq C h).hom) := by
  cases h; rfl

/-- A functional transported along an equality of degrees, precomposed with the transport, is the
original functional.  The two proofs `h₁`, `h₂` of the degree equality are a priori different
(`h₁` comes from the Leibniz rule, `h₂` from the statement), which is why they are both explicit. -/
lemma cast_comp_XIsoOfEq (C : ChainComplex (ModuleCat ℤ) ℕ) {a b : ℕ} (h₁ h₂ : a = b)
    (F : (dualComplex ℤ C).X a) :
    ((show ↑(C.X b) →ₗ[ℤ] ℤ from h₁ ▸ F)
        ∘ₗ ModuleCat.Hom.hom (HomologicalComplex.XIsoOfEq C h₂).hom)
      = (show ↑(C.X a) →ₗ[ℤ] ℤ from F) := by
  rw [Subsingleton.elim h₁ h₂]
  cases h₂
  rfl

/-! ## The differential of the dual complex -/

/-- The differential of the dual complex is the transpose of the boundary. -/
lemma dualComplex_d_apply (C : ChainComplex (ModuleCat ℤ) ℕ) (m : ℕ)
    (y : (dualComplex ℤ C).X m) :
    ModuleCat.Hom.hom ((dualComplex ℤ C).d m (m+1)) y
      = y ∘ₗ (ModuleCat.Hom.hom (C.d (m+1) m)) := by
  simp only [Work.Cohomology.dualComplex, CochainComplex.of_d, Work.Cohomology.dualDiff,
    ModuleCat.hom_ofHom]
  rfl

/-- The coboundary of a cochain on the small simplices of the cover is the transpose of the
boundary, i.e. the differential of the dual complex of the small chains. -/
lemma cochainDiff_small_eq (X : TopCat) (U V : Set X) (p : ℕ)
    (ψ : (dualComplex ℤ (smallChains U V)).X p) :
    cochainDiff ℤ (smallSSet U V) ψ
      = ModuleCat.Hom.hom ((dualComplex ℤ (smallChains U V)).d p (p+1)) ψ := by
  rw [dualComplex_d_apply]
  rfl

/-! ## Restriction to the small simplices -/

/-- **Restriction to the small simplices commutes with the coboundary.**  The restriction is the
transpose of the degreewise inclusion of the small chains, hence it is a morphism of cochain
complexes. -/
lemma restrSmall_cochainDiff (X : TopCat) (U V : Set X) (n : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n) :
    restrSmall X U V (n+1) (cochainDiff ℤ (TopCat.toSSet.obj X) t)
      = cochainDiff ℤ (smallSSet U V) (restrSmall X U V n t) := by
  have hcomm := HomologicalComplex.Hom.comm
    (SSet.chainComplexMap (smallSubcomplex U V).ι (ModuleCat.of ℤ ℤ)) (n+1) n
  have hcomm' := congrArg (fun k => ModuleCat.Hom.hom k) hcomm
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hcomm'
  apply LinearMap.ext; intro x
  simp only [restrSmall, cochainDiff, LinearMap.comp_apply, LinearMap.dualMap_apply]
  have key := LinearMap.congr_fun hcomm' x
  simp only [LinearMap.comp_apply] at key
  rw [key]

/-- **The restriction of a cocycle to the small simplices is a cocycle.** -/
lemma restrSmall_cocycle (X : TopCat) (U V : Set X) (n : ℕ)
    (t : Cochain ℤ (TopCat.toSSet.obj X) n)
    (hdt : cochainDiff ℤ (TopCat.toSSet.obj X) t = 0) :
    cochainDiff ℤ (smallSSet U V) (restrSmall X U V n t) = 0 := by
  rw [← restrSmall_cochainDiff, hdt]
  simp [restrSmall]

/-! ## The Leibniz rule with one factor a cocycle -/

/-- **The Leibniz rule for a degree `p` cochain and a degree `n` cocycle**:
`δ(ψ ⌣ t) = (δψ) ⌣ t`, with the product transported to the degree `(p+1)+n = p+n+1`. -/
lemma cup_d_cocycle (X : SSet) (p n : ℕ) (ψ : Cochain ℤ X p) (t' : Cochain ℤ X n)
    (hdt : cochainDiff ℤ X t' = 0) (h : (p+1)+n = p+n+1) :
    cochainDiff ℤ X (cup ℤ X ψ t')
      = h ▸ (cup ℤ X (cochainDiff ℤ X ψ) t') := by
  have hleib := cupLeibniz ℤ X ψ t'
  rw [hdt] at hleib
  rw [cup_zero_right', smul_zero, add_zero] at hleib
  have hh0 : Nat.add_right_comm p 1 n = h := Subsingleton.elim _ _
  rwa [hh0] at hleib

/-! ## The main identity -/

theorem cupDescendMor_d_comm (X : TopCat) (A U V : Set X) (n p : ℕ)
    (t : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) n) (ht : t ∈ Work.Cohomology.relKern ℤ X A n)
    (hdt : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t = 0)
    (ψ : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.smallChains U V)).X p) :
    ModuleCat.Hom.hom (Work.Thom.cupDescendMor X A U V n (p+1) t ht
        (ModuleCat.Hom.hom ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.smallChains U V)).d p (p+1)) ψ))
      = ModuleCat.Hom.hom (HomologicalComplex.XIsoOfEq (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V))
            (by omega : (p+1)+n = p+n+1)).inv
          (ModuleCat.Hom.hom ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relMVTopC X A U V)).d (p+n) (p+n+1))
            (ModuleCat.Hom.hom (Work.Thom.cupDescendMor X A U V n p t ht ψ))) := by
  -- The right hand side, up to the transport of the outer `XIsoOfEq`, is the cup product with the
  -- *coboundary* of `ψ`, so it suffices to compare both sides after composition with the cokernel
  -- projection `C^{U,V}_*(X) ⟶ C^{U,V}_*(X,A)` (which is degreewise epi).
  rw [XIsoOfEq_dual_inv_apply]
  rw [show (ModuleCat.Hom.hom ((dualComplex ℤ (relMVTopC X A U V)).d (p+n) (p+n+1)))
        (ModuleCat.Hom.hom (cupDescendMor X A U V n p t ht ψ))
      = ModuleCat.Hom.hom ((relMVTopC X A U V).d (p+n+1) (p+n) ≫
          cupDescendMor X A U V n p t ht ψ) from ?_]
  swap
  · rw [dualComplex_d_apply, ModuleCat.hom_comp]
  rw [← ModuleCat.hom_comp]
  apply congrArg (fun k => ModuleCat.Hom.hom k)
  have hEpi : Epi ((cokernel.π (smallInToSmall U V A)).f ((p+1)+n)) :=
    epi_cokernel_π_f (smallInToSmall U V A) ((p+1)+n)
  refine (cancel_epi ((cokernel.π (smallInToSmall U V A)).f ((p+1)+n))).mp ?_
  -- the left hand side is the cup product with the coboundary of `ψ`, by `cupDescendMor_spec`
  rw [cupDescendMor_spec X A U V n (p+1) t ht
    (ModuleCat.Hom.hom ((dualComplex ℤ (smallChains U V)).d p (p+1)) ψ)]
  -- on the right, the transport commutes with the cokernel projection and with the differential
  rw [← Category.assoc]
  rw [HomologicalComplex.XIsoOfEq_hom_naturality]
  rw [Category.assoc]
  rw [HomologicalComplex.Hom.comm_assoc]
  -- and the projection intertwines the descended cup product with the cup product
  rw [cupDescendMor_spec X A U V n p t ht ψ]
  -- it remains to compare the cup products on the small chains: this is the Leibniz rule
  apply ModuleCat.hom_ext
  change (show ↑((smallChains U V).X ((p+1)+n)) →ₗ[ℤ] ℤ from
      cup ℤ (smallSSet U V) (ModuleCat.Hom.hom ((dualComplex ℤ (smallChains U V)).d p (p+1)) ψ)
        (restrSmall X U V n t))
    = (cochainDiff ℤ (smallSSet U V) (cup ℤ (smallSSet U V) ψ (restrSmall X U V n t)))
        ∘ₗ (ModuleCat.Hom.hom (HomologicalComplex.XIsoOfEq (smallChains U V)
              (by omega : (p+1)+n = p+n+1)).hom)
  have hdt' : cochainDiff ℤ (smallSSet U V) (restrSmall X U V n t) = 0 :=
    restrSmall_cocycle X U V n t hdt
  rw [cup_d_cocycle (smallSSet U V) p n ψ (restrSmall X U V n t) hdt'
        (show (p+1)+n = p+n+1 from by omega)]
  rw [cochainDiff_small_eq]
  exact (cast_comp_XIsoOfEq (smallChains U V) _ _ _).symm

end

end Work.Thom
