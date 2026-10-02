import Mathlib
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.CapH
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.relChainsProjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cap product on cycles

This file descends the relative cap product `relCapHalf` of
`Submission/Work/Cohomology/RelCap.lean` to the cycle level, mirroring the absolute construction
`Work.Cohomology.capZ` of `Submission/Work/Cohomology/exists_capH.lean`.

The main theorem `relCapH` produces the pairing

  `⌢ : Z^n(X,A;ℤ) →ₗ (Z_{n+m}(X,A;ℤ) →ₗ Z_m(X;ℤ))`

whose value on a relative cocycle `z` and a relative cycle `c` is computed by the relative cap
product of the two underlying chains:

  `iCycles (z ⌢ c) = relCapHalf z (I (iCycles c))`,

where `I = relChains_cokernelIso` identifies the relative chains `C_{n+m}(X,A)` with the degreewise
cokernel of the inclusion `C_{n+m}(A) ⟶ C_{n+m}(X)`.

The only point to check is that the cap product of a relative *cocycle* with a relative *cycle* is an
absolute cycle: if `x` is any `(n+m)`-chain of `X` representing the relative cycle, then `dx` is
supported on `A`, and the cap product of a relative cochain with a chain supported on `A` vanishes.

## Main results

* `relChains_cokernelIso_canon` — `relChains_cokernelIso` is the canonical comparison with the
  cokernel projection;
* `relCapHalf_add`, `relCapHalf_zero`, `relCapHalf_smul` — `relCapHalf` is linear in the cochain;
* `relCapZHom_d` — the cap product of a relative cocycle with a relative cycle is a cycle;
* `relCapZ`, `relCapH` — the relative cap product on cycles, and the pairing `relCapH`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The comparison iso is the canonical one -/

/-- The general form of the canonicality of the comparison of a colimit with the colimit computed
degreewise: composing with the projection out of a colimit cocone and the comparison iso
`isoOfNatIso` of an isomorphism of diagrams gives the target projection. -/
theorem coconePointUniqueUpToIso_comp_isoOfNatIso_ι {J C : Type*} [Category J] [Category C]
    {F G : J ⥤ C} [HasColimit F] [HasColimit G]
    (s : Cocone F) (P : IsColimit s) (w : F ≅ G) (j : J) :
    s.ι.app j ≫ ((P.coconePointUniqueUpToIso (colimit.isColimit F)) ≪≫
        (HasColimit.isoOfNatIso w)).hom
      = w.hom.app j ≫ colimit.ι G j := by
  rw [Iso.trans_hom, ← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
  exact HasColimit.isoOfNatIso_ι_hom w j

/-- **`relChains_cokernelIso` is the canonical comparison**: composed with the projection
`cokernel.π (inclChains X A)` it is the degreewise cokernel projection. -/
theorem relChains_cokernelIso_canon (X : TopCat) (A : Set X) (n : ℕ) :
    (cokernel.π (inclChains X A)).f n ≫ (relChains_cokernelIso X A n).hom =
      cokernel.π ((inclChains X A).f n) := by
  simp only [relChains_cokernelIso]
  have hs : ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapCocone
      (colimit.cocone (parallelPair (inclChains X A) 0))).ι.app WalkingParallelPair.one
      = (cokernel.π (inclChains X A)).f n := rfl
  rw [← hs]
  rw [coconePointUniqueUpToIso_comp_isoOfNatIso_ι
    ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapCocone
      (colimit.cocone (parallelPair (inclChains X A) 0)))
    _ (eqToIso _) WalkingParallelPair.one]
  simp

/-- The elementwise form of `relChains_cokernelIso_canon`. -/
theorem relChains_cokernelIso_canon_apply (X : TopCat) (A : Set X) (n : ℕ)
    (z : (singularChains ℤ X).X n) :
    (relChains_cokernelIso X A n).hom (((cokernel.π (inclChains X A)).f n).hom z)
      = (cokernel.π ((inclChains X A).f n)).hom z := by
  have h := congrArg ModuleCat.Hom.hom (relChains_cokernelIso_canon X A n)
  simp only [ModuleCat.hom_comp] at h
  exact LinearMap.congr_fun h z

/-- The comparison iso is a (degreewise) retraction of its inverse. -/
theorem relChains_cokernelIso_inv_hom_apply (X : TopCat) (A : Set X) (n : ℕ)
    (a : (relChains X A).X n) :
    (relChains_cokernelIso X A n).inv.hom ((relChains_cokernelIso X A n).hom a) = a := by
  have h := congrArg ModuleCat.Hom.hom (relChains_cokernelIso X A n).hom_inv_id
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h a

/-! ## Linearity of `relCapHalf` in the cochain -/

/-- The relative cap product is additive in the (relative) cochain. -/
theorem relCapHalf_add (X : TopCat) (A : Set X) {n : ℕ} (α β : relKern ℤ X A n) (m : ℕ) :
    relCapHalf ℤ X A (α + β) m = relCapHalf ℤ X A α m + relCapHalf ℤ X A β m := by
  let f := (SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of ℤ ℤ)).f (n + m)
  haveI : Epi (cokernel.π f) := inferInstance
  refine (cancel_epi (cokernel.π f)).mp ?_
  rw [Preadditive.comp_add]
  rw [show cokernel.π f ≫ relCapHalf ℤ X A (α + β) m
        = capHom ℤ (TopCat.toSSet.obj X) (α + β).1 m from cokernel_π_relCapHalf ℤ X A (α + β) m]
  rw [show cokernel.π f ≫ relCapHalf ℤ X A α m
        = capHom ℤ (TopCat.toSSet.obj X) α.1 m from cokernel_π_relCapHalf ℤ X A α m]
  rw [show cokernel.π f ≫ relCapHalf ℤ X A β m
        = capHom ℤ (TopCat.toSSet.obj X) β.1 m from cokernel_π_relCapHalf ℤ X A β m]
  rw [show (α + β).1 = α.1 + β.1 from rfl, capHom_add]

/-- The relative cap product of the zero cochain vanishes. -/
theorem relCapHalf_zero (X : TopCat) (A : Set X) {n : ℕ} (m : ℕ) :
    relCapHalf ℤ X A (0 : relKern ℤ X A n) m = 0 := by
  have h := relCapHalf_add X A (0 : relKern ℤ X A n) 0 m
  rw [add_zero] at h
  have h' : relCapHalf ℤ X A (0 : relKern ℤ X A n) m + 0
      = relCapHalf ℤ X A (0 : relKern ℤ X A n) m
        + relCapHalf ℤ X A (0 : relKern ℤ X A n) m := by
    rw [add_zero]; exact h
  exact (add_left_cancel h').symm

/-- The underlying additive map of the relative cap product in the cochain. -/
noncomputable def relCapHalfAddHom (X : TopCat) (A : Set X) (n m : ℕ) :
    ↥(relKern ℤ X A n) →+ (relChainsModule ℤ X A (n + m) ⟶ singChains ℤ X m) where
  toFun α := relCapHalf ℤ X A α m
  map_zero' := relCapHalf_zero X A m
  map_add' α β := relCapHalf_add X A α β m

/-- The relative cap product is homogeneous in the (relative) cochain.  Since the map
`α ↦ relCapHalf α m` is additive, its `ℤ`-linearity is automatic (`AddMonoidHom.map_zsmul`). -/
theorem relCapHalf_smul (X : TopCat) (A : Set X) {n : ℕ} (r : ℤ) (α : relKern ℤ X A n)
    (m : ℕ) :
    relCapHalf ℤ X A (r • α) m = r • relCapHalf ℤ X A α m :=
  AddMonoidHom.map_zsmul (relCapHalfAddHom X A n m) r α

/-- The computation rule for `relCapHalf` on a degreewise cokernel representative. -/
theorem relCapHalf_apply_incl (X : TopCat) (A : Set X) {n m : ℕ} (α : relKern ℤ X A n)
    (c : (singularChains ℤ X).X (n + m)) :
    (relCapHalf ℤ X A α m).hom ((cokernel.π ((inclChains X A).f (n + m))).hom c)
      = (cap ℤ (TopCat.toSSet.obj X) α.1 m) c :=
  relCapHalf_apply ℤ X A (m := m) α c

/-! ## The relative cycles of `relComplex` -/

/-- A relative cocycle is a cocycle for the relative differential. -/
theorem relDiffLM_iCycles (X : TopCat) (A : Set X) (n : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    relDiffLM ℤ X A n (((relComplex ℤ X A).iCycles n).hom z) = 0 := by
  have h := congrArg
    (fun (g : (relComplex ℤ X A).cycles n ⟶ (relComplex ℤ X A).X (n+1)) => g.hom z)
    (HomologicalComplex.iCycles_d (relComplex ℤ X A) n (n+1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  rw [relComplex_d] at h
  exact h

/-- The underlying absolute cochain of a relative cocycle is an absolute cocycle. -/
theorem cochainDiff_relComplex_iCycles (X : TopCat) (A : Set X) (n : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    cochainDiff ℤ (TopCat.toSSet.obj X) (((relComplex ℤ X A).iCycles n).hom z).1 = 0 :=
  relClassOf_cochainDiff (R := ℤ) X A _ (relDiffLM_iCycles X A n z)

/-! ## The cap product of a relative cocycle with a relative cycle is a cycle -/

/-- **The cap product of a relative cocycle with a relative cycle is an absolute cycle.**

Composing the relative cap product (followed by the comparison `relChains_cokernelIso`) with the
differential of the singular chains is zero on relative cycles: for a lift `x` of the relative cycle,
the boundary `dx` is supported on `A`, where the relative cochain vanishes. -/
theorem relCapZHom_d (X : TopCat) (A : Set X) (n m : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    ((relChains X A).iCycles (n+m) ≫ (relChains_cokernelIso X A (n+m)).hom ≫
      relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom z) m) ≫
      (singularChains ℤ X).d m ((ComplexShape.down ℕ).next m) = 0 := by
  cases m with
  | zero =>
    rw [show (ComplexShape.down ℕ).next 0 = 0 from
      ComplexShape.next_eq_self' (ComplexShape.down ℕ) 0 (by
        intro k hk
        have hk' : k + 1 = 0 := hk
        omega)]
    rw [show (singularChains ℤ X).d 0 0 = 0 from
      HomologicalComplex.shape (singularChains ℤ X) 0 0 (by
        intro h
        have h' : 0 + 1 = 0 := h
        omega)]
    exact comp_zero
  | succ k =>
    rw [show (ComplexShape.down ℕ).next (k+1) = k from
      ComplexShape.next_eq' (ComplexShape.down ℕ) (i := k+1) (j := k) rfl]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    set α : relKern ℤ X A n := ((relComplex ℤ X A).iCycles n).hom z with hαdef
    set w : (relChains X A).X (n + (k+1)) :=
      ((relChains X A).iCycles (n + (k+1))).hom y with hwdef
    have hwcyc : ((relChains X A).d (n + (k+1)) (n + k)).hom w = 0 := by
      have h := congrArg
        (fun (g : (relChains X A).cycles (n+(k+1)) ⟶ (relChains X A).X (n+k)) => g.hom y)
        (HomologicalComplex.iCycles_d (relChains X A) (n+(k+1)) (n+k))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at h
      exact h
    obtain ⟨x, hx⟩ : ∃ x : (singularChains ℤ X).X (n + (k+1)),
        (cokernel.π ((inclChains X A).f (n + (k+1)))).hom x
          = (relChains_cokernelIso X A (n + (k+1))).hom w :=
      (ModuleCat.epi_iff_surjective (cokernel.π ((inclChains X A).f (n + (k+1))))).mp
        inferInstance _
    have hP : ((cokernel.π (inclChains X A)).f (n + (k+1))).hom x = w := by
      have hIP : (relChains_cokernelIso X A (n + (k+1))).hom
          (((cokernel.π (inclChains X A)).f (n + (k+1))).hom x)
          = (relChains_cokernelIso X A (n + (k+1))).hom w := by
        rw [relChains_cokernelIso_canon_apply, hx]
      calc ((cokernel.π (inclChains X A)).f (n + (k+1))).hom x
          = (relChains_cokernelIso X A (n + (k+1))).inv.hom
              ((relChains_cokernelIso X A (n + (k+1))).hom
                (((cokernel.π (inclChains X A)).f (n + (k+1))).hom x)) :=
              (relChains_cokernelIso_inv_hom_apply X A (n + (k+1)) _).symm
        _ = (relChains_cokernelIso X A (n + (k+1))).inv.hom
              ((relChains_cokernelIso X A (n + (k+1))).hom w) := by rw [hIP]
        _ = w := relChains_cokernelIso_inv_hom_apply X A (n + (k+1)) w
    have hPd : ((cokernel.π (inclChains X A)).f (n + k)).hom
        (((singularChains ℤ X).d (n + (k+1)) (n + k)).hom x) = 0 := by
      have hcomm := congrArg
        (fun (g : (singularChains ℤ X).X (n+(k+1)) ⟶ (relChains X A).X (n+k)) => g.hom x)
        (HomologicalComplex.Hom.comm (cokernel.π (inclChains X A)) (n+(k+1)) (n+k))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
      exact hcomm.symm.trans (by rw [hP]; exact hwcyc)
    have hπ0 : (cokernel.π ((inclChains X A).f (n + k))).hom
        (((singularChains ℤ X).d (n + (k+1)) (n + k)).hom x) = 0 := by
      rw [← relChains_cokernelIso_canon_apply, hPd, map_zero]
    have hcapk : (ModuleCat.Hom.hom (capHom ℤ (TopCat.toSSet.obj X) α.1 k))
        ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (n + k + 1) (n + k))) x) = 0 := by
      have h1 := relCapHalf_apply ℤ X A (m := k) α
        ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (n + k + 1) (n + k))) x)
      have hz : (cokernel.π ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
          (ModuleCat.of ℤ ℤ)).f (n + k))).hom
          ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d
            (n + k + 1) (n + k))) x) = 0 := hπ0
      have hz2 : (relCapHalf ℤ X A α k).hom
          ((cokernel.π ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
            (ModuleCat.of ℤ ℤ)).f (n + k))).hom
            ((ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d
              (n + k + 1) (n + k))) x)) = 0 := by
        rw [hz, map_zero]
      exact h1.symm.trans hz2
    have hval : (relCapHalf ℤ X A α (k+1)).hom ((relChains_cokernelIso X A (n+(k+1))).hom w)
        = (cap ℤ (TopCat.toSSet.obj X) α.1 (k+1)) x := by
      rw [← hx]
      exact relCapHalf_apply_incl X A (m := k+1) α x
    have hcore : ((singularChains ℤ X).d (k+1) k).hom
        ((cap ℤ (TopCat.toSSet.obj X) α.1 (k+1)) x) = 0 := by
      have hcd := capHom_comp_d_of_cocycle ℤ (TopCat.toSSet.obj X) (m := k) α.1
        (cochainDiff_relComplex_iCycles X A n z)
      have happ := congrArg
        (fun (g : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X (n + (k+1)) ⟶
            ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X k) => g.hom x) hcd
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul,
        LinearMap.smul_apply] at happ
      refine happ.trans ?_
      convert smul_zero ((-1 : ℤ)^n) using 2
      all_goals exact hcapk
    exact (congrArg (fun y => ((singularChains ℤ X).d (k+1) k).hom y) hval).trans hcore

/-! ## The relative cap product on cycles -/

/-- **The cap product of a relative cocycle with a relative chain**, at the cycle level: the linear
map `Z_{n+m}(X,A) ⟶ Z_m(X)` induced by `c ↦ relCapHalf α (I c)`. -/
noncomputable def relCapZHom (X : TopCat) (A : Set X) (n m : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    (relChains X A).cycles (n+m) ⟶ (singularChains ℤ X).cycles m :=
  HomologicalComplex.liftCycles (singularChains ℤ X)
    ((relChains X A).iCycles (n+m) ≫ (relChains_cokernelIso X A (n+m)).hom ≫
      relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom z) m)
    ((ComplexShape.down ℕ).next m) rfl (relCapZHom_d X A n m z)

/-- The computation rule for `relCapZHom`: on the underlying chains it is the relative cap
product. -/
theorem relCapZHom_iCycles (X : TopCat) (A : Set X) (n m : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    relCapZHom X A n m z ≫ (singularChains ℤ X).iCycles m =
      (relChains X A).iCycles (n+m) ≫ (relChains_cokernelIso X A (n+m)).hom ≫
        relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom z) m := by
  rw [relCapZHom]
  exact HomologicalComplex.liftCycles_i (singularChains ℤ X) _ ((ComplexShape.down ℕ).next m) rfl
    (relCapZHom_d X A n m z)

/-- `relCapZHom` is additive in the relative cocycle. -/
theorem relCapZHom_add (X : TopCat) (A : Set X) (n m : ℕ)
    (z z' : (relComplex ℤ X A).cycles n) :
    relCapZHom X A n m (z + z') = relCapZHom X A n m z + relCapZHom X A n m z' := by
  apply (cancel_mono ((singularChains ℤ X).iCycles m)).mp
  rw [Preadditive.add_comp, relCapZHom_iCycles, relCapZHom_iCycles, relCapZHom_iCycles]
  calc (relChains X A).iCycles (n+m) ≫ (relChains_cokernelIso X A (n+m)).hom ≫
        relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom (z + z')) m
      = (relChains X A).iCycles (n+m) ≫ (relChains_cokernelIso X A (n+m)).hom ≫
          (relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom z) m +
            relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom z') m) := by
        rw [show ((relComplex ℤ X A).iCycles n).hom (z + z')
            = ((relComplex ℤ X A).iCycles n).hom z + ((relComplex ℤ X A).iCycles n).hom z'
            from map_add _ z z', relCapHalf_add]
    _ = ((relChains X A).iCycles (n+m) ≫ (relChains_cokernelIso X A (n+m)).hom ≫
          relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom z) m) +
        ((relChains X A).iCycles (n+m) ≫ (relChains_cokernelIso X A (n+m)).hom ≫
          relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom z') m) := by
        simp only [Preadditive.comp_add]

/-- `relCapZHom` vanishes on the zero relative cocycle. -/
theorem relCapZHom_zero (X : TopCat) (A : Set X) (n m : ℕ) :
    relCapZHom X A n m (0 : (relComplex ℤ X A).cycles n) = 0 := by
  apply (cancel_mono ((singularChains ℤ X).iCycles m)).mp
  rw [zero_comp, relCapZHom_iCycles]
  rw [show ((relComplex ℤ X A).iCycles n).hom (0 : (relComplex ℤ X A).cycles n) = 0
    from map_zero _]
  rw [relCapHalf_zero]
  simp

/-- `relCapZHom` is homogeneous in the relative cocycle. -/
theorem relCapZHom_smul (X : TopCat) (A : Set X) (n m : ℕ)
    (r : ℤ) (z : (relComplex ℤ X A).cycles n) :
    relCapZHom X A n m (r • z) = r • relCapZHom X A n m z := by
  apply (cancel_mono ((singularChains ℤ X).iCycles m)).mp
  rw [CategoryTheory.Linear.smul_comp, relCapZHom_iCycles, relCapZHom_iCycles]
  calc (relChains X A).iCycles (n+m) ≫ (relChains_cokernelIso X A (n+m)).hom ≫
        relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom (r • z)) m
      = (relChains X A).iCycles (n+m) ≫ (relChains_cokernelIso X A (n+m)).hom ≫
          (r • relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom z) m) := by
        rw [show ((relComplex ℤ X A).iCycles n).hom (r • z)
            = r • ((relComplex ℤ X A).iCycles n).hom z from by simp, relCapHalf_smul]
    _ = r • ((relChains X A).iCycles (n+m) ≫ (relChains_cokernelIso X A (n+m)).hom ≫
          relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom z) m) := by
        simp only [CategoryTheory.Linear.comp_smul]

/-- The additive structure of `relCapZHom` in the cocycle: the underlying additive map of the
relative cap product on cycles. -/
noncomputable def relCapZHomAdd (X : TopCat) (A : Set X) (n m : ℕ) :
    ↥((relComplex ℤ X A).cycles n) →+
      (↥((relChains X A).cycles (n+m)) →ₗ[ℤ] ↥((singularChains ℤ X).cycles m)) where
  toFun z := (relCapZHom X A n m z).hom
  map_zero' := by rw [relCapZHom_zero, ModuleCat.hom_zero]
  map_add' := by intro z z'; rw [← ModuleCat.hom_add, relCapZHom_add]

/-- **The relative cap product on cycles**, as a `ℤ`-linear map in the relative cocycle. -/
noncomputable def relCapZ (X : TopCat) (A : Set X) (n m : ℕ) :
    ((relComplex ℤ X A).cycles n) →ₗ[ℤ]
      (((relChains X A).cycles (n+m)) →ₗ[ℤ] ((singularChains ℤ X).cycles m)) where
  toFun z := (relCapZHom X A n m z).hom
  map_add' z z' := by rw [← ModuleCat.hom_add, relCapZHom_add]
  map_smul' r z := by
    rw [RingHom.id_apply]
    have h := AddMonoidHom.map_zsmul (relCapZHomAdd X A n m) r z
    convert h using 1
    · dsimp only [relCapZHomAdd]
      exact congrArg (fun w => (relCapZHom X A n m w).hom)
        (int_smul_eq_zsmul (inferInstance : Module ℤ ↥((relComplex ℤ X A).cycles n)) r z)
    · dsimp only [relCapZHomAdd]
      rfl

set_option backward.isDefEq.respectTransparency true

/-- **The relative cap product pairing on cycles** `Z^n(X,A) × Z_{n+m}(X,A) → Z_m(X)`.

The value on a relative cocycle `z` and a relative cycle `c` is the relative cap product of the
underlying (co)chains, transported along `relChains_cokernelIso`. -/
theorem relCapH (X : TopCat) (A : Set X) (n m : ℕ) :
    ∃ capZ : (Work.Cohomology.relComplex ℤ X A).cycles n →ₗ[ℤ]
        ((Work.Cohomology.relChains X A).cycles (n + m) →ₗ[ℤ]
          (Work.Cohomology.singularChains ℤ X).cycles m),
      ∀ (z : (Work.Cohomology.relComplex ℤ X A).cycles n)
        (c : (Work.Cohomology.relChains X A).cycles (n + m)),
        (Work.Cohomology.singularChains ℤ X).iCycles m (capZ z c) =
          Work.Cohomology.relCapHalf ℤ X A
            (((Work.Cohomology.relComplex ℤ X A).iCycles n).hom z) m
            ((Work.Cohomology.relChains_cokernelIso X A (n + m)).hom
              ((Work.Cohomology.relChains X A).iCycles (n + m) c)) := by
  refine ⟨relCapZ X A n m, ?_⟩
  intro z c
  convert congrArg
    (fun (g : (relChains X A).cycles (n + m) ⟶ (singularChains ℤ X).X m) => g.hom c)
    (relCapZHom_iCycles X A n m z) using 2
  all_goals rfl

end

end Work.Cohomology
