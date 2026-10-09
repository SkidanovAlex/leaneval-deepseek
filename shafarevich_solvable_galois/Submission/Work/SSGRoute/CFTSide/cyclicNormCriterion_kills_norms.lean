import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.phi1_defs
import Submission.Commons.RepresentationTheory.GroupCohomology.isZero_groupCohomology_coind_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The "kills norms" half of the cyclic norm criterion

This file proves `Work.SSGRoute.CFTSide.cyclicNormCriterion_kills_norms`: the cup product class
`a ∪ δh ∈ H²(Gal(L/k), C_L)` vanishes whenever `a ∈ C_L` is a norm and `h ∈ H¹(Gal(L/k), 𝔽_p)`.

The proof follows the `ℤ`-coefficient route `NK.NUV2.RouteC.map_powHom_eq_zero_of_mem_normGroup`:
writing `a = N b = ∑_σ σ • b`, the coefficient map `1 ↦ a` factors through the left regular
representation `Coeff[G]` (`powHomCls_eq_traceHomC_comp`), and `H²(G, Coeff[G]) = 0`
(`subsingleton_groupCohomology_leftRegular_commRing`, obtained from Shapiro's lemma via
`Coeff[G] ≅ Coind_1^G Coeff`).  The acyclicity lemmas are proved here over an arbitrary
commutative coefficient ring, since the coefficient ring of the `Ext` core is `Coeff = ULift ℤ`.
-/

open CategoryTheory
open SSGRoute.PTExt

namespace Work.SSGRoute.CFTSide

set_option linter.style.haveILetI false

noncomputable section

/- `ULift.module` competes with the module structure stored in a representation; prefer the
structure instances, as in `NK/HassePrinciple/injective_h2_units_of_subsingleton_h1_classRep.lean`. -/
attribute [local instance 10000] Rep.hV2 Rep.hV1

/-- The norm endomorphism of a representation is the sum of the action: `A.norm a = ∑_g g · a`
(for any commutative coefficient ring). -/
lemma norm_apply_eq_sum_coeff {R : Type} [CommRing R] {G : Type} [Group G] [Fintype G]
    (A : Rep R G) (a : A) : A.norm.hom a = ∑ g : G, A.ρ g a := by
  rw [Rep.norm_apply, Representation.norm]
  exact LinearMap.sum_apply Finset.univ (fun g : G => A.ρ g) a

/-- The trace (norm) element `∑_{σ ∈ G} σ` of the group algebra `Coeff[G]`. -/
noncomputable def leftRegularTraceC (G : Type) [Group G] [Fintype G] : MonoidAlgebra Coeff G :=
  ∑ g : G, MonoidAlgebra.single g (1 : Coeff)

/-- The trace element of the regular representation is `G`-invariant. -/
lemma leftRegular_ρ_traceC (G : Type) [Group G] [Fintype G] (τ : G) :
    (Rep.leftRegular Coeff G).ρ τ (leftRegularTraceC G) = leftRegularTraceC G := by
  unfold leftRegularTraceC
  rw [map_sum]
  have h : ∀ σ : G, (Rep.leftRegular Coeff G).ρ τ (MonoidAlgebra.single σ (1 : Coeff))
      = MonoidAlgebra.single (τ * σ) (1 : Coeff) := by
    intro σ
    rw [Representation.ofMulAction_single]
    simp
  rw [Finset.sum_congr rfl (fun σ _ => h σ)]
  exact Fintype.sum_equiv (Equiv.mulLeft τ)
    (fun σ : G => MonoidAlgebra.single (τ * σ) (1 : Coeff))
    (fun σ : G => MonoidAlgebra.single σ (1 : Coeff)) (fun σ => rfl)

/-- **The trace map `Coeff ⟶ Coeff[G]`, `1 ↦ ∑_{σ} σ`**, as a morphism of representations. -/
noncomputable def traceHomC (G : Type) [Group G] [Fintype G] :
    Rep.trivial Coeff G Coeff ⟶ Rep.leftRegular Coeff G :=
  Rep.ofHom
    ⟨LinearMap.toSpanSingleton Coeff (MonoidAlgebra Coeff G) (leftRegularTraceC G), fun τ => by
      apply LinearMap.ext
      intro n
      show n • leftRegularTraceC G
        = (Rep.leftRegular Coeff G).ρ τ (n • leftRegularTraceC G)
      rw [map_smul, leftRegular_ρ_traceC]⟩

@[simp] lemma traceHomC_apply (G : Type) [Group G] [Fintype G] (n : Coeff) :
    (Rep.Hom.hom (traceHomC G)) n = n • leftRegularTraceC G := rfl

/-- **The left regular representation is the coinduction from the trivial subgroup**, over an
arbitrary commutative ring `R`: `R[G] ≅ Coind_1^G R`.

Coefficient-ring-general form of `NU.leftRegularIsoCoind` (the case `R = ℤ`, in
`Submission/Commons/RepresentationTheory/TateCohomology/natCard_tateCohomology_eq_of_fundamental_class.lean`);
the proof is that of the `ℤ` case with `ℤ` replaced by `R`. -/
theorem leftRegularIsoCoind_commRing (R G : Type) [CommRing R] [Group G] [Fintype G] :
    Nonempty (Rep.leftRegular R G ≅
      Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial R (↥(⊥ : Subgroup G)) R)) := by
  classical
  set W : Rep R (↥(⊥ : Subgroup G)) := Rep.trivial R (↥(⊥ : Subgroup G)) R with hW
  set σ : Representation R G (Representation.coindV (⊥ : Subgroup G).subtype W.ρ) :=
    (Rep.coind (⊥ : Subgroup G).subtype W).ρ with hσ
  let pinv : (G → R) ≃ₗ[R] (G → R) := LinearEquiv.funCongrLeft R R (Equiv.inv G)
  have hpinv : ∀ h : G → R, pinv h = fun x => h x⁻¹ := fun h => by ext x; rfl
  -- the `R`-linear isomorphism `R[G] → (G → R)`, `f ↦ (x ↦ f.coeff x⁻¹)`
  let eLin : MonoidAlgebra R G →ₗ[R] (G → R) :=
    ((MonoidAlgebra.coeffLinearEquiv (R := R) (S := R) (M := G)).trans
      (Finsupp.linearEquivFunOnFinite R R G)).trans pinv |>.toLinearMap
  have heLin_aux : ∀ f : MonoidAlgebra R G,
      eLin f = pinv (Finsupp.linearEquivFunOnFinite R R G (MonoidAlgebra.coeff f)) :=
    fun _ => rfl
  have heLin : ∀ f : MonoidAlgebra R G, eLin f = fun x => (MonoidAlgebra.coeff f) x⁻¹ := by
    intro f
    rw [heLin_aux, hpinv]
    rfl
  have hinj : Function.Injective eLin := by
    intro f g h
    apply MonoidAlgebra.coeff_injective
    ext y
    have h2 := congrFun h y⁻¹
    rw [heLin f, heLin g] at h2
    simpa using h2
  have hsurj : Function.Surjective eLin := by
    intro h
    refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (fun x => h x⁻¹)), ?_⟩
    ext x
    rw [heLin]
    simp
  have hmem : ∀ f : MonoidAlgebra R G,
      eLin f ∈ Representation.coindV (⊥ : Subgroup G).subtype W.ρ := by
    intro f
    rw [Representation.mem_coindV]
    intro s h
    rw [show ((⊥ : Subgroup G).subtype s : G) = 1 from Subgroup.mem_bot.mp s.2, one_mul]
    simp [heLin, W, Rep.trivial]
  let e : MonoidAlgebra R G →ₗ[R] Representation.coindV (⊥ : Subgroup G).subtype W.ρ :=
    eLin.codRestrict _ hmem
  have he : ∀ f : MonoidAlgebra R G,
      ((e f : Representation.coindV (⊥ : Subgroup G).subtype W.ρ) : G → R)
        = fun x => (MonoidAlgebra.coeff f) x⁻¹ := fun f => rfl
  have hbij : Function.Bijective e := by
    constructor
    · intro f g hfg
      apply hinj
      have h2 := congrArg (Subtype.val) hfg
      simpa [e] using h2
    · intro g
      obtain ⟨f, hf⟩ := hsurj (g : G → R)
      refine ⟨f, ?_⟩
      apply Subtype.ext
      simpa [e] using hf
  let eL : MonoidAlgebra R G ≃ₗ[R] Representation.coindV (⊥ : Subgroup G).subtype W.ρ :=
    LinearEquiv.ofBijective e hbij
  have heL : ∀ f : MonoidAlgebra R G,
      ((eL f : Representation.coindV (⊥ : Subgroup G).subtype W.ρ) : G → R)
        = fun x => (MonoidAlgebra.coeff f) x⁻¹ := fun f => he f
  refine ⟨Rep.mkIso (Representation.Equiv.mk eL ?_)⟩
  intro g
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [heL]
  change (MonoidAlgebra.coeff ((Representation.ofMulAction R G G) g f)) x⁻¹
      = ((eL f : Representation.coindV (⊥ : Subgroup G).subtype W.ρ) : G → R) (x * g)
  rw [heL]
  show (MonoidAlgebra.coeff ((Representation.ofMulAction R G G) g f)) x⁻¹
      = (fun y => (MonoidAlgebra.coeff f) y⁻¹) (x * g)
  rw [Representation.coeff_ofMulAction]
  simp only [smul_eq_mul, mul_inv_rev]

/-- **The left regular representation has no positive cohomology**, over an arbitrary commutative
ring `R` and finite group `G`: `Hⁿ⁺¹(G, R[G]) = 0`.

Coefficient-ring-general form of `NK.NUV2.RouteC.subsingleton_groupCohomology_leftRegular`
(the case `R = ℤ`): combine `leftRegularIsoCoind_commRing` with
`Commons.RepresentationTheory.GroupCohomology.isZero_groupCohomology_coind_bot`. -/
theorem subsingleton_groupCohomology_leftRegular_commRing (R G : Type) [CommRing R] [Group G]
    [Fintype G] (n : ℕ) :
    Subsingleton (groupCohomology (Rep.leftRegular R G) (n + 1)) := by
  classical
  set W : Rep R (↥(⊥ : Subgroup G)) := Rep.trivial R (↥(⊥ : Subgroup G)) R with hW
  have hiso : Rep.leftRegular R G ≅ Rep.coind (⊥ : Subgroup G).subtype W :=
    Classical.choice (leftRegularIsoCoind_commRing R G)
  have hz : CategoryTheory.Limits.IsZero
      (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype W) (n + 1)) :=
    Commons.RepresentationTheory.GroupCohomology.isZero_groupCohomology_coind_bot W n
  have h2 : groupCohomology (Rep.leftRegular R G) (n + 1)
      ≅ groupCohomology (Rep.coind (⊥ : Subgroup G).subtype W) (n + 1) :=
    CategoryTheory.Iso.mk
      (groupCohomology.map (MonoidHom.id G) hiso.hom (n + 1))
      (groupCohomology.map (MonoidHom.id G) hiso.inv (n + 1))
      (by rw [← groupCohomology.map_id_comp hiso.hom hiso.inv (n + 1), Iso.hom_inv_id]
          simp only [Rep.res_id]
          rw [groupCohomology.map_id])
      (by rw [← groupCohomology.map_id_comp hiso.inv hiso.hom (n + 1), Iso.inv_hom_id]
          simp only [Rep.res_id]
          rw [groupCohomology.map_id])
  exact ModuleCat.subsingleton_of_isZero (CategoryTheory.Limits.IsZero.of_iso hz h2)

/-- **The factorisation of `powHomCls a` through the regular representation when `a` is a norm.**

For `a = N b` (with `N` the norm endomorphism of `C_L`), the coefficient map `1 ↦ a` factors as
`Coeff --(trace)--> Coeff[G] --(σ ↦ σ • b)--> C_L`. -/
lemma powHomCls_eq_traceHomC_comp
    (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (a : classesK k L) (hafix : ∀ σ : L ≃ₐ[k] L, (classesK k L).ρ σ a = a)
    (b : classesK k L) (hb : (classesK k L).norm.hom b = a) :
    Work.SSGRoute.Phi1.powHomCls k L a hafix
      = traceHomC (L ≃ₐ[k] L) ≫ Rep.leftRegularHom (classesK k L) b := by
  apply Rep.hom_ext
  rw [Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro n
  show n • a
    = (Rep.leftRegularHom (classesK k L) b).hom.toLinearMap
        (n • leftRegularTraceC (L ≃ₐ[k] L))
  have hsum : (Rep.leftRegularHom (classesK k L) b).hom.toLinearMap
        (leftRegularTraceC (L ≃ₐ[k] L))
      = ∑ σ : L ≃ₐ[k] L, (classesK k L).ρ σ b := by
    rw [leftRegularTraceC, map_sum]
    exact Finset.sum_congr rfl (fun σ _ =>
      (Rep.leftRegularHom_hom_single (A := classesK k L) σ b (1 : Coeff)).trans (one_smul _ _))
  rw [map_smul]
  congr 1
  rw [← hb, norm_apply_eq_sum_coeff, hsum]


end

/-- **The "kills norms" half of the cyclic norm criterion** (`C_L` coefficients).

For a finite Galois extension `L/k` of number fields and an element `a` of `C_L` which is a norm
from `L` (i.e. lies in the image of the norm endomorphism of the representation `classesK k L`)
and any character `h ∈ H¹(Gal(L/k), 𝔽_p)`, the cup product class
`groupCohomology.map (id) (powHomCls a) 2 (δ h)` vanishes, `δ` being the connecting map of the
coefficient sequence `SSGRoute.Phi1.coeffSES` (i.e. the Bockstein).

Route (the coefficient-module version of `NK.NUV2.RouteC.map_powHom_eq_zero_of_mem_normGroup`):
write `a = N b = Σ_σ σ • b`; the coefficient map `1 ↦ a` factors as
`ℤ --trace--> ℤ[G] --(σ ↦ σ • b)--> C_L` through the left regular representation
`Rep.leftRegular Coeff G`, so the class is the image under a map factoring through
`H²(G, ℤ[G]) = 0` (Shapiro/coinduction acyclicity:
`Commons.RepresentationTheory.GroupCohomology.isZero_groupCohomology_coind_bot` together with
`Rep.leftRegular Coeff G ≅ Rep.coind ⊥ (trivial)`, cf. the `ℤ`-coefficient version
`NK.NUV2.RouteC.subsingleton_groupCohomology_leftRegular`).  Budget for the transport of those
`ℤ`-coefficient acyclicity lemmas across `ULift ℤ ≃+* ℤ`. -/
theorem cyclicNormCriterion_kills_norms (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime]
    (a : SSGRoute.PTExt.classesK k L)
    (hafix : ∀ σ : L ≃ₐ[k] L, (SSGRoute.PTExt.classesK k L).ρ σ a = a)
    (hnorm : a ∈ Set.range ((SSGRoute.PTExt.classesK k L).norm.hom))
    (h : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p)) 1) :
    groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
      (SSGRoute.Phi1.powHomCls k L a hafix) 2
      ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom h) = 0 := by
  classical
  obtain ⟨b, hb⟩ := hnorm
  have hfac := powHomCls_eq_traceHomC_comp k L a hafix b hb
  haveI : Subsingleton (groupCohomology (Rep.leftRegular SSGRoute.PTExt.Coeff (L ≃ₐ[k] L)) 2) :=
    subsingleton_groupCohomology_leftRegular_commRing SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) 1
  have h0 : (groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L)) (traceHomC (L ≃ₐ[k] L)) 2)
      ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom h) = 0 :=
    Subsingleton.elim _ _
  have hcomp := groupCohomology.map_id_comp (traceHomC (L ≃ₐ[k] L))
    (Rep.leftRegularHom (SSGRoute.PTExt.classesK k L) b) 2
  set_option backward.isDefEq.respectTransparency false in
  rw [hfac, hcomp]
  change (ConcreteCategory.hom
        (groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L))
          (Rep.leftRegularHom (SSGRoute.PTExt.classesK k L) b) 2))
      ((ConcreteCategory.hom
        (groupCohomology.map (MonoidHom.id (L ≃ₐ[k] L)) (traceHomC (L ≃ₐ[k] L)) 2))
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (L ≃ₐ[k] L) p) 1 2 rfl).hom h)) = 0
  rw [h0]
  exact map_zero _

end Work.SSGRoute.CFTSide
