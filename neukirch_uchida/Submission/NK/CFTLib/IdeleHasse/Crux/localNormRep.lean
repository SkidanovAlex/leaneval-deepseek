import Mathlib
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitsRep_helpers
import Submission.NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind
import Submission.NeukirchUchida.Local.LocalGalois
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion

/-!
# The norm endomorphism of the local units representation at a finite place

The range of the norm endomorphism `Rep.norm` of the `Γ_q`-representation
`NK.HassePrinciple.localUnitsRep K N (Place.ofFinite q)` (`Γ_q` the decomposition group of `q`)
is exactly the image of the local norm `N_{N_q/K_Q}` under the canonical local embedding
`K_Q → N_q`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option autoImplicit false

open NK.GlobalCFT
open CategoryTheory
open scoped NumberField
open NumberField IsDedekindDomain

variable {K N : Type} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]

namespace NK.CFTLib.IdeleHasse.Crux

/-- `Additive.ofMul` turns a product into a sum (in the additive group `Additive M`). -/
lemma sum_ofMul_eq_ofMul_prod {ι M : Type*} [CommMonoid M] (s : Finset ι) (f : ι → M) :
    (∑ i ∈ s, (Additive.ofMul (f i) : Additive M)) = Additive.ofMul (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ih]; rfl

/-- **The norm endomorphism of the local units ``representation`` is the product of the
conjugates.** -/
lemma localUnitsRep_norm_apply (w : Place N)
    [Fintype ↥(MulAction.stabilizer (N ≃ₐ[K] N) w)]
    (y : (Place.localField N w)ˣ) :
    (Rep.Hom.hom (Rep.norm (NK.HassePrinciple.localUnitsRep K N w))).toLinearMap
        (Additive.ofMul y)
      = Additive.ofMul (∏ γ : ↥(MulAction.stabilizer (N ≃ₐ[K] N) w),
          NK.HassePrinciple.localUnitsEquiv w γ y) := by
  change (Rep.Hom.hom (Rep.norm (NK.HassePrinciple.localUnitsRep K N w))) (Additive.ofMul y) = _
  rw [Rep.norm_apply]
  unfold Representation.norm
  rw [LinearMap.sum_apply]
  rw [show (∑ d, (NK.HassePrinciple.localUnitsRep K N w).ρ d (Additive.ofMul y))
      = ∑ d, (Additive.ofMul (NK.HassePrinciple.localUnitsEquiv w d y) :
          Additive (Place.localField N w)ˣ) from
    Finset.sum_congr rfl (fun d _ => by
      simp only [NK.HassePrinciple.localUnitsRep, Rep.ofDistribMulAction_ρ_apply_apply]
      rfl)]
  rw [sum_ofMul_eq_ofMul_prod]

/-- **The product of the `Γ_q`-conjugates is the algebra-map image of the local norm.**

The decomposition group of `q` is the local Galois group of `N_q / K_Q`, so the product of the
conjugates `∏_{γ ∈ Γ_q} γ(y)` is the image of the field norm `N_{N_q/K_Q}(y)`. -/
lemma prod_localUnitsEquiv_eq (q : HeightOneSpectrum (𝓞 N)) (Q : HeightOneSpectrum (𝓞 K))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    [Fintype ↥(MulAction.stabilizer (N ≃ₐ[K] N) (Place.ofFinite q))]
    (y : (Place.localField N (Place.ofFinite q))ˣ) :
    (∏ γ : ↥(MulAction.stabilizer (N ≃ₐ[K] N) (Place.ofFinite q)),
        NK.HassePrinciple.localUnitsEquiv (Place.ofFinite q) γ y)
      = Units.map (Place.localAlgebraMapFinite q Q hq).toMonoidHom
          (Place.localNormFinite q Q hq y) := by
  let Γ := ↥(MulAction.stabilizer (N ≃ₐ[K] N) (Place.ofFinite q))
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion N) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion N) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : IsGalois (Q.adicCompletion K) (q.adicCompletion N) :=
    Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q hq
  have hDΓ : NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := N) (Place.ofFinite q)
      = MulAction.stabilizer (N ≃ₐ[K] N) (Place.ofFinite q) := by
    ext σ
    rw [NK.GlobalCFTdeep.mem_decompositionSubgroup, MulAction.mem_stabilizer_iff]
  let ι : Γ ≃* NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := N) (Place.ofFinite q) :=
    { toFun := fun γ => ⟨γ.1, by rw [hDΓ]; exact γ.2⟩
      invFun := fun δ => ⟨δ.1, by rw [← hDΓ]; exact δ.2⟩
      left_inv := fun γ => Subtype.ext rfl
      right_inv := fun δ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  let e : Γ ≃* (q.adicCompletion N ≃ₐ[Q.adicCompletion K] q.adicCompletion N) :=
    ι.trans (NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois Q q hq)
  have he : ∀ γ : Γ,
      (e γ).toRingEquiv = NK.HassePrinciple.localAutHom (Place.ofFinite q) γ := by
    intro γ
    rw [MulEquiv.trans_apply, NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois_apply]
    rw [← NK.GlobalCFTdeep.localAction_eq_decompositionToAdicCompletion]
    rw [NK.GlobalCFTdeep.localAction_eq_localAut]
    rfl
  apply Units.ext
  have hstep1 : ((∏ γ : Γ, (NK.HassePrinciple.localUnitsEquiv (Place.ofFinite q) γ y :
      (Place.localField N (Place.ofFinite q))ˣ) : (Place.localField N (Place.ofFinite q))ˣ) :
      Place.localField N (Place.ofFinite q))
      = ∏ γ : Γ, (e γ) (y : Place.localField N (Place.ofFinite q)) := by
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl (fun γ _ => ?_)
    rw [NK.HassePrinciple.coe_localUnitsEquiv, ← he]
    rfl
  have hstep2 : (∏ γ : Γ, (e γ) (y : Place.localField N (Place.ofFinite q)))
      = ∏ σ : (q.adicCompletion N ≃ₐ[Q.adicCompletion K] q.adicCompletion N),
          σ (y : Place.localField N (Place.ofFinite q)) :=
    Fintype.prod_equiv e.toEquiv _ _ (fun γ => rfl)
  rw [hstep1, hstep2, ← Algebra.norm_eq_prod_automorphisms]
  rfl

/-- **The range of the norm endomorphism of the local units representation at a finite place is
the image of the local norm.** -/
theorem mem_range_norm_localUnitsRep_ofFinite (q : HeightOneSpectrum (𝓞 N))
    (Q : HeightOneSpectrum (𝓞 K)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    [Fintype ↥(MulAction.stabilizer (N ≃ₐ[K] N) (Place.ofFinite q))]
    (u : (Place.localField N (Place.ofFinite q))ˣ) :
    (Additive.ofMul u ∈ LinearMap.range
      (Rep.Hom.hom (Rep.norm (NK.HassePrinciple.localUnitsRep K N
        (Place.ofFinite q)))).toLinearMap)
      ↔ (∃ y, Units.map (Place.localAlgebraMapFinite q Q hq).toMonoidHom
            (Place.localNormFinite q Q hq y) = u) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨Additive.toMul z, ?_⟩
    rw [← prod_localUnitsEquiv_eq]
    apply Additive.ofMul.injective
    rw [← localUnitsRep_norm_apply (K := K) (N := N) (Place.ofFinite q) (Additive.toMul z)]
    change (Rep.Hom.hom (Rep.norm (NK.HassePrinciple.localUnitsRep K N
        (Place.ofFinite q)))).toLinearMap z = Additive.ofMul u
    exact hz
  · rintro ⟨y, rfl⟩
    refine ⟨Additive.ofMul y, ?_⟩
    rw [localUnitsRep_norm_apply, prod_localUnitsEquiv_eq]

end NK.CFTLib.IdeleHasse.Crux
