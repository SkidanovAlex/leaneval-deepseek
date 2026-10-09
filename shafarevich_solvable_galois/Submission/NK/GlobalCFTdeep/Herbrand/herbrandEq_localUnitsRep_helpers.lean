/-
Helper lemmas for `herbrandEq_localUnitsRep_ofFinite`.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.LocalUnits
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAction
import Submission.NeukirchUchida.Local.LocalGalois
import Submission.NK.LocalReciprocity.LocalSetup
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

theorem decompositionSubgroup_eq_commons (q : HeightOneSpectrum (𝓞 L)) :
    decompositionSubgroup (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q) =
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q := by
  apply Subgroup.ext
  intro σ
  rw [NK.GlobalCFTdeep.mem_decompositionSubgroup,
    NK.GlobalCFT.Inclusion.globalCFT_mem_decompositionSubgroup_iff]
  constructor
  · intro h
    have h2 : NK.GlobalCFT.Place.ofFinite (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q)
        = NK.GlobalCFT.Place.ofFinite q := by
      rw [← NK.GlobalCFT.Place.smul_ofFinite]; exact h
    exact NK.GlobalCFT.Place.ofFinite_inj.mp h2
  · intro h
    rw [NK.GlobalCFT.Place.smul_ofFinite, h]

noncomputable def decompositionSubgroupIsoCommons (q : HeightOneSpectrum (𝓞 L)) :
    decompositionSubgroup (K:=K) (L:=L) (NK.GlobalCFT.Place.ofFinite q) ≃*
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K:=K) q where
  toFun σ := ⟨σ.1, by rw [← decompositionSubgroup_eq_commons (K:=K) (L:=L) q]; exact σ.2⟩
  invFun y := ⟨y.1, by rw [decompositionSubgroup_eq_commons (K:=K) (L:=L) q]; exact y.2⟩
  left_inv σ := Subtype.ext rfl
  right_inv y := Subtype.ext rfl
  map_mul' σ τ := Subtype.ext rfl

theorem decompositionSubgroupIsoCommons_apply (q : HeightOneSpectrum (𝓞 L))
    (σ : decompositionSubgroup (K:=K) (L:=L) (NK.GlobalCFT.Place.ofFinite q)) :
    (decompositionSubgroupIsoCommons (K:=K) (L:=L) q σ).1 = σ.1 := rfl

theorem decompositionSubgroupIsoCommons_val (q : HeightOneSpectrum (𝓞 L))
    (σ : decompositionSubgroup (K:=K) (L:=L) (NK.GlobalCFT.Place.ofFinite q)) :
    (decompositionSubgroupIsoCommons (K:=K) (L:=L) q σ) =
      (⟨σ.1, by rw [← decompositionSubgroup_eq_commons (K:=K) (L:=L) q]; exact σ.2⟩ :
        Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K:=K) q) :=
  Subtype.ext rfl

theorem decompositionUnitsAction_smul (w : NK.GlobalCFT.Place L)
    (σ : decompositionSubgroup (K:=K) (L:=L) w) (u : (NK.GlobalCFT.Place.localField L w)ˣ) :
    (decompositionUnitsAction (K:=K) (L:=L) w).smul σ u =
      Units.map (NK.GlobalCFT.Inclusion.Place.localAction (σ : L ≃ₐ[K] L) w σ.2).toMonoidHom u :=
  rfl

theorem localAction_eq_decompositionToAdicCompletion (q : HeightOneSpectrum (𝓞 L))
    (σ : L ≃ₐ[K] L) (hσ : σ • NK.GlobalCFT.Place.ofFinite q = NK.GlobalCFT.Place.ofFinite q) :
    NK.GlobalCFT.Inclusion.Place.localAction σ (NK.GlobalCFT.Place.ofFinite q) hσ =
      Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion (K := K) q
        ⟨σ, by
          rw [Commons.NumberTheory.NumberField.Completion.mem_decompositionSubgroup,
            NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum]
          exact NK.GlobalCFT.Place.ofFinite_inj.mp
            ((NK.GlobalCFT.Place.smul_ofFinite σ q).trans hσ)⟩ := by
  have hmem : σ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q := by
    rw [Commons.NumberTheory.NumberField.Completion.mem_decompositionSubgroup,
      NK.GlobalCFT.Inclusion.globalCFT_placeSmul_eq_smulHeightOneSpectrum]
    exact NK.GlobalCFT.Place.ofFinite_inj.mp ((NK.GlobalCFT.Place.smul_ofFinite σ q).trans hσ)
  apply RingEquiv.ext
  intro y
  have hfun : (fun y : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q) =>
        NK.GlobalCFT.Inclusion.Place.localAction σ (NK.GlobalCFT.Place.ofFinite q) hσ y)
      = fun y : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q) =>
        Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion (K := K) q ⟨σ, hmem⟩ y := by
    refine DenseRange.equalizer (NK.GlobalCFT.Galois.denseRange_algebraMap_localField _)
      (NK.GlobalCFT.Inclusion.Place.continuous_localAction _ _ _)
      (Commons.NumberTheory.NumberField.Completion.continuous_decompositionToAdicCompletion q ⟨σ, hmem⟩) ?_
    funext x
    rw [Function.comp_apply, NK.GlobalCFTdeep.localAction_algebraMap_eq]
    exact (Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion_coe q ⟨σ, hmem⟩ x).symm
  exact congrFun hfun y

noncomputable def decompositionSubgroupIsoLocalGalois
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal) :
    decompositionSubgroup (K:=K) (L:=L) (NK.GlobalCFT.Place.ofFinite q) ≃*
      (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
  (decompositionSubgroupIsoCommons (K:=K) (L:=L) q).trans
    (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois Q q hq)

theorem decompositionSubgroupIsoLocalGalois_apply
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (σ : decompositionSubgroup (K:=K) (L:=L) (NK.GlobalCFT.Place.ofFinite q)) :
    (decompositionSubgroupIsoLocalGalois Q q hq σ).toRingEquiv =
      Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion (K:=K) q
        ⟨σ.1, by rw [← decompositionSubgroup_eq_commons (K:=K) (L:=L) q]; exact σ.2⟩ := by
  rw [decompositionSubgroupIsoLocalGalois, MulEquiv.trans_apply,
    decompositionSubgroupIsoCommons_val,
    Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe]
  exact RingEquiv.ext (fun z => congrFun
    (Commons.NumberTheory.NumberField.Completion.decompositionToLocalGaloisFun_apply Q q hq _) z)


section Transfer

open CategoryTheory

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]

/-- Group cohomology is invariant under restricting a representation along a group isomorphism;
degree one of Tate cohomology is group cohomology, so the same holds there. -/
theorem natCard_tateCohomology_one_of_mulEquiv_res (e : G ≃* H)
    {V : Type} [AddCommGroup V] [Module ℤ V] (ρ : Representation ℤ H V) :
    Nat.card (tateCohomology (Rep.of (ρ.comp e.toMonoidHom)) 1) =
      Nat.card (tateCohomology (Rep.of ρ) 1) := by
  have h1 : Nat.card (tateCohomology (Rep.of (ρ.comp e.toMonoidHom)) 1) =
      Nat.card (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) 1) :=
    Nat.card_congr (Iso.toLinearEquiv
      ((TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app
        (Rep.of (ρ.comp e.toMonoidHom)))).toEquiv
  have h2 : Nat.card (tateCohomology (Rep.of ρ) 1) =
      Nat.card (groupCohomology (Rep.of ρ) 1) :=
    Nat.card_congr (Iso.toLinearEquiv
      ((TateCohomology.isoGroupCohomology (R := ℤ) (G := H) 1).app (Rep.of ρ))).toEquiv
  rw [h1, h2]
  exact Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv e (Rep.of ρ) 1

/-- Degree zero of Tate cohomology is the quotient of the invariants by the norm, and both the
invariants and the norm are unchanged when the representation is restricted along a group
isomorphism. -/
theorem natCard_tateCohomology_zero_of_mulEquiv_res (e : G ≃* H)
    {V : Type} [AddCommGroup V] [Module ℤ V] (ρ : Representation ℤ H V) :
    Nat.card (tateCohomology (Rep.of (ρ.comp e.toMonoidHom)) 0) =
      Nat.card (tateCohomology (Rep.of ρ) 0) := by
  obtain ⟨e1⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso (ρ.comp e.toMonoidHom)
  obtain ⟨e2⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso ρ
  rw [Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv]
  have hinv : Representation.invariants (ρ.comp e.toMonoidHom) = Representation.invariants ρ := by
    ext v
    rw [Representation.mem_invariants, Representation.mem_invariants]
    constructor
    · intro h w
      obtain ⟨g, rfl⟩ := e.surjective w
      exact h g
    · intro h g
      exact h (e g)
  have hnorm : Representation.norm (ρ.comp e.toMonoidHom) = Representation.norm ρ := by
    rw [Representation.norm, Representation.norm]
    exact Equiv.sum_comp e.toEquiv (fun h => ρ h)
  rw [hinv, hnorm]

end Transfer

section RepRes

open CategoryTheory

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The local units representation of the decomposition group is the restriction of the local
Galois representation along the isomorphism `D_q ≃* Gal(L_q/K_Q)`.** -/
theorem localUnitsRep_eq_res
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    [Fintype (decompositionSubgroup (K:=K) (L:=L) (NK.GlobalCFT.Place.ofFinite q))] :
    localUnitsRep (K:=K) (L:=L) (NK.GlobalCFT.Place.ofFinite q) =
      Rep.res (decompositionSubgroupIsoLocalGalois Q q hq).toMonoidHom
        (Rep.ofMulDistribMulAction (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
          (q.adicCompletion L)ˣ) := by
  letI : MulDistribMulAction
      (decompositionSubgroup (K:=K) (L:=L) (NK.GlobalCFT.Place.ofFinite q)) ((q.adicCompletion L)ˣ) :=
    decompositionUnitsAction (K:=K) (L:=L) (NK.GlobalCFT.Place.ofFinite q)
  rw [localUnitsRep]
  refine congrArg Rep.of ?_
  apply MonoidHom.ext
  intro σ
  apply LinearMap.ext
  intro a
  have hsmul : (decompositionUnitsAction (K:=K) (L:=L) (NK.GlobalCFT.Place.ofFinite q)).smul
        σ (Additive.toMul a)
      = (decompositionSubgroupIsoLocalGalois Q q hq σ) • (Additive.toMul a) := by
    rw [decompositionUnitsAction_smul, AlgEquiv.smul_units_def]
    have hringRing : NK.GlobalCFT.Inclusion.Place.localAction σ.1
          (NK.GlobalCFT.Place.ofFinite q) σ.2
        = (decompositionSubgroupIsoLocalGalois Q q hq σ).toRingEquiv := by
      rw [localAction_eq_decompositionToAdicCompletion, decompositionSubgroupIsoLocalGalois_apply]
    rw [show (↑(decompositionSubgroupIsoLocalGalois Q q hq σ) :
          (q.adicCompletion L) →* (q.adicCompletion L))
        = ((decompositionSubgroupIsoLocalGalois Q q hq σ).toRingEquiv).toMonoidHom from rfl]
    rw [← hringRing]
  exact congrArg Additive.ofMul hsmul

/-- The cardinality of the decomposition group is the local degree. -/
theorem natCard_decompositionSubgroup_eq_finrank
    (Q : HeightOneSpectrum (𝓞 K)) (q : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Nat.card (decompositionSubgroup (K:=K) (L:=L) (NK.GlobalCFT.Place.ofFinite q)) =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) := by
  rw [Nat.card_congr (decompositionSubgroupIsoLocalGalois Q q hq).toEquiv]
  exact Submission.NeukirchUchida.Local.natCard_algEquiv_adicCompletion_eq_finrank Q q hq

end RepRes

end NK.GlobalCFTdeep
