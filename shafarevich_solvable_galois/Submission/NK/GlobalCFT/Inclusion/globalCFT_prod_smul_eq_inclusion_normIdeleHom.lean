import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.NormFunctorial
import Submission.NK.GlobalCFT.GaloisIdelesAction
import Submission.NeukirchUchida.Local.LocalGalois
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_localAlgebraMapUnits
import Submission.NK.GlobalCFT.Galois.globalCFT_mul_smul_idele
import Submission.NK.GlobalCFT.Galois.globalCFT_smul_principalIdele
import Submission.NK.GlobalCFT.Galois.globalCFT_one_smul_idele
import Submission.Commons.NumberTheory.NumberField.liesOver_map_galRestrict
import Submission.NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom
import Submission.NK.GlobalCFT.Galois.range_completionMap_of_isReal_under
import Submission.NK.GlobalCFT.Galois.completionMap_surjective_of_isComplex_under
import Submission.NK.GlobalCFT.Galois.globalCFT_place_smul_liesOver
import Submission.Commons.FieldTheory.Galois.natCard_algEquiv_le_finrank
import Submission.NK.GlobalCFT.Galois.globalCFT_smul_place_smul
import Submission.NK.GlobalCFT.Galois.globalCFT_one_smul_place

open Classical
open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace NK.GlobalCFT.Inclusion

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Transport lemmas -/

lemma cast_dep_apply {α : Type*} {P : α → Type*} (x : (a : α) → P a) {a b : α}
    (h : a = b) : h ▸ x a = x b := by cases h; rfl

lemma Idele.apply_of_eq {x : Idele L} {a b : Place L} (h : a = b) :
    x a = h.symm ▸ (x b) := by cases h; rfl

lemma continuous_ringEquiv_cast {a b : Place L} (h : a = b) :
    Continuous (RingEquiv.cast h : Place.localField L a → Place.localField L b) := by
  cases h; exact continuous_id

lemma castRingEquiv_algebraMap {a b : Place L} (h : a = b) (t : L) :
    (RingEquiv.cast h) (algebraMap L (Place.localField L a) t) =
      algebraMap L (Place.localField L b) t := by
  cases h; rfl

lemma castRingEquiv_apply_eq {a b : Place L} (h : a = b) (x : Place.localField L a) :
    (RingEquiv.cast h) x = h ▸ x := by
  cases h; rfl

/-! ## Bridge A : `smulHeightOneSpectrum = placeSmul` -/

theorem ringOfIntegersEquiv_eq_galRestrict (σ : L ≃ₐ[K] L) :
    Place.ringOfIntegersEquiv σ = (galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv := by
  refine RingEquiv.ext fun x => NumberField.RingOfIntegers.coe_injective ?_
  simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap]
  rw [Place.ringOfIntegersEquiv_apply]
  rw [show (((galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv x) : L) =
    (galRestrict (𝓞 K) K L (𝓞 L) σ) x from rfl]
  simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, algebraMap_galRestrict_apply]

theorem smulHeightOneSpectrum_eq_placeSmul (σ : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L)) :
    Place.smulHeightOneSpectrum σ q = Submission.NeukirchUchida.Local.placeSmul σ q := by
  apply HeightOneSpectrum.ext
  show Ideal.map (↑(Place.ringOfIntegersEquiv σ) : 𝓞 L →+* 𝓞 L) q.asIdeal =
    Ideal.map (↑((galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv) : 𝓞 L →+* 𝓞 L) q.asIdeal
  rw [ringOfIntegersEquiv_eq_galRestrict σ]

/-! ## Continuity of the inverse local isomorphism -/

lemma localRingEquiv_symm_apply (σ : L ≃ₐ[K] L) (v : Place L)
    (h : σ⁻¹ • (σ • v) = v) (z : Place.localField L (σ • v)) :
    (Place.localRingEquiv σ v).symm z = h ▸ ((Place.localRingEquiv σ⁻¹ (σ • v)) z) := by
  have hfun : (fun z : Place.localField L (σ • v) =>
      (Place.localRingEquiv σ v) (h ▸ ((Place.localRingEquiv σ⁻¹ (σ • v)) z))) = id := by
    refine DenseRange.equalizer (Galois.denseRange_algebraMap_localField (σ • v)) ?_ ?_ ?_
    · exact (Galois.continuous_localRingEquiv σ v).comp
        (Galois.continuous_localField_cast h (Galois.continuous_localRingEquiv σ⁻¹ (σ • v)))
    · exact continuous_id
    · funext t
      simp only [Function.comp_apply, id_eq]
      rw [Place.localRingEquiv_algebraMap σ⁻¹ (σ • v) t,
        Galois.localField_cast_algebraMap h (σ⁻¹ t),
        Place.localRingEquiv_algebraMap σ v (σ⁻¹ t)]
      congr 1
      simp
  have key : ∀ z, (Place.localRingEquiv σ v)
      (h ▸ ((Place.localRingEquiv σ⁻¹ (σ • v)) z)) = z := fun z => congrFun hfun z
  conv_lhs => rw [← key z]
  exact RingEquiv.symm_apply_apply _ _

lemma continuous_localRingEquiv_symm (σ : L ≃ₐ[K] L) (v : Place L) :
    Continuous (Place.localRingEquiv σ v).symm := by
  have h : σ⁻¹ • (σ • v) = v := by
    rw [Galois.globalCFT_smul_place_smul σ σ⁻¹ v, inv_mul_cancel, Galois.globalCFT_one_smul_place]
  rw [show ⇑(Place.localRingEquiv σ v).symm =
      fun z => h ▸ ((Place.localRingEquiv σ⁻¹ (σ • v)) z) from funext (localRingEquiv_symm_apply σ v h)]
  exact Galois.continuous_localField_cast h (Galois.continuous_localRingEquiv σ⁻¹ (σ • v))

/-! ## Comparison with the decomposition group action -/

lemma localRingEquiv_symm_algebraMap_ofFinite (σ : L ≃ₐ[K] L) (q : HeightOneSpectrum (𝓞 L))
    (t : L) :
    (Place.localRingEquiv σ⁻¹ (Place.ofFinite q)).symm
        (algebraMap L (Place.localField L (Place.ofFinite (Place.smulHeightOneSpectrum σ⁻¹ q))) t)
      = algebraMap L (Place.localField L (Place.ofFinite q)) (σ t) := by
  have h := Galois.globalCFT_localRingEquiv_symm_algebraMap σ (Place.ofFinite q) t
  simpa only [Place.smul_ofFinite] using h

lemma localRingEquiv_symm_eq_decompositionToAdicCompletion
    (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (σ : L ≃ₐ[K] L) (hi : Place.smulHeightOneSpectrum σ⁻¹ q = q)
    (hσ : Submission.NeukirchUchida.Local.placeSmul σ q = q) (z : q.adicCompletion L) :
    (Place.localRingEquiv σ⁻¹ (Place.ofFinite q)).symm
        ((RingEquiv.cast (R := fun v => Place.localField L v) (congrArg Place.ofFinite hi).symm) z)
      = (Submission.NeukirchUchida.Local.decompositionToAdicCompletion q ⟨σ, hσ⟩) z := by
  have hdense := Galois.denseRange_algebraMap_localField (Place.ofFinite q)
  have key : (fun z : q.adicCompletion L =>
      (Place.localRingEquiv σ⁻¹ (Place.ofFinite q)).symm
        ((RingEquiv.cast (R := fun v => Place.localField L v)
          (congrArg Place.ofFinite hi).symm) z))
      = fun z : q.adicCompletion L =>
        (Submission.NeukirchUchida.Local.decompositionToAdicCompletion q ⟨σ, hσ⟩) z := by
    refine DenseRange.equalizer hdense ?_ ?_ ?_
    · exact (continuous_localRingEquiv_symm σ⁻¹ (Place.ofFinite q)).comp
        (continuous_ringEquiv_cast (congrArg Place.ofFinite hi).symm)
    · exact Submission.NeukirchUchida.Local.continuous_decompositionToAdicCompletion q ⟨σ, hσ⟩
    · funext t
      change (Place.localRingEquiv σ⁻¹ (Place.ofFinite q)).symm
          ((RingEquiv.cast (R := fun v => Place.localField L v)
            (congrArg Place.ofFinite hi).symm)
            ((algebraMap L (Place.localField L (Place.ofFinite q))) t))
        = (Submission.NeukirchUchida.Local.decompositionToAdicCompletion q ⟨σ, hσ⟩)
            ((algebraMap L (Place.localField L (Place.ofFinite q))) t)
      rw [castRingEquiv_algebraMap (congrArg Place.ofFinite hi).symm t,
        localRingEquiv_symm_algebraMap_ofFinite σ q t]
      simp only [Galois.globalCFT_algebraMap_eq_coe,
        Submission.NeukirchUchida.Local.decompositionToAdicCompletion_coe]
  exact congrFun key z


/-! ## The stabilizer identity at a finite place -/

lemma smulHeightOneSpectrum_one (q : HeightOneSpectrum (𝓞 L)) :
    Place.smulHeightOneSpectrum (1 : L ≃ₐ[K] L) q = q := by
  have h : (1 : L ≃ₐ[K] L) • (Place.ofFinite q) = Place.ofFinite q :=
    Galois.globalCFT_one_smul_place _
  rw [Place.smul_ofFinite] at h
  exact Place.ofFinite_inj.mp h

lemma smulHeightOneSpectrum_inv {q : HeightOneSpectrum (𝓞 L)} {σ : L ≃ₐ[K] L}
    (hs : Place.smulHeightOneSpectrum σ q = q) : Place.smulHeightOneSpectrum σ⁻¹ q = q := by
  have h := Galois.smulHeightOneSpectrum_mul σ σ⁻¹ q
  rw [hs, inv_mul_cancel, smulHeightOneSpectrum_one] at h
  exact h

lemma units_cast_eq {a b : Place L} (h : a = b) (x : (Place.localField L a)ˣ) :
    Units.map (RingEquiv.cast (R := fun v => Place.localField L v) h).toMonoidHom x = h ▸ x := by
  cases h; rfl

lemma Units_map_trans_apply' {A B C : Type*} [Semiring A] [Semiring B] [Semiring C]
    (e : A ≃+* B) (f : B ≃+* C) (u : Aˣ) :
    Units.map (e.trans f).toMonoidHom u = Units.map f.toMonoidHom (Units.map e.toMonoidHom u) := by
  ext
  simp [RingEquiv.trans_apply]

theorem prod_units_map_algEquiv_eq_map_norm {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (x : Eˣ) :
    (∏ g : E ≃ₐ[F] E, Units.map g.toRingEquiv.toMonoidHom x)
      = Units.map ((algebraMap F E : F →+* E).toMonoidHom)
          (Units.map (Algebra.norm F : E →* F) x) := by
  apply Units.ext
  rw [Units.coe_prod]
  simp only [Units.coe_map]
  change ∏ i : E ≃ₐ[F] E, i (↑x : E) = algebraMap F E (Algebra.norm F (↑x : E))
  rw [← Algebra.norm_eq_prod_automorphisms]

theorem localNormFinite_stab_prod (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (y : Idele L) :
    (∏ δ : {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q}, (δ.1 • y) (Place.ofFinite q))
      = Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q) (Place.liesOver_ofFinite hq)
          (Place.localNormFinite q Q hq (y (Place.ofFinite q))) := by
  classical
  have hterm : ∀ δ : {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q},
      (δ.1 • y) (Place.ofFinite q)
        = Units.map (((RingEquiv.cast (R := fun v => Place.localField L v)
              (congrArg Place.ofFinite (smulHeightOneSpectrum_inv δ.2)).symm).trans
            ((Place.localRingEquiv δ.1⁻¹ (Place.ofFinite q)).symm))).toMonoidHom
          (y (Place.ofFinite q)) := by
    intro δ
    rw [Idele.smul_apply]
    have hcast : y (δ.1⁻¹ • Place.ofFinite q)
        = Units.map (RingEquiv.cast (R := fun v => Place.localField L v)
            (congrArg Place.ofFinite (smulHeightOneSpectrum_inv δ.2)).symm).toMonoidHom
          (y (Place.ofFinite q)) := by
      rw [units_cast_eq]
      exact (cast_dep_apply y (congrArg Place.ofFinite (smulHeightOneSpectrum_inv δ.2)).symm).symm
    rw [hcast, Units_map_trans_apply']
  rw [Finset.prod_congr rfl (fun δ _ => hterm δ)]
  have hcomp : ∀ δ : {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q},
      ((RingEquiv.cast (R := fun v => Place.localField L v)
            (congrArg Place.ofFinite (smulHeightOneSpectrum_inv δ.2)).symm).trans
          ((Place.localRingEquiv δ.1⁻¹ (Place.ofFinite q)).symm))
        = Submission.NeukirchUchida.Local.decompositionToAdicCompletion q
            ⟨δ.1, (smulHeightOneSpectrum_eq_placeSmul δ.1 q).symm.trans δ.2⟩ := by
    intro δ
    refine RingEquiv.ext fun z => ?_
    exact localRingEquiv_symm_eq_decompositionToAdicCompletion q Q hq δ.1
      (smulHeightOneSpectrum_inv δ.2) _ z
  rw [Finset.prod_congr rfl (fun δ _ => by rw [hcomp δ])]
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    Submission.NeukirchUchida.Local.adicCompletionAlgebra Q q hq
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q hq
  letI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
  -- the associated local Galois automorphisms
  have hint : ∀ δ : {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q},
      ∀ x : Q.adicCompletion K,
        (Submission.NeukirchUchida.Local.decompositionToAdicCompletion q
            ⟨δ.1, (smulHeightOneSpectrum_eq_placeSmul δ.1 q).symm.trans δ.2⟩)
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) x)
          = algebraMap (Q.adicCompletion K) (q.adicCompletion L) x := by
    intro δ x
    rw [Submission.NeukirchUchida.Local.decompositionToAdicCompletion_algebraMap Q q hq]
  let F : {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q} →
      (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := fun δ =>
    AlgEquiv.ofRingEquiv
      (f := Submission.NeukirchUchida.Local.decompositionToAdicCompletion q
        ⟨δ.1, (smulHeightOneSpectrum_eq_placeSmul δ.1 q).symm.trans δ.2⟩)
      (hint δ)
  have hF_inj : Function.Injective F := by
    intro δ₁ δ₂ h
    have h3 : ∀ u : L, δ₁.1 u = δ₂.1 u := by
      intro u
      have h4 := congrFun (congrArg DFunLike.coe h) (algebraMap L (q.adicCompletion L) u)
      rw [AlgEquiv.ofRingEquiv_apply, AlgEquiv.ofRingEquiv_apply] at h4
      have e1 : (Submission.NeukirchUchida.Local.decompositionToAdicCompletion q
            ⟨δ₁.1, (smulHeightOneSpectrum_eq_placeSmul δ₁.1 q).symm.trans δ₁.2⟩)
            (algebraMap L (q.adicCompletion L) u)
          = algebraMap L (q.adicCompletion L) (δ₁.1 u) := by
        rw [Galois.globalCFT_algebraMap_eq_coe,
          Submission.NeukirchUchida.Local.decompositionToAdicCompletion_coe,
          Galois.globalCFT_algebraMap_eq_coe]
      have e2 : (Submission.NeukirchUchida.Local.decompositionToAdicCompletion q
            ⟨δ₂.1, (smulHeightOneSpectrum_eq_placeSmul δ₂.1 q).symm.trans δ₂.2⟩)
            (algebraMap L (q.adicCompletion L) u)
          = algebraMap L (q.adicCompletion L) (δ₂.1 u) := by
        rw [Galois.globalCFT_algebraMap_eq_coe,
          Submission.NeukirchUchida.Local.decompositionToAdicCompletion_coe,
          Galois.globalCFT_algebraMap_eq_coe]
      rw [e1, e2] at h4
      exact Submission.NeukirchUchida.Local.injective_algebraMap_adicCompletion q h4
    exact Subtype.ext (AlgEquiv.ext h3)
  have hcard : Nat.card {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q}
      = Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (p := fun δ : L ≃ₐ[K] L =>
          Place.smulHeightOneSpectrum δ q = q)
        (q := fun δ : L ≃ₐ[K] L => Submission.NeukirchUchida.Local.placeSmul δ q = q)
        (fun δ => ⟨fun hh => by rw [← smulHeightOneSpectrum_eq_placeSmul δ q]; exact hh,
          fun hh => by rw [smulHeightOneSpectrum_eq_placeSmul δ q]; exact hh⟩))]
    change Nat.card (↥(Submission.NeukirchUchida.Local.decompositionSubgroup q))
      = Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
    rw [Submission.NeukirchUchida.Local.card_decompositionSubgroup Q q hq,
      ← Submission.NeukirchUchida.Local.finrank_adicCompletion_eq_ef' Q q hq]
    exact (IsGalois.card_aut_eq_finrank (Q.adicCompletion K) (q.adicCompletion L)).symm
  have hbij : Function.Bijective F :=
    Function.Injective.bijective_of_nat_card_le hF_inj hcard.ge
  rw [Fintype.prod_bijective F hbij
    (fun δ : {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q} =>
      Units.map (Submission.NeukirchUchida.Local.decompositionToAdicCompletion q
        ⟨δ.1, (smulHeightOneSpectrum_eq_placeSmul δ.1 q).symm.trans δ.2⟩).toMonoidHom
        (y (Place.ofFinite q)))
    (fun g : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L =>
      Units.map g.toRingEquiv.toMonoidHom (y (Place.ofFinite q)))
    (fun δ => rfl)]
  have hnorm : (∏ g : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      Units.map g.toRingEquiv.toMonoidHom (y (Place.ofFinite q)))
      = Units.map ((algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom)
        (Place.localNormFinite q Q hq (y (Place.ofFinite q))) := by
    exact prod_units_map_algEquiv_eq_map_norm (F := Q.adicCompletion K)
      (E := q.adicCompletion L) (y (Place.ofFinite q))
  refine hnorm.trans ?_
  rw [show Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q)
        (Place.liesOver_ofFinite hq)
      = Units.map ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toMonoidHom) from by
    show (dite (q.asIdeal.LiesOver Q.asIdeal)
      (fun hL => Units.map ((Commons.RingTheory.Henselian.adicCompletionMap Q q hL).toMonoidHom))
      (fun _ => 1)) = _
    rw [dif_pos hq]]
  rfl


/-! ## The fibre identity at a finite place -/

lemma RingEquiv_cast_adicCompletionMap {Q : HeightOneSpectrum (𝓞 K)}
    {q q' : HeightOneSpectrum (𝓞 L)} (hc : Place.ofFinite q = Place.ofFinite q')
    (h : q.asIdeal.LiesOver Q.asIdeal) (h' : q'.asIdeal.LiesOver Q.asIdeal)
    (a : Q.adicCompletion K) :
    (RingEquiv.cast (R := fun v => Place.localField L v) hc)
        (Commons.RingTheory.Henselian.adicCompletionMap Q q h a)
      = Commons.RingTheory.Henselian.adicCompletionMap Q q' h' a := by
  have hqq : q = q' := Place.ofFinite_inj.mp hc
  subst hqq
  rw [show hc = rfl from Subsingleton.elim hc rfl,
    show h' = h from Subsingleton.elim h' h]
  simp only [RingEquiv.cast_apply, cast_eq]

lemma exists_smul_eq_place' (Q : HeightOneSpectrum (𝓞 K)) (q q₀ : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (hq₀ : q₀.asIdeal.LiesOver Q.asIdeal) :
    ∃ σ : L ≃ₐ[K] L, Place.smulHeightOneSpectrum σ q = q₀ := by
  letI : MulSemiringAction Gal(L/K) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  haveI : MulAction.IsPretransitive (L ≃ₐ[K] L) ↥(Q.asIdeal.primesOver (𝓞 L)) :=
    Ideal.isPretransitive_of_isGaloisGroup Q.asIdeal (L ≃ₐ[K] L)
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L)
    (show ↥(Q.asIdeal.primesOver (𝓞 L)) from ⟨q.asIdeal, q.isPrime, hq⟩)
    (show ↥(Q.asIdeal.primesOver (𝓞 L)) from ⟨q₀.asIdeal, q₀.isPrime, hq₀⟩)
  refine ⟨σ, ?_⟩
  have h2 : Ideal.map (galRestrict (𝓞 K) K L (𝓞 L) σ) q.asIdeal = q₀.asIdeal := by
    have h3 := congrArg Subtype.val hσ
    rwa [Ideal.coe_smul_primesOver_mk_eq_map_galRestrict K L σ q.asIdeal] at h3
  rw [smulHeightOneSpectrum_eq_placeSmul]
  exact HeightOneSpectrum.ext h2


lemma smulHeightOneSpectrum_injective (σ : L ≃ₐ[K] L) :
    Function.Injective (Place.smulHeightOneSpectrum σ) := by
  intro a b h
  have h1 := congrArg (Place.smulHeightOneSpectrum σ⁻¹) h
  simp only [Galois.smulHeightOneSpectrum_mul, inv_mul_cancel, smulHeightOneSpectrum_one] at h1
  exact h1

lemma localAlgebraMapUnits_ofFinite_eq (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q) (Place.liesOver_ofFinite hq)
      = Units.map ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toMonoidHom) := by
  show (dite (q.asIdeal.LiesOver Q.asIdeal)
    (fun hL => Units.map ((Commons.RingTheory.Henselian.adicCompletionMap Q q hL).toMonoidHom))
    (fun _ => 1)) = _
  rw [dif_pos hq]

theorem globalCFT_inner_prod_finite (Q : HeightOneSpectrum (𝓞 K))
    (q q₀ : HeightOneSpectrum (𝓞 L)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hq₀ : q₀.asIdeal.LiesOver Q.asIdeal) (y : Idele L) :
    (∏ σ : {σ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum σ⁻¹ q₀ = q},
        (σ.1 • y) (Place.ofFinite q₀))
      = Place.localAlgebraMapUnits (Place.ofFinite q₀) (Place.ofFinite Q)
          (Place.liesOver_ofFinite hq₀)
          (Place.localNormFinite q Q hq (y (Place.ofFinite q))) := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := exists_smul_eq_place' Q q q₀ hq hq₀
  have hσ₀' : Place.smulHeightOneSpectrum σ₀⁻¹ q₀ = q := by
    have h1 : Place.smulHeightOneSpectrum σ₀⁻¹ (Place.smulHeightOneSpectrum σ₀ q) =
        Place.smulHeightOneSpectrum σ₀⁻¹ q₀ := by rw [hσ₀]
    rw [Galois.smulHeightOneSpectrum_mul, inv_mul_cancel, smulHeightOneSpectrum_one] at h1
    exact h1.symm
  have hq' : (Place.smulHeightOneSpectrum σ₀⁻¹ q₀).asIdeal.LiesOver Q.asIdeal :=
    (Galois.globalCFT_finitePlace_smul_liesOver σ₀⁻¹ q₀ Q).mpr hq₀
  have hc' : Place.ofFinite q = σ₀⁻¹ • Place.ofFinite q₀ :=
    (congrArg Place.ofFinite hσ₀').symm
  have hterm2 : ∀ δ : {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q},
      ((σ₀ * δ.1) • y) (Place.ofFinite q₀)
        = Units.map ((RingEquiv.cast (R := fun v => Place.localField L v) hc').trans
            ((Place.localRingEquiv σ₀⁻¹ (Place.ofFinite q₀)).symm)).toMonoidHom
          ((δ.1 • y) (Place.ofFinite q)) := by
    intro δ
    rw [Galois.globalCFT_mul_smul_idele, Idele.smul_apply]
    have hcast : (δ.1 • y) (σ₀⁻¹ • Place.ofFinite q₀)
        = Units.map (RingEquiv.cast (R := fun v => Place.localField L v) hc').toMonoidHom
            ((δ.1 • y) (Place.ofFinite q)) := by
      rw [units_cast_eq]
      exact (cast_dep_apply (δ.1 • y) hc').symm
    rw [hcast, Units_map_trans_apply']
  have hmu : ∀ a : (Q.adicCompletion K)ˣ,
      Units.map ((RingEquiv.cast (R := fun v => Place.localField L v) hc').trans
          ((Place.localRingEquiv σ₀⁻¹ (Place.ofFinite q₀)).symm)).toMonoidHom
          (Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q)
            (Place.liesOver_ofFinite hq) a)
        = Place.localAlgebraMapUnits (Place.ofFinite q₀) (Place.ofFinite Q)
            (Place.liesOver_ofFinite hq₀) a := by
    intro a
    rw [localAlgebraMapUnits_ofFinite_eq q Q hq, Units_map_trans_apply']
    have hcast2 : Units.map (RingEquiv.cast (R := fun v => Place.localField L v) hc').toMonoidHom
          (Units.map ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toMonoidHom) a)
        = Place.localAlgebraMapUnits (Place.ofFinite (Place.smulHeightOneSpectrum σ₀⁻¹ q₀))
            (Place.ofFinite Q) (Place.liesOver_ofFinite hq') a := by
      rw [localAlgebraMapUnits_ofFinite_eq (Place.smulHeightOneSpectrum σ₀⁻¹ q₀) Q hq']
      apply Units.ext
      show (RingEquiv.cast (R := fun v => Place.localField L v) hc')
          ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq) ↑a)
        = (Commons.RingTheory.Henselian.adicCompletionMap Q
            (Place.smulHeightOneSpectrum σ₀⁻¹ q₀) hq') ↑a
      exact RingEquiv_cast_adicCompletionMap hc' hq hq' ↑a
    rw [hcast2]
    have heq : Units.map (Place.localRingEquiv σ₀⁻¹ (Place.ofFinite q₀)).toMonoidHom
          (Place.localAlgebraMapUnits (Place.ofFinite q₀) (Place.ofFinite Q)
            (Place.liesOver_ofFinite hq₀) a)
        = Place.localAlgebraMapUnits (Place.ofFinite (Place.smulHeightOneSpectrum σ₀⁻¹ q₀))
            (Place.ofFinite Q) (Place.liesOver_ofFinite hq') a :=
      Galois.globalCFT_localRingEquiv_localAlgebraMapUnits (σ₀⁻¹) (Place.liesOver_ofFinite hq₀)
        (Place.liesOver_ofFinite hq') a
    rw [← heq]
    ext
    simp
  have hmem : ∀ δ : {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q},
      Place.smulHeightOneSpectrum (σ₀ * δ.1)⁻¹ q₀ = q := by
    intro δ
    rw [mul_inv_rev, ← Galois.smulHeightOneSpectrum_mul, hσ₀']
    exact smulHeightOneSpectrum_inv δ.2
  have hbij : Function.Bijective
      (fun δ : {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q} =>
        (⟨σ₀ * δ.1, hmem δ⟩ : {σ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum σ⁻¹ q₀ = q})) := by
    constructor
    · intro δ₁ δ₂ h
      exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
    · intro σ
      obtain ⟨σ1, hσ1⟩ := σ
      have h2 : Place.smulHeightOneSpectrum σ1 q = q₀ := by
        have h := congrArg (fun qq : HeightOneSpectrum (𝓞 L) =>
          Place.smulHeightOneSpectrum σ1 qq) hσ1
        rw [Galois.smulHeightOneSpectrum_mul, mul_inv_cancel, smulHeightOneSpectrum_one] at h
        exact h.symm
      refine ⟨⟨σ₀⁻¹ * σ1, ?_⟩, ?_⟩
      · rw [← Galois.smulHeightOneSpectrum_mul, h2, hσ₀']
      · apply Subtype.ext
        show σ₀ * (σ₀⁻¹ * σ1) = σ1
        group
  rw [← Fintype.prod_bijective (fun δ : {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q} =>
        (⟨σ₀ * δ.1, hmem δ⟩ : {σ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum σ⁻¹ q₀ = q})) hbij
      (fun δ : {δ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum δ q = q} =>
        ((σ₀ * δ.1) • y) (Place.ofFinite q₀))
      (fun σ : {σ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum σ⁻¹ q₀ = q} =>
        (σ.1 • y) (Place.ofFinite q₀))
      (fun δ => rfl)]
  rw [Finset.prod_congr rfl (fun δ _ => hterm2 δ)]
  rw [← map_prod]
  rw [localNormFinite_stab_prod q Q hq y]
  exact hmu (Place.localNormFinite q Q hq (y (Place.ofFinite q)))

/-! ## The archimedean place: elementary lemmas -/

/-- The restriction of an infinite place `w` of `L` to `K` is the place of `K` below it. -/
lemma comap_algebraMap_eq_of_liesOver {w : InfinitePlace L} {v : InfinitePlace K}
    (h : w.LiesOver v) : w.comap (algebraMap K L) = v := by
  refine InfinitePlace.ext _ _ fun k => ?_
  rw [InfinitePlace.comap_apply]
  exact DFunLike.congr_fun (AbsoluteValue.LiesOver.comp_eq (w := w.val) (v := v.val)) k

/-- If `v` and `w` are both real, the completion map is surjective. -/
theorem completionMap_surjective_of_isReal_under {v : InfinitePlace K} {w : InfinitePlace L}
    [h : w.LiesOver v] (hv : v.IsReal) (hw : w.IsReal) :
    Function.Surjective (NumberField.LiesOver.completionMap (v := v) (w := w)) := by
  intro y
  rw [← Set.mem_range]
  rw [NK.GlobalCFT.Galois.range_completionMap_of_isReal_under (K := K) (L := L) hv]
  rw [Set.mem_setOf_eq,
    ← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw y]
  exact Complex.ofReal_im _

/-- The local algebra map at an archimedean place, in terms of `completionMap`. -/
lemma localAlgebraMapUnits_ofInfinite {w : InfinitePlace L} {v : InfinitePlace K}
    (h : w.LiesOver v) :
    Place.localAlgebraMapUnits (Place.ofInfinite w) (Place.ofInfinite v)
        (Place.liesOver_ofInfinite h) =
      Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom := by
  classical
  change dite (w.LiesOver v)
      (fun _ => Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom)
      (fun _ => 1) =
    Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom
  rw [dif_pos h]

/-- Transporting a completion map along an equality of the corresponding infinite places. -/
lemma RingEquiv_cast_completionMap {v : InfinitePlace K} {w w' : InfinitePlace L}
    (hc : Place.ofInfinite w = Place.ofInfinite w') (h : w.LiesOver v) (h' : w'.LiesOver v)
    (a : v.Completion) :
    (RingEquiv.cast (R := fun p => Place.localField L p) hc)
        (NumberField.LiesOver.completionMap (v := v) (w := w) a) =
      NumberField.LiesOver.completionMap (v := v) (w := w') a := by
  have hww : w = w' := Place.ofInfinite_inj.mp hc
  subst hww
  rw [show hc = rfl from Subsingleton.elim hc rfl, show h' = h from Subsingleton.elim h' h]
  simp only [RingEquiv.cast_apply, cast_eq]

/-- A field extension spanned by the image of the base field has degree at most `1`. -/
lemma finrank_le_one_of_surjective {A B : Type*} [Field A] [Field B] [Algebra A B]
    (h : Function.Surjective (algebraMap A B)) : Module.finrank A B ≤ 1 := by
  have htop : (⊤ : Submodule A B) = Submodule.span A ({1} : Set B) := by
    have hmem : ∀ b : B, b ∈ Submodule.span A ({1} : Set B) := by
      intro b
      obtain ⟨a, rfl⟩ := h b
      exact Submodule.mem_span_singleton.mpr ⟨a, by simp [Algebra.algebraMap_eq_smul_one]⟩
    rw [eq_comm, Submodule.eq_top_iff']
    exact hmem
  calc Module.finrank A B = Module.finrank A (⊤ : Submodule A B) := (finrank_top A B).symm
    _ = Module.finrank A (Submodule.span A ({1} : Set B)) := by rw [htop]
    _ ≤ ({1} : Set B).toFinset.card := finrank_span_le_card _
    _ = 1 := by simp

/-! ## The archimedean analogue of the local Galois group of a place -/

/-- For `δ` in the stabiliser of an archimedean place, `δ⁻¹` is in the stabiliser too. -/
lemma infStabInv {w : InfinitePlace L}
    (δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w}) :
    (δ.1⁻¹) • Place.ofInfinite w = Place.ofInfinite w := by
  have h : (δ.1⁻¹) • (δ.1 • Place.ofInfinite w) = (δ.1⁻¹) • Place.ofInfinite w := by rw [δ.2]
  rw [Galois.globalCFT_smul_place_smul, inv_mul_cancel, Galois.globalCFT_one_smul_place] at h
  exact h.symm

/-- The local field isomorphism attached to the inverse of a stabiliser element, as a self-map of
the local field. -/
noncomputable def infF {w : InfinitePlace L}
    (δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w}) :
    Place.localField L (Place.ofInfinite w) ≃+* Place.localField L (Place.ofInfinite w) :=
  (RingEquiv.cast (R := fun p => Place.localField L p) (infStabInv δ).symm).trans
    ((Place.localRingEquiv (δ.1⁻¹) (Place.ofInfinite w)).symm)

/-- The compatibility of the completion map with the extension embeddings into `ℂ`, when the
place below is real. -/
lemma completionMap_extensionEmbedding {v : InfinitePlace K} {w : InfinitePlace L}
    [hv : w.LiesOver v] (hvr : v.IsReal) (a : v.Completion) :
    NumberField.InfinitePlace.Completion.extensionEmbedding w
        (NumberField.LiesOver.completionMap (v := v) (w := w) a) =
      NumberField.InfinitePlace.Completion.extensionEmbedding v a := by
  have h := (NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hvr).over
  have h2 : ⇑(algebraMap v.Completion w.Completion)
      = ⇑(NumberField.LiesOver.completionMap (v := v) (w := w)) := by
    rw [RingHom.algebraMap_toAlgebra]
  simpa [RingHom.comp_apply, h2] using congrFun (congrArg DFunLike.coe h) a

/-- The archimedean local extension has degree `2` in the ramified case. -/
theorem finrank_completionMap {v : InfinitePlace K} {w : InfinitePlace L} [hv : w.LiesOver v]
    (hvr : v.IsReal) (hwc : w.IsComplex) :
    Module.finrank (v.Completion) (w.Completion) = 2 := by
  have hc : (algebraMap ℝ ℂ).comp
        (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvr).toRingHom =
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).toRingHom.comp
        (algebraMap (v.Completion) (w.Completion)) := by
    ext a
    show (algebraMap ℝ ℂ) ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvr) a) =
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc)
        ((algebraMap (v.Completion) (w.Completion)) a)
    rw [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply hvr a,
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hwc
        ((algebraMap (v.Completion) (w.Completion)) a),
      show (algebraMap (v.Completion) (w.Completion))
        = NumberField.LiesOver.completionMap (v := v) (w := w) from by
          rw [RingHom.algebraMap_toAlgebra],
      completionMap_extensionEmbedding (K := K) (L := L) hvr a,
      ← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hvr a]
    rfl
  have hmain := Algebra.finrank_eq_of_equiv_equiv (R₀ := v.Completion) (S₀ := w.Completion)
    (R₁ := ℝ) (S₁ := ℂ)
    (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvr)
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc) hc
  rw [hmain, Complex.finrank_real_complex]

/-- The archimedean local extension is finite dimensional. -/
theorem finiteDimensional_completionMap {v : InfinitePlace K} {w : InfinitePlace L}
    [hv : w.LiesOver v] (hvr : v.IsReal) (hwc : w.IsComplex) :
    Module.Finite (v.Completion) (w.Completion) :=
  Module.finite_of_finrank_eq_succ (n := 1) (by rw [finrank_completionMap hvr hwc])

/-- The local extension is spanned by the base field in the unramified case: the degree is `≤ 1`. -/
theorem finrank_le_one_of_isUnramified {v : InfinitePlace K} {w : InfinitePlace L}
    [hv : w.LiesOver v] (hu : InfinitePlace.IsUnramified K w) :
    Module.finrank (v.Completion) (w.Completion) ≤ 1 := by
  have hcomap : w.comap (algebraMap K L) = v := comap_algebraMap_eq_of_liesOver hv
  rcases (InfinitePlace.isUnramified_iff.mp hu) with hwr | hvc
  · have hvr : v.IsReal := by
      have h2 := InfinitePlace.IsReal.comap (algebraMap K L) hwr
      rwa [hcomap] at h2
    exact finrank_le_one_of_surjective (A := v.Completion) (B := w.Completion) (by
      rw [RingHom.algebraMap_toAlgebra]
      exact completionMap_surjective_of_isReal_under (K := K) (L := L) hvr hwr)
  · have hvc' : v.IsComplex := by rwa [hcomap] at hvc
    exact finrank_le_one_of_surjective (A := v.Completion) (B := w.Completion) (by
      rw [RingHom.algebraMap_toAlgebra]
      exact NK.GlobalCFT.Galois.completionMap_surjective_of_isComplex_under
        (K := K) (L := L) hvc')

/-- The stabiliser of an archimedean place, as a subtype of the Galois group. -/
theorem natCard_infStab_of_isUnramified {w : InfinitePlace L} (hu : InfinitePlace.IsUnramified K w) :
    Nat.card {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w} = 1 := by
  have h1 : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) = 1 :=
    InfinitePlace.isUnramified_iff_card_stabilizer_eq_one.mp hu
  rw [← h1]
  exact Nat.card_congr (Equiv.subtypeEquivRight
    (p := fun δ : L ≃ₐ[K] L => δ • Place.ofInfinite w = Place.ofInfinite w)
    (q := fun δ : L ≃ₐ[K] L => δ • w = w)
    (fun δ => ⟨fun hh => Place.ofInfinite_inj.mp hh, fun hh => by
      show Place.ofInfinite (δ • w) = Place.ofInfinite w
      rw [hh]⟩))

/-- The stabiliser of a ramified archimedean place. -/
theorem natCard_infStab_of_not_isUnramified {w : InfinitePlace L}
    (hu : ¬ InfinitePlace.IsUnramified K w) :
    Nat.card {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w} = 2 := by
  have h1 : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) = 2 :=
    InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two.mp hu
  rw [← h1]
  exact Nat.card_congr (Equiv.subtypeEquivRight
    (p := fun δ : L ≃ₐ[K] L => δ • Place.ofInfinite w = Place.ofInfinite w)
    (q := fun δ : L ≃ₐ[K] L => δ • w = w)
    (fun δ => ⟨fun hh => Place.ofInfinite_inj.mp hh, fun hh => by
      show Place.ofInfinite (δ • w) = Place.ofInfinite w
      rw [hh]⟩))

/-- The canonical embedding of `L` into its completion at an archimedean place is injective. -/
lemma injective_algebraMap_ofInfinite (w : InfinitePlace L) :
    Function.Injective (algebraMap L (Place.localField L (Place.ofInfinite w))) := by
  intro x y hxy
  apply w.embedding.injective
  have h := congrArg (NumberField.InfinitePlace.Completion.extensionEmbedding w) hxy
  simpa [NumberField.InfinitePlace.Completion.algebraMap_apply] using h

/-- A field extension spanned by the base field is finite. -/
lemma finite_of_surjective_algebraMap {A B : Type*} [Field A] [Field B] [Algebra A B]
    (h : Function.Surjective (algebraMap A B)) : Module.Finite A B :=
  Module.Finite.of_surjective (Algebra.linearMap A B) h

/-- In the unramified case the completion map is surjective. -/
theorem surjective_completionMap_of_isUnramified {v : InfinitePlace K} {w : InfinitePlace L}
    [hv : w.LiesOver v] (hu : InfinitePlace.IsUnramified K w) :
    Function.Surjective (algebraMap (v.Completion) (w.Completion)) := by
  have hcomap : w.comap (algebraMap K L) = v := comap_algebraMap_eq_of_liesOver hv
  rw [show (algebraMap (v.Completion) (w.Completion))
      = NumberField.LiesOver.completionMap (v := v) (w := w) from by
    rw [RingHom.algebraMap_toAlgebra]]
  rcases (InfinitePlace.isUnramified_iff.mp hu) with hwr | hvc
  · have hvr : v.IsReal := by
      have h2 := InfinitePlace.IsReal.comap (algebraMap K L) hwr
      rwa [hcomap] at h2
    exact completionMap_surjective_of_isReal_under (K := K) (L := L) hvr hwr
  · have hvc' : v.IsComplex := by rwa [hcomap] at hvc
    exact NK.GlobalCFT.Galois.completionMap_surjective_of_isComplex_under
      (K := K) (L := L) hvc'

/-- In the unramified case the local extension is finite. -/
theorem finite_of_isUnramified {v : InfinitePlace K} {w : InfinitePlace L}
    [hv : w.LiesOver v] (hu : InfinitePlace.IsUnramified K w) :
    Module.Finite (v.Completion) (w.Completion) :=
  finite_of_surjective_algebraMap (surjective_completionMap_of_isUnramified (K := K) (L := L) hu)

/-- In the ramified archimedean case the place below is real. -/
theorem isReal_of_not_isUnramified {v : InfinitePlace K} {w : InfinitePlace L}
    [hv : w.LiesOver v] (hu : ¬ InfinitePlace.IsUnramified K w) : v.IsReal := by
  have hcomap : w.comap (algebraMap K L) = v := comap_algebraMap_eq_of_liesOver hv
  rcases (InfinitePlace.isUnramified_iff).not.mp hu with h
  push_neg at h
  obtain ⟨hw, hv⟩ := h
  exact InfinitePlace.not_isComplex_iff_isReal.mp (fun hvc => hv (by rwa [hcomap]))

/-- In the ramified archimedean case the place above is complex. -/
theorem isComplex_of_not_isUnramified {v : InfinitePlace K} {w : InfinitePlace L}
    [hv : w.LiesOver v] (hu : ¬ InfinitePlace.IsUnramified K w) : w.IsComplex := by
  have hcomap : w.comap (algebraMap K L) = v := comap_algebraMap_eq_of_liesOver hv
  rcases (InfinitePlace.isUnramified_iff).not.mp hu with h
  push_neg at h
  obtain ⟨hw, hv⟩ := h
  exact InfinitePlace.not_isReal_iff_isComplex.mp hw

/-- The archimedean local extension is finite dimensional in all cases. -/
theorem finite_completionMap {v : InfinitePlace K} {w : InfinitePlace L} [hv : w.LiesOver v] :
    Module.Finite (v.Completion) (w.Completion) := by
  by_cases hu : InfinitePlace.IsUnramified K w
  · exact finite_of_isUnramified (K := K) (L := L) (v := v) (w := w) hu
  · exact finiteDimensional_completionMap (K := K) (L := L) (v := v) (w := w)
      (isReal_of_not_isUnramified (K := K) (L := L) (v := v) (w := w) hu)
      (isComplex_of_not_isUnramified (K := K) (L := L) (v := v) (w := w) hu)

/-- The completion map is compatible with the embeddings of the base field. -/
lemma completionMap_algebraMap {v : InfinitePlace K} {w : InfinitePlace L} [hw : w.LiesOver v]
    (k : K) :
    NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap K v.Completion k)
      = algebraMap L w.Completion (algebraMap K L k) := by
  have h1 : NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap K v.Completion k)
      = algebraMap K w.Completion k := by
    rw [show ⇑(NumberField.LiesOver.completionMap (v := v) (w := w))
        = ⇑(algebraMap (v.Completion) (w.Completion)) from by
      rw [RingHom.algebraMap_toAlgebra]]
    exact (IsScalarTower.algebraMap_apply K (v.Completion) (w.Completion) k).symm
  rw [h1]
  rfl

/-- The local field isomorphisms attached to `Gal(L/K)` intertwine the completion maps: the
archimedean analogue of `globalCFT_adicCongrEquiv_adicCompletionMap`. -/
lemma localRingEquiv_completionMap {σ : L ≃ₐ[K] L} {w : InfinitePlace L} {v : InfinitePlace K}
    [hw : w.LiesOver v] [hw' : (σ • w).LiesOver v] (x : v.Completion) :
    (Place.localRingEquiv σ (Place.ofInfinite w))
        (NumberField.LiesOver.completionMap (v := v) (w := w) x)
      = NumberField.LiesOver.completionMap (v := v) (w := σ • w) x := by
  have hdense : DenseRange (algebraMap K (v.Completion)) :=
    Galois.denseRange_algebraMap_localField (Place.ofInfinite v)
  have hcont1 : Continuous (fun x : v.Completion => (Place.localRingEquiv σ (Place.ofInfinite w))
      (NumberField.LiesOver.completionMap (v := v) (w := w) x)) :=
    (Galois.continuous_localRingEquiv σ (Place.ofInfinite w)).comp
      (NumberField.LiesOver.continuous_completionMap (v := v) (w := w))
  have hcont2 : Continuous (NumberField.LiesOver.completionMap (v := v) (w := σ • w)) :=
    NumberField.LiesOver.continuous_completionMap (v := v) (w := σ • w)
  refine congrFun (DenseRange.equalizer hdense hcont1 hcont2 ?_) x
  funext k
  show (Place.localRingEquiv σ (Place.ofInfinite w))
      (NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap K v.Completion k))
    = NumberField.LiesOver.completionMap (v := v) (w := σ • w) (algebraMap K v.Completion k)
  rw [completionMap_algebraMap (K := K) (L := L) (v := v) (w := w) k,
    completionMap_algebraMap (K := K) (L := L) (v := v) (w := σ • w) k,
    Place.localRingEquiv_algebraMap σ (Place.ofInfinite w) (algebraMap K L k)]
  exact congrArg (fun y => (algebraMap L (Place.localField L (σ • Place.ofInfinite w))) y)
    (AlgEquiv.commutes σ k)

/-- The archimedean analogue of `localNormFinite_stab_prod`. -/
theorem localNormInfinite_stab_prod (w : InfinitePlace L) (v : InfinitePlace K)
    [hv : w.LiesOver v] (y : Idele L) :
    (∏ δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w},
      (δ.1 • y) (Place.ofInfinite w))
      = Place.localAlgebraMapUnits (Place.ofInfinite w) (Place.ofInfinite v)
          (Place.liesOver_ofInfinite hv)
          (Place.localNormInfinite w v (y (Place.ofInfinite w))) := by
  classical
  have hterm : ∀ δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w},
      (δ.1 • y) (Place.ofInfinite w) =
        Units.map (infF δ).toMonoidHom (y (Place.ofInfinite w)) := by
    intro δ
    rw [Idele.smul_apply]
    have hcast : y (δ.1⁻¹ • Place.ofInfinite w)
        = Units.map (RingEquiv.cast (R := fun p => Place.localField L p)
            (infStabInv δ).symm).toMonoidHom (y (Place.ofInfinite w)) := by
      rw [units_cast_eq]
      exact (cast_dep_apply y (infStabInv δ).symm).symm
    rw [hcast]
    show Units.map (Place.localRingEquiv (δ.1⁻¹) (Place.ofInfinite w)).symm.toMonoidHom
        (Units.map (RingEquiv.cast (R := fun p => Place.localField L p)
          (infStabInv δ).symm).toMonoidHom (y (Place.ofInfinite w)))
      = Units.map (infF δ).toMonoidHom (y (Place.ofInfinite w))
    rw [show infF δ = (RingEquiv.cast (R := fun p => Place.localField L p)
        (infStabInv δ).symm).trans
        ((Place.localRingEquiv (δ.1⁻¹) (Place.ofInfinite w)).symm) from rfl]
    rw [Units_map_trans_apply']
  rw [Finset.prod_congr rfl (fun δ _ => hterm δ)]
  -- the local algebra structure is preserved by the action
  have hmem : ∀ δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w},
      (δ.1⁻¹ • w).LiesOver v := by
    intro δ
    have hh : Place.LiesOver ((δ.1⁻¹) • Place.ofInfinite w) (Place.ofInfinite v) :=
      (Galois.globalCFT_place_smul_liesOver (δ.1⁻¹) (Place.ofInfinite w) (Place.ofInfinite v)).mpr
        (Place.liesOver_ofInfinite hv)
    exact (Galois.globalCFT_liesOver_ofInfinite_iff (δ.1⁻¹ • w) v).mp hh
  have hcast2 : ∀ δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w},
      ∀ x : v.Completion,
      (RingEquiv.cast (R := fun p => Place.localField L p) (infStabInv δ).symm)
          (NumberField.LiesOver.completionMap (v := v) (w := w) x)
        = NumberField.LiesOver.completionMap (v := v) (w := δ.1⁻¹ • w) x :=
    fun δ x => RingEquiv_cast_completionMap (infStabInv δ).symm hv (hmem δ) x
  have hint : ∀ δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w},
      ∀ x : v.Completion,
      infF δ (algebraMap (v.Completion) (w.Completion) x)
        = algebraMap (v.Completion) (w.Completion) x := by
    intro δ x
    rw [show (algebraMap (v.Completion) (w.Completion))
        = NumberField.LiesOver.completionMap (v := v) (w := w) from by
      rw [RingHom.algebraMap_toAlgebra]]
    rw [show infF δ = (RingEquiv.cast (R := fun p => Place.localField L p)
        (infStabInv δ).symm).trans
        ((Place.localRingEquiv (δ.1⁻¹) (Place.ofInfinite w)).symm) from rfl]
    rw [RingEquiv.trans_apply, hcast2 δ x,
      ← localRingEquiv_completionMap (K := K) (L := L) (σ := δ.1⁻¹) (v := v) (w := w) x,
      RingEquiv.symm_apply_apply]
  haveI : Module.Finite (v.Completion) (w.Completion) :=
    finite_completionMap (K := K) (L := L) (v := v) (w := w)
  let F : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w} →
      (w.Completion ≃ₐ[v.Completion] w.Completion) := fun δ =>
    AlgEquiv.ofRingEquiv (f := infF δ) (hint δ)
  have hF_inj : Function.Injective F := by
    intro δ₁ δ₂ h
    have h3 : ∀ u : L, δ₁.1 u = δ₂.1 u := by
      intro u
      have h4 := congrFun (congrArg DFunLike.coe h)
        (algebraMap L (Place.localField L (Place.ofInfinite w)) u)
      rw [AlgEquiv.ofRingEquiv_apply, AlgEquiv.ofRingEquiv_apply] at h4
      have e1 : infF δ₁ (algebraMap L (Place.localField L (Place.ofInfinite w)) u)
          = algebraMap L (Place.localField L (Place.ofInfinite w)) (δ₁.1 u) := by
        rw [show infF δ₁ = (RingEquiv.cast (R := fun p => Place.localField L p)
            (infStabInv δ₁).symm).trans
            ((Place.localRingEquiv (δ₁.1⁻¹) (Place.ofInfinite w)).symm) from rfl]
        rw [RingEquiv.trans_apply, castRingEquiv_algebraMap (infStabInv δ₁).symm u,
          Galois.globalCFT_localRingEquiv_symm_algebraMap (δ₁.1) (Place.ofInfinite w) u]
      have e2 : infF δ₂ (algebraMap L (Place.localField L (Place.ofInfinite w)) u)
          = algebraMap L (Place.localField L (Place.ofInfinite w)) (δ₂.1 u) := by
        rw [show infF δ₂ = (RingEquiv.cast (R := fun p => Place.localField L p)
            (infStabInv δ₂).symm).trans
            ((Place.localRingEquiv (δ₂.1⁻¹) (Place.ofInfinite w)).symm) from rfl]
        rw [RingEquiv.trans_apply, castRingEquiv_algebraMap (infStabInv δ₂).symm u,
          Galois.globalCFT_localRingEquiv_symm_algebraMap (δ₂.1) (Place.ofInfinite w) u]
      rw [e1, e2] at h4
      exact injective_algebraMap_ofInfinite w h4
    exact Subtype.ext (AlgEquiv.ext h3)
  have hgal : Nat.card {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w}
      = Nat.card (w.Completion ≃ₐ[v.Completion] w.Completion)
    ∧ Nat.card (w.Completion ≃ₐ[v.Completion] w.Completion)
      = Module.finrank (v.Completion) (w.Completion) := by
    haveI : Finite (w.Completion ≃ₐ[v.Completion] w.Completion) := inferInstance
    haveI : Nonempty (w.Completion ≃ₐ[v.Completion] w.Completion) := ⟨AlgEquiv.refl⟩
    have hle : Nat.card (w.Completion ≃ₐ[v.Completion] w.Completion)
        ≤ Module.finrank (v.Completion) (w.Completion) :=
      Commons.FieldTheory.Galois.natCard_algEquiv_le_finrank
    have hge : Nat.card {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w}
        ≤ Nat.card (w.Completion ≃ₐ[v.Completion] w.Completion) :=
      Nat.card_le_card_of_injective F hF_inj
    have hpos : 0 < Nat.card (w.Completion ≃ₐ[v.Completion] w.Completion) := Nat.card_pos
    by_cases hu : InfinitePlace.IsUnramified K w
    · have h1 := natCard_infStab_of_isUnramified (K := K) (L := L) hu
      have h2 := finrank_le_one_of_isUnramified (K := K) (L := L) (v := v) (w := w) hu
      exact ⟨by rw [h1]; omega, by omega⟩
    · have h1 := natCard_infStab_of_not_isUnramified (K := K) (L := L) hu
      have h2 : Module.finrank (v.Completion) (w.Completion) = 2 :=
        finrank_completionMap (K := K) (L := L)
          (isReal_of_not_isUnramified (K := K) (L := L) (v := v) (w := w) hu)
          (isComplex_of_not_isUnramified (K := K) (L := L) (v := v) (w := w) hu)
      exact ⟨by rw [h1]; omega, by omega⟩
  haveI : IsGalois (v.Completion) (w.Completion) :=
    IsGalois.of_card_aut_eq_finrank (v.Completion) (w.Completion) hgal.2
  letI : Fintype (w.Completion ≃ₐ[v.Completion] w.Completion) :=
    AlgEquiv.fintype (v.Completion) (w.Completion)
  rw [Fintype.prod_bijective F
    (Function.Injective.bijective_of_nat_card_le hF_inj hgal.1.ge)
    (fun δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w} =>
      Units.map (infF δ).toMonoidHom (y (Place.ofInfinite w)))
    (fun g : w.Completion ≃ₐ[v.Completion] w.Completion =>
      Units.map g.toRingEquiv.toMonoidHom (y (Place.ofInfinite w)))
    (fun δ => rfl)]
  have hnorm : (∏ g : w.Completion ≃ₐ[v.Completion] w.Completion,
      Units.map g.toRingEquiv.toMonoidHom (y (Place.ofInfinite w)))
      = Units.map ((algebraMap (v.Completion) (w.Completion)).toMonoidHom)
        (Place.localNormInfinite w v (y (Place.ofInfinite w))) := by
    exact prod_units_map_algEquiv_eq_map_norm (F := v.Completion) (E := w.Completion)
      (y (Place.ofInfinite w))
  refine hnorm.trans ?_
  rw [show Place.localAlgebraMapUnits (Place.ofInfinite w) (Place.ofInfinite v)
        (Place.liesOver_ofInfinite hv)
      = Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom
      from localAlgebraMapUnits_ofInfinite hv]
  rfl

/-! ## The fibre identity at an archimedean place -/

/-- The archimedean analogue of `globalCFT_inner_prod_finite`. -/
theorem globalCFT_inner_prod_infinite (v : InfinitePlace K) (w w₀ : InfinitePlace L)
    [hw : w.LiesOver v] (h₀ : w₀.LiesOver v) (y : Idele L) :
    (∏ σ : {σ : L ≃ₐ[K] L // σ⁻¹ • w₀ = w}, (σ.1 • y) (Place.ofInfinite w₀))
      = Place.localAlgebraMapUnits (Place.ofInfinite w₀) (Place.ofInfinite v)
          (Place.liesOver_ofInfinite h₀)
          (Place.localNormInfinite w v (y (Place.ofInfinite w))) := by
  classical
  rw [show (∏ σ : {σ : L ≃ₐ[K] L // σ⁻¹ • w₀ = w}, (σ.1 • y) (Place.ofInfinite w₀))
      = ∏ σ : {σ : L ≃ₐ[K] L // σ⁻¹ • Place.ofInfinite w₀ = Place.ofInfinite w},
          (σ.1 • y) (Place.ofInfinite w₀) from
    Fintype.prod_equiv
      (Equiv.subtypeEquivRight
        (p := fun σ : L ≃ₐ[K] L => σ⁻¹ • w₀ = w)
        (q := fun σ : L ≃ₐ[K] L => σ⁻¹ • Place.ofInfinite w₀ = Place.ofInfinite w)
        (fun σ => ⟨fun hh => by
            show Place.ofInfinite (σ⁻¹ • w₀) = Place.ofInfinite w
            rw [hh],
          fun hh => Place.ofInfinite_inj.mp hh⟩))
      (fun σ : {σ : L ≃ₐ[K] L // σ⁻¹ • w₀ = w} => (σ.1 • y) (Place.ofInfinite w₀))
      (fun σ : {σ : L ≃ₐ[K] L // σ⁻¹ • Place.ofInfinite w₀ = Place.ofInfinite w} =>
        (σ.1 • y) (Place.ofInfinite w₀))
      (fun _ => rfl)]
  obtain ⟨σ₀, hσ₀c⟩ : ∃ σ : L ≃ₐ[K] L, σ • w = w₀ :=
    InfinitePlace.exists_smul_eq_of_comap_eq (by
      rw [NumberField.InfinitePlace.LiesOver.comap_eq w v,
        NumberField.InfinitePlace.LiesOver.comap_eq w₀ v])
  have hσ₀ : σ₀ • Place.ofInfinite w = Place.ofInfinite w₀ := congrArg Place.ofInfinite hσ₀c
  have hσ₀' : σ₀⁻¹ • Place.ofInfinite w₀ = Place.ofInfinite w := by
    have h := congrArg (fun q => σ₀⁻¹ • q) hσ₀
    rw [Galois.globalCFT_smul_place_smul, inv_mul_cancel,
      Galois.globalCFT_one_smul_place] at h
    exact h.symm
  have hw' : (σ₀⁻¹ • w₀).LiesOver v :=
    (Galois.globalCFT_infinitePlace_smul_liesOver σ₀⁻¹ w₀ v).mpr h₀
  have hc' : Place.ofInfinite w = σ₀⁻¹ • Place.ofInfinite w₀ := hσ₀'.symm
  · -- main body
    have hterm2 : ∀ δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w},
        ((σ₀ * δ.1) • y) (Place.ofInfinite w₀)
          = Units.map ((RingEquiv.cast (R := fun p => Place.localField L p) hc').trans
              ((Place.localRingEquiv σ₀⁻¹ (Place.ofInfinite w₀)).symm)).toMonoidHom
            ((δ.1 • y) (Place.ofInfinite w)) := by
      intro δ
      rw [Galois.globalCFT_mul_smul_idele, Idele.smul_apply]
      have hcast : (δ.1 • y) (σ₀⁻¹ • Place.ofInfinite w₀)
          = Units.map (RingEquiv.cast (R := fun p => Place.localField L p) hc').toMonoidHom
              ((δ.1 • y) (Place.ofInfinite w)) := by
        rw [units_cast_eq]
        exact (cast_dep_apply (δ.1 • y) hc').symm
      rw [hcast, Units_map_trans_apply']
    have hmu : ∀ a : (v.Completion)ˣ,
        Units.map ((RingEquiv.cast (R := fun p => Place.localField L p) hc').trans
            ((Place.localRingEquiv σ₀⁻¹ (Place.ofInfinite w₀)).symm)).toMonoidHom
            (Place.localAlgebraMapUnits (Place.ofInfinite w) (Place.ofInfinite v)
              (Place.liesOver_ofInfinite hw) a)
          = Place.localAlgebraMapUnits (Place.ofInfinite w₀) (Place.ofInfinite v)
              (Place.liesOver_ofInfinite h₀) a := by
      intro a
      rw [localAlgebraMapUnits_ofInfinite hw, Units_map_trans_apply']
      have hcast2 : Units.map (RingEquiv.cast (R := fun p => Place.localField L p) hc').toMonoidHom
            (Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom a)
          = Place.localAlgebraMapUnits (Place.ofInfinite (σ₀⁻¹ • w₀)) (Place.ofInfinite v)
              (Place.liesOver_ofInfinite hw') a := by
        rw [localAlgebraMapUnits_ofInfinite hw']
        apply Units.ext
        exact RingEquiv_cast_completionMap hc' hw hw' ↑a
      rw [hcast2]
      have heq : Units.map (Place.localRingEquiv σ₀⁻¹ (Place.ofInfinite w₀)).toMonoidHom
            (Place.localAlgebraMapUnits (Place.ofInfinite w₀) (Place.ofInfinite v)
              (Place.liesOver_ofInfinite h₀) a)
          = Place.localAlgebraMapUnits (Place.ofInfinite (σ₀⁻¹ • w₀)) (Place.ofInfinite v)
              (Place.liesOver_ofInfinite hw') a :=
        Galois.globalCFT_localRingEquiv_localAlgebraMapUnits (σ₀⁻¹)
          (Place.liesOver_ofInfinite h₀) (Place.liesOver_ofInfinite hw') a
      rw [← heq]
      ext
      simp
    have hmem : ∀ δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w},
        (σ₀ * δ.1)⁻¹ • Place.ofInfinite w₀ = Place.ofInfinite w := by
      intro δ
      rw [mul_inv_rev, ← Galois.globalCFT_smul_place_smul, hσ₀']
      exact infStabInv δ
    have hbij : Function.Bijective
        (fun δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w} =>
          (⟨σ₀ * δ.1, hmem δ⟩ : {σ : L ≃ₐ[K] L // σ⁻¹ • Place.ofInfinite w₀ = Place.ofInfinite w})) := by
      constructor
      · intro δ₁ δ₂ h
        exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
      · intro σ
        obtain ⟨σ1, hσ1⟩ := σ
        have h2 : σ1 • Place.ofInfinite w = Place.ofInfinite w₀ := by
          have h := congrArg (fun q => σ1 • q) hσ1
          rw [Galois.globalCFT_smul_place_smul, mul_inv_cancel,
            Galois.globalCFT_one_smul_place] at h
          exact h.symm
        refine ⟨⟨σ₀⁻¹ * σ1, ?_⟩, ?_⟩
        · rw [← Galois.globalCFT_smul_place_smul, h2, hσ₀']
        · apply Subtype.ext
          show σ₀ * (σ₀⁻¹ * σ1) = σ1
          group
    rw [← Fintype.prod_bijective
      (fun δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w} =>
        (⟨σ₀ * δ.1, hmem δ⟩ : {σ : L ≃ₐ[K] L // σ⁻¹ • Place.ofInfinite w₀ = Place.ofInfinite w}))
      hbij
      (fun δ : {δ : L ≃ₐ[K] L // δ • Place.ofInfinite w = Place.ofInfinite w} =>
        ((σ₀ * δ.1) • y) (Place.ofInfinite w₀))
      (fun σ : {σ : L ≃ₐ[K] L // σ⁻¹ • Place.ofInfinite w₀ = Place.ofInfinite w} =>
        (σ.1 • y) (Place.ofInfinite w₀))
      (fun δ => rfl)]
    rw [Finset.prod_congr rfl (fun δ _ => hterm2 δ)]
    rw [← map_prod]
    rw [localNormInfinite_stab_prod w v y]
    exact hmu (Place.localNormInfinite w v (y (Place.ofInfinite w)))

/-! ## The assembly -/

/-- The projection of a product of conjugates of an idèle to a place. -/
lemma prod_smul_apply (y : Idele L) (w : Place L) :
    (∏ σ : L ≃ₐ[K] L, σ • y) w = ∏ σ : L ≃ₐ[K] L, (σ • y) w := by
  show (Idele.eval w) (∏ σ : L ≃ₐ[K] L, σ • y) = _
  rw [map_prod]
  rfl

lemma prod_smul_decomp_infinite (v : InfinitePlace K) (w₀ : InfinitePlace L)
    (h₀ : w₀.LiesOver v) (y : Idele L) :
    (∏ σ : L ≃ₐ[K] L, (σ • y) (Place.ofInfinite w₀))
      = ∏ w' ∈ Place.fiberInfinite (K := K) (L := L) v,
          ∏ σ : {σ : L ≃ₐ[K] L // σ⁻¹ • w₀ = w'},
            (σ.1 • y) (Place.ofInfinite w₀) := by
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ)
    (t := Place.fiberInfinite (K := K) (L := L) v)
    (g := fun σ : L ≃ₐ[K] L => σ⁻¹ • w₀)
    (h := fun σ _ => (Place.mem_fiberInfinite (K := K) (L := L)).mpr
      ((Galois.globalCFT_infinitePlace_smul_liesOver σ⁻¹ w₀ v).mpr h₀))
    (f := fun σ => (σ • y) (Place.ofInfinite w₀))]
  refine Finset.prod_congr rfl (fun w' hw' => ?_)
  exact Finset.prod_subtype
    (Finset.univ.filter (fun σ : L ≃ₐ[K] L => σ⁻¹ • w₀ = w'))
    (fun x => by simp) _

/-- The product of the conjugates of an idèle at a nonarchimedean place, decomposed into the
fibres of the orbit. -/
lemma prod_smul_decomp_finite (Q : HeightOneSpectrum (𝓞 K)) (q₀ : HeightOneSpectrum (𝓞 L))
    (h₀ : q₀.asIdeal.LiesOver Q.asIdeal) (y : Idele L) :
    (∏ σ : L ≃ₐ[K] L, (σ • y) (Place.ofFinite q₀))
      = ∏ q' ∈ Place.primesOverFinite (K := K) (L := L) Q,
          ∏ σ : {σ : L ≃ₐ[K] L // Place.smulHeightOneSpectrum σ⁻¹ q₀ = q'},
            (σ.1 • y) (Place.ofFinite q₀) := by
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ)
    (t := Place.primesOverFinite (K := K) (L := L) Q)
    (g := fun σ : L ≃ₐ[K] L => Place.smulHeightOneSpectrum σ⁻¹ q₀)
    (h := fun σ _ => (Place.mem_primesOverFinite (K := K) (L := L)).mpr
      ((Galois.globalCFT_finitePlace_smul_liesOver σ⁻¹ q₀ Q).mpr h₀))
    (f := fun σ => (σ • y) (Place.ofFinite q₀))]
  refine Finset.prod_congr rfl (fun q' hq' => ?_)
  exact Finset.prod_subtype
    (Finset.univ.filter (fun σ : L ≃ₐ[K] L => Place.smulHeightOneSpectrum σ⁻¹ q₀ = q'))
    (fun x => by simp) _

/-- **The pointwise form of the main identity.**  For a place `v` of `K`, a place `w` of `L` above
it and an idèle `x` of `K`, the product of the conjugates of `y` at `w` is the image under the
local algebra map of `x v`. -/
theorem globalCFT_prod_smul_apply_eq (v : Place K) (w : Place L) (h : Place.LiesOver w v)
    (y : 𝕀[L]) :
    (∏ σ : L ≃ₐ[K] L, (σ • y) w)
      = Place.localAlgebraMapUnits w v h ((Idele.normIdeleHom K L y) v) := by
  classical
  cases w with
  | inl w₀ =>
    cases v with
    | inl v' =>
      have h' : w₀.LiesOver v' := (Galois.globalCFT_liesOver_ofInfinite_iff w₀ v').mp h
      rw [show Place.localAlgebraMapUnits (Place.ofInfinite w₀) (Place.ofInfinite v') h
          = Place.localAlgebraMapUnits (Place.ofInfinite w₀) (Place.ofInfinite v')
              (Place.liesOver_ofInfinite h') from
        congrArg (fun hh => Place.localAlgebraMapUnits (Place.ofInfinite w₀) (Place.ofInfinite v')
          hh) (Subsingleton.elim h (Place.liesOver_ofInfinite h'))]
      rw [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofInfinite, map_prod,
        prod_smul_decomp_infinite (K := K) (L := L) v' w₀ h' y]
      conv_lhs => rw [← Finset.prod_attach]
      refine Finset.prod_congr rfl (fun w' _ => ?_)
      exact globalCFT_inner_prod_infinite (v := v') (w := w'.1) (w₀ := w₀)
        (hw := (Place.mem_fiberInfinite (K := K) (L := L)).mp w'.2) (h₀ := h') y
    | inr Q =>
      rcases h with ⟨w', v'', h1, h2, _⟩ | ⟨q', Q', h1, h2, _⟩
      · exact absurd h2.symm (Place.ofInfinite_ne_ofFinite v'' Q)
      · exact absurd h1 (Place.ofInfinite_ne_ofFinite w₀ q')
  | inr q₀ =>
    cases v with
    | inl v' =>
      rcases h with ⟨w', v'', h1, h2, _⟩ | ⟨q', Q', h1, h2, _⟩
      · exact absurd h1.symm (Place.ofInfinite_ne_ofFinite w' q₀)
      · exact absurd h2 (Place.ofInfinite_ne_ofFinite v' Q')
    | inr Q =>
      have h' : q₀.asIdeal.LiesOver Q.asIdeal := (Galois.globalCFT_liesOver_ofFinite_iff q₀ Q).mp h
      rw [show Place.localAlgebraMapUnits (Place.ofFinite q₀) (Place.ofFinite Q) h
          = Place.localAlgebraMapUnits (Place.ofFinite q₀) (Place.ofFinite Q)
              (Place.liesOver_ofFinite h') from
        congrArg (fun hh => Place.localAlgebraMapUnits (Place.ofFinite q₀) (Place.ofFinite Q)
          hh) (Subsingleton.elim h (Place.liesOver_ofFinite h'))]
      rw [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofFinite, map_prod,
        prod_smul_decomp_finite (K := K) (L := L) Q q₀ h' y]
      conv_lhs => rw [← Finset.prod_attach]
      refine Finset.prod_congr rfl (fun q' _ => ?_)
      exact globalCFT_inner_prod_finite Q q'.1 q₀
        ((Place.mem_primesOverFinite (K := K) (L := L)).mp q'.2) h' y

theorem globalCFT_prod_smul_eq_inclusion_normIdeleHom {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w))) (y : 𝕀[L]) :
    (∏ σ : L ≃ₐ[K] L, σ • y) = φ (Idele.normIdeleHom K L y) := by
  refine Idele.ext fun w => ?_
  rw [prod_smul_apply]
  rw [hφ (Idele.normIdeleHom K L y) w]
  exact globalCFT_prod_smul_apply_eq (u w) w (hu w) y

end NK.GlobalCFT.Inclusion
