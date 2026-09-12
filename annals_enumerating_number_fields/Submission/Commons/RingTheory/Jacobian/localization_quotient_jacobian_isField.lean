import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

namespace Commons.RingTheory.Jacobian

open MvPolynomial

variable {k : Type*} [Field k] {r : ℕ}

/-- The quotient ring `k[x₁,…,xᵣ]/(E₁,…,Eᵣ)`. -/
abbrev jacQuot (E : Fin r → MvPolynomial (Fin r) k) :=
  MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range E)

/-- The naive pre-submersive presentation of the quotient ring. -/
noncomputable def jacPres (E : Fin r → MvPolynomial (Fin r) k) :
    Algebra.PreSubmersivePresentation k (jacQuot E) (Fin r) (Fin r) :=
  Algebra.PreSubmersivePresentation.naive (v := E) id Function.injective_id

lemma jacPres_jacobiMatrix {E : Fin r → MvPolynomial (Fin r) k} :
    (jacPres E).jacobiMatrix =
      (Matrix.of (fun i j => MvPolynomial.pderiv j (E i))).transpose := by
  funext i j
  rw [Matrix.transpose_apply, Matrix.of_apply]
  simp only [jacPres, Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
  rfl

/-- The class of `det (∂Eᵢ/∂xⱼ)` in the quotient ring, equal to the Jacobian of `jacPres`. -/
lemma jacPres_jacobian_eq_det {E : Fin r → MvPolynomial (Fin r) k} :
    (jacPres E).jacobian =
      Ideal.Quotient.mk _ (Matrix.det (fun i j => MvPolynomial.pderiv j (E i))) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, jacPres_jacobiMatrix,
    Matrix.det_transpose]
  rfl

/-- The determinant `det (∂Eᵢ/∂xⱼ)` viewed in the quotient ring. -/
noncomputable def jacDet (E : Fin r → MvPolynomial (Fin r) k) : jacQuot E :=
  (jacPres E).jacobian

/-- The quotient ring localised away from the Jacobian determinant. -/
noncomputable abbrev jacAway (E : Fin r → MvPolynomial (Fin r) k) :=
  Localization.Away (jacDet E)

noncomputable def jacQ0 (E : Fin r → MvPolynomial (Fin r) k) :
    Algebra.SubmersivePresentation (jacQuot E) (jacAway E) Unit Unit :=
  Algebra.SubmersivePresentation.localizationAway (S := jacAway E) (jacDet E)

noncomputable def jacQp (E : Fin r → MvPolynomial (Fin r) k) :
    Algebra.PreSubmersivePresentation k (jacAway E) (Unit ⊕ Fin r) (Unit ⊕ Fin r) :=
  (jacQ0 E).toPreSubmersivePresentation.comp (jacPres E)

lemma jacQp_jacobian_isUnit {E : Fin r → MvPolynomial (Fin r) k} :
    IsUnit (jacQp E).jacobian := by
  change IsUnit ((jacQ0 E).toPreSubmersivePresentation.comp (jacPres E)).jacobian
  rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian]
  have h : Algebra.PreSubmersivePresentation.jacobian (jacQ0 E).toPreSubmersivePresentation
      = algebraMap _ (jacAway E) (jacDet E) :=
    Algebra.PreSubmersivePresentation.localizationAway_jacobian (S := jacAway E) (jacDet E)
  rw [h]
  have h2 : (jacPres E).jacobian = jacDet E := rfl
  rw [h2, Algebra.smul_def]
  exact IsUnit.mul (IsLocalization.Away.algebraMap_isUnit (S := jacAway E) (jacDet E))
    (IsLocalization.Away.algebraMap_isUnit (S := jacAway E) (jacDet E))

noncomputable def jacQS (E : Fin r → MvPolynomial (Fin r) k) :
    Algebra.SubmersivePresentation k (jacAway E) (Unit ⊕ Fin r) (Unit ⊕ Fin r) where
  toPreSubmersivePresentation := jacQp E
  jacobian_isUnit := jacQp_jacobian_isUnit

lemma jacQp_dim (E : Fin r → MvPolynomial (Fin r) k) : (jacQp E).dimension = 0 := by
  change ((jacQ0 E).toPreSubmersivePresentation.comp (jacPres E)).dimension = 0
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  have h1 : (jacQ0 E).toPreSubmersivePresentation.dimension = 0 :=
    Algebra.Presentation.localizationAway_dimension_zero (S := jacAway E) (jacDet E)
  have h2 : (jacPres E).dimension = 0 := by
    rw [Algebra.Presentation.dimension]
    simp [Nat.card_eq_fintype_card]
  rw [h1, h2]

lemma jacAway_etale (E : Fin r → MvPolynomial (Fin r) k) : Algebra.Etale k (jacAway E) :=
  (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero).mpr
    (Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension (jacQS E) (jacQp_dim E))

theorem localization_quotient_jacobian_isField
    {k : Type*} [Field k] {r : ℕ} (E : Fin r → MvPolynomial (Fin r) k)
    (K : Type*) [Field K]
    (ψ : (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range E)) →+* K)
    (hsurj : Function.Surjective ψ)
    (hunit : IsUnit (ψ (Ideal.Quotient.mk _ (Matrix.det (fun i j => MvPolynomial.pderiv j (E i)))))) :
    Nonempty (@Localization.AtPrime _ _ (RingHom.ker ψ) (RingHom.ker_isPrime ψ) ≃+* K) := by
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  haveI : Algebra.FormallyEtale k (jacAway E) := (jacAway_etale E).formallyEtale
  have hJ : IsUnit (ψ (jacDet E)) := by rw [jacDet, jacPres_jacobian_eq_det]; exact hunit
  have hJmem : jacDet E ∉ RingHom.ker ψ := fun h => (IsUnit.ne_zero hJ) (RingHom.mem_ker.mp h)
  have hmem : jacDet E ∈ (RingHom.ker ψ).primeCompl := by
    simpa [Ideal.primeCompl] using hJmem
  have hJunit : IsUnit (algebraMap (jacQuot E) (Localization.AtPrime (RingHom.ker ψ)) (jacDet E)) :=
    IsLocalization.map_units (Localization.AtPrime (RingHom.ker ψ)) ⟨jacDet E, hmem⟩
  let f : jacAway E →ₐ[jacQuot E] Localization.AtPrime (RingHom.ker ψ) :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (jacDet E)) (f := Algebra.ofId (jacQuot E) _) (by
      rintro ⟨y, hy⟩
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff y (jacDet E)).mp hy
      simpa only [Algebra.ofId_apply, map_pow] using hJunit.pow n)
  algebraize [f.toRingHom]
  have hloc : IsLocalization
      (((RingHom.ker ψ).primeCompl).map (algebraMap (jacQuot E) (jacAway E)))
      (Localization.AtPrime (RingHom.ker ψ)) :=
    IsLocalization.isLocalization_of_submonoid_le (jacAway E) _ (Submonoid.powers (jacDet E))
      (RingHom.ker ψ).primeCompl (Submonoid.powers_le.mpr hmem)
  haveI hST1 : IsScalarTower (jacQuot E) (jacAway E) (Localization.AtPrime (RingHom.ker ψ)) :=
    IsScalarTower.of_algebraMap_eq (R := jacQuot E) (S := jacAway E)
      (A := Localization.AtPrime (RingHom.ker ψ)) (fun x => (f.commutes x).symm)
  haveI : Algebra.FormallyEtale (jacAway E) (Localization.AtPrime (RingHom.ker ψ)) :=
    Algebra.FormallyEtale.of_isLocalization
      (((RingHom.ker ψ).primeCompl).map (algebraMap (jacQuot E) (jacAway E)))
  haveI : IsScalarTower k (jacAway E) (Localization.AtPrime (RingHom.ker ψ)) :=
    IsScalarTower.to₁₃₄ (M := k) (N := jacQuot E) (P := jacAway E)
      (Q := Localization.AtPrime (RingHom.ker ψ))
  have hfe : Algebra.FormallyEtale k (Localization.AtPrime (RingHom.ker ψ)) :=
    Algebra.FormallyEtale.comp k (jacAway E) (Localization.AtPrime (RingHom.ker ψ))
  haveI : Algebra.FormallyEtale k (Localization.AtPrime (RingHom.ker ψ)) := hfe
  have hfu : Algebra.FormallyUnramified k (Localization.AtPrime (RingHom.ker ψ)) := inferInstance
  haveI hEss : Algebra.EssFiniteType k (Localization.AtPrime (RingHom.ker ψ)) :=
    Algebra.EssFiniteType.comp k (jacQuot E) (Localization.AtPrime (RingHom.ker ψ))
  have hred : IsReduced (Localization.AtPrime (RingHom.ker ψ)) :=
    Algebra.FormallyUnramified.isReduced_of_field k (Localization.AtPrime (RingHom.ker ψ))
  haveI : Module.Free k (Localization.AtPrime (RingHom.ker ψ)) := Module.Free.of_divisionRing k (Localization.AtPrime (RingHom.ker ψ))
  have hfin : Module.Finite k (Localization.AtPrime (RingHom.ker ψ)) :=
    Algebra.FormallyUnramified.finite_of_free k (Localization.AtPrime (RingHom.ker ψ))
  haveI : Module.Finite k (Localization.AtPrime (RingHom.ker ψ)) := hfin
  have hArt : IsArtinianRing (Localization.AtPrime (RingHom.ker ψ)) :=
    IsArtinianRing.of_finite k (Localization.AtPrime (RingHom.ker ψ))
  haveI : IsNoetherianRing (Localization.AtPrime (RingHom.ker ψ)) :=
    IsNoetherianRing.of_finite k (Localization.AtPrime (RingHom.ker ψ))
  have hKrull : Ring.KrullDimLE 0 (Localization.AtPrime (RingHom.ker ψ)) :=
    (isArtinianRing_iff_krullDimLE_zero (R := Localization.AtPrime (RingHom.ker ψ))).mp hArt
  have hnil : nilradical (Localization.AtPrime (RingHom.ker ψ)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_nilradical] at hx
    exact (isReduced_iff _).mp hred x hx
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker ψ)) = ⊥ := by
    rw [← Ring.KrullDimLE.nilradical_eq_maximalIdeal]; exact hnil
  have hfield : IsField (Localization.AtPrime (RingHom.ker ψ)) :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmax
  -- construct the surjection `At →+* K`
  have hunitK : ∀ y : (RingHom.ker ψ).primeCompl, IsUnit (ψ y) := by
    rintro ⟨y, hy⟩
    rw [isUnit_iff_ne_zero]
    exact fun h => hy (RingHom.mem_ker.mpr h)
  let Φ : Localization.AtPrime (RingHom.ker ψ) →+* K :=
    IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (g := ψ) hunitK
  have hΦ : Φ.comp (algebraMap (jacQuot E) (Localization.AtPrime (RingHom.ker ψ))) = ψ :=
    IsLocalization.lift_comp hunitK
  have hsurjΦ : Function.Surjective Φ := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨algebraMap (jacQuot E) (Localization.AtPrime (RingHom.ker ψ)) y,
      RingHom.congr_fun hΦ y⟩
  have hker : RingHom.ker Φ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [RingHom.mem_ker] at hx
    by_contra hx0
    have hxne : x ≠ 0 := fun h => hx0 (by rw [h]; exact Submodule.zero_mem _)
    obtain ⟨u, hxu⟩ := hfield.mul_inv_cancel hxne
    have h10 : (1 : K) = 0 := by
      calc (1 : K) = Φ 1 := (map_one Φ).symm
        _ = Φ (x * ↑u) := by rw [hxu]
        _ = Φ x * Φ ↑u := map_mul Φ x ↑u
        _ = 0 := by rw [hx, zero_mul]
    exact one_ne_zero h10
  have hinjΦ : Function.Injective Φ := by
    rw [RingHom.injective_iff_ker_eq_bot]; exact hker
  exact ⟨RingEquiv.ofBijective Φ ⟨hinjΦ, hsurjΦ⟩⟩

end Commons.RingTheory.Jacobian