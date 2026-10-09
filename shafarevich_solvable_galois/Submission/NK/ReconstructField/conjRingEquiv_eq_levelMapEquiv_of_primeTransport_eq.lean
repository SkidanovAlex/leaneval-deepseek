import Mathlib
import Submission.NK.ReconstructField.LevelPrimeBijective
import Submission.NK.ReconstructField.levelPrimeMap_smul_of_lift
import Submission.NK.UchidaKummer.SplitPrimes
import Submission.NK.ReconstructField.eq_one_of_primeTransport_eq_self_of_splitCompletely
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

/-! ## Functoriality of the transport of primes along ring isomorphisms

The transport `NK.Reconstruct.primeTransport τ` of primes along a ring isomorphism `τ` is
functorial, and it agrees with the Galois action on primes when `τ` is a Galois automorphism. -/

/-- **The isomorphism of rings of integers induced by a composite is the composite.** -/
lemma ringOfIntegersEquiv_trans {A B C : Type*} [Field A] [Field B] [Field C]
    (e : A ≃+* B) (f : B ≃+* C) :
    NK.Reconstruct.ringOfIntegersEquiv (e.trans f) =
      (NK.Reconstruct.ringOfIntegersEquiv e).trans (NK.Reconstruct.ringOfIntegersEquiv f) := by
  apply RingEquiv.ext
  intro x
  apply Subtype.ext
  show ((NK.Reconstruct.ringOfIntegersEquiv (e.trans f) x : NumberField.RingOfIntegers C) : C) =
    ((NK.Reconstruct.ringOfIntegersEquiv f
      (NK.Reconstruct.ringOfIntegersEquiv e x) : NumberField.RingOfIntegers C) : C)
  rw [NK.Reconstruct.ringOfIntegersEquiv_apply, NK.Reconstruct.ringOfIntegersEquiv_apply,
    NK.Reconstruct.ringOfIntegersEquiv_apply]
  rfl

/-- **Functoriality of the transport of primes**: transporting a prime along a composite of ring
isomorphisms is transporting it successively. -/
lemma primeTransport_trans {A B C : Type*} [Field A] [NumberField A] [Field B] [NumberField B]
    [Field C] [NumberField C] (e : A ≃+* B) (f : B ≃+* C)
    (P : NK.Chebotarev.PrimeIdeal A) :
    NK.Reconstruct.primeTransport (e.trans f) P =
      NK.Reconstruct.primeTransport f (NK.Reconstruct.primeTransport e P) := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  show Ideal.map ((NK.Reconstruct.ringOfIntegersEquiv (e.trans f) :
      NumberField.RingOfIntegers A →+* NumberField.RingOfIntegers C)) P.asIdeal =
    Ideal.map ((NK.Reconstruct.ringOfIntegersEquiv f :
      NumberField.RingOfIntegers B →+* NumberField.RingOfIntegers C))
      (Ideal.map ((NK.Reconstruct.ringOfIntegersEquiv e :
        NumberField.RingOfIntegers A →+* NumberField.RingOfIntegers B)) P.asIdeal)
  rw [Ideal.map_map]
  congr 1

/-- **Transporting a prime along the identity is the identity.** -/
lemma primeTransport_refl {A : Type*} [Field A] [NumberField A]
    (P : NK.Chebotarev.PrimeIdeal A) :
    NK.Reconstruct.primeTransport (RingEquiv.refl A) P = P := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  show Ideal.map ((NK.Reconstruct.ringOfIntegersEquiv (RingEquiv.refl A) :
      NumberField.RingOfIntegers A →+* NumberField.RingOfIntegers A)) P.asIdeal = P.asIdeal
  have h1 : ((NK.Reconstruct.ringOfIntegersEquiv (RingEquiv.refl A) :
      NumberField.RingOfIntegers A →+* NumberField.RingOfIntegers A))
      = RingHom.id (NumberField.RingOfIntegers A) := by
    apply RingHom.ext
    intro x
    apply Subtype.ext
    show ((NK.Reconstruct.ringOfIntegersEquiv (RingEquiv.refl A) x :
      NumberField.RingOfIntegers A) : A) = ((x : NumberField.RingOfIntegers A) : A)
    rw [NK.Reconstruct.ringOfIntegersEquiv_apply]
    rfl
  rw [h1, Ideal.map_id]

/-- **The transport of a prime back and forth is the identity.** -/
lemma primeTransport_symm_apply {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] (e : A ≃+* B) (P : NK.Chebotarev.PrimeIdeal B) :
    NK.Reconstruct.primeTransport e (NK.Reconstruct.primeTransport e.symm P) = P := by
  have h := primeTransport_trans e.symm e P
  rw [show (e.symm.trans e) = RingEquiv.refl B from
    RingEquiv.ext (fun x => e.apply_symm_apply x)] at h
  rw [← h, primeTransport_refl]

/-- **The conjugate `τ d τ⁻¹` acting on primes is the transport along `d` transported by `τ`.** -/
lemma primeTransport_conjRingEquiv {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] (τ : A ≃+* B) (d : A ≃+* A) (P : NK.Chebotarev.PrimeIdeal B) :
    NK.Reconstruct.primeTransport (NK.Reconstruct.conjRingEquiv τ d) P =
      NK.Reconstruct.primeTransport τ (NK.Reconstruct.primeTransport d
        (NK.Reconstruct.primeTransport τ.symm P)) := by
  have hconj : NK.Reconstruct.conjRingEquiv τ d = (τ.symm.trans d).trans τ := by
    ext x
    rfl
  rw [hconj, primeTransport_trans, primeTransport_trans]

/-- **The isomorphism of rings of integers induced by a Galois automorphism is its restriction**
`galRestrict` to the rings of integers. -/
lemma ringOfIntegersEquiv_eq_galRestrict {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (σ : Gal(L/K)) :
    (NK.Reconstruct.ringOfIntegersEquiv σ.toRingEquiv :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) =
      (galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  show ((NK.Reconstruct.ringOfIntegersEquiv σ.toRingEquiv x :
      NumberField.RingOfIntegers L) : L) =
    ((galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ x :
      NumberField.RingOfIntegers L) : L)
  rw [NK.Reconstruct.ringOfIntegersEquiv_apply]
  exact (algebraMap_galRestrict_apply (NumberField.RingOfIntegers K) σ x).symm

/-- **The transport of primes along a Galois automorphism is the Galois action on primes.** -/
lemma primeTransport_eq_smul {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (σ : Gal(L/K))
    (P : NK.Chebotarev.PrimeIdeal L) :
    NK.Reconstruct.primeTransport σ.toRingEquiv P = σ • P := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NK.Chebotarev.smul_primeIdeal_asIdeal]
  show Ideal.map ((NK.Reconstruct.ringOfIntegersEquiv σ.toRingEquiv :
      NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L)) P.asIdeal =
    Ideal.map ((galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ :
      NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L)) P.asIdeal
  rw [ringOfIntegersEquiv_eq_galRestrict]

/-! ## The isomorphism of Galois groups of corresponding levels is restriction -/

/-- **`levelMapEquiv` on a restricted Galois element is the restriction of `ϕ`**: for a level `L`
and `g : Gal(K₁'/K₁)`, the element of `Gal(↥(levelMap ϕ L)/K₂)` attached to the restriction of `g`
to `L` is the restriction of `ϕ g` to `levelMap ϕ L`. -/
lemma levelMapEquiv_restrictNormalHom {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (g : Gal(K₁'/K₁)) :
    NK.Reconstruct.levelMapEquiv hϕ L (AlgEquiv.restrictNormalHom L g) =
      AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g) := by
  have h1 : (AlgEquiv.restrictNormalHom L) g =
      (NK.Reconstruct.quotientEquivOfLevel L) (QuotientGroup.mk g) := rfl
  rw [NK.Reconstruct.levelMapEquiv, MulEquiv.trans_apply, h1, MulEquiv.symm_apply_apply,
    MulEquiv.trans_apply, QuotientGroup.congr_mk]
  rfl

/-! ## The pinning of the level isomorphism by the prime correspondence -/

/-- **A level isomorphism matching the prime correspondence of `ϕ` at a completely split rational
prime is the correspondence of `ϕ` on the Galois groups.**

Let `M/K₁` be a finite normal level, `levelMap ϕ M` its image under the correspondence of `ϕ`, and
`τ : ↥M ≃+* ↥(levelMap ϕ M)` an isomorphism of the two levels whose induced map on primes is the
correspondence `levelPrimeMap ϕ hϕ a M` of `ϕ`.  If `p` is a rational prime splitting completely in
`levelMap ϕ M`, then conjugating the Galois group of `M/K₁` by `τ` gives exactly the isomorphism
`levelMapEquiv hϕ M` of Galois groups of corresponding levels. -/
theorem conjRingEquiv_eq_levelMapEquiv_of_primeTransport_eq {K₁ K₂ K₁' K₂' : Type*} [Field K₁]
    [Field K₂] [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁']
    [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (M : IntermediateField K₁ K₁') [FiniteDimensional K₁ M] [Normal K₁ M] [NumberField ↥M]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ M)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ M)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ M)]
    [IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ M)]
    (τ : ↥M ≃+* ↥(NK.Reconstruct.levelMap ϕ M))
    (hcorr : NK.Reconstruct.primeTransport τ =
      NK.ReconstructField.levelPrimeMap ϕ hϕ a M)
    (p : NK.Chebotarev.PrimeIdeal ℚ)
    (hsplit : ∀ Q : NK.Chebotarev.PrimeIdeal ↥(NK.Reconstruct.levelMap ϕ M),
      Q.asIdeal.LiesOver p.asIdeal →
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1 ∧
          Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) = 1) :
    ∀ g : Gal(↥M/K₁),
      NK.Reconstruct.conjRingEquiv τ g.toRingEquiv =
        (NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv := by
  classical
  let L : IntermediateField K₂ K₂' := NK.Reconstruct.levelMap ϕ M
  haveI hMgal : IsGalois K₁ ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hLgal : IsGalois K₂ ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- a rational prime of `𝓞 (levelMap ϕ M)` above `p`
  obtain ⟨P₀⟩ :=
    (inferInstance : Nonempty (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)))
  set Q : NK.Chebotarev.PrimeIdeal ↥L :=
    ⟨P₀.1, P₀.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot P₀.2⟩ with hQdef
  have hQlies : Q.asIdeal.LiesOver p.asIdeal := P₀.2.2
  intro g
  -- a lift of `g` to the absolute Galois group
  obtain ⟨g', hg'⟩ := AlgEquiv.restrictNormalHom_surjective (F := K₁) (K₁ := ↥M) (E := K₁') g
  -- the two automorphisms of the level act in the same way on every prime
  have huv : ∀ Q' : NK.Chebotarev.PrimeIdeal ↥L,
      NK.Reconstruct.primeTransport (NK.Reconstruct.conjRingEquiv τ g.toRingEquiv) Q' =
        NK.Reconstruct.primeTransport
          ((NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv) Q' := by
    intro Q'
    set 𝔭 : NK.Chebotarev.PrimeIdeal ↥M := NK.Reconstruct.primeTransport τ.symm Q' with h𝔭
    have h𝔭spec : NK.Reconstruct.primeTransport τ 𝔭 = Q' := by
      rw [h𝔭]
      exact primeTransport_symm_apply τ Q'
    -- the correspondence of primes is the correspondence of `ϕ`
    have h𝔭lev : NK.ReconstructField.levelPrimeMap ϕ hϕ a M 𝔭 = Q' := by
      rw [← hcorr, h𝔭spec]
    -- the action of the conjugate of `g` by `τ`
    have hu : NK.Reconstruct.primeTransport (NK.Reconstruct.conjRingEquiv τ g.toRingEquiv) Q'
        = NK.Reconstruct.primeTransport τ (g • 𝔭) := by
      rw [primeTransport_conjRingEquiv, ← h𝔭]
      rw [primeTransport_eq_smul]
    -- the action of the Galois correspondence `levelMapEquiv`
    have hv : NK.Reconstruct.primeTransport
        ((NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv) Q' =
        (NK.Reconstruct.levelMapEquiv hϕ M g) • Q' :=
      primeTransport_eq_smul (NK.Reconstruct.levelMapEquiv hϕ M g) Q'
    -- `levelMapEquiv` is the restriction of `ϕ`
    have hlm : NK.Reconstruct.levelMapEquiv hϕ M g =
        AlgEquiv.restrictNormalHom ↥L (ϕ g') := by
      rw [← hg']
      exact levelMapEquiv_restrictNormalHom ϕ hϕ M g'
    -- the Galois equivariance of the prime correspondence
    have hsmul : (AlgEquiv.restrictNormalHom ↥L) (ϕ g') • Q' =
        NK.ReconstructField.levelPrimeMap ϕ hϕ a M (g • 𝔭) := by
      rw [← h𝔭lev, ← hg']
      exact (levelPrimeMap_smul_of_lift ϕ hϕ a M g' 𝔭).symm
    rw [hu, hv, hlm, hsmul, ← hcorr]
  -- the conjugate of `v` by `u` fixes the prime `Q`
  have hfix : NK.Reconstruct.primeTransport
      (NK.Reconstruct.conjRingEquiv τ g.toRingEquiv *
        (NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv.symm) Q = Q := by
    have h1 : NK.Reconstruct.conjRingEquiv τ g.toRingEquiv *
        (NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv.symm =
        ((NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv.symm.trans
          (NK.Reconstruct.conjRingEquiv τ g.toRingEquiv)) := rfl
    rw [h1, primeTransport_trans, huv, primeTransport_symm_apply]
  -- and is therefore trivial
  have hw : NK.Reconstruct.conjRingEquiv τ g.toRingEquiv *
      (NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv.symm = 1 :=
    eq_one_of_primeTransport_eq_self_of_splitCompletely _ Q
      (hsplit Q hQlies).1 (hsplit Q hQlies).2 hfix
  have hone : NK.Reconstruct.conjRingEquiv τ g.toRingEquiv =
      (NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv := by
    have h' := mul_eq_one_iff_eq_inv.mp hw
    rw [show (NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv.symm =
      ((NK.Reconstruct.levelMapEquiv hϕ M g).toRingEquiv)⁻¹ from rfl, inv_inv] at h'
    exact h'
  exact hone

end NK.ReconstructField
