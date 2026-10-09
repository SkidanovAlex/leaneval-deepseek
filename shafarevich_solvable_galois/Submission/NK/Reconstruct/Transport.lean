import Submission.NK.Reconstruct.Basic
import Submission.NeukirchUchida.Conjugation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transport of levels, primes of rings of integers, and Frobenius elements along a field
isomorphism

The reconstruction step compares the action of `ϕ` with the conjugation by a field isomorphism
`σ : K₂' ≃+* K₁'` on *finite levels*:

* `sigmaLevel σ hσ L₂` is the image `σ(L₂)` of a finite extension `L₂/K₂` inside `K₁'`, again an
  intermediate field of `K₁'/K₁` (finite, normal, Galois, and a number field when `L₂` is);
* `sigmaLevelEquiv σ hσ L₂ : ↥(sigmaLevel σ hσ L₂) ≃+* ↥L₂` is the restriction of `σ⁻¹`, whose
  underlying function is literally `σ.symm`;
* `primeTransport τ P` is the prime of `𝓞 L₂` corresponding to a prime `P` of `𝓞 L₁` under a ring
  isomorphism `τ : L₁ ≃+* L₂`;
* `conjRingEquiv τ hτ d` is the conjugate `τ d τ⁻¹` of an element of `Gal(L₁/K₁)`.

The API proved here is the raw material for
`NK.Reconstruct.isFrobAt_primeTransport_iff` (Frobenius elements are preserved by the
correspondence of primes) and for the endgame of the reconstruction.
-/

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-! ## The induced map on rings of integers -/

/-- **The ring homomorphism of rings of integers induced by an isomorphism of number fields.**
Algebraic integers are carried to algebraic integers. -/
noncomputable def ringOfIntegersHom {L₁ L₂ : Type*} [Field L₁] [Field L₂] (τ : L₁ ≃+* L₂) :
    NumberField.RingOfIntegers L₁ →+* NumberField.RingOfIntegers L₂ :=
  (((τ : L₁ →+* L₂).comp
      (algebraMap (NumberField.RingOfIntegers L₁) L₁))).codRestrict (integralClosure ℤ L₂)
    (fun x => (mem_integralClosure_iff ℤ L₂).mpr
      (IsIntegral.map (f := RingHom.toIntAlgHom (τ : L₁ →+* L₂))
        ((mem_integralClosure_iff ℤ L₁).mp x.2)))

@[simp] lemma ringOfIntegersHom_apply {L₁ L₂ : Type*} [Field L₁] [Field L₂] (τ : L₁ ≃+* L₂)
    (x : NumberField.RingOfIntegers L₁) :
    ((ringOfIntegersHom τ x : NumberField.RingOfIntegers L₂) : L₂) = τ x := rfl

lemma ringOfIntegersHom_injective {L₁ L₂ : Type*} [Field L₁] [Field L₂] (τ : L₁ ≃+* L₂) :
    Function.Injective (ringOfIntegersHom τ) := by
  intro x y h
  have h' : (τ x : L₂) = τ y := congrArg Subtype.val h
  exact Subtype.ext (τ.injective h')

lemma ringOfIntegersHom_surjective {L₁ L₂ : Type*} [Field L₁] [Field L₂] (τ : L₁ ≃+* L₂) :
    Function.Surjective (ringOfIntegersHom τ) := by
  intro y
  refine ⟨⟨τ.symm y, IsIntegral.map (f := RingHom.toIntAlgHom (τ.symm : L₂ →+* L₁))
    ((mem_integralClosure_iff ℤ L₂).mp y.2)⟩, ?_⟩
  apply Subtype.ext
  exact τ.apply_symm_apply y

/-- **The ring isomorphism of rings of integers induced by an isomorphism of number fields.** -/
noncomputable def ringOfIntegersEquiv {L₁ L₂ : Type*} [Field L₁] [Field L₂] (τ : L₁ ≃+* L₂) :
    NumberField.RingOfIntegers L₁ ≃+* NumberField.RingOfIntegers L₂ :=
  RingEquiv.ofBijective (ringOfIntegersHom τ)
    ⟨ringOfIntegersHom_injective τ, ringOfIntegersHom_surjective τ⟩

@[simp] lemma ringOfIntegersEquiv_apply {L₁ L₂ : Type*} [Field L₁] [Field L₂] (τ : L₁ ≃+* L₂)
    (x : NumberField.RingOfIntegers L₁) :
    ((ringOfIntegersEquiv τ x : NumberField.RingOfIntegers L₂) : L₂) = τ x := rfl

/-- **The prime of `𝓞 L₂` corresponding to a prime of `𝓞 L₁` under a ring isomorphism.** -/
noncomputable def primeTransport {L₁ L₂ : Type*} [Field L₁] [NumberField L₁] [Field L₂]
    [NumberField L₂] (τ : L₁ ≃+* L₂)
    (P : NK.Chebotarev.PrimeIdeal L₁) : NK.Chebotarev.PrimeIdeal L₂ :=
  ⟨Ideal.map (ringOfIntegersEquiv τ) P.asIdeal, Ideal.map_isPrime_of_equiv _,
    fun h => P.ne_bot ((Ideal.map_eq_bot_iff_of_injective (ringOfIntegersEquiv τ).injective).mp h)⟩

section Levels

variable (L₁ : IntermediateField K₁ K₁') (L₂ : IntermediateField K₂ K₂')

/-- **A ring isomorphism of finite levels is compatible with the base fields** if it carries the
embedded copy of `K₁` into the embedded copy of `K₂` and vice versa.  This is the level-wise shadow
of `Submission.NeukirchUchida.MapsBase`. -/
def MapsBaseLevel (τ : ↥L₁ ≃+* ↥L₂) : Prop :=
  (∀ a : K₁, ∃ c : K₂, τ (algebraMap K₁ ↥L₁ a) = algebraMap K₂ ↥L₂ c) ∧
    (∀ b : K₂, ∃ c : K₁, τ.symm (algebraMap K₂ ↥L₂ b) = algebraMap K₁ ↥L₁ c)

/-- The compatibility of the inverse. -/
theorem MapsBaseLevel.symm {τ : ↥L₁ ≃+* ↥L₂} (h : MapsBaseLevel L₁ L₂ τ) :
    MapsBaseLevel L₂ L₁ τ.symm := by
  refine ⟨h.2, fun a => ?_⟩
  obtain ⟨c, hc⟩ := h.1 a
  refine ⟨c, ?_⟩
  rw [RingEquiv.symm_symm]
  exact hc

end Levels

/-- **Conjugation by a ring isomorphism of number fields**, for `τ` compatible with an
identification of the two base fields. -/
def conjRingEquiv {L₁ L₂ : Type*} [Field L₁] [Field L₂] (τ : L₁ ≃+* L₂)
    (d : L₁ ≃+* L₁) : L₂ ≃+* L₂ where
  toFun y := τ (d (τ.symm y))
  invFun y := τ (d.symm (τ.symm y))
  left_inv y := by simp
  right_inv y := by simp
  map_mul' x y := by simp [map_mul]
  map_add' x y := by simp [map_add]

@[simp] lemma conjRingEquiv_apply {L₁ L₂ : Type*} [Field L₁] [Field L₂] (τ : L₁ ≃+* L₂)
    (d : L₁ ≃+* L₁) (x : L₂) : conjRingEquiv τ d x = τ (d (τ.symm x)) := rfl

section ConjAlg

variable {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}

/-- **The conjugate `τ d τ⁻¹` of a Galois automorphism of a level, as an automorphism of the
transported level.** -/
noncomputable def conjAlgEquiv (τ : ↥L₁ ≃+* ↥L₂) (h : MapsBaseLevel L₁ L₂ τ)
    (d : Gal(↥L₁/K₁)) : Gal(↥L₂/K₂) :=
  AlgEquiv.ofRingEquiv (f := conjRingEquiv τ d.toRingEquiv) (by
    intro b
    obtain ⟨c, hc⟩ := h.2 b
    have hfix : d.toRingEquiv (algebraMap K₁ ↥L₁ c) = algebraMap K₁ ↥L₁ c := d.commutes c
    show conjRingEquiv τ d.toRingEquiv (algebraMap K₂ ↥L₂ b) = algebraMap K₂ ↥L₂ b
    rw [conjRingEquiv_apply, show τ.symm (algebraMap K₂ ↥L₂ b) = algebraMap K₁ ↥L₁ c from hc,
      hfix, ← hc]
    simp)

@[simp] lemma conjAlgEquiv_apply (τ : ↥L₁ ≃+* ↥L₂) (h : MapsBaseLevel L₁ L₂ τ)
    (d : Gal(↥L₁/K₁)) (x : ↥L₂) :
    conjAlgEquiv τ h d x = τ (d (τ.symm x)) := rfl

end ConjAlg

/-! ## The image of an intermediate field under a field isomorphism -/

/-- **The image `σ(L)` of a finite extension `L / K₂` under `σ : K₂' ≃+* K₁'`**, presented as an
intermediate field of `K₁'/K₁`. -/
def sigmaLevel (σ : K₂' ≃+* K₁') (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁')
    (algebraMap K₂ K₂') σ) (L : IntermediateField K₂ K₂') : IntermediateField K₁ K₁' :=
  Subfield.toIntermediateField (L.toSubfield.comap (σ.symm : K₁' →+* K₂')) (fun a => by
    obtain ⟨b, hb⟩ := Submission.NeukirchUchida.mapsBase_mem_symm (algebraMap K₁ K₁')
      (algebraMap K₂ K₂') hσ (x := algebraMap K₁ K₁' a) ⟨a, rfl⟩
    show σ.symm (algebraMap K₁ K₁' a) ∈ L
    rw [← hb]
    exact L.algebraMap_mem b)

lemma mem_sigmaLevel {σ : K₂' ≃+* K₁'}
    {hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ}
    {L : IntermediateField K₂ K₂'} {x : K₁'} :
    x ∈ sigmaLevel σ hσ L ↔ σ.symm x ∈ L := Iff.rfl

/-- **The isomorphism `↥(σ L) ≃+* ↥L` given by `σ⁻¹`.** -/
def sigmaLevelEquiv (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₂ K₂') : ↥(sigmaLevel σ hσ L) ≃+* ↥L where
  toFun x := ⟨σ.symm (x : K₁'), x.2⟩
  invFun y := ⟨σ (y : K₂'), by
    rw [mem_sigmaLevel]
    simpa using y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma sigmaLevelEquiv_apply (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₂ K₂') (x : ↥(sigmaLevel σ hσ L)) :
    ((sigmaLevelEquiv σ hσ L x : ↥L) : K₂') = σ.symm (x : K₁') := rfl

end NK.Reconstruct

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **Conjugating back**: the conjugate by `τ⁻¹` of the conjugate by `τ` is the original
automorphism. -/
theorem conjAlgEquiv_conjAlgEquiv_symm {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'} (τ : ↥L₁ ≃+* ↥L₂) (h : MapsBaseLevel L₁ L₂ τ)
    (u : Gal(↥L₂/K₂)) :
    conjAlgEquiv τ h (conjAlgEquiv τ.symm h.symm u) = u := by
  ext x
  simp only [conjAlgEquiv_apply]
  simp

/-- **Input (b) of the reconstruction: the Frobenius correspondence.**

At every pair of finite levels `L₁/K₁`, `L₂/K₂` which are identified by the field isomorphism `σ`
(`τ` is the restriction of `σ⁻¹`, so that `(τ x : K₂') = σ.symm x`), the isomorphism `ϕ` of absolute
Galois groups matches the arithmetic Frobenius elements: if `g` is a Frobenius element at a prime
`P` of `𝓞 L₁` lying over a prime `p` of `K₁` unramified in `L₁`, then `ϕ g` is a Frobenius element
at the corresponding prime `τ P` of `𝓞 L₂`.

This is the finite-level form of Shimizu's Lemma 2.1.5 (the isomorphism commutes with the `ℓ`-adic
cyclotomic character, whence it maps `Frob_𝔭` to `Frob_{𝔭'}`), equivalently of Neukirch's local
correspondence CoNF (12.1.9) together with the reconstruction of XII §12.2. -/
def FrobeniusCorrespondence (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (σ : K₂' ≃+* K₁') : Prop :=
  ∀ (L₂ : IntermediateField K₂ K₂') [FiniteDimensional K₂ L₂] [Normal K₂ L₂] [NumberField ↥L₂]
    (L₁ : IntermediateField K₁ K₁') [FiniteDimensional K₁ L₁] [Normal K₁ L₁] [NumberField ↥L₁]
    (τ : ↥L₁ ≃+* ↥L₂), (∀ x : ↥L₁, (τ x : K₂') = σ.symm (x : K₁')) →
    ∀ (p : NK.Chebotarev.PrimeIdeal K₁) (P : NK.Chebotarev.PrimeIdeal ↥L₁),
      P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K₁) = 1 →
      ∀ g : Gal(K₁'/K₁),
        NK.Chebotarev.IsFrobAt P (AlgEquiv.restrictNormalHom L₁ g) →
          NK.Chebotarev.IsFrobAt (primeTransport τ P)
            (AlgEquiv.restrictNormalHom L₂ (ϕ g))

end NK.Reconstruct
