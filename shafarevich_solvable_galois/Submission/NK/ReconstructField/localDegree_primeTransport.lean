import Mathlib
import Submission.NK.Reconstruct.Transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local degree `e · f` is invariant under an isomorphism of number field extensions

Let `A₁ → B₁` and `A₂ → B₂` be extensions of number fields, and let `μ : B₁ ≃+* B₂` be a field
isomorphism which is compatible with a field isomorphism `μ₀ : A₁ ≃+* A₂` of the base fields,
`μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x)`.  Then `μ` induces a ring isomorphism
`𝓞 B₁ ≃+* 𝓞 B₂` of the rings of integers which is compatible, in turn, with the induced
isomorphism `𝓞 A₁ ≃+* 𝓞 A₂` of the rings of integers of the base fields.

Hence the whole arithmetic of the extension `B₁/A₁` transports to `B₂/A₂`: for a prime `P` of
`𝓞 B₁`, the corresponding prime `primeTransport μ P = μ(P)` of `𝓞 B₂` has the same ramification
index and the same inertia degree over the base field.  Consequently the *local degree*
`e(P) · f(P)` — the degree of the local extension at `P` — is preserved:

`P.ramificationIdx (𝓞 A₁) * P.inertiaDeg (𝓞 A₁)
   = (primeTransport μ P).ramificationIdx (𝓞 A₂) * (primeTransport μ P).inertiaDeg (𝓞 A₂)`.

The proof is a transport of the definitions:
* the ramification index is the multiplicity of `P` in the extension of the prime below it
  (`Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity`), and multiplicity is invariant under a
  ring equivalence of the ideal monoids (`multiplicity_map_eq`);
* the inertia degree is the degree of the residue field extension
  (`Ideal.inertiaDeg_eq_of_isMaximal`), and the residue field extension is transported by the
  induced isomorphism of quotients (`Ideal.quotientEquiv`), whence the degrees agree
  (`Algebra.finrank_eq_of_equiv_equiv`).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace NK.ReconstructField

section Abstract

variable {R₁ R₂ S₁ S₂ : Type*} [CommRing R₁] [CommRing R₂] [CommRing S₁] [CommRing S₂]

/-- **The prime below the image is the image of the prime below.**

Let `f₁ : R₁ →+* S₁`, `f₂ : R₂ →+* S₂` be two ring homomorphisms, let `φ : S₁ ≃+* S₂` and
`φ₀ : R₁ ≃+* R₂` be ring equivalences commuting with them, `φ (f₁ x) = f₂ (φ₀ x)`.  Then for every
ideal `q` of `S₁`, the contraction of the image `φ q` along `f₂` is the image under `φ₀` of the
contraction of `q` along `f₁`. -/
lemma comap_map_eq_map_comap (φ : S₁ ≃+* S₂) (φ₀ : R₁ ≃+* R₂) (f₁ : R₁ →+* S₁)
    (f₂ : R₂ →+* S₂) (hφ : ∀ x : R₁, φ (f₁ x) = f₂ (φ₀ x)) (q : Ideal S₁) :
    Ideal.comap f₂ (Ideal.map φ q) = Ideal.map φ₀ (Ideal.comap f₁ q) := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap, Ideal.mem_map_of_equiv φ] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Ideal.mem_map_of_equiv φ₀]
    refine ⟨φ₀.symm x, ?_, ?_⟩
    · rw [Ideal.mem_comap]
      have hxy : f₁ (φ₀.symm x) = y := by
        apply φ.injective
        rw [hφ, φ₀.apply_symm_apply]
        exact hyx.symm
      rw [hxy]
      exact hy
    · simp
  · intro x hx
    rw [Ideal.mem_map_of_equiv φ₀] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [Ideal.mem_comap, ← hφ z]
    exact Ideal.mem_map_of_mem φ (Ideal.mem_comap.mp hz)

/-- **The ring equivalence of ideal monoids induced by a ring equivalence.**

The map `Ideal.map e` is a bijection on ideals, hence a ring equivalence of the (multiplicative)
monoids of ideals.  It is used to transport multiplicities, hence ramification indices. -/
noncomputable def idealMapRingEquiv (e : R₁ ≃+* R₂) : Ideal R₁ ≃+* Ideal R₂ :=
  RingEquiv.ofBijective (Ideal.mapHom e) (by
    have hleft : ∀ K : Ideal R₁,
        Ideal.map (e.symm : R₂ →+* R₁) ((Ideal.mapHom e) K) = K := by
      intro K
      rw [Ideal.mapHom_apply]
      change Ideal.map (e.symm : R₂ →+* R₁) (Ideal.map (e : R₁ →+* R₂) K) = K
      rw [Ideal.map_map,
        show (e.symm : R₂ →+* R₁).comp (e : R₁ →+* R₂) = RingHom.id R₁ from
          RingHom.ext fun x => e.symm_apply_apply x,
        Ideal.map_id]
    have hright : ∀ K : Ideal R₂,
        Ideal.map (e : R₁ →+* R₂) ((Ideal.mapHom e.symm) K) = K := by
      intro K
      rw [Ideal.mapHom_apply]
      change Ideal.map (e : R₁ →+* R₂) (Ideal.map (e.symm : R₂ →+* R₁) K) = K
      rw [Ideal.map_map,
        show (e : R₁ →+* R₂).comp (e.symm : R₂ →+* R₁) = RingHom.id R₂ from
          RingHom.ext fun x => e.apply_symm_apply x,
        Ideal.map_id]
    refine ⟨fun I J h => ?_, fun J => ⟨Ideal.map (e.symm : R₂ →+* R₁) J, hright J⟩⟩
    have h2 := congrArg (fun K => Ideal.map (e.symm : R₂ →+* R₁) K) h
    rwa [hleft I, hleft J] at h2)

end Abstract

section NumberField

open NumberField

variable {A₁ A₂ B₁ B₂ : Type*} [Field A₁] [NumberField A₁]
    [Field A₂] [NumberField A₂] [Field B₁] [NumberField B₁] [Field B₂] [NumberField B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂]

/-- **Compatibility of the induced maps of rings of integers.**

If `μ : B₁ ≃+* B₂` carries the image of `A₁` into that of `A₂` through `μ₀ : A₁ ≃+* A₂`, then the
induced isomorphism `𝓞 B₁ ≃+* 𝓞 B₂` carries the image of `𝓞 A₁` into that of `𝓞 A₂` through the
induced isomorphism `𝓞 A₁ ≃+* 𝓞 A₂`. -/
lemma ringOfIntegersEquiv_algebraMap (μ : B₁ ≃+* B₂) (μ₀ : A₁ ≃+* A₂)
    (hμ : ∀ x : A₁, μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x))
    (x : NumberField.RingOfIntegers A₁) :
    NK.Reconstruct.ringOfIntegersEquiv μ
        (algebraMap (NumberField.RingOfIntegers A₁) (NumberField.RingOfIntegers B₁) x) =
      algebraMap (NumberField.RingOfIntegers A₂) (NumberField.RingOfIntegers B₂)
        (NK.Reconstruct.ringOfIntegersEquiv μ₀ x) := by
  apply NumberField.RingOfIntegers.ext
  simp only [NK.Reconstruct.ringOfIntegersEquiv_apply,
    show (algebraMap (NumberField.RingOfIntegers A₁) (NumberField.RingOfIntegers B₁))
      = NumberField.RingOfIntegers.mapRingHom (algebraMap A₁ B₁) from rfl,
    show (algebraMap (NumberField.RingOfIntegers A₂) (NumberField.RingOfIntegers B₂))
      = NumberField.RingOfIntegers.mapRingHom (algebraMap A₂ B₂) from rfl,
    NumberField.RingOfIntegers.mapRingHom_apply]
  exact hμ _

/-- **The prime below the transported prime is the transported prime below.** -/
lemma under_map_ringOfIntegersEquiv (μ : B₁ ≃+* B₂) (μ₀ : A₁ ≃+* A₂)
    (hμ : ∀ x : A₁, μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x))
    (q : Ideal (NumberField.RingOfIntegers B₁)) :
    (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
        (NumberField.RingOfIntegers A₂) =
      Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ₀)
        (q.under (NumberField.RingOfIntegers A₁)) := by
  exact comap_map_eq_map_comap _ _ _ _ (fun x => ringOfIntegersEquiv_algebraMap μ μ₀ hμ x) q

/-- **The ramification index is preserved by an isomorphism of the extensions.**

For `q` a nonzero prime of `𝓞 B₁`, the ramification index of the transported prime
`μ(q) = Ideal.map (ringOfIntegersEquiv μ) q` over `𝓞 A₂` equals that of `q` over `𝓞 A₁`. -/
lemma ramificationIdx_map_ringOfIntegersEquiv (μ : B₁ ≃+* B₂) (μ₀ : A₁ ≃+* A₂)
    (hμ : ∀ x : A₁, μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x))
    (q : Ideal (NumberField.RingOfIntegers B₁)) [q.IsPrime] (hq0 : q ≠ ⊥) :
    (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).ramificationIdx
        (NumberField.RingOfIntegers A₂) =
      q.ramificationIdx (NumberField.RingOfIntegers A₁) := by
  let φ : NumberField.RingOfIntegers B₁ →+* NumberField.RingOfIntegers B₂ :=
    NK.Reconstruct.ringOfIntegersEquiv μ
  let φ₀ : NumberField.RingOfIntegers A₁ →+* NumberField.RingOfIntegers A₂ :=
    NK.Reconstruct.ringOfIntegersEquiv μ₀
  let f₁ : NumberField.RingOfIntegers A₁ →+* NumberField.RingOfIntegers B₁ := algebraMap _ _
  let f₂ : NumberField.RingOfIntegers A₂ →+* NumberField.RingOfIntegers B₂ := algebraMap _ _
  change (Ideal.map φ q).ramificationIdx (NumberField.RingOfIntegers A₂) =
    q.ramificationIdx (NumberField.RingOfIntegers A₁)
  have hφ : ∀ x : NumberField.RingOfIntegers A₁, φ (f₁ x) = f₂ (φ₀ x) :=
    fun x => ringOfIntegersEquiv_algebraMap μ μ₀ hμ x
  have hcomp : f₂.comp φ₀ = φ.comp f₁ := RingHom.ext fun x => (hφ x).symm
  have hφinj : Function.Injective φ := (NK.Reconstruct.ringOfIntegersEquiv μ).injective
  have hunder : (Ideal.map φ q).under (NumberField.RingOfIntegers A₂) =
      Ideal.map φ₀ (q.under (NumberField.RingOfIntegers A₁)) :=
    under_map_ringOfIntegersEquiv μ μ₀ hμ q
  have hp0 : Ideal.map f₁ (q.under (NumberField.RingOfIntegers A₁)) ≠ ⊥ := by
    rw [Ideal.under_def]
    exact Ideal.map_ne_bot_of_ne_bot
      (Ideal.IsIntegral.comap_ne_bot (NumberField.RingOfIntegers A₁) hq0)
  have hq'0 : Ideal.map φ q ≠ ⊥ := fun h =>
    hq0 ((Ideal.map_eq_bot_iff_of_injective hφinj).mp h)
  haveI : (Ideal.map φ q).IsPrime :=
    Ideal.map_isPrime_of_equiv (NK.Reconstruct.ringOfIntegersEquiv μ)
  have hmap : Ideal.map f₂ ((Ideal.map φ q).under (NumberField.RingOfIntegers A₂)) =
      Ideal.map φ (Ideal.map f₁ (q.under (NumberField.RingOfIntegers A₁))) := by
    rw [hunder, Ideal.map_map, hcomp, ← Ideal.map_map]
  have hp0' : Ideal.map f₂ ((Ideal.map φ q).under (NumberField.RingOfIntegers A₂)) ≠ ⊥ :=
    fun h => hp0 ((Ideal.map_eq_bot_iff_of_injective hφinj).mp (hmap ▸ h))
  calc (Ideal.map φ q).ramificationIdx (NumberField.RingOfIntegers A₂)
      = multiplicity (Ideal.map φ q)
          (Ideal.map f₂ ((Ideal.map φ q).under (NumberField.RingOfIntegers A₂))) :=
        Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hp0'
    _ = multiplicity (Ideal.map φ q)
          (Ideal.map φ (Ideal.map f₁ (q.under (NumberField.RingOfIntegers A₁)))) := by
        rw [hmap]
    _ = multiplicity q (Ideal.map f₁ (q.under (NumberField.RingOfIntegers A₁))) :=
        multiplicity_map_eq (idealMapRingEquiv (NK.Reconstruct.ringOfIntegersEquiv μ))
    _ = q.ramificationIdx (NumberField.RingOfIntegers A₁) :=
        (Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hp0).symm

/-- **The inertia degree is preserved by an isomorphism of the extensions.**

For `q` a nonzero prime of `𝓞 B₁`, the inertia degree of the transported prime
`μ(q) = Ideal.map (ringOfIntegersEquiv μ) q` over `𝓞 A₂` equals that of `q` over `𝓞 A₁`. -/
lemma inertiaDeg_map_ringOfIntegersEquiv (μ : B₁ ≃+* B₂) (μ₀ : A₁ ≃+* A₂)
    (hμ : ∀ x : A₁, μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x))
    (q : Ideal (NumberField.RingOfIntegers B₁)) [hq : q.IsPrime] (hq0 : q ≠ ⊥) :
    (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).inertiaDeg
        (NumberField.RingOfIntegers A₂) =
      q.inertiaDeg (NumberField.RingOfIntegers A₁) := by
  have hunder : (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
        (NumberField.RingOfIntegers A₂) =
      Ideal.map (↑(NK.Reconstruct.ringOfIntegersEquiv μ₀) :
        NumberField.RingOfIntegers A₁ →+* NumberField.RingOfIntegers A₂)
        (q.under (NumberField.RingOfIntegers A₁)) :=
    under_map_ringOfIntegersEquiv μ μ₀ hμ q
  have hJ : Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q =
      Ideal.map (↑(NK.Reconstruct.ringOfIntegersEquiv μ) :
        NumberField.RingOfIntegers B₁ →+* NumberField.RingOfIntegers B₂) q := rfl
  have hφinj : Function.Injective (NK.Reconstruct.ringOfIntegersEquiv μ) :=
    (NK.Reconstruct.ringOfIntegersEquiv μ).injective
  have hφ₀inj : Function.Injective
      (↑(NK.Reconstruct.ringOfIntegersEquiv μ₀) :
        NumberField.RingOfIntegers A₁ →+* NumberField.RingOfIntegers A₂) := fun x y h =>
    (NK.Reconstruct.ringOfIntegersEquiv μ₀).injective h
  have hp0 : q.under (NumberField.RingOfIntegers A₁) ≠ ⊥ :=
    Ideal.under_ne_bot (NumberField.RingOfIntegers A₁) hq0
  have hq'0 : Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q ≠ ⊥ := fun h =>
    hq0 ((Ideal.map_eq_bot_iff_of_injective hφinj).mp h)
  have hp'0 : (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
      (NumberField.RingOfIntegers A₂) ≠ ⊥ := by
    rw [hunder]
    exact fun h => hp0 ((Ideal.map_eq_bot_iff_of_injective hφ₀inj).mp h)
  haveI hqM : q.IsMaximal := hq.isMaximal hq0
  haveI hpM : (q.under (NumberField.RingOfIntegers A₁)).IsMaximal :=
    (inferInstance : (q.under (NumberField.RingOfIntegers A₁)).IsPrime).isMaximal hp0
  haveI hq'M : (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).IsMaximal :=
    (Ideal.map_isPrime_of_equiv (NK.Reconstruct.ringOfIntegersEquiv μ)).isMaximal hq'0
  haveI hp'M : ((Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
      (NumberField.RingOfIntegers A₂)).IsMaximal :=
    (inferInstance : ((Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
      (NumberField.RingOfIntegers A₂)).IsPrime).isMaximal hp'0
  rw [Ideal.inertiaDeg_eq_of_isMaximal (q.under (NumberField.RingOfIntegers A₁)) q,
    Ideal.inertiaDeg_eq_of_isMaximal
      ((Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
        (NumberField.RingOfIntegers A₂))
      (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q)]
  refine (Algebra.finrank_eq_of_equiv_equiv
    (Ideal.quotientEquiv (q.under (NumberField.RingOfIntegers A₁))
      ((Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
        (NumberField.RingOfIntegers A₂))
      (NK.Reconstruct.ringOfIntegersEquiv μ₀) hunder)
    (Ideal.quotientEquiv q (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q)
      (NK.Reconstruct.ringOfIntegersEquiv μ) hJ) ?_).symm
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [Ideal.quotientEquiv_mk,
    Ideal.Quotient.algebraMap_mk_of_liesOver
      (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q)
      ((Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q).under
        (NumberField.RingOfIntegers A₂)),
    Ideal.Quotient.algebraMap_mk_of_liesOver q (q.under (NumberField.RingOfIntegers A₁)),
    Ideal.quotientEquiv_mk]
  exact congrArg (Ideal.Quotient.mk (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) q))
    (ringOfIntegersEquiv_algebraMap μ μ₀ hμ a).symm

/-- **The `asIdeal` of the transported prime.** -/
lemma primeTransport_asIdeal (μ : B₁ ≃+* B₂) (P : NK.Chebotarev.PrimeIdeal B₁) :
    (NK.Reconstruct.primeTransport μ P).asIdeal =
      Ideal.map (NK.Reconstruct.ringOfIntegersEquiv μ) P.asIdeal := rfl

/-- **The local degree `e · f` is invariant under an isomorphism of number field extensions.**

Let `A₁ → B₁` and `A₂ → B₂` be extensions of number fields and let `μ : B₁ ≃+* B₂` be a field
isomorphism compatible with an isomorphism `μ₀ : A₁ ≃+* A₂` of the base fields.  Then for every
prime `P` of `𝓞 B₁` the local degree `e(P) · f(P)` of `P` over `A₁` equals that of the
corresponding prime `μ(P)` of `𝓞 B₂` over `A₂`. -/
theorem localDegree_primeTransport {A₁ A₂ B₁ B₂ : Type*} [Field A₁] [NumberField A₁]
    [Field A₂] [NumberField A₂] [Field B₁] [NumberField B₁] [Field B₂] [NumberField B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂] (μ : B₁ ≃+* B₂) (μ₀ : A₁ ≃+* A₂)
    (hμ : ∀ x : A₁, μ (algebraMap A₁ B₁ x) = algebraMap A₂ B₂ (μ₀ x))
    (P : NK.Chebotarev.PrimeIdeal B₁) (𝔭 : NK.Chebotarev.PrimeIdeal A₁)
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) :
    P.asIdeal.ramificationIdx (NumberField.RingOfIntegers A₁) *
        P.asIdeal.inertiaDeg (NumberField.RingOfIntegers A₁) =
      (NK.Reconstruct.primeTransport μ P).asIdeal.ramificationIdx
          (NumberField.RingOfIntegers A₂) *
        (NK.Reconstruct.primeTransport μ P).asIdeal.inertiaDeg
          (NumberField.RingOfIntegers A₂) := by
  rw [primeTransport_asIdeal μ P,
    ramificationIdx_map_ringOfIntegersEquiv μ μ₀ hμ P.asIdeal P.ne_bot,
    inertiaDeg_map_ringOfIntegersEquiv μ μ₀ hμ P.asIdeal P.ne_bot]

end NumberField

end NK.ReconstructField
