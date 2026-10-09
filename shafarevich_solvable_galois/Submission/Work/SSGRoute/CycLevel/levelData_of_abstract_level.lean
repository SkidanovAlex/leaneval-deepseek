import Mathlib
import Submission.Work.SSGRoute.CycLevel.LevelData
import Submission.Work.SSGRoute.CycLevel.GrunwaldImports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Packaging an abstract cyclic level into `LevelData`

An abstract field `L` with `k ⊆ L` finite, Galois, cyclic of `q`-power order divisible by `q`,
in which every place above `v₀` has full local degree (the stabiliser in `Gal(L/k)` of every place
of `L` above `v₀` is the whole group), produces a `LevelData k q 1 v₀`, i.e. a subfield
`M ⊆ AlgebraicClosure k` with the same properties.

The construction embeds `L` into `AlgebraicClosure k` (finite extensions of a number field embed
into an algebraic closure), takes `M` to be the image, and transports the Galois group, the
cardinality, cyclicity, and the place/Galois-action compatibility (`LiesOver` and stabilisers)
along the induced `k`-algebra isomorphism `L ≃ₐ[k] M`.

The transport of the place data is isolated in the auxiliary lemmas below: the nonzero primes of
`𝓞 M` are transported along the induced isomorphism `𝓞 M ≃ₐ[𝓞 k] 𝓞 L` of rings of integers, and
this transport is compatible with the conjugation action of the Galois groups
(`AlgEquiv.autCongr`).  The `LevelData` fields themselves are then read off from
`IsGalois.of_algEquiv`, `AlgEquiv.autCongr` and `isCyclic_of_surjective`.
-/

open scoped NumberField

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.CycLevel

open NK.GlobalCFT

/-! ## Auxiliary lemmas: transport of places along a `k`-algebra isomorphism -/

/-- For `x : 𝓞 M`, the element of `L` attached to the image of `x` under the ring-of-integers
transport along `e : M ≃ₐ[k] L` is `e x`. -/
private lemma coe_mapAlgEquiv_ringOfIntegers {k M L : Type*} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra k L] (e : M ≃ₐ[k] L) (x : NumberField.RingOfIntegers M) :
    (((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv :
        NumberField.RingOfIntegers M →+* NumberField.RingOfIntegers L) x : L) = e (x : M) := by
  change (NumberField.RingOfIntegers.mapRingHom (e : M →+* L) x : L) = e (x : M)
  rw [NumberField.RingOfIntegers.mapRingHom_apply]
  rfl

/-- The conjugation formula: `AlgEquiv.autCongr e σ` sends `e x` to `e (σ x)`. -/
private lemma autCongr_apply_el {k M L : Type*} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra k L] (e : M ≃ₐ[k] L) (σ : M ≃ₐ[k] M) (x : M) :
    (AlgEquiv.autCongr e σ) (e x) = e (σ x) := by
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

/-- Naturality of the transport to rings of integers: transporting along `e` intertwines the
action of `σ` on `𝓞 M` with the action of the conjugate `AlgEquiv.autCongr e σ` on `𝓞 L`. -/
private lemma ringOfIntegers_maps_commute {k M L : Type*} [Field k] [NumberField k] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra k M] [Algebra k L]
    (e : M ≃ₐ[k] L) (σ : M ≃ₐ[k] M) (x : NumberField.RingOfIntegers M) :
    (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv
        ((Place.ringOfIntegersEquiv σ : NumberField.RingOfIntegers M →+*
          NumberField.RingOfIntegers M) x)
      = (Place.ringOfIntegersEquiv (AlgEquiv.autCongr e σ) :
          NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L)
        ((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv x) := by
  apply NumberField.RingOfIntegers.ext
  have h₁ : (((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv
        ((Place.ringOfIntegersEquiv σ : NumberField.RingOfIntegers M →+*
          NumberField.RingOfIntegers M) x) : NumberField.RingOfIntegers L) : L)
      = e (σ (x : M)) :=
    (coe_mapAlgEquiv_ringOfIntegers e _).trans
      (congrArg e (coe_mapAlgEquiv_ringOfIntegers σ x))
  have h₂ : (((Place.ringOfIntegersEquiv (AlgEquiv.autCongr e σ) :
          NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L)
        ((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv x) :
          NumberField.RingOfIntegers L) : L) = e (σ (x : M)) :=
    (coe_mapAlgEquiv_ringOfIntegers (AlgEquiv.autCongr e σ) _).trans
      ((congrArg (AlgEquiv.autCongr e σ) (coe_mapAlgEquiv_ringOfIntegers e x)).trans
        (autCongr_apply_el e σ (x : M)))
  exact h₁.trans h₂.symm

/-- The transport of prime ideals is compatible with the Galois actions. -/
private lemma ideal_map_map_smul {k M L : Type*} [Field k] [NumberField k] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra k M] [Algebra k L]
    (e : M ≃ₐ[k] L) (σ : M ≃ₐ[k] M) (I : Ideal (NumberField.RingOfIntegers M)) :
    Ideal.map ((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv :
        NumberField.RingOfIntegers M →+* NumberField.RingOfIntegers L)
        (Ideal.map (Place.ringOfIntegersEquiv σ : NumberField.RingOfIntegers M →+*
          NumberField.RingOfIntegers M) I)
      = Ideal.map (Place.ringOfIntegersEquiv (AlgEquiv.autCongr e σ) :
          NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L)
        (Ideal.map ((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv :
          NumberField.RingOfIntegers M →+* NumberField.RingOfIntegers L) I) := by
  have h₁ := Ideal.map_map
    (f := (Place.ringOfIntegersEquiv σ : NumberField.RingOfIntegers M →+*
      NumberField.RingOfIntegers M))
    (g := ((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv :
      NumberField.RingOfIntegers M →+* NumberField.RingOfIntegers L)) (I := I)
  have h₂ := Ideal.map_map
    (f := ((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv :
      NumberField.RingOfIntegers M →+* NumberField.RingOfIntegers L))
    (g := (Place.ringOfIntegersEquiv (AlgEquiv.autCongr e σ) :
      NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L)) (I := I)
  have hcomp : (((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv :
          NumberField.RingOfIntegers M →+* NumberField.RingOfIntegers L).comp
        (Place.ringOfIntegersEquiv σ : NumberField.RingOfIntegers M →+*
          NumberField.RingOfIntegers M))
      = ((Place.ringOfIntegersEquiv (AlgEquiv.autCongr e σ) :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L).comp
        ((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv :
          NumberField.RingOfIntegers M →+* NumberField.RingOfIntegers L)) :=
    RingHom.ext (fun y => ringOfIntegers_maps_commute e σ y)
  exact h₁.trans ((congrArg (fun f : NumberField.RingOfIntegers M →+*
      NumberField.RingOfIntegers L => Ideal.map f I) hcomp).trans h₂.symm)

/-- Transport of nonzero primes along a `k`-algebra isomorphism, obtained from the induced
isomorphism of rings of integers. -/
private noncomputable def primeTransport {k M L : Type*} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra k L] (e : M ≃ₐ[k] L) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M) ≃
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) where
  toFun q :=
    ⟨Ideal.map ((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv :
        NumberField.RingOfIntegers M →+* NumberField.RingOfIntegers L) q.asIdeal,
      Ideal.map_isPrime_of_equiv (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv,
      fun h => q.ne_bot ((Ideal.map_eq_bot_iff_of_injective
        (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv.injective).mp h)⟩
  invFun Q :=
    ⟨Ideal.map ((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv.symm :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers M) Q.asIdeal,
      Ideal.map_isPrime_of_equiv (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv.symm,
      fun h => Q.ne_bot ((Ideal.map_eq_bot_iff_of_injective
        (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv.symm.injective).mp h)⟩
  left_inv q := IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
    (Ideal.map_of_equiv (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv)
  right_inv Q := IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
    (Ideal.map_of_equiv (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv.symm)

private lemma primeTransport_apply_asIdeal {k M L : Type*} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra k L] (e : M ≃ₐ[k] L)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M)) :
    (primeTransport e q).asIdeal = Ideal.map ((NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv :
        NumberField.RingOfIntegers M →+* NumberField.RingOfIntegers L) q.asIdeal :=
  rfl

/-- **The transport statement.**  For an isomorphism `e : M ≃ₐ[k] L` of number fields over `k`
there is an equivalence of the nonzero primes of `𝓞 M` and `𝓞 L` which preserves the primes above
a fixed prime `v₀` of `𝓞 k` and which intertwines the Galois action via conjugation by `e`. -/
private theorem exists_primeTransport_spec {k M L : Type*} [Field k] [NumberField k] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra k M] [Algebra k L]
    (e : M ≃ₐ[k] L) (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :
    (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M),
        q.asIdeal.LiesOver v₀.asIdeal → (primeTransport e q).asIdeal.LiesOver v₀.asIdeal) ∧
      (∀ (σ : M ≃ₐ[k] M)
          (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M)),
        primeTransport e (Place.smulHeightOneSpectrum σ q) =
          Place.smulHeightOneSpectrum (AlgEquiv.autCongr e σ) (primeTransport e q)) := by
  constructor
  · intro q hq
    haveI : q.asIdeal.LiesOver v₀.asIdeal := hq
    rw [primeTransport_apply_asIdeal]
    exact Ideal.map_equiv_liesOver q.asIdeal v₀.asIdeal
      (NumberField.RingOfIntegers.mapAlgEquiv e)
  · intro σ q
    apply IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
    simp only [primeTransport_apply_asIdeal, Place.smulHeightOneSpectrum_asIdeal]
    exact ideal_map_map_smul e σ q.asIdeal

/-- The transport statement, in existential form. -/
private theorem exists_primeTransport {k M L : Type*} [Field k] [NumberField k] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra k M] [Algebra k L]
    (e : M ≃ₐ[k] L) (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :
    ∃ Φ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M) ≃
        IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M),
        q.asIdeal.LiesOver v₀.asIdeal → (Φ q).asIdeal.LiesOver v₀.asIdeal) ∧
      (∀ (σ : M ≃ₐ[k] M)
          (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M)),
        Φ (Place.smulHeightOneSpectrum σ q) =
          Place.smulHeightOneSpectrum (AlgEquiv.autCongr e σ) (Φ q)) :=
  ⟨primeTransport e, exists_primeTransport_spec e v₀⟩

/-! ## Reading off the place data for a place of an abstract level -/

/-- A place of `M` lying over the finite place `v₀` is a finite place: it is `ofFinite q` for some
nonzero prime `q` of `𝓞 M` lying over `v₀`. -/
private lemma exists_ofFinite_of_liesOver {M : Type*} [Field M] [NumberField M]
    {k : Type*} [Field k] [NumberField k] [Algebra k M]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 k)) {w : Place M}
    (hw : Place.LiesOver w (Place.ofFinite v)) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (𝓞 M),
      w = Place.ofFinite q ∧ q.asIdeal.LiesOver v.asIdeal := by
  rw [Place.liesOver_iff] at hw
  rcases hw with ⟨w', v', h1, h2, h3⟩ | ⟨q, Q, h1, h2, h3⟩
  · exact absurd h2.symm (Place.ofInfinite_ne_ofFinite v' v)
  · refine ⟨q, h1, ?_⟩
    rw [Place.ofFinite_inj] at h2
    simpa [← h2] using h3

/-- Membership of a Galois automorphism in the stabiliser of a finite place, expressed on the
underlying prime. -/
private lemma smul_ofFinite_eq_iff {k M : Type*} [Field k] [NumberField k] [Field M]
    [NumberField M] [Algebra k M] {σ : M ≃ₐ[k] M}
    {q : IsDedekindDomain.HeightOneSpectrum (𝓞 M)} :
    σ • Place.ofFinite q = Place.ofFinite q ↔ Place.smulHeightOneSpectrum σ q = q := by
  rw [Place.smul_ofFinite, Place.ofFinite_inj]

/-- **Transfer of the full-local-degree property along a `k`-algebra isomorphism.**

If every place of `L` above `v₀` has full local degree and `Φ` transports the primes of `𝓞 M`
above `v₀` to those of `𝓞 L` above `v₀` compatibly with the conjugation action
`AlgEquiv.autCongr e`, then every place of `M` above `v₀` has full local degree. -/
private theorem fullLocal_transfer {k M L : Type*} [Field k] [NumberField k]
    [Field M] [NumberField M] [Algebra k M] [FiniteDimensional k M]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L]
    (e : M ≃ₐ[k] L) (v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 k))
    (Φ : IsDedekindDomain.HeightOneSpectrum (𝓞 M) ≃ IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hΦlies : ∀ q : IsDedekindDomain.HeightOneSpectrum (𝓞 M),
      q.asIdeal.LiesOver v₀.asIdeal → (Φ q).asIdeal.LiesOver v₀.asIdeal)
    (hΦsmul : ∀ (σ : M ≃ₐ[k] M) (q : IsDedekindDomain.HeightOneSpectrum (𝓞 M)),
      Φ (Place.smulHeightOneSpectrum σ q) =
        Place.smulHeightOneSpectrum (AlgEquiv.autCongr e σ) (Φ q))
    (hloc : ∀ w : Place L, Place.LiesOver w (Place.ofFinite v₀) →
      Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w) = Nat.card (L ≃ₐ[k] L)) :
    ∀ w : Place M, Place.LiesOver w (Place.ofFinite v₀) →
      Nat.card (MulAction.stabilizer (M ≃ₐ[k] M) w) = Nat.card (M ≃ₐ[k] M) := by
  intro w hw
  obtain ⟨q, rfl, hq⟩ := exists_ofFinite_of_liesOver v₀ hw
  have hq' : (Φ q).asIdeal.LiesOver v₀.asIdeal := hΦlies q hq
  have hL : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (Place.ofFinite (Φ q)))
      = Nat.card (L ≃ₐ[k] L) := hloc _ (Place.liesOver_ofFinite hq')
  have hstab : (MulAction.stabilizer (M ≃ₐ[k] M) (Place.ofFinite q)).map
        (AlgEquiv.autCongr e).toMonoidHom
      = MulAction.stabilizer (L ≃ₐ[k] L) (Place.ofFinite (Φ q)) := by
    ext τ
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨σ, hσ, hστ⟩
      have hσ' : Place.smulHeightOneSpectrum σ q = q :=
        (smul_ofFinite_eq_iff).mp ((MulAction.mem_stabilizer_iff).mp hσ)
      rw [← hστ]
      refine (MulAction.mem_stabilizer_iff).mpr ?_
      change (AlgEquiv.autCongr e σ) • Place.ofFinite (Φ q) = Place.ofFinite (Φ q)
      exact (smul_ofFinite_eq_iff).mpr (by rw [← hΦsmul σ q, hσ'])
    · intro hτ
      have hτ' : Place.smulHeightOneSpectrum τ (Φ q) = Φ q :=
        (smul_ofFinite_eq_iff).mp ((MulAction.mem_stabilizer_iff).mp hτ)
      refine ⟨(AlgEquiv.autCongr e).symm τ, ?_, ?_⟩
      · exact (smul_ofFinite_eq_iff).mpr
          (Φ.injective (by rw [hΦsmul ((AlgEquiv.autCongr e).symm τ) q,
            (AlgEquiv.autCongr e).apply_symm_apply τ, hτ']))
      · exact (AlgEquiv.autCongr e).apply_symm_apply τ
  have hcard : Nat.card (MulAction.stabilizer (M ≃ₐ[k] M) (Place.ofFinite q))
      = Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (Place.ofFinite (Φ q))) := by
    rw [← hstab]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ (AlgEquiv.autCongr e).toMonoidHom
      (AlgEquiv.autCongr e).injective).toEquiv
  rw [hcard, hL]
  exact (Nat.card_congr (AlgEquiv.autCongr e).toEquiv).symm

/-! ## The main theorem -/

/-- **Packaging an abstract cyclic level into `LevelData`.**

An abstract field `L` with `k ⊆ L` finite, Galois, cyclic of `q`-power order divisible by `q`, in
which every place above `v₀` has full local degree (the stabiliser in `Gal(L/k)` of every place of
`L` above `v₀` is the whole group), produces a `LevelData k q 1 v₀`, i.e. a subfield
`M ⊆ AlgebraicClosure k` with the same properties.

The construction embeds `L` into `AlgebraicClosure k` (finite extensions of a number field embed
into an algebraic closure), takes `M` to be the image, and transports the Galois group, the
cardinality, cyclicity, and the place/Galois-action compatibility (`LiesOver` and stabilisers) along
the induced `k`-algebra isomorphism `L ≃ₐ[k] M`. -/
theorem levelData_of_abstract_level (k : Type) [Field k] [NumberField k]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : ℕ) (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L]
    [IsGalois k L] [IsMulCommutative (L ≃ₐ[k] L)]
    (hcyc : IsCyclic (L ≃ₐ[k] L)) (hcard : ∃ a : ℕ, Nat.card (L ≃ₐ[k] L) = q ^ a)
    (hdvd : q ∣ Nat.card (L ≃ₐ[k] L))
    (hloc : ∀ w : NK.GlobalCFT.Place L,
      NK.GlobalCFT.Place.LiesOver w (NK.GlobalCFT.Place.ofFinite v₀) →
        Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w) = Nat.card (L ≃ₐ[k] L)) :
    Nonempty (LevelData k q 1 v₀) := by
  classical
  haveI : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  -- ## Step 1: embed `L` into `AlgebraicClosure k`
  let f : L →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift (R := k) (S := L) (M := AlgebraicClosure k)
  let e : L ≃ₐ[k] ↥f.fieldRange := AlgHom.equivFieldRange f
  haveI hMfd : FiniteDimensional k ↥f.fieldRange := e.toLinearEquiv.finiteDimensional
  haveI hMnf : NumberField ↥f.fieldRange := inferInstance
  haveI hMgal : IsGalois k ↥f.fieldRange := IsGalois.of_algEquiv e
  -- ## Step 2: the group-theoretic data
  haveI hLcyc : IsCyclic (L ≃ₐ[k] L) := hcyc
  have hMcyc : IsCyclic (↥f.fieldRange ≃ₐ[k] ↥f.fieldRange) :=
    isCyclic_of_surjective (AlgEquiv.autCongr e).toMonoidHom (AlgEquiv.autCongr e).surjective
  have hcardM : ∃ a : ℕ, Nat.card (↥f.fieldRange ≃ₐ[k] ↥f.fieldRange) = q ^ a := by
    obtain ⟨a, ha⟩ := hcard
    refine ⟨a, ?_⟩
    rw [← Nat.card_congr (AlgEquiv.autCongr e).toEquiv]
    exact ha
  have hdvdM : q ^ 1 ∣ Nat.card (↥f.fieldRange ≃ₐ[k] ↥f.fieldRange) := by
    rw [pow_one, ← Nat.card_congr (AlgEquiv.autCongr e).toEquiv]
    exact hdvd
  -- ## Step 3: the place data, transported across `e.symm`
  obtain ⟨Φ, hΦlies, hΦsmul⟩ := exists_primeTransport (e.symm) v₀
  have hfull := fullLocal_transfer (e.symm) v₀ Φ hΦlies hΦsmul hloc
  exact ⟨{ M := f.fieldRange, fd := hMfd, nf := hMnf, gal := hMgal, cyc := hMcyc,
           qpow := hcardM, dvd := hdvdM, fullLocal := hfull }⟩

end Work.SSGRoute.CycLevel
