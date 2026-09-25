import Mathlib
import Submission.NK.Reconstruct.levelIsoInput_of_localCorrespondence
import Submission.NK.Reconstruct.levelIsoInput_transport
import Submission.NK.Reconstruct.exists_localCorrespondence_transport
import Submission.NK.Reconstruct.exists_frobeniusCorrespondence_transport
import Submission.NK.Reconstruct.exists_sigma_of_levelPrimeIdentification
import Submission.NK.Reconstruct.exists_algebra_isSepClosure
import Submission.NK.Reconstruct.fourf5Gen
import Submission.NK.Reconstruct.levelPairData
import Submission.NK.Mine.ExistsSigmaOfLocalCorrespondence
import Submission.NK.ReconstructField.primeOf_comap_eq_primeTransport
import Submission.NK.NeukirchUchida.isHomeomorph_conjHomEquiv
import Submission.NK.Reconstruct.charP_quotient_primeTransport
import Submission.NK.Reconstruct.localDegree_primeTransport_of_ringEquiv

namespace NK.Reconstruct

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Pointwise

/-!
# The σ-producing step of Neukirch–Uchida from the local correspondence, the Frobenius
correspondence, the rank inputs and Čebotarev

This module proves `NK.Reconstruct.exists_sigma_of_localCorrespondence`: from the σ-free local
correspondence (a) `LocalCorrespondence ϕ` (CoNF (12.1.9)), the Frobenius correspondence (b), a prime
`ℓ`, the three rank inputs of Shimizu's §4 (`HausRankInput`, `RankStrictMonoLevelInputGen`,
`ResRankInputGen`) and the Čebotarev density input `ChebotarevInput ℚ K₁'`, there is a field
isomorphism `σ : K₂' ≃+* K₁'` with `Conjugates σ ϕ`.

## The route

1. put both separable closures into one field `Ω := K₁'` (the embedding `K₂ →ₐ[ℚ] Ω` is
   `NK.Reconstruct.exists_algebra_isSepClosure`), with `e : K₂' ≃ₐ[K₂] Ω` the isomorphism of
   separable closures and `ψ := e ∘ ϕ ∘ e⁻¹ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)`;
2. transport (a) and (b) along `e` (`NK.Reconstruct.exists_localCorrespondence_transport`,
   `NK.Reconstruct.exists_frobeniusCorrespondence_transport`), in the explicit form below;
3. the level-pair bridge `NK.Reconstruct.levelIsoInput_of_localCorrespondence` is stated for the
   pair of *number-field levels* `K₁.L`, `K₂.L` inside `Ω`; taking them to be the images of `K₁` and
   `K₂` inside `Ω` requires changing the *model* of the base field (`K₁` vs `↥K₁.L`) — the
   base-change lemmas below;
4. the resulting `LevelIsoInput θ hθ` is transported back to `ϕ`
   (`NK.Reconstruct.levelIsoInput_transport`);
5. the endgame `NK.Mine.exists_sigma_of_localCorrespondence` produces `σ`.
-/

/-- **The `ℚ`-algebra structure of a number field `K` is compatible with any `K`-algebra structure
on a field `Ω`**: the two ring homomorphisms `ℚ → Ω` agree because they agree on `1`. -/
theorem isScalarTower_rat_of_numberField {K Ω : Type*} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [Algebra ℚ Ω] : IsScalarTower ℚ K Ω := by
  refine IsScalarTower.of_algebraMap_eq (fun q => ?_)
  exact (RingHom.congr_fun (RingHom.ext_rat (f := (algebraMap K Ω).comp (algebraMap ℚ K))
    (g := algebraMap ℚ Ω)) q).symm

/-- **The `ℚ`-algebra homomorphism `K →ₐ[ℚ] Ω` given by the algebra structure.** -/
noncomputable def baseAlgHom (K : Type*) [Field K] [NumberField K] (Ω : Type*) [Field Ω]
    [Algebra K Ω] [Algebra ℚ Ω] [IsScalarTower ℚ K Ω] : K →ₐ[ℚ] Ω where
  toFun := algebraMap K Ω
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' q := (IsScalarTower.algebraMap_apply ℚ K Ω q).symm

@[simp] theorem baseAlgHom_apply (K : Type*) [Field K] [NumberField K] (Ω : Type*) [Field Ω]
    [Algebra K Ω] [Algebra ℚ Ω] [IsScalarTower ℚ K Ω] (x : K) :
    baseAlgHom K Ω x = algebraMap K Ω x := rfl

/-- **Base change of algebra automorphisms along an isomorphism of base fields.**

Let `K → Ω` be a `k`-algebra structure on `Ω`, let `L ⊆ Ω` be an intermediate field of `k → Ω` such
that the `k`-algebra map `K → Ω` has image `L`, and let `e : K ≃ₐ[k] ↥L` be the induced isomorphism
of `k`-algebras (`he` records the compatibility `algebraMap ↥L Ω ∘ e = algebraMap K Ω`).  Then every
`K`-algebra automorphism of `Ω` is an `↥L`-algebra automorphism and conversely, with the *same*
underlying map; this is the group isomorphism `Gal(Ω/K) ≃* Gal(Ω/↥L)`. -/
noncomputable def galEquivOfBaseEquiv {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K]
    [Algebra k Ω] [Algebra K Ω] (L : IntermediateField k Ω) (e : K ≃+* ↥L)
    (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x) :
    (Ω ≃ₐ[K] Ω) ≃* (Ω ≃ₐ[↥L] Ω) where
  toFun f := AlgEquiv.mk f.toEquiv f.map_mul' f.map_add' (fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [show (algebraMap (↥L) Ω) (e x) = algebraMap K Ω x from he x]
    exact f.commutes x)
  invFun g := AlgEquiv.mk g.toEquiv g.map_mul' g.map_add' (fun x => by
    rw [show (algebraMap K Ω) x = (algebraMap (↥L) Ω) (e x) from (he x).symm]
    exact g.commutes (e x))
  left_inv f := by ext x; rfl
  right_inv g := by ext x; rfl
  map_mul' f g := by ext x; rfl

@[simp] theorem galEquivOfBaseEquiv_apply_coe {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] (L : IntermediateField k Ω) (e : K ≃+* ↥L)
    (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x) (f : Ω ≃ₐ[K] Ω) :
    ((galEquivOfBaseEquiv L e he f : Ω ≃ₐ[↥L] Ω) : Ω → Ω) = f := rfl

@[simp] theorem galEquivOfBaseEquiv_symm_apply_coe {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] (L : IntermediateField k Ω) (e : K ≃+* ↥L)
    (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x) (g : Ω ≃ₐ[↥L] Ω) :
    (((galEquivOfBaseEquiv L e he).symm g : Ω ≃ₐ[K] Ω) : Ω → Ω) = g := rfl

/-! ## Conjugation by an isomorphism of separable closures is a homeomorphism -/

/-- **Conjugation by an isomorphism `e : X ≃ₐ[F] Y` of separable closures is a homeomorphism** of
the absolute Galois groups, for the Krull topologies.  This is
`NK.NeukirchUchida.isHomeomorph_conjHomEquiv` applied to the base-field-mapping isomorphism
`e.symm` (conjugation by `e` is `algEquivConjHom e`, which is `conjHomEquiv` for `e.symm`). -/
theorem isHomeomorph_algEquivConjHom {F X Y : Type*} [Field F] [Field X] [Field Y] [Algebra F X]
    [Algebra F Y] (e : X ≃ₐ[F] Y) : IsHomeomorph (algEquivConjHom e) := by
  have hbase : Submission.NeukirchUchida.MapsBase (algebraMap F X) (algebraMap F Y)
      (e.symm : Y ≃+* X) := by
    unfold Submission.NeukirchUchida.MapsBase
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := RingHom.mem_range.mp hy
      exact RingHom.mem_range.mpr ⟨c, by simp⟩
    · rintro ⟨c, rfl⟩
      exact ⟨algebraMap F Y c, RingHom.mem_range.mpr ⟨c, rfl⟩, by simp⟩
  have h := NK.NeukirchUchida.isHomeomorph_conjHomEquiv (K₁ := F) (K₂ := F) (K₁' := X)
    (K₂' := Y) (e.symm : Y ≃+* X) hbase
  convert h using 1
  ext g x
  rfl

/-! ## The inverse of `primeTransport` -/

/-- **The inverse property of `primeTransport`**: transporting a prime along a ring isomorphism and
back returns the original prime. -/
theorem primeTransport_symm_transport {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] (e : K ≃+* L) (P : NK.Chebotarev.PrimeIdeal K) :
    primeTransport (e.symm) (primeTransport e P) = P := by
  refine IsDedekindDomain.HeightOneSpectrum.ext ?_
  show Ideal.map (ringOfIntegersEquiv e.symm :
      NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers K)
    (Ideal.map (ringOfIntegersEquiv e :
      NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers L) P.asIdeal) = P.asIdeal
  have hcomp : ((ringOfIntegersEquiv e.symm :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers K)).comp
      ((ringOfIntegersEquiv e :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers L)) =
      RingHom.id (NumberField.RingOfIntegers K) := by
    ext x
    change ((ringOfIntegersEquiv e.symm) ((ringOfIntegersEquiv e) x) : K) = (x : K)
    rw [ringOfIntegersEquiv_apply, ringOfIntegersEquiv_apply]
    exact e.symm_apply_apply x
  rw [Ideal.map_map (f := (ringOfIntegersEquiv e :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers L))
    (g := (ringOfIntegersEquiv e.symm :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers K)), hcomp, Ideal.map_id]

/-- **The transport of primes along a ring isomorphism, as an equivalence.** -/
noncomputable def primeEquiv {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃+* L) : NK.Chebotarev.PrimeIdeal K ≃ NK.Chebotarev.PrimeIdeal L where
  toFun := primeTransport e
  invFun := primeTransport e.symm
  left_inv P := primeTransport_symm_transport e P
  right_inv Q := by
    have h := primeTransport_symm_transport (e := e.symm) Q
    rwa [RingEquiv.symm_symm] at h

@[simp] theorem primeEquiv_apply {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃+* L) (P : NK.Chebotarev.PrimeIdeal K) :
    primeEquiv e P = primeTransport e P := rfl

/-! ## Places and decomposition groups are unchanged by a change of the base field's model -/

/-- **The preimage of a proper valuation subring along a surjective ring homomorphism is proper.** -/
lemma comap_ne_top_iff_of_surjective {R S : Type*} [Field R] [Field S] (f : R →+* S)
    (hf : Function.Surjective f) (B : ValuationSubring S) : B.comap f ≠ ⊤ ↔ B ≠ ⊤ := by
  have hiff : B.comap f = ⊤ ↔ B = ⊤ := by
    constructor
    · intro h
      refine eq_top_iff.mpr fun y _ => ?_
      obtain ⟨x, rfl⟩ := hf y
      exact (ValuationSubring.mem_comap).mpr (by rw [← ValuationSubring.mem_comap, h]; trivial)
    · intro h
      rw [h]
      refine eq_top_iff.mpr fun x _ => ?_
      rw [ValuationSubring.mem_comap]
      trivial
  exact not_congr hiff

/-- **The places over the finite primes are unchanged by a change of the base field's model.**

If `e : K ≃+* ↥L` identifies a number field `K` with the intermediate field `L ⊆ Ω` (compatibly
with the algebra maps, `he`), then the places of `Ω` over the finite primes of `K` and those over the
finite primes of `↥L` are the same, via the identity of the underlying valuation subring. -/
noncomputable def baseChangePlaceEquiv {K Ω : Type*} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [Algebra ℚ Ω] (L : IntermediateField ℚ Ω) [NumberField ↥L]
    (e : K ≃+* ↥L) (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x) :
    FinitePlaceOf ↥L Ω ≃ FinitePlaceOf K Ω where
  toFun A := ⟨A.1, by
    have hcomap : (A.1.comap (algebraMap ↥L Ω)).comap (e : K →+* ↥L) =
        A.1.comap (algebraMap K Ω) := by
      rw [ValuationSubring.comap_comap]
      congr 1
      ext x
      exact he x
    rw [← hcomap]
    exact (comap_ne_top_iff_of_surjective (e : K →+* ↥L) e.surjective
      (A.1.comap (algebraMap ↥L Ω))).mpr A.2⟩
  invFun A := ⟨A.1, by
    have hcomap : (A.1.comap (algebraMap ↥L Ω)).comap (e : K →+* ↥L) =
        A.1.comap (algebraMap K Ω) := by
      rw [ValuationSubring.comap_comap]
      congr 1
      ext x
      exact he x
    have hB : (A.1.comap (algebraMap ↥L Ω)).comap (e : K →+* ↥L) ≠ ⊤ := by
      rw [hcomap]; exact A.2
    exact (comap_ne_top_iff_of_surjective (e : K →+* ↥L) e.surjective
      (A.1.comap (algebraMap ↥L Ω))).mp hB⟩
  left_inv A := rfl
  right_inv A := rfl

@[simp] theorem baseChangePlaceEquiv_apply_val {K Ω : Type*} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [Algebra ℚ Ω] (L : IntermediateField ℚ Ω) [NumberField ↥L]
    (e : K ≃+* ↥L) (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x)
    (A : FinitePlaceOf ↥L Ω) :
    (baseChangePlaceEquiv L e he A).1 = A.1 := rfl

@[simp] theorem baseChangePlaceEquiv_symm_apply_val {K Ω : Type*} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [Algebra ℚ Ω] (L : IntermediateField ℚ Ω) [NumberField ↥L]
    (e : K ≃+* ↥L) (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x)
    (A : FinitePlaceOf K Ω) :
    ((baseChangePlaceEquiv L e he).symm A).1 = A.1 := rfl

/-- **The action of an algebra automorphism on a valuation subring is the preimage along its
inverse.** -/
lemma smul_comap_algEquiv {R Ω : Type*} [Field R] [Field Ω] [Algebra R Ω] (g : Ω ≃ₐ[R] Ω)
    (A : ValuationSubring Ω) : g • A = A.comap (g.symm : Ω →+* Ω) := by
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists, ValuationSubring.mem_comap]
  constructor
  · rintro ⟨s, hs, rfl⟩
    show g.symm (g s) ∈ A
    rw [AlgEquiv.symm_apply_apply]
    exact hs
  · intro h
    exact ⟨g.symm x, h, g.apply_symm_apply x⟩

/-- **The action on places depends only on the underlying map**: two algebra automorphisms of `Ω`
with the same underlying function (possibly over different base fields) act in the same way on
valuation subrings. -/
lemma smul_eq_of_coe_eq {R R' Ω : Type*} [Field R] [Field R'] [Field Ω] [Algebra R Ω]
    [Algebra R' Ω] (g : Ω ≃ₐ[R] Ω) (h : Ω ≃ₐ[R'] Ω) (hg : (g : Ω → Ω) = (h : Ω → Ω))
    (A : ValuationSubring Ω) : g • A = h • A := by
  rw [smul_comap_algEquiv g A, smul_comap_algEquiv h A]
  have hsymm : (g.symm : Ω →+* Ω) = (h.symm : Ω →+* Ω) := by
    refine RingHom.ext fun x => ?_
    have h1 : g (h.symm x) = x := by
      rw [congrFun hg (h.symm x), AlgEquiv.apply_symm_apply]
    calc g.symm x = g.symm (g (h.symm x)) := by rw [h1]
      _ = h.symm x := AlgEquiv.symm_apply_apply g (h.symm x)
  rw [hsymm]

/-- **The `placeMap` and the `placeSmul`s of two models of the base field agree.** -/
theorem baseChangePlaceEquiv_placeSmul {K Ω : Type*} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [Algebra ℚ Ω] [IsSepClosure K Ω] (L : IntermediateField ℚ Ω) [NumberField ↥L]
    [IsSepClosure ↥L Ω]
    (e : K ≃+* ↥L) (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x)
    (g : Ω ≃ₐ[↥L] Ω) (g' : Ω ≃ₐ[K] Ω) (hg : (g : Ω → Ω) = (g' : Ω → Ω))
    (A : FinitePlaceOf ↥L Ω) :
    baseChangePlaceEquiv L e he (placeSmul g A) = placeSmul g' (baseChangePlaceEquiv L e he A) := by
  refine Subtype.ext ?_
  show (g • A.1) = (g' • A.1)
  exact smul_eq_of_coe_eq g g' hg A.1

/-- The same statement in the `placeSmul₂` presentation of the second field. -/
theorem baseChangePlaceEquiv_placeSmul₂ {K Ω : Type*} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [Algebra ℚ Ω] [IsSepClosure K Ω] (L : IntermediateField ℚ Ω) [NumberField ↥L]
    [IsSepClosure ↥L Ω]
    (e : K ≃+* ↥L) (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x)
    (g : Ω ≃ₐ[↥L] Ω) (g' : Ω ≃ₐ[K] Ω) (hg : (g : Ω → Ω) = (g' : Ω → Ω))
    (A : FinitePlaceOf ↥L Ω) :
    baseChangePlaceEquiv L e he (placeSmul₂ (K₂ := ↥L) (K₂' := Ω) g A) =
      placeSmul₂ (K₂ := K) (K₂' := Ω) g' (baseChangePlaceEquiv L e he A) := by
  refine Subtype.ext ?_
  show (g • A.1) = (g' • A.1)
  exact smul_eq_of_coe_eq g g' hg A.1

/-- **The stabilisers of a valuation subring in the two models of the base field correspond** under
the base-change isomorphism of Galois groups. -/
theorem map_galEquivOfBaseEquiv_stabilizer {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K]
    [Algebra k Ω] [Algebra K Ω] (L : IntermediateField k Ω) (e : K ≃+* ↥L)
    (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x) (A : ValuationSubring Ω) :
    (MulAction.stabilizer (Ω ≃ₐ[K] Ω) A).map (galEquivOfBaseEquiv L e he) =
      MulAction.stabilizer (Ω ≃ₐ[↥L] Ω) A := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [MulAction.mem_stabilizer_iff] at hh ⊢
    calc (galEquivOfBaseEquiv L e he h) • A = h • A :=
          smul_eq_of_coe_eq _ h (galEquivOfBaseEquiv_apply_coe L e he h) A
      _ = A := hh
  · intro hg
    refine ⟨(galEquivOfBaseEquiv L e he).symm g, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff] at hg ⊢
      calc ((galEquivOfBaseEquiv L e he).symm g) • A = g • A :=
            smul_eq_of_coe_eq _ g (galEquivOfBaseEquiv_symm_apply_coe L e he g) A
        _ = A := hg
    · exact MulEquiv.apply_symm_apply (galEquivOfBaseEquiv L e he) g

/-- The same statement for the inverse isomorphism. -/
theorem map_galEquivOfBaseEquiv_symm_stabilizer {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] (L : IntermediateField k Ω) (e : K ≃+* ↥L)
    (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x) (A : ValuationSubring Ω) :
    (MulAction.stabilizer (Ω ≃ₐ[↥L] Ω) A).map (galEquivOfBaseEquiv L e he).symm =
      MulAction.stabilizer (Ω ≃ₐ[K] Ω) A := by
  rw [← map_galEquivOfBaseEquiv_stabilizer L e he A, Subgroup.map_map]
  congr 1
  ext g
  simp

/-- The base-change isomorphism of Galois groups carries the decomposition group of a place over
`K` to the decomposition group of the same place over `↥L`. -/
theorem decompositionGroup_baseChange {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K]
    [Algebra k Ω] [Algebra K Ω] (L : IntermediateField k Ω) (e : K ≃+* ↥L)
    (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x) (A : ValuationSubring Ω) :
    (Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := Ω) A).map
        (galEquivOfBaseEquiv L e he) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := ↥L) (K₁' := Ω) A :=
  map_galEquivOfBaseEquiv_stabilizer L e he A

/-- The same for the inverse isomorphism. -/
theorem decompositionGroup_baseChange_symm {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] (L : IntermediateField k Ω) (e : K ≃+* ↥L)
    (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x) (A : ValuationSubring Ω) :
    (Submission.NeukirchUchida.decompositionGroup (K₁ := ↥L) (K₁' := Ω) A).map
        (galEquivOfBaseEquiv L e he).symm =
      Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := Ω) A :=
  map_galEquivOfBaseEquiv_symm_stabilizer L e he A

/-! ## The base change of `primeOf` -/

/-- `primeOf` does not depend on the proof of properness of the trace. -/
lemma primeOf_proof_irrel {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    (A : ValuationSubring K') (h₁ h₂ : A.comap (algebraMap K K') ≠ ⊤) :
    Submission.NeukirchUchida.primeOf (K₁ := K) (K₁' := K') A h₁ =
      Submission.NeukirchUchida.primeOf (K₁ := K) (K₁' := K') A h₂ := by
  rw [Subsingleton.elim h₁ h₂]

/-- **The prime of `𝓞 ↥L` below a place of `Ω` is the transport along `e : K ≃+* ↥L` of the prime of
`𝓞 K` below the same place.**  This is
`NK.ReconstructField.primeOf_comap_eq_primeTransport` with the identity realisation of the place
correspondence. -/
theorem primeOf_baseChange {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsSepClosure ℚ Ω]
    (L : IntermediateField ℚ Ω) [NumberField ↥L] [IsSepClosure ↥L Ω]
    {K : Type*} [Field K] [NumberField K] [Algebra K Ω] [IsSepClosure K Ω] [Algebra ℚ K]
    [IsScalarTower ℚ K Ω]
    (e : K ≃+* ↥L) (he : ∀ x : K, (algebraMap ↥L Ω) (e x) = algebraMap K Ω x)
    (A : ValuationSubring Ω) (hA : A.comap (algebraMap ↥L Ω) ≠ ⊤)
    (hK : A.comap (algebraMap K Ω) ≠ ⊤) :
    primeTransport e
        (Submission.NeukirchUchida.primeOf (K₁ := K) (K₁' := Ω) A hK) =
      Submission.NeukirchUchida.primeOf (K₁ := ↥L) (K₁' := Ω) A hA := by
  have hrange : (algebraMap K Ω).range = (algebraMap ↥L Ω).range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e y, he y⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e.symm z, by rw [← he (e.symm z), RingEquiv.apply_symm_apply]⟩
  have hσ : Submission.NeukirchUchida.MapsBase (algebraMap ↥L Ω) (algebraMap K Ω)
      (RingEquiv.refl Ω) := by
    unfold Submission.NeukirchUchida.MapsBase
    rw [show ((RingEquiv.refl Ω).toRingHom) = RingHom.id Ω from rfl, Subring.map_id, hrange]
  have hbase : ∀ x : ↥L, (RingEquiv.refl Ω) (algebraMap K Ω (e.symm x)) = algebraMap ↥L Ω x := by
    intro x
    show algebraMap K Ω (e.symm x) = algebraMap ↥L Ω x
    rw [← he (e.symm x), RingEquiv.apply_symm_apply]
  have h := NK.ReconstructField.primeOf_comap_eq_primeTransport (K₁ := ↥L) (K₂ := K)
    (K₁' := Ω) (K₂' := Ω) (τ := e.symm) (σ := RingEquiv.refl Ω) hσ hbase ⟨A, hA⟩
  have hstep : Submission.NeukirchUchida.primeOf (K₁ := K) (K₁' := Ω) A hK =
      Submission.NeukirchUchida.primeOf (K₁ := K) (K₁' := Ω)
        (A.comap ((RingEquiv.refl Ω : Ω ≃+* Ω) : Ω →+* Ω))
        (NK.Reconstruct.comap_sigma_comap_ne_top hσ hA) := by
    refine Submission.NeukirchUchida.primeOf_eq_of_comap_eq (A := A)
      (B := A.comap ((RingEquiv.refl Ω : Ω ≃+* Ω) : Ω →+* Ω)) hK _ ?_
    rw [ValuationSubring.comap_comap]
    congr 1
  have hfinal := primeTransport_symm_transport (e := e.symm)
    (P := Submission.NeukirchUchida.primeOf (K₁ := ↥L) (K₁' := Ω) A hA)
  rw [RingEquiv.symm_symm] at hfinal
  rw [hstep, h, hfinal]


/-! ## The base change of the local correspondence -/

section BaseChange

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
variable {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Algebra K₁ Ω] [Algebra K₂ Ω] [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]

omit [IsGalois ℚ Ω] in
/-- **The group isomorphism `Gal(Ω/↥A.L) ≃* Gal(Ω/↥B.L)` induced by `ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)`
and the identifications of `K₁` with `A.L` and `K₂` with `B.L`.** -/
noncomputable def baseChangeGalEquiv (A B : NumFieldIn ℚ Ω) (eA : K₁ ≃+* ↥A.L)
    (hA : ∀ x : K₁, (algebraMap ↥A.L Ω) (eA x) = algebraMap K₁ Ω x) (eB : K₂ ≃+* ↥B.L)
    (hB : ∀ x : K₂, (algebraMap ↥B.L Ω) (eB x) = algebraMap K₂ Ω x)
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) : Gal(Ω/↥A.L) ≃* Gal(Ω/↥B.L) :=
  (galEquivOfBaseEquiv A.L eA hA).symm.trans (ψ.trans (galEquivOfBaseEquiv B.L eB hB))

theorem baseChangeGalEquiv_apply_coe (A B : NumFieldIn ℚ Ω) (eA : K₁ ≃+* ↥A.L)
    (hA : ∀ x : K₁, (algebraMap ↥A.L Ω) (eA x) = algebraMap K₁ Ω x) (eB : K₂ ≃+* ↥B.L)
    (hB : ∀ x : K₂, (algebraMap ↥B.L Ω) (eB x) = algebraMap K₂ Ω x)
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (g : Gal(Ω/↥A.L)) :
    ((baseChangeGalEquiv A B eA hA eB hB ψ g : Ω ≃ₐ[↥B.L] Ω) : Ω → Ω) =
      ((ψ ((galEquivOfBaseEquiv A.L eA hA).symm g) : Ω ≃ₐ[K₂] Ω) : Ω → Ω) := rfl

omit [IsGalois ℚ Ω] in
/-- The composition of subgroup maps along a product of group isomorphisms. -/
lemma Subgroup.map_trans {G H I : Type*} [Group G] [Group H] [Group I] (H₀ : Subgroup G)
    (f : G ≃* H) (g : H ≃* I) :
    H₀.map ((f.trans g : G ≃* I) : G →* I) = (H₀.map (f : G →* H)).map (g : H →* I) := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨f y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- **The base change of a local correspondence.**

Let `ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)` and let `A`, `B` be number-field levels of `Ω/ℚ` whose underlying
fields are identified with `K₁`, `K₂` by `eA`, `eB` (compatibly with the algebra maps, `hA`, `hB`).
Then a local correspondence `a` for `ψ` transports to a local correspondence for
`baseChangeGalEquiv A B eA hA eB hB ψ`, with the place map obtained by transporting the places
along the identity of the underlying valuation subrings. -/
noncomputable def localCorrespondence_baseChange (A B : NumFieldIn ℚ Ω) [IsSepClosure ↥A.L Ω]
    [IsSepClosure ↥B.L Ω] [NumberField ↥A.L] [NumberField ↥B.L] (eA : K₁ ≃+* ↥A.L)
    (hA : ∀ x : K₁, (algebraMap ↥A.L Ω) (eA x) = algebraMap K₁ Ω x) (eB : K₂ ≃+* ↥B.L)
    (hB : ∀ x : K₂, (algebraMap ↥B.L Ω) (eB x) = algebraMap K₂ Ω x)
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (a : LocalCorrespondence ψ) :
    LocalCorrespondence (baseChangeGalEquiv A B eA hA eB hB ψ) where
  placeMap := (baseChangePlaceEquiv A.L eA hA).trans
    (a.placeMap.trans (baseChangePlaceEquiv B.L eB hB).symm)
  map_smul := fun g A' => by
    haveI : IsSepClosure ↥A.L Ω := ‹_›
    haveI : IsSepClosure ↥B.L Ω := ‹_›
    show (baseChangePlaceEquiv B.L eB hB).symm
        (a.placeMap (baseChangePlaceEquiv A.L eA hA (placeSmul g A'))) =
      placeSmul₂ (baseChangeGalEquiv A B eA hA eB hB ψ g)
        ((baseChangePlaceEquiv B.L eB hB).symm
          (a.placeMap (baseChangePlaceEquiv A.L eA hA A')))
    have h1 := baseChangePlaceEquiv_placeSmul A.L eA hA g
      ((galEquivOfBaseEquiv A.L eA hA).symm g) rfl A'
    rw [h1, a.map_smul]
    have h2 := baseChangePlaceEquiv_placeSmul₂ B.L eB hB
      (baseChangeGalEquiv A B eA hA eB hB ψ g)
      (ψ ((galEquivOfBaseEquiv A.L eA hA).symm g)) rfl
      ((baseChangePlaceEquiv B.L eB hB).symm
        (a.placeMap (baseChangePlaceEquiv A.L eA hA A')))
    simp only [Equiv.apply_symm_apply] at h2
    rw [← h2]
    simp
  map_decomp := fun A' => by
    haveI : IsSepClosure ↥A.L Ω := ‹_›
    haveI : IsSepClosure ↥B.L Ω := ‹_›
    change (Submission.NeukirchUchida.decompositionGroup (K₁ := ↥A.L) (K₁' := Ω) A'.1).map
        (baseChangeGalEquiv A B eA hA eB hB ψ) =
      Submission.NeukirchUchida.decompositionGroup (K₁ := ↥B.L) (K₁' := Ω)
        ((baseChangePlaceEquiv B.L eB hB).symm
          (a.placeMap (baseChangePlaceEquiv A.L eA hA A'))).1
    rw [show (baseChangeGalEquiv A B eA hA eB hB ψ) =
        (galEquivOfBaseEquiv A.L eA hA).symm.trans
          (ψ.trans (galEquivOfBaseEquiv B.L eB hB)) from rfl]
    rw [Subgroup.map_trans, Subgroup.map_trans]
    simp only [baseChangePlaceEquiv_apply_val, baseChangePlaceEquiv_symm_apply_val]
    rw [decompositionGroup_baseChange_symm A.L eA hA A'.1]
    rw [a.map_decomp ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩]
    rw [decompositionGroup_baseChange B.L eB hB]
    congr 1
  primeMap := (primeEquiv eA).symm.trans (a.primeMap.trans (primeEquiv eB))
  primeMap_spec := fun A' => by
    haveI : IsSepClosure ↥A.L Ω := ‹_›
    haveI : IsSepClosure ↥B.L Ω := ‹_›
    change (primeEquiv eB) (a.primeMap ((primeEquiv eA).symm
        (Submission.NeukirchUchida.primeOf (K₁ := ↥A.L) (K₁' := Ω) A'.1 A'.2))) =
      Submission.NeukirchUchida.primeOf (K₁ := ↥B.L) (K₁' := Ω)
        ((baseChangePlaceEquiv B.L eB hB).symm
          (a.placeMap (baseChangePlaceEquiv A.L eA hA A'))).1
        ((baseChangePlaceEquiv B.L eB hB).symm
          (a.placeMap (baseChangePlaceEquiv A.L eA hA A'))).2
    have h1 : (primeEquiv eA).symm (Submission.NeukirchUchida.primeOf (K₁ := ↥A.L) (K₁' := Ω)
        A'.1 A'.2) =
        Submission.NeukirchUchida.primeOf (K₁ := K₁) (K₁' := Ω) A'.1
          (baseChangePlaceEquiv A.L eA hA A').2 := by
      rw [Equiv.symm_apply_eq]
      exact (primeOf_baseChange A.L eA hA A'.1 A'.2
        (baseChangePlaceEquiv A.L eA hA A').2).symm
    rw [h1]
    simp only [baseChangePlaceEquiv_symm_apply_val]
    rw [a.primeMap_spec ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩]
    exact primeOf_baseChange B.L eB hB
      ((a.placeMap (baseChangePlaceEquiv A.L eA hA A')).1)
      ((baseChangePlaceEquiv B.L eB hB).symm
        (a.placeMap (baseChangePlaceEquiv A.L eA hA A'))).2
      (a.placeMap (baseChangePlaceEquiv A.L eA hA A')).2
  residueChar := fun A' ℓ h => by
    haveI : IsSepClosure ↥A.L Ω := ‹_›
    haveI : IsSepClosure ↥B.L Ω := ‹_›
    have h₁ : CharP (NumberField.RingOfIntegers K₁ ⧸
        (Submission.NeukirchUchida.primeOf (K₁ := K₁) (K₁' := Ω) A'.1
          (baseChangePlaceEquiv A.L eA hA A').2).asIdeal) ℓ := by
      refine (charP_quotient_primeTransport eA (Submission.NeukirchUchida.primeOf (K₁ := K₁)
        (K₁' := Ω) A'.1 (baseChangePlaceEquiv A.L eA hA A').2) ℓ).mpr ?_
      rw [primeOf_baseChange A.L eA hA A'.1 A'.2 (baseChangePlaceEquiv A.L eA hA A').2]
      exact h
    have h₂ := a.residueChar ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩ ℓ h₁
    have h₃ : CharP (NumberField.RingOfIntegers ↥B.L ⧸
        (Submission.NeukirchUchida.primeOf (K₁ := ↥B.L) (K₁' := Ω)
          (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).1
          ((baseChangePlaceEquiv B.L eB hB).symm
            (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩)).2).asIdeal) ℓ := by
      have h4 := (charP_quotient_primeTransport eB (Submission.NeukirchUchida.primeOf (K₁ := K₂)
        (K₁' := Ω) (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).1
        (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).2) ℓ).mp h₂
      rw [primeOf_baseChange B.L eB hB
        (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).1
        ((baseChangePlaceEquiv B.L eB hB).symm
          (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩)).2
        (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).2] at h4
      exact h4
    exact h₃
  localDegree := fun A' => by
    haveI : IsSepClosure ↥A.L Ω := ‹_›
    haveI : IsSepClosure ↥B.L Ω := ‹_›
    have h₁ : (Submission.NeukirchUchida.primeOf (K₁ := ↥A.L) (K₁' := Ω) A'.1
          A'.2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf (K₁ := ↥A.L) (K₁' := Ω) A'.1
            A'.2).asIdeal.ramificationIdx ℤ =
        (Submission.NeukirchUchida.primeOf (K₁ := K₁) (K₁' := Ω) A'.1
          (baseChangePlaceEquiv A.L eA hA A').2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf (K₁ := K₁) (K₁' := Ω) A'.1
            (baseChangePlaceEquiv A.L eA hA A').2).asIdeal.ramificationIdx ℤ := by
      rw [← primeOf_baseChange A.L eA hA A'.1 A'.2 (baseChangePlaceEquiv A.L eA hA A').2]
      exact localDegree_primeTransport_of_ringEquiv eA _
    have h₂ := a.localDegree ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩
    have h₃ : (Submission.NeukirchUchida.primeOf (K₁ := K₂) (K₁' := Ω)
          (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).1
          (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf (K₁ := K₂) (K₁' := Ω)
            (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).1
            (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).2).asIdeal.ramificationIdx ℤ =
        (Submission.NeukirchUchida.primeOf (K₁ := ↥B.L) (K₁' := Ω)
          (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).1
          ((baseChangePlaceEquiv B.L eB hB).symm
            (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩)).2).asIdeal.inertiaDeg ℤ *
          (Submission.NeukirchUchida.primeOf (K₁ := ↥B.L) (K₁' := Ω)
            (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).1
            ((baseChangePlaceEquiv B.L eB hB).symm
              (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩)).2).asIdeal.ramificationIdx ℤ := by
      have h4 := localDegree_primeTransport_of_ringEquiv eB (Submission.NeukirchUchida.primeOf
        (K₁ := K₂) (K₁' := Ω)
        (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).1
        (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).2)
      rw [primeOf_baseChange B.L eB hB
        (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).1
        ((baseChangePlaceEquiv B.L eB hB).symm
          (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩)).2
        (a.placeMap ⟨A'.1, (baseChangePlaceEquiv A.L eA hA A').2⟩).2] at h4
      exact h4.symm
    exact h₁.trans (h₂.trans h₃)

end BaseChange

/-- **The local correspondence transported along an isomorphism of separable closures**, with the
place map exposed: the transported place map is `a.placeMap` composed with the inverse of the place
bijection `placeCongr e`, i.e. the place of `Ω` obtained by pulling back along `e.symm`. -/
theorem localCorrespondence_conj {K₁ K₂ K₁' K₂' Ω : Type*} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Field Ω] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [Algebra K₂ Ω] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] [IsSepClosure K₂ Ω]
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (a : LocalCorrespondence ϕ) (e : K₂' ≃ₐ[K₂] Ω)
    (ψ : Gal(K₁'/K₁) ≃* Gal(Ω/K₂))
    (hψ : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g)) :
    ∃ a' : LocalCorrespondence ψ,
      ∀ A : FinitePlaceOf K₁ K₁',
        (a'.placeMap A).1 = (a.placeMap A).1.comap (e.symm : Ω →+* K₂') := by

  classical
  -- `ψ` is the composite of `ϕ` with the conjugation isomorphism induced by `e`
  have hψhom : (ψ : Gal(K₁'/K₁) →* Gal(Ω/K₂)) =
      (algEquivConjHom e).comp (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) :=
  MonoidHom.ext fun g => hψ g
  -- the inverse conjugation carries `ψ g` back to `ϕ g`
  have hplace : ∀ g : Gal(K₁'/K₁), algEquivConjHom e.symm (ψ g) = ϕ g := by
    intro g
    rw [hψ g]
    exact algEquivConjHom_symm_apply_apply e (ϕ g)
  -- the prime below a place is unchanged by the transport along `e`
  have hprime : ∀ A : FinitePlaceOf K₁ K₁',
      Submission.NeukirchUchida.primeOf ((placeCongr e).symm (a.placeMap A)).1
          ((placeCongr e).symm (a.placeMap A)).2 =
        Submission.NeukirchUchida.primeOf (a.placeMap A).1 (a.placeMap A).2 :=
    fun A => primeOf_placeCongr_symm (K := K₂) (K' := K₂') (Ω := Ω) e (a.placeMap A)
  refine ⟨{ placeMap := a.placeMap.trans (placeCongr e).symm
            map_smul := ?_
            map_decomp := ?_
            primeMap := a.primeMap
            primeMap_spec := ?_
            residueChar := ?_
            localDegree := ?_ }, ?_⟩
  · intro g A
    show (placeCongr e).symm (a.placeMap (placeSmul g A)) =
      placeSmul₂ (K₂ := K₂) (K₂' := Ω) (ψ g) ((placeCongr e).symm (a.placeMap A))
    rw [a.map_smul g A]
    have h := placeCongr_symm_placeSmul₂ (K := K₂) (K' := K₂') (Ω := Ω) e (ψ g) (a.placeMap A)
    rw [hplace g] at h
    exact h
  · intro A
    show (Submission.NeukirchUchida.decompositionGroup (K₁ := K₁) (K₁' := K₁') A.1).map
          (ψ : Gal(K₁'/K₁) →* Gal(Ω/K₂)) =
        Submission.NeukirchUchida.decompositionGroup (K₁ := K₂) (K₁' := Ω)
          ((placeCongr e).symm (a.placeMap A)).1
    rw [hψhom]
    rw [← Subgroup.map_map]
    rw [a.map_decomp A]
    have hpc := placeCongr_decomp (K := K₂) (K' := K₂') (Ω := Ω) e
      ((placeCongr e).symm (a.placeMap A))
    rw [Equiv.apply_symm_apply] at hpc
    rw [hpc]
    rw [Subgroup.map_map]
    rw [algEquivConjHom_comp_symm_comp e]
    rw [Subgroup.map_id]
  · intro A
    show a.primeMap (Submission.NeukirchUchida.primeOf A.1 A.2) =
      Submission.NeukirchUchida.primeOf ((placeCongr e).symm (a.placeMap A)).1
        ((placeCongr e).symm (a.placeMap A)).2
    rw [hprime A]
    exact a.primeMap_spec A
  · intro A ℓ h
    show CharP (NumberField.RingOfIntegers K₂ ⧸
        (Submission.NeukirchUchida.primeOf ((placeCongr e).symm (a.placeMap A)).1
          ((placeCongr e).symm (a.placeMap A)).2).asIdeal) ℓ
    rw [hprime A]
    exact a.residueChar A ℓ h
  · intro A
    show ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ) *
        ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ) =
      ((Submission.NeukirchUchida.primeOf ((placeCongr e).symm (a.placeMap A)).1
          ((placeCongr e).symm (a.placeMap A)).2).asIdeal.inertiaDeg ℤ) *
        ((Submission.NeukirchUchida.primeOf ((placeCongr e).symm (a.placeMap A)).1
          ((placeCongr e).symm (a.placeMap A)).2).asIdeal.ramificationIdx ℤ)
    rw [hprime A]
    exact a.localDegree A
  · intro A
    exact coe_placeCongr_symm (K := K₂) (K' := K₂') (Ω := Ω) e (a.placeMap A)


/-! ## The change of the base field's model for intermediate fields and levels -/

section LevelBaseChange

variable {k k' Ω : Type*} [Field k] [Field k'] [Field Ω] [Algebra k Ω] [Algebra k' Ω]

/-- **The same intermediate field, viewed over the other model of the base field.**

If `e : k ≃+* k'` identifies the two models of the base field (compatibly with the algebra maps,
`he`), then a level `L` of `Ω/k'` is also a level of `Ω/k`, with the same carrier. -/
def levelBaseChange (e : k ≃+* k') (he : ∀ x : k, (algebraMap k' Ω) (e x) = algebraMap k Ω x)
    (L : IntermediateField k' Ω) : IntermediateField k Ω where
  carrier := L
  mul_mem' := L.mul_mem'
  one_mem' := L.one_mem'
  add_mem' := L.add_mem'
  zero_mem' := L.zero_mem'
  inv_mem' := L.inv_mem'
  algebraMap_mem' x := by
    rw [← he x]
    exact L.algebraMap_mem (e x)

@[simp] theorem levelBaseChange_carrier (e : k ≃+* k')
    (he : ∀ x : k, (algebraMap k' Ω) (e x) = algebraMap k Ω x) (L : IntermediateField k' Ω) :
    (levelBaseChange e he L : Set Ω) = (L : Set Ω) := rfl

@[simp] theorem levelBaseChange_mem (e : k ≃+* k')
    (he : ∀ x : k, (algebraMap k' Ω) (e x) = algebraMap k Ω x) (L : IntermediateField k' Ω)
    (x : Ω) : x ∈ levelBaseChange e he L ↔ x ∈ L := Iff.rfl

end LevelBaseChange


/-! ## The level correspondence and the base change -/

section LevelMapBaseChange

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
variable {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Algebra K₁ Ω] [Algebra K₂ Ω] [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]

omit [IsGalois ℚ Ω] in
/-- **The `ϕ`-image of a level is unchanged by a change of the model of the base field.**

The level map `levelMap θ L` of the base-changed isomorphism `θ = baseChangeGalEquiv ... ψ` at a
level `L` over `↥A.L` is the same level of `Ω` as the `ψ`-image of `L` viewed over `K₁`. -/
theorem levelMap_baseChange (A B : NumFieldIn ℚ Ω) [NumberField ↥A.L] [NumberField ↥B.L]
    [IsSepClosure ↥A.L Ω] [IsSepClosure ↥B.L Ω]
    (eA : K₁ ≃+* ↥A.L)
    (hA : ∀ x : K₁, (algebraMap ↥A.L Ω) (eA x) = algebraMap K₁ Ω x) (eB : K₂ ≃+* ↥B.L)
    (hB : ∀ x : K₂, (algebraMap ↥B.L Ω) (eB x) = algebraMap K₂ Ω x)
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (L : IntermediateField ↥A.L Ω) :
    (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L : Set Ω) =
      (levelMap ψ (levelBaseChange eA hA L) : Set Ω) := by
  ext x
  change x ∈ levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L ↔
    x ∈ levelMap ψ (levelBaseChange eA hA L)
  rw [mem_levelMap_iff, mem_levelMap_iff]
  constructor
  · intro h g₀ hg₀
    have hg : ∀ y : ↥L, (galEquivOfBaseEquiv A.L eA hA g₀) y = y := fun y => hg₀ y
    have hθ := h (galEquivOfBaseEquiv A.L eA hA g₀) hg
    have hEq : (ψ g₀) x = (baseChangeGalEquiv A B eA hA eB hB ψ
        (galEquivOfBaseEquiv A.L eA hA g₀)) x := by
      simp only [baseChangeGalEquiv, MulEquiv.trans_apply, galEquivOfBaseEquiv_apply_coe,
        MulEquiv.symm_apply_apply]
    rw [hEq]
    exact hθ
  · intro h g hg
    have hg' : ∀ y : ↥(levelBaseChange eA hA L),
        ((galEquivOfBaseEquiv A.L eA hA).symm g) y = y := fun y => hg y
    have hψ := h ((galEquivOfBaseEquiv A.L eA hA).symm g) hg'
    have hEq : (baseChangeGalEquiv A B eA hA eB hB ψ g) x =
        (ψ ((galEquivOfBaseEquiv A.L eA hA).symm g)) x := by
      simp only [baseChangeGalEquiv, MulEquiv.trans_apply, galEquivOfBaseEquiv_apply_coe]
    rw [hEq]
    exact hψ

end LevelMapBaseChange



/-- **A ring isomorphism between two intermediate fields of `Ω` with the same carrier.** -/
noncomputable def ringEquivOfCarrierEq {K K' Ω : Type*} [Field K] [Field K'] [Field Ω]
    [Algebra K Ω] [Algebra K' Ω] (L : IntermediateField K Ω) (L' : IntermediateField K' Ω)
    (h : (L : Set Ω) = (L' : Set Ω)) : ↥L ≃+* ↥L' where
  toFun x := ⟨x.1, by
    have hx : (x.1 : Ω) ∈ (L : Set Ω) := x.2
    rw [h] at hx
    exact hx⟩
  invFun y := ⟨y.1, by
    have hy : (y.1 : Ω) ∈ (L' : Set Ω) := y.2
    rw [← h] at hy
    exact hy⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl

@[simp] theorem ringEquivOfCarrierEq_apply_coe {K K' Ω : Type*} [Field K] [Field K'] [Field Ω]
    [Algebra K Ω] [Algebra K' Ω] (L : IntermediateField K Ω) (L' : IntermediateField K' Ω)
    (h : (L : Set Ω) = (L' : Set Ω)) (x : ↥L) :
    ((ringEquivOfCarrierEq L L' h x : ↥L') : Ω) = x.1 := rfl

@[simp] theorem ringEquivOfCarrierEq_symm_apply_coe {K K' Ω : Type*} [Field K] [Field K'] [Field Ω]
    [Algebra K Ω] [Algebra K' Ω] (L : IntermediateField K Ω) (L' : IntermediateField K' Ω)
    (h : (L : Set Ω) = (L' : Set Ω)) (y : ↥L') :
    (((ringEquivOfCarrierEq L L' h).symm y : ↥L) : Ω) = y.1 := rfl


/-! ## The base change of the Frobenius correspondence -/

section FrobeniusBaseChange

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
variable {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Algebra K₁ Ω] [Algebra K₂ Ω] [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]

omit [IsGalois ℚ Ω] in
/-- **The level isomorphism between the two models of the base field is compatible with the base
fields.**  The identity identification of `↥L` with `↥(levelBaseChange eA hA L)` carries the
embedded copy of `↥A.L` onto the embedded copy of `K₁`. -/
theorem mapsBaseLevel_levelBaseChange (A : NumFieldIn ℚ Ω) [NumberField ↥A.L]
    (eA : K₁ ≃+* ↥A.L) (hA : ∀ x : K₁, (algebraMap ↥A.L Ω) (eA x) = algebraMap K₁ Ω x)
    (L : IntermediateField ↥A.L Ω) :
    MapsBaseLevel L (levelBaseChange eA hA L)
      (RingEquiv.refl ↥L : ↥L ≃+* ↥(levelBaseChange eA hA L)) := by
  constructor
  · intro a
    refine ⟨eA.symm a, ?_⟩
    apply Subtype.ext
    show (algebraMap ↥A.L Ω a : Ω) = algebraMap K₁ Ω (eA.symm a)
    rw [← hA (eA.symm a), RingEquiv.apply_symm_apply]
  · intro b
    refine ⟨eA b, ?_⟩
    apply Subtype.ext
    show algebraMap K₁ Ω b = (algebraMap ↥A.L Ω (eA b) : Ω)
    rw [hA b]

omit [IsGalois ℚ Ω] in
/-- **The two corresponding levels of the two models of the base field are compatible.** -/
theorem mapsBaseLevel_levelMap_baseChange (A B : NumFieldIn ℚ Ω) [NumberField ↥A.L] [NumberField ↥B.L]
    [IsSepClosure ↥A.L Ω] [IsSepClosure ↥B.L Ω]
    (eA : K₁ ≃+* ↥A.L) (hA : ∀ x : K₁, (algebraMap ↥A.L Ω) (eA x) = algebraMap K₁ Ω x)
    (eB : K₂ ≃+* ↥B.L) (hB : ∀ x : K₂, (algebraMap ↥B.L Ω) (eB x) = algebraMap K₂ Ω x)
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (L : IntermediateField ↥A.L Ω) :
    MapsBaseLevel (levelMap ψ (levelBaseChange eA hA L))
      (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
      (ringEquivOfCarrierEq _ _ (levelMap_baseChange A B eA hA eB hB ψ L).symm) := by
  constructor
  · intro a
    refine ⟨eB a, ?_⟩
    apply Subtype.ext
    show (algebraMap K₂ Ω a : Ω) = (algebraMap ↥B.L Ω (eB a) : Ω)
    rw [hB a]
  · intro b
    refine ⟨eB.symm b, ?_⟩
    apply Subtype.ext
    show (algebraMap ↥B.L Ω b : Ω) = (algebraMap K₂ Ω (eB.symm b) : Ω)
    rw [← hB (eB.symm b), RingEquiv.apply_symm_apply]


end FrobeniusBaseChange


/-! ## Changing the model of the base field

The level-pair bridge `NK.Reconstruct.LevelIsoInputOfLocalCorrespondence` is stated for base
fields which are *intermediate fields of `Ω` over `ℚ`*.  The reconstruction step of the target
theorem, however, is stated for the number field `K` with its own (arbitrary) embedding into `Ω`.
The lemmas of this section transport the whole level calculus (finiteness, normality, the level
correspondence `levelMap`) along the identification of `K` with its image `L₀` in `Ω`.

Here `k` is the bottom field (`ℚ` in the applications), `L₀ ⊆ Ω` is a level over `k` identified
with the field `K` by `e : K ≃+* ↥L₀`. -/

section ModelChange

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
variable {K : Type*} [Field K] [Algebra k K] [Algebra K Ω]
variable (L₀ : IntermediateField k Ω) (e : K ≃+* ↥L₀)
  (he : ∀ x : K, (algebraMap ↥L₀ Ω) (e x) = algebraMap K Ω x)
include L₀ e he

/-- The compatibility of the identification `e : K ≃+* ↥L₀` with the two embeddings into `Ω`, read
in the reverse direction. -/
theorem he_symm (x : ↥L₀) : (algebraMap K Ω) (e.symm x) = algebraMap ↥L₀ Ω x := by
  rw [← he (e.symm x), RingEquiv.apply_symm_apply]

/-- **A level over `↥L₀` viewed over `K`**: the same set of elements of `Ω`. -/
noncomputable def levelModel (M : IntermediateField ↥L₀ Ω) : IntermediateField K Ω :=
  levelBaseChange e he M

@[simp] theorem levelModel_carrier (M : IntermediateField ↥L₀ Ω) :
    (levelModel L₀ e he M : Set Ω) = (M : Set Ω) := rfl

/-- The reverse of `levelModel`. -/
noncomputable def levelModel' (N : IntermediateField K Ω) : IntermediateField ↥L₀ Ω :=
  levelBaseChange e.symm (he_symm L₀ e he) N

@[simp] theorem levelModel'_carrier (N : IntermediateField K Ω) :
    (levelModel' L₀ e he N : Set Ω) = (N : Set Ω) := rfl

/-- **`Ω` is a separable closure of the image `L₀` of `K`.** -/
theorem isSepClosure_model [IsSepClosure K Ω] : IsSepClosure ↥L₀ Ω :=
  NK.ReconstructField.isSepClosure_of_isSepClosed_of_ringEquiv e (by
    ext x
    exact (he_symm L₀ e he x).symm)

/-- **The image of a number field is a number field.** -/
theorem numberField_model [NumberField K] : NumberField ↥L₀ :=
  NumberField.of_ringEquiv K ↥L₀ e

/-- **Finiteness of a level is insensitive to the model of the base field.** -/
theorem finiteDimensional_model (M : IntermediateField ↥L₀ Ω) [FiniteDimensional ↥L₀ M] :
    FiniteDimensional K (levelModel L₀ e he M) :=
  Commons.Algebra.Module.moduleFinite_of_ringEquiv (B := ↥L₀) (E := ↥M) (B₀ := K)
    (E₀ := ↥(levelModel L₀ e he M)) e.symm (RingEquiv.refl ↥M) (fun x => by
      apply Subtype.ext
      show (algebraMap ↥L₀ Ω) x = (algebraMap K Ω) (e.symm x)
      rw [he_symm L₀ e he x])

/-- **Finiteness of a level is insensitive to the model of the base field** (the other
direction). -/
theorem finiteDimensional_model_symm (M : IntermediateField ↥L₀ Ω)
    [FiniteDimensional K (levelModel L₀ e he M)] : FiniteDimensional ↥L₀ M :=
  Commons.Algebra.Module.moduleFinite_of_ringEquiv (B := K) (E := ↥(levelModel L₀ e he M))
    (B₀ := ↥L₀) (E₀ := ↥M) e (RingEquiv.refl ↥(levelModel L₀ e he M)) (fun x => by
      apply Subtype.ext
      show (algebraMap K Ω) x = (algebraMap ↥L₀ Ω) (e x)
      rw [he x])

/-- **The identification `Gal(Ω/K) ≃* Gal(Ω/↥L₀)`**, as maps of `Ω`. -/
noncomputable def galModel : Gal(Ω/K) ≃* Gal(Ω/↥L₀) :=
  galEquivOfBaseEquiv L₀ e he

@[simp] theorem galModel_apply_coe (σ : Gal(Ω/K)) :
    ((galModel L₀ e he σ : Ω ≃ₐ[↥L₀] Ω) : Ω → Ω) = σ := rfl

@[simp] theorem galModel_symm_apply_coe (τ : Gal(Ω/↥L₀)) :
    (((galModel L₀ e he).symm τ : Ω ≃ₐ[K] Ω) : Ω → Ω) = τ := rfl

/-- **Normality of a level is insensitive to the model of the base field.** -/
theorem normal_model [Normal K Ω] [Normal ↥L₀ Ω] (M : IntermediateField ↥L₀ Ω) [Normal ↥L₀ M] :
    Normal K (levelModel L₀ e he M) := by
  rw [IntermediateField.normal_iff_forall_map_le' (F := K) (L := Ω)
    (K := levelModel L₀ e he M)]
  intro σ
  have hσ := (IntermediateField.normal_iff_forall_map_le' (F := ↥L₀) (L := Ω) (K := M)).mp
    (inferInstanceAs (Normal ↥L₀ M)) (galModel L₀ e he σ)
  intro x hx
  rw [IntermediateField.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hτ : (galModel L₀ e he σ) y ∈ M :=
    hσ (by rw [IntermediateField.mem_map]; exact ⟨y, hy, rfl⟩)
  rw [← hyx]
  exact hτ

/-- **A level over the image of `K` viewed over `K`**: the same set of elements of `Ω`. -/
theorem levelModel_mem (M : IntermediateField ↥L₀ Ω) (x : Ω) :
    x ∈ levelModel L₀ e he M ↔ x ∈ M := Iff.rfl

/-- **The identification of the Galois groups of the two models of the base field is a
homeomorphism** for the Krull topologies.  The map is the identity on underlying automorphisms of
`Ω`, and the Krull topology on `Gal(Ω/K)` has as a neighbourhood basis of `1` the fixing subgroups
of the finite levels over `K`, which correspond to those over `↥L₀`. -/
theorem isHomeomorph_galModel [IsSepClosure k Ω] [IsSepClosure K Ω] :
    IsHomeomorph (galModel L₀ e he) := by
  haveI : Algebra.IsAlgebraic ↥L₀ Ω :=
    Algebra.IsAlgebraic.tower_top (K := k) (L := ↥L₀) (A := Ω)
  haveI : Algebra.IsIntegral ↥L₀ Ω := Algebra.IsAlgebraic.isIntegral
  haveI : T2Space Gal(Ω/↥L₀) := krullTopology_t2
  haveI : CompactSpace Gal(Ω/K) := inferInstance
  refine (isHomeomorph_iff_continuous_bijective).mpr
    ⟨?_, (galModel L₀ e he).bijective⟩
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff ↥L₀ Ω] at hU
  obtain ⟨E, hEfd, hEU⟩ := hU
  haveI : FiniteDimensional ↥L₀ E := hEfd
  refine Filter.mem_of_superset ?_ (Set.preimage_mono hEU)
  have hpre : (galModel L₀ e he : Gal(Ω/K) → Gal(Ω/↥L₀)) ⁻¹'
      (E.fixingSubgroup : Set Gal(Ω/↥L₀)) =
      ((levelModel L₀ e he E).fixingSubgroup : Set Gal(Ω/K)) := by
    ext σ
    simp only [Set.mem_preimage]
    change ((galModel L₀ e he) σ : Ω ≃ₐ[↥L₀] Ω) ∈ E.fixingSubgroup ↔
      σ ∈ (levelModel L₀ e he E).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx; exact h x hx
    · intro h x hx; exact h x hx
  rw [hpre]
  haveI : FiniteDimensional K (levelModel L₀ e he E) := finiteDimensional_model L₀ e he E
  refine IsOpen.mem_nhds (IntermediateField.fixingSubgroup_isOpen (levelModel L₀ e he E)) ?_
  change (1 : Gal(Ω/K)) ∈ (levelModel L₀ e he E).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rfl

end ModelChange


/-! ## The prime of a level: independence of the model of the base field -/

section PrimeLevelModel

variable {k k' Ω : Type*} [Field k] [Field k'] [Field Ω] [Algebra k Ω] [Algebra k' Ω]

/-- **The prime of a level below a place depends only on the place and the *set* of elements of the
level**, not on the model of the base field: it is transported by the identity isomorphism of the
two models of the level. -/
theorem primeTransport_ringEquivOfCarrierEq (A : ValuationSubring Ω) (L : IntermediateField k Ω)
    (L' : IntermediateField k' Ω) (h : (L : Set Ω) = (L' : Set Ω))
    [NumberField k] [IsSepClosure k Ω] [NumberField k'] [IsSepClosure k' Ω]
    [NumberField ↥L] [NumberField ↥L']
    (hA : A.comap (algebraMap ↥L Ω) ≠ ⊤) (hA' : A.comap (algebraMap ↥L' Ω) ≠ ⊤) :
    primeTransport (ringEquivOfCarrierEq L L' h) (primeOfLevel A L hA) =
      primeOfLevel A L' hA' := by
  apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥L')
  rw [NK.Reconstruct.valuationSubringAtPrime_primeTransport (ringEquivOfCarrierEq L L' h)
      (primeOfLevel A L hA),
    ← primeOfLevel_spec A L hA, ← primeOfLevel_spec A L' hA']
  rw [ValuationSubring.comap_comap]
  congr 1

end PrimeLevelModel



/-! ## The base change of the Frobenius correspondence -/

section FrobBaseChangeGen

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
variable {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Algebra K₁ Ω] [Algebra K₂ Ω] [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]

/-- **The base-change isomorphism `Gal(Ω/↥A.L) ≃* Gal(Ω/↥B.L)` is a homeomorphism** for the Krull
topologies, since it is the identity on underlying automorphisms. -/
theorem isHomeomorph_baseChangeGalEquiv (A B : NumFieldIn ℚ Ω) [IsSepClosure ↥A.L Ω]
    [IsSepClosure ↥B.L Ω]
    (eA : K₁ ≃+* ↥A.L) (hA : ∀ x : K₁, (algebraMap ↥A.L Ω) (eA x) = algebraMap K₁ Ω x)
    (eB : K₂ ≃+* ↥B.L) (hB : ∀ x : K₂, (algebraMap ↥B.L Ω) (eB x) = algebraMap K₂ Ω x)
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ) :
    IsHomeomorph (baseChangeGalEquiv A B eA hA eB hB ψ) := by
  have h1 : IsHomeomorph (galEquivOfBaseEquiv A.L eA hA) :=
    isHomeomorph_galModel (K := K₁) (Ω := Ω) A.L eA hA
  have h2 : IsHomeomorph (galEquivOfBaseEquiv B.L eB hB) :=
    isHomeomorph_galModel (K := K₂) (Ω := Ω) B.L eB hB
  have h3 : IsHomeomorph (ψ.trans (galEquivOfBaseEquiv B.L eB hB)) :=
    isHomeomorph_trans' ψ (galEquivOfBaseEquiv B.L eB hB) hψ h2
  exact isHomeomorph_trans' (galEquivOfBaseEquiv A.L eA hA).symm
    (ψ.trans (galEquivOfBaseEquiv B.L eB hB)) (isHomeomorph_symm' _ h1) h3

/-- **The base change of the Frobenius correspondence.**

Let `ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)` and let `A`, `B` be number-field levels of `Ω/ℚ` whose underlying
fields are identified with `K₁`, `K₂` by `eA`, `eB`.  A Frobenius correspondence for `ψ` transports
to a Frobenius correspondence for the base-changed isomorphism
`baseChangeGalEquiv A B eA hA eB hB ψ`. -/
theorem frobeniusCorrespondencePlace_baseChange (A B : NumFieldIn ℚ Ω) [IsSepClosure ↥A.L Ω]
    [IsSepClosure ↥B.L Ω]
    (eA : K₁ ≃+* ↥A.L) (hA : ∀ x : K₁, (algebraMap ↥A.L Ω) (eA x) = algebraMap K₁ Ω x)
    (eB : K₂ ≃+* ↥B.L) (hB : ∀ x : K₂, (algebraMap ↥B.L Ω) (eB x) = algebraMap K₂ Ω x)
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ) (a : LocalCorrespondence ψ)
    (b : FrobeniusCorrespondencePlace ψ hψ a) :
    FrobeniusCorrespondencePlace (baseChangeGalEquiv A B eA hA eB hB ψ)
      (isHomeomorph_baseChangeGalEquiv A B eA hA eB hB ψ hψ)
      (localCorrespondence_baseChange A B eA hA eB hB ψ a) := by
  intro L hfdL hnormL hnfL hnfLθ hnormLθ A' g hg
  haveI : FiniteDimensional ↥A.L L := hfdL
  haveI : Normal ↥A.L L := hnormL
  haveI : NumberField ↥L := hnfL
  haveI : NumberField ↥(levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L) := hnfLθ
  haveI : Normal ↥B.L (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L) := hnormLθ
  haveI hfdθ : FiniteDimensional ↥B.L (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L) :=
    finiteDimensional_levelMap (isHomeomorph_baseChangeGalEquiv A B eA hA eB hB ψ hψ) L
  -- the ψ-side level
  let M : IntermediateField K₁ Ω := levelBaseChange eA hA L
  haveI hfdM : FiniteDimensional K₁ M := finiteDimensional_model A.L eA hA L
  haveI hnfM : NumberField ↥M := hnfL
  haveI hnormM : Normal K₁ M := normal_model A.L eA hA L
  -- the ψ-side place and Galois element
  let A₀ : FinitePlaceOf K₁ Ω := baseChangePlaceEquiv A.L eA hA A'
  let g₀ : Gal(Ω/K₁) := (galModel A.L eA hA).symm g
  have hg₀eq : (g₀ : Ω → Ω) = (g : Ω → Ω) := rfl
  -- the level isomorphism between the two models of the ψ-side level
  have hmap1 : MapsBaseLevel M L (ringEquivOfCarrierEq M L rfl) := by
    constructor
    · intro a'
      refine ⟨eA a', ?_⟩
      apply Subtype.ext
      show (algebraMap K₁ Ω a' : Ω) = (algebraMap ↥A.L Ω (eA a') : Ω)
      rw [hA a']
    · intro b'
      refine ⟨eA.symm b', ?_⟩
      apply Subtype.ext
      show (algebraMap ↥A.L Ω b' : Ω) = (algebraMap K₁ Ω (eA.symm b') : Ω)
      rw [← hA (eA.symm b'), RingEquiv.apply_symm_apply]
  -- step D: the Frobenius statement is transported to the ψ-side model of the level
  have hgM : NK.Chebotarev.IsFrobAt (primeOfLevel A₀.1 M (comap_level_ne_top A₀.2 M))
      (AlgEquiv.restrictNormalHom M g₀) := by
    refine (isFrobAt_primeTransport_iff (K₁ := K₁) (K₂ := ↥A.L) (K₁' := Ω) (K₂' := Ω)
      (L₁ := M) (L₂ := L) (τ := ringEquivOfCarrierEq M L rfl) hmap1
      (AlgEquiv.restrictNormalHom M g₀) (primeOfLevel A₀.1 M (comap_level_ne_top A₀.2 M))).mpr ?_
    have hp : primeTransport (ringEquivOfCarrierEq M L rfl)
        (primeOfLevel A₀.1 M (comap_level_ne_top A₀.2 M)) =
        primeOfLevel A'.1 L (comap_level_ne_top A'.2 L) :=
      primeTransport_ringEquivOfCarrierEq (A := A₀.1) (L := M) (L' := L) (h := rfl)
        (comap_level_ne_top A₀.2 M) (comap_level_ne_top A'.2 L)
    have hconj : conjAlgEquiv (ringEquivOfCarrierEq M L rfl) hmap1
        (AlgEquiv.restrictNormalHom M g₀) = AlgEquiv.restrictNormalHom L g := by
      refine AlgEquiv.ext (fun x => Subtype.ext rfl)
    rw [hp, hconj]
    exact hg
  -- step E: apply the Frobenius correspondence for `ψ`
  haveI : NumberField ↥(levelMap ψ M) := numberField_levelMap hψ M
  haveI : Normal K₂ (levelMap ψ M) := normal_levelMap hψ M
  have hbM : NK.Chebotarev.IsFrobAt
      (primeOfLevel (a.placeMap A₀).1 (levelMap ψ M)
        (comap_level_ne_top (a.placeMap A₀).2 (levelMap ψ M)))
      (AlgEquiv.restrictNormalHom (levelMap ψ M) (ψ g₀)) :=
    b M A₀ g₀ hgM
  haveI hfdψM : FiniteDimensional K₂ ↥(levelMap ψ M) := finiteDimensional_levelMap hψ M
  -- step F: transport back to the θ-side
  obtain hres : NK.Chebotarev.IsFrobAt
      (primeTransport (ringEquivOfCarrierEq (levelMap ψ M)
        (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
        (levelMap_baseChange A B eA hA eB hB ψ L).symm)
        (primeOfLevel (a.placeMap A₀).1 (levelMap ψ M)
          (comap_level_ne_top (a.placeMap A₀).2 (levelMap ψ M))))
      (conjAlgEquiv (ringEquivOfCarrierEq (levelMap ψ M)
        (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
        (levelMap_baseChange A B eA hA eB hB ψ L).symm)
        (mapsBaseLevel_levelMap_baseChange A B eA hA eB hB ψ L)
        (AlgEquiv.restrictNormalHom (levelMap ψ M) (ψ g₀))) :=
    (isFrobAt_primeTransport_iff (K₁ := K₂) (K₂ := ↥B.L) (K₁' := Ω) (K₂' := Ω)
      (L₁ := levelMap ψ M)
      (L₂ := levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
      (τ := ringEquivOfCarrierEq (levelMap ψ M)
        (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
        (levelMap_baseChange A B eA hA eB hB ψ L).symm)
      (mapsBaseLevel_levelMap_baseChange A B eA hA eB hB ψ L)
      (AlgEquiv.restrictNormalHom (levelMap ψ M) (ψ g₀))
      (primeOfLevel (a.placeMap A₀).1 (levelMap ψ M)
        (comap_level_ne_top (a.placeMap A₀).2 (levelMap ψ M)))).mp hbM
  have hp2 : primeTransport (ringEquivOfCarrierEq (levelMap ψ M)
        (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
        (levelMap_baseChange A B eA hA eB hB ψ L).symm)
        (primeOfLevel (a.placeMap A₀).1 (levelMap ψ M)
          (comap_level_ne_top (a.placeMap A₀).2 (levelMap ψ M))) =
      primeOfLevel ((localCorrespondence_baseChange A B eA hA eB hB ψ a).placeMap A').1
        (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
        (comap_level_ne_top ((localCorrespondence_baseChange A B eA hA eB hB ψ a).placeMap A').2
          (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)) :=
    primeTransport_ringEquivOfCarrierEq (A := (a.placeMap A₀).1) (L := levelMap ψ M)
      (L' := levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
      (h := (levelMap_baseChange A B eA hA eB hB ψ L).symm)
      (comap_level_ne_top (a.placeMap A₀).2 (levelMap ψ M))
      (comap_level_ne_top ((localCorrespondence_baseChange A B eA hA eB hB ψ a).placeMap A').2
        (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L))
  have hconj2 : conjAlgEquiv (ringEquivOfCarrierEq (levelMap ψ M)
        (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
        (levelMap_baseChange A B eA hA eB hB ψ L).symm)
        (mapsBaseLevel_levelMap_baseChange A B eA hA eB hB ψ L)
        (AlgEquiv.restrictNormalHom (levelMap ψ M) (ψ g₀)) =
      AlgEquiv.restrictNormalHom (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
        (baseChangeGalEquiv A B eA hA eB hB ψ g) := by
    refine AlgEquiv.ext (fun x => Subtype.ext ?_)
    have hf : ((baseChangeGalEquiv A B eA hA eB hB ψ g : Ω ≃ₐ[↥B.L] Ω) : Ω → Ω)
        = ((ψ g₀ : Ω ≃ₐ[K₂] Ω) : Ω → Ω) := baseChangeGalEquiv_apply_coe A B eA hA eB hB ψ g
    rw [AlgEquiv.restrictNormalHom_apply, hf]
    have h1 : conjAlgEquiv (ringEquivOfCarrierEq (levelMap ψ M)
        (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
        (levelMap_baseChange A B eA hA eB hB ψ L).symm)
        (mapsBaseLevel_levelMap_baseChange A B eA hA eB hB ψ L)
        (AlgEquiv.restrictNormalHom (levelMap ψ M) (ψ g₀)) x =
        (ringEquivOfCarrierEq (levelMap ψ M)
          (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
          (levelMap_baseChange A B eA hA eB hB ψ L).symm)
          ((AlgEquiv.restrictNormalHom (levelMap ψ M) (ψ g₀))
            ((ringEquivOfCarrierEq (levelMap ψ M)
              (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L)
              (levelMap_baseChange A B eA hA eB hB ψ L).symm).symm x)) :=
      conjAlgEquiv_apply _ _ _ _
    rw [h1, ringEquivOfCarrierEq_apply_coe, AlgEquiv.restrictNormalHom_apply,
      ringEquivOfCarrierEq_symm_apply_coe]
  rw [hp2, hconj2] at hres
  exact hres

end FrobBaseChangeGen

section LevelMapCongr

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
variable {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Algebra K₁ Ω] [Algebra K₂ Ω] [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]

omit [IsGalois ℚ Ω] in
/-- **The level correspondence depends only on the set of elements of the level.** -/
theorem levelMap_congr {ϕ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)} {L L' : IntermediateField K₁ Ω}
    (h : (L : Set Ω) = (L' : Set Ω)) : levelMap ϕ L = levelMap ϕ L' := by
  unfold levelMap
  congr 1
  have hsub : L.fixingSubgroup = L'.fixingSubgroup := by
    ext g
    rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hg x hx
      have hx' : x ∈ (L : Set Ω) := by rw [h]; exact hx
      exact hg x hx'
    · intro hg x hx
      have hx' : x ∈ (L' : Set Ω) := by rw [← h]; exact hx
      exact hg x hx'
  rw [hsub]

end LevelMapCongr

section LevelIsoBaseChange

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
variable {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Algebra K₁ Ω] [Algebra K₂ Ω] [IsSepClosure K₁ Ω] [IsSepClosure K₂ Ω]

/-- **The base change of the level-wise weak Neukirch–Uchida input.**

If every level over `↥A.L` is isomorphic to its image under the base-changed isomorphism
`θ = baseChangeGalEquiv A B eA hA eB hB ψ`, then every level over `K₁` is isomorphic to its image
under `ψ`. -/
theorem levelIsoInput_baseChange (A B : NumFieldIn ℚ Ω) [IsSepClosure ↥A.L Ω]
    [IsSepClosure ↥B.L Ω]
    (eA : K₁ ≃+* ↥A.L) (hA : ∀ x : K₁, (algebraMap ↥A.L Ω) (eA x) = algebraMap K₁ Ω x)
    (eB : K₂ ≃+* ↥B.L) (hB : ∀ x : K₂, (algebraMap ↥B.L Ω) (eB x) = algebraMap K₂ Ω x)
    (ψ : Gal(Ω/K₁) ≃* Gal(Ω/K₂)) (hψ : IsHomeomorph ψ)
    (hlev : NK.ReconstructField.LevelIsoInput (baseChangeGalEquiv A B eA hA eB hB ψ)
      (isHomeomorph_baseChangeGalEquiv A B eA hA eB hB ψ hψ)) :
    NK.ReconstructField.LevelIsoInput ψ hψ := by
  intro L hfdL
  haveI : FiniteDimensional K₁ L := hfdL
  let L' : IntermediateField ↥A.L Ω := levelModel' A.L eA hA L
  haveI hfdL' : FiniteDimensional ↥A.L L' :=
    Commons.Algebra.Module.moduleFinite_of_ringEquiv (B := K₁) (E := ↥L) (B₀ := ↥A.L)
      (E₀ := ↥L') eA (RingEquiv.refl ↥L) (fun x => by
        apply Subtype.ext
        exact (hA x).symm)
  obtain ⟨σ⟩ := hlev L'
  have hcarrier : (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L' : Set Ω) =
      (levelMap ψ L : Set Ω) := by
    rw [levelMap_baseChange A B eA hA eB hB ψ L']
    exact congrArg (fun S : IntermediateField K₂ Ω => (S : Set Ω))
      (levelMap_congr (ϕ := ψ) (L := levelBaseChange eA hA L') (L' := L) rfl)
  exact ⟨σ.trans (ringEquivOfCarrierEq (levelMap (baseChangeGalEquiv A B eA hA eB hB ψ) L')
    (levelMap ψ L) hcarrier)⟩

end LevelIsoBaseChange

/-! ## The σ-producing step of Neukirch–Uchida from the local correspondence -/

section MainTheorem

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

theorem exists_sigma_of_localCorrespondence {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] [Algebra ℚ K₁'] [IsGalois ℚ K₁']
    [IsSepClosure ℚ K₁'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) (ℓ : ℕ) [Fact ℓ.Prime]
    (hH : NK.Reconstruct.HausRankInput K₁' ℓ)
    (hM : NK.Reconstruct.RankStrictMonoLevelInputGen K₁' ℓ)
    (hR : NK.Reconstruct.ResRankInputGen K₁' ℓ)
    (hc : NK.Reconstruct.ChebotarevInput ℚ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  -- ## Step 1: put both separable closures into the single field `K₁'`
  haveI hstA : IsScalarTower ℚ K₁ K₁' := isScalarTower_rat_of_numberField
  haveI hsepClosed : IsSepClosed K₁' := IsSepClosure.sep_closed ℚ
  haveI halg : Algebra.IsAlgebraic ℚ K₁' := inferInstance
  obtain ⟨ι, hι⟩ := NK.Reconstruct.exists_algebra_isSepClosure (K₂ := K₂) (K₁' := K₁') halg
  letI : Algebra K₂ K₁' := ι.toRingHom.toAlgebra
  haveI hιS : IsSepClosure K₂ K₁' := hι
  -- ## Step 2: the model `A` of `K₁` inside `K₁'`
  let fA : K₁ →ₐ[ℚ] K₁' := baseAlgHom K₁ K₁'
  let eA : K₁ ≃+* ↥fA.fieldRange :=
    (AlgEquiv.ofInjective fA (RingHom.injective (fA : K₁ →+* K₁'))).toRingEquiv
  have hA : ∀ x : K₁, (algebraMap ↥fA.fieldRange K₁') (eA x) = algebraMap K₁ K₁' x := fun x => rfl
  haveI hnfA : NumberField ↥fA.fieldRange := numberField_model fA.fieldRange eA hA
  haveI hfdA : FiniteDimensional ℚ ↥fA.fieldRange := by
    let fL : K₁ →ₗ[ℚ] ↥fA.fieldRange :=
      { toFun := fun x => ⟨fA x, ⟨x, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (map_add fA x y)
        map_smul' := fun q x => Subtype.ext (map_smul fA q x) }
    exact Module.Finite.of_surjective fL
      (fun y => ⟨Classical.choose y.2, Subtype.ext (Classical.choose_spec y.2)⟩)
  haveI hspA : IsSepClosure ↥fA.fieldRange K₁' := isSepClosure_model fA.fieldRange eA hA
  let A : NumFieldIn ℚ K₁' := ⟨fA.fieldRange, hfdA, hnfA⟩
  -- ## Step 3: the model `B` of `K₂` inside `K₁'`
  let eB : K₂ ≃+* ↥ι.fieldRange :=
    (AlgEquiv.ofInjective ι (RingHom.injective (ι : K₂ →+* K₁'))).toRingEquiv
  have hB : ∀ x : K₂, (algebraMap ↥ι.fieldRange K₁') (eB x) = algebraMap K₂ K₁' x := fun x => rfl
  haveI hnfB : NumberField ↥ι.fieldRange := numberField_model ι.fieldRange eB hB
  haveI hfdB : FiniteDimensional ℚ ↥ι.fieldRange := by
    let fL : K₂ →ₗ[ℚ] ↥ι.fieldRange :=
      { toFun := fun x => ⟨ι x, ⟨x, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (map_add ι x y)
        map_smul' := fun q x => Subtype.ext (map_smul ι q x) }
    exact Module.Finite.of_surjective fL
      (fun y => ⟨Classical.choose y.2, Subtype.ext (Classical.choose_spec y.2)⟩)
  haveI hspB : IsSepClosure ↥ι.fieldRange K₁' := isSepClosure_model ι.fieldRange eB hB
  let B : NumFieldIn ℚ K₁' := ⟨ι.fieldRange, hfdB, hnfB⟩
  -- ## Step 4: the conjugate `ψ` of `ϕ` by the isomorphism of separable closures
  let e : K₂' ≃ₐ[K₂] K₁' := IsSepClosure.equiv K₂ K₂' K₁'
  let ψ : Gal(K₁'/K₁) ≃* Gal(K₁'/K₂) :=
    { toFun := fun g => algEquivConjHom e (ϕ g)
      invFun := fun h => ϕ.symm (algEquivConjHom e.symm h)
      left_inv := by
        intro g
        show ϕ.symm (algEquivConjHom e.symm (algEquivConjHom e (ϕ g))) = g
        rw [algEquivConjHom_symm_apply_apply e (ϕ g), MulEquiv.symm_apply_apply]
      right_inv := by
        intro h
        show algEquivConjHom e (ϕ (ϕ.symm (algEquivConjHom e.symm h))) = h
        rw [MulEquiv.apply_symm_apply, algEquivConjHom_apply_apply_symm e h]
      map_mul' := by
        intro g g'
        show algEquivConjHom e (ϕ (g * g')) =
          algEquivConjHom e (ϕ g) * algEquivConjHom e (ϕ g')
        rw [map_mul, map_mul] }
  have hψeq : ∀ g : Gal(K₁'/K₁), ψ g = algEquivConjHom e (ϕ g) := fun g => rfl
  have hψ : IsHomeomorph ψ := by
    have h2 : IsHomeomorph (algEquivConjHom e) := isHomeomorph_algEquivConjHom e
    rw [show ⇑ψ = ⇑(algEquivConjHom e) ∘ ⇑ϕ from rfl]
    exact h2.comp hϕ
  -- ## Step 5: transport the local correspondence and the Frobenius correspondence
  obtain ⟨a', ha'⟩ := localCorrespondence_conj ϕ a e ψ hψeq
  have b' : FrobeniusCorrespondencePlace ψ hψ a' :=
    exists_frobeniusCorrespondence_transport ϕ hϕ a b e ψ hψeq hψ a' ha'
  -- ## Step 6: the level-pair bridge at the base-changed isomorphism
  have hlevθ : NK.ReconstructField.LevelIsoInput
      (baseChangeGalEquiv A B eA hA eB hB ψ)
      (isHomeomorph_baseChangeGalEquiv A B eA hA eB hB ψ hψ) :=
    levelIsoInput_of_localCorrespondence (Ω := K₁') A B ℓ
      (baseChangeGalEquiv A B eA hA eB hB ψ)
      (isHomeomorph_baseChangeGalEquiv A B eA hA eB hB ψ hψ)
      (localCorrespondence_baseChange A B eA hA eB hB ψ a')
      (frobeniusCorrespondencePlace_baseChange A B eA hA eB hB ψ hψ a' b')
      hH hM hR hc
  -- ## Step 7: transport the level-wise input back to `ϕ`
  have hlevψ : NK.ReconstructField.LevelIsoInput ψ hψ :=
    levelIsoInput_baseChange A B eA hA eB hB ψ hψ hlevθ
  have hlevϕ : NK.ReconstructField.LevelIsoInput ϕ hϕ :=
    levelIsoInput_transport ϕ hϕ e ψ hψeq hψ hlevψ
  exact NK.Mine.exists_sigma_of_localCorrespondence ϕ hϕ a hlevϕ

end MainTheorem

end NK.Reconstruct
