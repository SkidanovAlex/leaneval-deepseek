import Mathlib
import Submission.NK.NUV2.ArtinBridge.KummerSUnitField
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_kummerAdjoin
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerField_ramificationIdx_eq_one_of_unit
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.NK.NUV2.ArtinBridge.galRestrict_restrictNormalHom_mem_under
import Submission.NK.NUV2.ArtinBridge.ramificationIdx_eq_one_of_algEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace IsDedekindDomain.HeightOneSpectrum

/-- `q.asIdele` is the prime ideal underlying a height one spectrum.  This is the notation used in
the statement of `NK.NUV2.ArtinBridge.ramificationIdx_eq_one_kummerSUnitField`; the ramification
index is a function of the underlying ideal, so `q.asIdele` stands for the prime ideal `q`
itself. -/
abbrev asIdele {R : Type*} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) :
    Ideal R := v.asIdeal

end IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField
open NumberField IsDedekindDomain

namespace NK.NUV2.ArtinBridge

/-- The canonical action of `Gal(L/K)` on the ring of integers of `L` is the action through
`galRestrict`. -/
theorem smul_ringOfIntegers_eq_galRestrict {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (x : NumberField.RingOfIntegers L) :
    σ • x = galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) σ x := by
  apply NumberField.RingOfIntegers.ext
  have h1 : ((σ • x : NumberField.RingOfIntegers L) : L) = σ (x : L) := rfl
  rw [h1]
  exact (algebraMap_galRestrict_apply (NumberField.RingOfIntegers K) σ x).symm

/-- The `S`-units of `K`. -/
noncomputable abbrev sUnits (K : Type) [Field K] [NumberField K]
    (S : Finset (NK.GlobalCFT.Place K)) : Subgroup Kˣ :=
  NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K))

/-- The `S`-units are local units at every finite place outside `S`. -/
theorem principalIdele_mem_localUnits_of_mem_sUnits {K : Type} [Field K] [NumberField K]
    (S : Finset (NK.GlobalCFT.Place K)) (b : Kˣ) (hb : b ∈ sUnits K S)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : NK.GlobalCFT.Place.ofFinite Q ∉ S) :
    NK.GlobalCFT.Idele.principalIdele K b (NK.GlobalCFT.Place.ofFinite Q) ∈
      NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q) := by
  rw [NK.GlobalCFT.Idele.principalIdele_apply]
  exact (NK.GlobalCFTdeep.mem_TUnits).mp hb (NK.GlobalCFT.Place.ofFinite Q) hQ

open NK.GlobalCFTdeep.SecondInequality.KummerCase in
/-- **The Kummer extension of a local unit is unramified** (universe-polymorphic form of
`KummerCase.kummerField_ramificationIdx_eq_one_of_unit`).

Let `K` be a number field with a primitive `p`-th root of unity `ζ` (`p` prime), `Ω` a separable
closure of `K`, `b ∈ Kˣ` and `L = kummerField p b ⊆ Ω`.  Let `Q` be a prime of `𝓞 K` with `p ∉ Q`
and with `b` a local unit at `Q`.  Then every prime of `𝓞 L` above `Q` is unramified over `Q`. -/
theorem kummerField_ramificationIdx_eq_one_of_unit_poly
    {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (b : Kˣ)
    [FiniteDimensional K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    [NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : (p : NumberField.RingOfIntegers K) ∉ Q.asIdeal)
    (hb : NK.GlobalCFT.Idele.principalIdele K b (NK.GlobalCFT.Place.ofFinite Q) ∈
      NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q)) :
    ∀ q : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ↥(NK.LocalAnabelian.kummerField (K' := Ω) p b)),
      q.asIdeal.LiesOver Q.asIdeal →
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
  classical
  intro q hq
  let Lf : IntermediateField K Ω := NK.LocalAnabelian.kummerField (K' := Ω) p b
  -- ## A chosen `p`-th root of `b` inside `L = kummerField p b`
  obtain ⟨α, hα⟩ :=
    NK.UchidaKummer.Kummer.exists_pow_eq_algebraMap_of_isSepClosure (k := K) (K' := Ω) p hp hζ b
  have hαL : α ∈ NK.LocalAnabelian.kummerField (K' := Ω) p b :=
    NK.LocalAnabelian.mem_kummerField_of_pow_eq hα
  have hα' : (⟨α, hαL⟩ : ↥Lf) ^ p = algebraMap K ↥Lf (b : K) := by
    apply Subtype.ext
    change (α : Ω) ^ p = algebraMap K Ω (b : K)
    exact hα
  -- ## `b` is a local unit at `Q`: its image in the completed integers is a unit
  obtain ⟨u, hu_coe, hbval⟩ := exists_unit_adicCompletionIntegers_of_mem_localUnits b Q hb
  have hppos : 0 < p := hp.pos
  by_cases hcase : ∃ c : (Q.adicCompletion K)ˣ,
      algebraMap K (Q.adicCompletion K) (b : K) = (c : Q.adicCompletion K) ^ p
  · -- ## Case 1: `b` is a `p`-th power in `K_Q`; the local extension is trivial
    have hloc := (NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff
      (K := K) (K' := Ω) p hp hζ b Lf rfl Q).mpr hcase
    have h1 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1 := hloc q hq
    exact Nat.eq_one_of_mul_eq_one_right h1
  · -- ## Case 2: `b` is not a `p`-th power in `K_Q`
    have hbnotpow : b ∉ NK.LocalAnabelian.powSubgroup p K := by
      intro hmem
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
      rw [powMonoidHom_apply] at hy
      refine hcase ⟨Units.map (algebraMap K (Q.adicCompletion K)) y, ?_⟩
      rw [Units.coe_map, ← map_pow]
      exact congrArg (algebraMap K (Q.adicCompletion K)) (by
        rw [← Units.val_pow_eq_pow_val, hy])
    have hfin : Module.finrank K ↥Lf = p :=
      (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω) p hp hζ b
        hbnotpow).2
    -- ## the image of the root in the completed integers of `L`
    have hθmem : algebraMap ↥Lf (q.adicCompletion ↥Lf) (⟨α, hαL⟩ : ↥Lf) ∈
        q.adicCompletionIntegers ↥Lf :=
      mem_adicCompletionIntegers_of_pow_eq_unit (K := K) (L := ↥Lf) p hp Q q hq (b := b) hbval hα'
    let θ : q.adicCompletionIntegers ↥Lf :=
      ⟨algebraMap ↥Lf (q.adicCompletion ↥Lf) (⟨α, hαL⟩ : ↥Lf), hθmem⟩
    -- ## the algebra structure on the completed integers
    let ρ : Q.adicCompletionIntegers K →+* q.adicCompletionIntegers ↥Lf :=
      ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers ↥Lf)
        (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2)
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers ↥Lf) :=
      RingHom.toAlgebra ρ
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion ↥Lf) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    haveI hST : IsScalarTower K (Q.adicCompletion K) (q.adicCompletion ↥Lf) :=
      Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
        (K := K) (L := ↥Lf) Q q hq
    have hlies : Ideal.LiesOver (IsLocalRing.maximalIdeal (q.adicCompletionIntegers ↥Lf))
        (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) :=
      Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
        (K := K) (L := ↥Lf) Q q hq
    have hθ : θ ^ p = algebraMap (Q.adicCompletionIntegers K) (q.adicCompletionIntegers ↥Lf) u := by
      apply Subtype.ext
      change (algebraMap ↥Lf (q.adicCompletion ↥Lf) (⟨α, hαL⟩ : ↥Lf)) ^ p
        = (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
            ((u : (Q.adicCompletionIntegers K)ˣ) : Q.adicCompletion K)
      rw [← map_pow, hα']
      rw [← IsScalarTower.algebraMap_apply K ↥Lf (q.adicCompletion ↥Lf) (b : K)]
      rw [IsScalarTower.algebraMap_apply K (Q.adicCompletion K) (q.adicCompletion ↥Lf) (b : K)]
      congr 1
      exact hu_coe.symm
    have hnot : ∀ c : (Q.adicCompletion K)ˣ,
        (c : Q.adicCompletion K) ^ p ≠ (u : Q.adicCompletion K) := by
      intro c hc
      refine hcase ⟨c, ?_⟩
      rw [hc]
      exact hu_coe.symm
    -- ## the residue degree bound
    have hfp : p ≤ q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
      le_inertiaDeg_of_pow_eq_adicCompletionIntegers (K := K) (L := ↥Lf) p hp Q q hq hQ hlies u
        θ hθ hnot
    -- ## `e · f ≤ [L : K] = p`
    have hle : Module.finrank (Q.adicCompletion K) (q.adicCompletion ↥Lf) ≤ Module.finrank K ↥Lf :=
      Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
        (K := K) (L := ↥Lf) Q q hq
    have hmul := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := K) (L := ↥Lf) Q q hq
    have hef : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ≤ p := by
      rw [hmul]
      exact hle.trans_eq hfin
    -- ## `e ≥ 1`
    have hepos : 0 < q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) := by
      haveI hmf : Module.Finite (Q.adicCompletion K) (q.adicCompletion ↥Lf) :=
        Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
          (K := K) (L := ↥Lf) Q q hq
      by_contra h
      have h0 : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 0 :=
        Nat.eq_zero_of_not_pos h
      have hpos : 0 < Module.finrank (Q.adicCompletion K) (q.adicCompletion ↥Lf) :=
        Module.finrank_pos
      rw [← hmul, h0, zero_mul] at hpos
      exact lt_irrefl 0 hpos
    -- ## arithmetic
    have hfle : q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ≤
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
          q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
      Nat.le_mul_of_pos_left _ hepos
    have hf0 : 0 < q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by omega
    have hprod : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)
        = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by omega
    refine Nat.mul_right_cancel hf0 ?_
    rw [one_mul]
    exact hprod


/-- `K(U(S)^{1/p})/K` is unramified at every finite place outside `S`.

Every element of `U(S) = TUnits S` is a local unit at `Q ∉ S` and `(p : 𝓞 K) ∉ Q.asIdeal` (else
`Q ∈ S` by `hSp`), so each single-generator Kummer field `K(b^{1/p})`, `b ∈ U(S)`, is unramified
at `Q` by `KummerCase.kummerField_ramificationIdx_eq_one_of_unit`. The field is the compositum of
these, and inertia is contained in every one of them: for a prime `q ∣ Q` of `L` the inertia
subgroup `I(q|Q) ≤ Gal(L/K)` maps into the inertia subgroup of `Gal(K(b^{1/p})/K)`, which is
trivial; by the Kummer pairing (injective, `kummerPairingQuot_injective`) a global automorphism
lying in `I(q|Q)` and fixing all the chosen roots `b^{1/p}` of `U(S)` is the identity, so
`I(q|Q) = 1` and `e(q|Q) = 1`. -/
theorem ramificationIdx_eq_one_kummerSUnitField {K : Type} [Field K] [NumberField K] {Ω : Type*}
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] {p : ℕ} (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S)
    [FiniteDimensional K ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S)]
    [NumberField ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S)]
    (hSp : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ q.asIdeal →
        NK.GlobalCFT.Place.ofFinite q ∈ S)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hQ : NK.GlobalCFT.Place.ofFinite Q ∉ S)
    (q : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S)))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    q.asIdele.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
  classical
  -- ## Notation and instances
  let LL : IntermediateField K Ω := NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S
  haveI hfdLL : FiniteDimensional K LL :=
    ‹FiniteDimensional K ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S)›
  haveI hnfLL : NumberField ↥LL :=
    ‹NumberField ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S)›
  haveI hgalLL : IsGalois K ↥LL :=
    NK.NUV2.ArtinBridge.isGalois_kummerSUnitField (K := K) (Ω := Ω) (p := p) (S := S) hp hζ
  have hLLeq : LL = NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S := rfl
  -- ## `p` is invertible at `Q`
  have hpQ : (p : NumberField.RingOfIntegers K) ∉ Q.asIdeal := fun h => hQ (hSp Q h)
  -- ## `LL` is generated by the Kummer fields of the `S`-units
  have hsup : LL = ⨆ c : ↥(sUnits K S), NK.LocalAnabelian.kummerField (K' := Ω) p (c : Kˣ) := by
    rw [hLLeq, NK.NUV2.ArtinBridge.kummerSUnitField_eq_kummerAdjoin,
      NK.NUV2.ArtinBridge.sUnitKummerGroup,
      NK.GlobalCFTdeep.SecondInequality.kummerAdjoin_sup_powSubgroup]
    exact NK.GlobalCFTdeep.SecondInequality.kummerAdjoin_eq_iSup_kummerField (K' := Ω) p _
  have hle : ∀ c : ↥(sUnits K S),
      NK.LocalAnabelian.kummerField (K' := Ω) p (c : Kˣ) ≤ LL := fun c => by
    rw [hsup]; exact le_iSup (fun c : ↥(sUnits K S) =>
      NK.LocalAnabelian.kummerField (K' := Ω) p (c : Kˣ)) c
  -- ## Every `S`-unit is a local unit at `Q`
  have hloc : ∀ c : ↥(sUnits K S),
      NK.GlobalCFT.Idele.principalIdele K (c : Kˣ) (NK.GlobalCFT.Place.ofFinite Q) ∈
        NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q) :=
    fun c => principalIdele_mem_localUnits_of_mem_sUnits S (c : Kˣ) c.2 Q hQ
  -- ## The `Q`-prime of `LL`
  have hqLL : q.asIdeal.LiesOver Q.asIdeal := hq
  -- ## Reduce to the triviality of the inertia subgroup
  rw [show q.asIdele = q.asIdeal from rfl]
  refine (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
    (F := K) (K := ↥LL) Q.asIdeal q.asIdeal).mp ?_
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  -- ## Unfold the inertia condition
  have hσ' : ∀ x : 𝓞 ↥LL,
      galRestrict (𝓞 K) K ↥LL (𝓞 ↥LL) σ x - x ∈ q.asIdeal := by
    intro x
    have h := hσ
    rw [Ideal.inertia, AddSubgroup.mem_inertia] at h
    have h2 := h x
    rwa [smul_ringOfIntegers_eq_galRestrict] at h2
  have hqL : Ideal.comap (algebraMap (𝓞 K) (𝓞 ↥LL)) q.asIdeal = Q.asIdeal := by
    rw [← Ideal.under_def]; exact hqLL.over.symm
  -- ## The sup of the restricted Kummer subfields is everything
  have hlift_top : IntermediateField.lift (⊤ : IntermediateField K ↥LL) = LL := by
    refine le_antisymm (IntermediateField.lift_le ⊤) ?_
    intro x hx
    have := (IntermediateField.mem_lift (F := LL) (E := (⊤ : IntermediateField K ↥LL))
      (⟨x, hx⟩ : ↥LL)).mpr (Set.mem_univ _)
    simpa using this
  have hkey : IntermediateField.lift (⨆ c : ↥(sUnits K S),
      IntermediateField.restrict (hle c)) = LL := by
    show (⨆ c : ↥(sUnits K S), IntermediateField.restrict (hle c)).map
      (IntermediateField.val LL) = LL
    rw [IntermediateField.iSup_eq_adjoin, IntermediateField.adjoin_map, Set.image_iUnion]
    have hset : (⋃ c : ↥(sUnits K S), IntermediateField.val LL ''
          ↑(IntermediateField.restrict (hle c))) =
        ⋃ c : ↥(sUnits K S),
          ↑(NK.LocalAnabelian.kummerField (K' := Ω) p (c : Kˣ)) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe]
      constructor
      · rintro ⟨c, y, hyc, rfl⟩
        exact ⟨c, (IntermediateField.mem_restrict (hle c) y).mp hyc⟩
      · rintro ⟨c, hx⟩
        exact ⟨c, ⟨x, hle c hx⟩,
          (IntermediateField.mem_restrict (hle c) ⟨x, hle c hx⟩).mpr hx, rfl⟩
    rw [hset, ← IntermediateField.iSup_eq_adjoin (f := fun c : ↥(sUnits K S) =>
      NK.LocalAnabelian.kummerField (K' := Ω) p (c : Kˣ)), ← hsup]
  have htop : (⨆ c : ↥(sUnits K S), IntermediateField.restrict (hle c)) = ⊤ := by
    apply IntermediateField.lift_injective LL
    rw [hlift_top]
    exact hkey
  -- ## Every element of the inertia subgroup fixes each Kummer subfield
  have hfix : ∀ c : ↥(sUnits K S), σ ∈ (IntermediateField.restrict (hle c)).fixingSubgroup := by
    intro c
    -- finiteness and number field structure for the Kummer field
    haveI hFgal : IsGalois K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p (c : Kˣ)) :=
      NK.GlobalCFTdeep.SecondInequality.isGalois_kummerField (K' := Ω) hp hζ (c : Kˣ)
    haveI hFfd : Module.Finite K ↥(NK.LocalAnabelian.kummerField (K' := Ω) p (c : Kˣ)) :=
      Module.Finite.equiv (IntermediateField.restrictAlgEquiv (hle c)).symm.toLinearEquiv
    haveI hFnf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p (c : Kˣ)) :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField _
    let G : IntermediateField K ↥LL := IntermediateField.restrict (hle c)
    haveI hGfd : FiniteDimensional K ↥G := inferInstance
    haveI hGnf : NumberField ↥G :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField G
    haveI hGgal : IsGalois K ↥G :=
      IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv (hle c))
    haveI hGnorm : Normal K ↥G := hGgal.to_normal
    -- the prime of `𝓞 G` below `q`
    let qc : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥G) :=
      ⟨q.asIdeal.under (𝓞 ↥G), Ideal.IsPrime.under _ _,
        fun h => q.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)⟩
    have hqcLies : qc.asIdeal.LiesOver Q.asIdeal := by
      refine ⟨?_⟩
      rw [Ideal.under_def]
      have hqc : qc.asIdeal = Ideal.under (𝓞 ↥G) q.asIdeal := rfl
      rw [hqc, Ideal.under_def, Ideal.comap_comap,
        ← IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 ↥G) (𝓞 ↥LL)]
      exact hqL.symm
    haveI : qc.asIdeal.LiesOver Q.asIdeal := hqcLies
    -- `e = 1` at the prime of the restricted field
    have hunit := hloc c
    have he1 : qc.asIdeal.ramificationIdx (𝓞 K) = 1 :=
      NK.NUV2.ArtinBridge.ramificationIdx_eq_one_of_algEquiv
        (e := IntermediateField.restrictAlgEquiv (hle c)) Q
        (fun q' hq' =>
          NK.NUV2.ArtinBridge.kummerField_ramificationIdx_eq_one_of_unit_poly
            (K := K) (Ω := Ω) hp hζ (c : Kˣ) Q hpQ hunit q' hq')
        qc hqcLies
    -- the inertia subgroup of `G` at `qc` is trivial
    have hbot : Ideal.inertia Gal(↥G/K) qc.asIdeal = ⊥ :=
      (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
        (F := K) (K := ↥G) Q.asIdeal qc.asIdeal).mpr he1
    -- the restricted automorphism lies in that inertia subgroup
    have hτ : AlgEquiv.restrictNormalHom G σ ∈ Ideal.inertia Gal(↥G/K) qc.asIdeal := by
      rw [Ideal.inertia, AddSubgroup.mem_inertia]
      intro y
      rw [smul_ringOfIntegers_eq_galRestrict]
      exact NK.NUV2.ArtinBridge.galRestrict_restrictNormalHom_mem_under
        (K := K) (L := ↥LL) G q σ hσ' y
    have hτ1 : AlgEquiv.restrictNormalHom G σ = 1 := by
      rw [hbot] at hτ
      exact Subgroup.mem_bot.mp hτ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h2 : (AlgEquiv.restrictNormalHom G σ) ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hτ1]; rfl
    have h3 := congrArg (fun z : ↥G => (z : ↥LL)) h2
    simpa [AlgEquiv.restrictNormalHom_apply] using h3
  have hle_fix : (⨆ c : ↥(sUnits K S), IntermediateField.restrict (hle c)) ≤
      IntermediateField.fixedField (Subgroup.zpowers σ) := by
    refine iSup_le fun c => ?_
    rw [IntermediateField.le_iff_le]
    exact Subgroup.zpowers_le.mpr (hfix c)
  -- ## Conclusion
  have hmem : σ ∈ (⨆ c : ↥(sUnits K S),
      IntermediateField.restrict (hle c)).fixingSubgroup :=
    (IntermediateField.le_iff_le _ _).mp hle_fix (Subgroup.mem_zpowers σ)
  rw [htop, IntermediateField.fixingSubgroup_top] at hmem
  exact Subgroup.mem_bot.mp hmem

end NK.NUV2.ArtinBridge
