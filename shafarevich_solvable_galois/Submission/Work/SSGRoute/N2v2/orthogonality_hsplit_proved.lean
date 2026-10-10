import Mathlib.FieldTheory.KrullTopology
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.GrunwaldEscapeCore.L1Korth.alpha_fixes_L1K
import Submission.Work.SSGRoute.N2v2.artin_fixes_of_local_factors
import Submission.Work.SSGRoute.N2v2.artin_fixes_of_local_units
import Submission.Work.SSGRoute.N2v2.artin_lifts_zdata
import Submission.Work.SSGRoute.N2v2.exists_artinMap_with_decompLift
import Submission.Work.SSGRoute.N2v2.heart_localSum_vanishes
import Submission.Work.SSGRoute.N2v2.isUnramifiedIn_of_unitIdeles_le_normClassSubgroup
import Submission.Work.SSGRoute.N2v2.kummer_level_realisation
import Submission.Work.SSGRoute.N2v2.levelField
import Submission.Work.SSGRoute.N2v2.restrictNormalHom_artinMap_eq_of_le
import Submission.Work.SSGRoute.N2v2.sup5_abelian_expP
import Submission.Work.SSGRoute.myv2.Hdata
import Submission.Work.SSGRoute.myv2.KummerFieldInst
import Submission.Work.SSGRoute.myv2.Sep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.N2v2

open scoped Pointwise IntermediateField
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000


/-! ## The idèlic Artin map of a finite abelian extension, with both lift clauses

`exists_artinMap_with_decompLift` (S1) and `exists_artinMap_with_inertiaLift_zdata` (S2) each produce
an idèlic Artin map of `E/↥K` with the kernel `N_{E/↥K}𝕀_E ⊔ ↥Kˣ` and the Frobenius normalisation;
these two clauses pin the map (Artin uniqueness), so the map produced by (S2) also has the
decomposition clause, which `decompLift_of_artinMap` proves for *any* map with the kernel and the
Frobenius normalisation.  Hence combining them is immediate, and the combined statement is what the
orthogonality consumes.

(Remark on the imports: `exists_artinMap_with_inertiaLift` and `exists_artinMap_with_decompLift`
cannot be imported in the same environment, because the former reaches
`ZConstruction/OddGate/D_isUnramifiedIn_of_inertia_subset_fixingSubgroup` and the latter
`ZDataMup/mupH1locLcHoms`, two modules that re-declare the same names.  The file
`N2v2/artin_lifts_zdata.lean` is a copy of the former carried out in the `ZDataMup` lane, so that
this combination is possible.) -/

/-- **The idèlic Artin map with the kernel, the Frobenius normalisation and both lift clauses.** -/
theorem exists_artinMap_with_lifts {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)] :
    ∃ Φ : NK.GlobalCFT.Idele ↥K →* (↥E ≃ₐ[↥K] ↥E),
      Φ.ker = NK.GlobalCFT.Idele.normImage ↥K ↥E ⊔
        NK.GlobalCFT.Idele.principalSubgroup ↥K ∧
      (∀ Q : NK.Chebotarev.PrimeIdeal ↥K,
        NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) Q →
        Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥E) Q) ∧
      (∀ (A : ValuationSubring Ω) (_hA : _root_.SSGRoute.IsFinPlace k A)
        (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
        A.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
        ∀ x : (↥K)ˣ,
        ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ _root_.SSGRoute.decomp (k := ↥K) A ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
            Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite 𝔭) x))) ∧
      (∀ (A : ValuationSubring Ω) (_hA : _root_.SSGRoute.IsFinPlace k A)
        (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
        A.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
        ∀ u : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ,
          u ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔭) →
        ∃ σ : Ω ≃ₐ[↥K] Ω, _root_.SSGRoute.IsInertia k A (σ.restrictScalars k) ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
            Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) u)) := by
  obtain ⟨Φ, hker, hfrob, hinertia⟩ :=
    Work.SSGRoute.N2v2.exists_artinMap_with_inertiaLift_zdata (K := K) E
  exact ⟨Φ, hker, hfrob,
    fun A hA 𝔭 h𝔭 x => Work.SSGRoute.N2v2.decompLift_of_artinMap (K := K) (E := E) Φ hker hfrob
      A hA 𝔭 h𝔭 x,
    hinertia⟩

/-! ## The exponent of `Gal(E/↥K)`

If the norm class subgroup of `E/↥K` contains the `p`-th powers of `C_↥K`, then `Gal(E/↥K)` has
exponent `p` (the `p`-power part of the norm group, seen through the Artin isomorphism). -/

/-- **`Gal(E/↥K)` has exponent `p`** when the `p`-th powers of `C_↥K` are norms from `E`. -/
theorem galExp_of_pPowSubgroup_le (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)]
    (hp : Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (IdeleClassGroup ↥K) ≤
      Idele.normClassSubgroup ↥K ↥E)
    (Φ : Idele ↥K →* (↥E ≃ₐ[↥K] ↥E))
    (hker : Φ.ker = Idele.normImage ↥K ↥E ⊔ Idele.principalSubgroup ↥K)
    (hfrob : ∀ Q : NK.Chebotarev.PrimeIdeal ↥K,
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) Q →
      Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥E) Q) :
    ∀ σ : ↥E ≃ₐ[↥K] ↥E, σ ^ p = 1 := by
  classical
  haveI hNumE : NumberField ↥E := NumberField.of_module_finite ↥K ↥E
  have hcomm : ∀ a b : (↥E ≃ₐ[↥K] ↥E), a * b = b * a := fun a b => mul_comm' a b
  have hartp : ∀ z : Idele ↥K, (Φ z) ^ p = 1 := by
    intro z
    rw [← map_pow]
    refine Work.GrunwaldEscapeCore.L1Korth.art_eq_one_of_mk_mem Φ hker ?_
    have hrange : (IdeleClassGroup.mk ↥K z) ^ p ∈
        Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (IdeleClassGroup ↥K) :=
      Work.SSGRoute.EscapeCoreLib.pow_mem_pPowSubgroup (IdeleClassGroup.mk ↥K z)
    rw [map_pow]
    exact hp hrange
  have hsurj : Function.Surjective Φ :=
    Work.SSGRoute.ZDataMup.ArtinReciprocity.surjective_of_frobAtPrime_unramified hcomm Φ hfrob
  intro σ
  obtain ⟨z, rfl⟩ := hsurj σ
  exact hartp z


/-! ## The full clause list of an idèlic Artin map

`exists_abelianArtin_localFactors` delivers, besides the kernel `N 𝕀_E ⊔ ↥Kˣ` and the Frobenius
normalisation, the *local* clause `Φ (onePlace v u) = 1 ↔ u ∈ N_{E_v/↥K_v}` and the product formula;
`decompLift_of_artinMap` and `inertiaLift_of_artinMap_zdata` add the decomposition and inertia lift
clauses (both are automatic consequences of the kernel and the Frobenius normalisation, by Artin
uniqueness).  Everything the orthogonality needs about `Φ` is collected here. -/

/-- **An idèlic Artin map with all the clauses used by the orthogonality.** -/
theorem exists_artinMap_fullClauses {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E]
    [IsMulCommutative (↥E ≃ₐ[↥K] ↥E)] :
    ∃ Φ : NK.GlobalCFT.Idele ↥K →* (↥E ≃ₐ[↥K] ↥E),
      Φ.ker = NK.GlobalCFT.Idele.normImage ↥K ↥E ⊔
        NK.GlobalCFT.Idele.principalSubgroup ↥K ∧
      (∀ (v : NK.GlobalCFT.Place ↥K)
        (u : (NK.GlobalCFT.Place.localField ↥K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v u) = 1 ↔
          u ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥E) v) ∧
      (∀ Q : NK.Chebotarev.PrimeIdeal ↥K,
        NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥E) Q →
        Φ (NK.HeckeL.ideleOfPrime ↥K Q) = NK.Chebotarev.frobAtPrime (K := ↥K) (L := ↥E) Q) ∧
      (∀ (x : (↥K)ˣ) (s : Finset (NK.GlobalCFT.Place ↥K)),
        (∀ v, v ∉ s →
          Φ (NK.HassePrinciple.onePlace v
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v x)) = 1) →
        NK.CFTLib.IdeleHasse.cprod (fun a b => mul_comm' a b) s
          (fun v => Φ (NK.HassePrinciple.onePlace v
            (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v x))) = 1) ∧
      (∀ (A : ValuationSubring Ω) (_hA : _root_.SSGRoute.IsFinPlace k A)
        (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
        A.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
        ∀ x : (↥K)ˣ,
        ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ _root_.SSGRoute.decomp (k := ↥K) A ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
            Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite 𝔭) x))) ∧
      (∀ (A : ValuationSubring Ω) (_hA : _root_.SSGRoute.IsFinPlace k A)
        (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
        A.comap (algebraMap ↥K Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
        ∀ u : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ,
          u ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔭) →
        ∃ σ : Ω ≃ₐ[↥K] Ω, _root_.SSGRoute.IsInertia k A (σ.restrictScalars k) ∧
          AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
            Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭) u)) := by
  haveI hNE : NumberField ↥E := NumberField.of_module_finite ↥K ↥E
  have hcomm : ∀ a b : (↥E ≃ₐ[↥K] ↥E), a * b = b * a := fun a b => mul_comm' a b
  obtain ⟨Φ, hker, _hnorm, _hprin, hloc, hfrob, hprod⟩ :=
    Work.SSGRoute.ZConstruction.exists_abelianArtin_localFactors (K := ↥K) (L := ↥E) hcomm
  exact ⟨Φ, hker, hloc, hfrob, hprod,
    fun A hA 𝔭 h𝔭 x => Work.SSGRoute.N2v2.decompLift_of_artinMap (K := K) (E := E) Φ hker hfrob
      A hA 𝔭 h𝔭 x,
    fun A hA 𝔭 h𝔭 u hu => Work.SSGRoute.N2v2.inertiaLift_of_artinMap_zdata (K := K) E Φ hker
      hfrob A hA 𝔭 h𝔭 u hu⟩

/-- **The instances of a Kummer field `↥K⟮x^{1/p}⟯`** (finite, Galois, a number field, with
commutative Galois group of exponent `p` over `↥K`), collected for the compositum step. -/
theorem kummerField_data (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (x : (↥K)ˣ) :
    FiniteDimensional ↥K (NK.LocalAnabelian.kummerField (K' := Ω) p x) ∧
      IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) p x) ∧
      NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p x) ∧
      IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) p x) ≃ₐ[↥K]
        ↥(NK.LocalAnabelian.kummerField (K' := Ω) p x)) ∧
      (∀ σ : ↥(NK.LocalAnabelian.kummerField (K' := Ω) p x) ≃ₐ[↥K]
        ↥(NK.LocalAnabelian.kummerField (K' := Ω) p x), σ ^ p = 1) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hSepK : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  haveI hfd : FiniteDimensional ↥K (NK.LocalAnabelian.kummerField (K' := Ω) p x) :=
    NK.GlobalCFTdeep.SecondInequality.finiteDimensional_kummerField (k := ↥K) (K' := Ω)
      (ζ := ζ) Fact.out hζ x
  refine ⟨hfd, ?_, ?_, kummerField_isMulCommutative p K ζ hζ x,
    kummerField_pow_eq_one p K ζ hζ x⟩
  · by_cases hx : x ∈ NK.LocalAnabelian.powSubgroup p ↥K
    · rw [kummerField_eq_bot_of_mem_powSubgroup p K ζ hζ x hx]
      infer_instance
    · exact (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (k := ↥K) (K' := Ω) p
        Fact.out hζ x hx).1
  · exact NumberField.of_module_finite ↥K _

/-- **The orthogonality of the escape-form Grünwald statement, with the `hsplit` repair (class-group form).**  For the class field `M` of `U_p = gesU ↾K ⊔ (p-th powers)`, the class of the `T'`-free part `𝔡` of the divisor of the Grünwald element `a` (which realises the datum `g + h` on the local groups of the primes of `T`, `ha`) lies in `U_p ⊔ N_{N/↾K}C_N` with `N` the copy over `↥K` of `L₁ ⊔ L₂`.  Exactly this statement sits in `Submission/Work/SSGRoute/GrunwaldEscapeCore/orthogonality_hsplit.lean` with a complete 180-line reduction (`charSeparation_exponent_p` + the Artin character `χA` of the class field) and a final gap; the `L₁ = K` specialisation of it, in the equivalent field form, is proved sorry-free in `Submission/Work/GrunwaldEscapeCore/L1Korth/alpha_fixes_L1K.lean` (545 lines, same structure, and the best template for this one).  The plan, the proved antisymmetry (`kummerCharZMod_antisymm`), the proved diagonal (`mem_localNormSubgroup_of_kummerRoot`) and the proved product formula (`localFactor_productFormula_clean`) are recorded in `Submission/Work/SSGRoute/GrunwaldEscapeCore/NOTE_orthogonality_route.md` (sections 2, 3, 6.3, 6.4 list the remaining reductions P1-P5).  The `hsplit` hypothesis is essential: without it the same statement is refuted (`COUNTEREXAMPLE_N2_grunwald_escape_relative.md`).  Warning from the reviewers of this statement: `SSG8Escape/Setup.lean`'s `alpha_fixes_inf_ssg8` and `myv2/Heart.lean`'s `alpha_fixes_inf_ssg8_hsplit` are the same statement with the hypothesis `hT'above` (prime of `T'` under a place of `T`) and `hsplit` dropped, and are FALSE; do not build on them, and note that `orthogonality_hsplit.lean` itself must not be imported here (its `sorry` would trivialise the job). -/
theorem orthogonality_hsplit_proved (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, _root_.SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, Work.SSGRoute.gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, Work.SSGRoute.gesKConj K A B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : _root_.SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, _root_.SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ Work.SSGRoute.gesKConj K A B) → ¬ _root_.SSGRoute.IsSplitIn k L₁ B →
      ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → χ σ = 0))
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ _root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, _root_.SSGRoute.IsInertia k A σ → χ σ = 0))
    (hsplit : ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
      (∀ σ ∈ (L₁ ⊔ L₂).fixingSubgroup, χ σ = 0) →
      ∃ χ₁ χ₂ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
        (∀ σ ∈ L₁.fixingSubgroup, χ₁ σ = 0) ∧
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
        (∀ σ ∈ L₂.fixingSubgroup, χ₂ σ = 0) ∧
        ∀ σ ∈ K.fixingSubgroup, χ σ = χ₁ σ + χ₂ σ)
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hTbelow : ∀ A ∈ T, ∃ 𝔭 ∈ T', A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (hT'above : ∀ 𝔭 ∈ T', ∃ A ∈ T, A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭)
    (N : IntermediateField ↥K Ω) [FiniteDimensional ↥K N] [IsGalois ↥K N] [NumberField ↥N]
    (hN : (N : Set Ω) = ((L₁ ⊔ L₂ : IntermediateField k Ω) : Set Ω))
    (a : (↥K)ˣ)
    (ha : ∀ A ∈ T, ∀ σ : ↥(_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      g (σ : Ω ≃ₐ[k] Ω) + h A (σ : Ω ≃ₐ[k] Ω) =
        Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ a
          (Work.SSGRoute.gesLocalToGalK K σ)) :
    NK.GlobalCFT.IdeleClassGroup.mk ↥K
        (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart T' a)) ∈
      (((NK.GlobalCFT.Idele.principalSubgroup ↥K ⊔ Work.SSGRoute.powTIdeles ↥K p T').map
          (NK.GlobalCFT.IdeleClassGroup.mk ↥K))
        ⊔ Work.SSGRoute.EscapeCoreLib.pPowSubgroup p (NK.GlobalCFT.IdeleClassGroup ↥K))
      ⊔ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥N := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- ## the level field `F` inside `N`, with `N_{F/↥K}C_F` the subgroup of the statement
  obtain ⟨F, hFfd, hFgal, hFnf, hFcomm, hFleN, hFnorm⟩ :=
    Work.SSGRoute.N2v2.exists_levelField_of_gesUPow_subfield_N p k Ω K L₁ L₂ hKL₁ hKL₂ T' N hN
  haveI hFfdI : FiniteDimensional ↥K F := hFfd
  haveI hFgalI : IsGalois ↥K F := hFgal
  haveI hFnfI : NumberField ↥F := hFnf
  haveI hFcommI : IsMulCommutative (↥F ≃ₐ[↥K] ↥F) := hFcomm
  -- ## the idèlic Artin map of `F/↥K`, with all the clauses
  obtain ⟨Φ, hΦker, hΦloc, hΦfrob, hΦprod, hΦdecomp, hΦinertia⟩ :=
    Work.SSGRoute.N2v2.exists_artinMap_fullClauses (K := K) F
  -- ## `F/↥K` is unramified outside `T'`
  have hFunr : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥F) 𝔮 := by
    intro 𝔮 h𝔮
    refine Work.SSGRoute.N2v2.isUnramifiedIn_of_unitIdeles_le_normClassSubgroup p k Ω K T' F ?_ 𝔮 h𝔮
    rw [hFnorm]
    exact le_trans le_sup_left le_sup_left
  -- ## `Gal(F/↥K)` has exponent `p`
  have hexpF : ∀ σ : ↥F ≃ₐ[↥K] ↥F, σ ^ p = 1 := by
    refine Work.SSGRoute.N2v2.galExp_of_pPowSubgroup_le p K F ?_ Φ hΦker hΦfrob
    rw [hFnorm]
    exact le_trans le_sup_right le_sup_left
  -- ## characters of `Gal(F/↥K)` separate the points, so it suffices to kill the Artin symbol
  have hPhi : Φ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
      = 1 := by
    have h1 : Φ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
        ∈ (⊥ : Subgroup (↥F ≃ₐ[↥K] ↥F)) := by
      letI hFcg : CommGroup (↥F ≃ₐ[↥K] ↥F) := { mul_comm := fun a b => mul_comm' a b }
      refine Work.SSGRoute.N2v2.mem_of_forall_monoidHom_eq_one (p := p) hexpF ⊥ ?_
      intro χ _
      -- realise the character as a Kummer character at level `F`
      obtain ⟨c, hcF, hχ⟩ :=
        Work.SSGRoute.N2v2.kummer_level_realisation p k Ω K ζ hζ F χ
      refine Work.SSGRoute.N2v2.artin_fixes_of_local_factors p K ζ hζ hKimag F c hcF χ hχ
        a T' hFunr Φ ?_ ?_ ?_
      · -- the principal idèles are killed (kernel clause)
        intro x
        rw [← MonoidHom.mem_ker, hΦker]
        exact Subgroup.mem_sup_right (Idele.mem_principalSubgroup.mpr ⟨x, rfl⟩)
      · -- the norm idèles are killed (kernel clause)
        intro y
        rw [← MonoidHom.mem_ker, hΦker]
        exact Subgroup.mem_sup_left (Idele.mem_normImage.mpr ⟨y, fun v => rfl⟩)
      · -- ## the per-place product: the heart of the orthogonality
        classical
        -- ### the Kummer element representing the datum `g`
        obtain ⟨bg, hbg⟩ :=
          Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
            p k Ω K ζ hζ g hg hgc
        -- ### the split of `c` along `hsplit` (at the `k`-level `L₁ ⊔ L₂`)
        have hKE : K ≤ (L₁ ⊔ L₂ : IntermediateField k Ω) := hKL₁.trans le_sup_left
        have hcbC : NK.LocalAnabelian.kummerField (K' := Ω) p c ≤
            Work.SSGRoute.EscapeCoreLib.baseChange K (L₁ ⊔ L₂) hKE := by
          rw [Work.SSGRoute.EscapeCoreLib.le_baseChange_iff]
          intro x hx
          exact hN ▸ hFleN (hcF hx)
        have hEfix : (L₁ ⊔ L₂ : IntermediateField k Ω).fixingSubgroup ≤
            (L₁.fixingSubgroup ⊓ L₂.fixingSubgroup) ⊔
              (Work.SSGRoute.N2v2.commPow ↥(K.fixingSubgroup) p).map
                K.fixingSubgroup.subtype := by
          rw [IntermediateField.fixingSubgroup_sup]
          exact le_sup_left
        obtain ⟨c₁, c₂, hc₁L', hc₂L', hsplitc⟩ :=
          Work.SSGRoute.N2v2.kummerSplit_of_hsplit p k Ω K ζ hζ L₁ L₂ hKL₁ hKL₂ hsplit
            (L₁ ⊔ L₂) hKE subset_rfl hEfix c hcbC
        have hc₁L : NK.LocalAnabelian.kummerField (K' := Ω) p c₁ ≤
            Work.SSGRoute.EscapeCoreLib.baseChange K L₁ hKL₁ := le_trans hc₁L' inf_le_right
        have hc₂L : NK.LocalAnabelian.kummerField (K' := Ω) p c₂ ≤
            Work.SSGRoute.EscapeCoreLib.baseChange K L₂ hKL₂ := le_trans hc₂L' inf_le_right
        -- ### the instances of the four Kummer fields
        have hFa := kummerField_data p K ζ hζ a
        haveI hFa_fd : FiniteDimensional ↥K
            (NK.LocalAnabelian.kummerField (K' := Ω) p a) := hFa.1
        haveI hFa_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) p a) := hFa.2.1
        haveI hFa_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p a) := hFa.2.2.1
        haveI hFa_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) p a) ≃ₐ[↥K]
          ↥(NK.LocalAnabelian.kummerField (K' := Ω) p a)) := hFa.2.2.2.1
        have hFa_exp : ∀ σ : ↥(NK.LocalAnabelian.kummerField (K' := Ω) p a) ≃ₐ[↥K]
            ↥(NK.LocalAnabelian.kummerField (K' := Ω) p a), σ ^ p = 1 := hFa.2.2.2.2
        have hFc₁ := kummerField_data p K ζ hζ c₁
        haveI hFc₁_fd : FiniteDimensional ↥K
            (NK.LocalAnabelian.kummerField (K' := Ω) p c₁) := hFc₁.1
        haveI hFc₁_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) p c₁) := hFc₁.2.1
        haveI hFc₁_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p c₁) :=
          hFc₁.2.2.1
        haveI hFc₁_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) p c₁) ≃ₐ[↥K]
          ↥(NK.LocalAnabelian.kummerField (K' := Ω) p c₁)) := hFc₁.2.2.2.1
        have hFc₁_exp : ∀ σ : ↥(NK.LocalAnabelian.kummerField (K' := Ω) p c₁) ≃ₐ[↥K]
            ↥(NK.LocalAnabelian.kummerField (K' := Ω) p c₁), σ ^ p = 1 := hFc₁.2.2.2.2
        have hFc₂ := kummerField_data p K ζ hζ c₂
        haveI hFc₂_fd : FiniteDimensional ↥K
            (NK.LocalAnabelian.kummerField (K' := Ω) p c₂) := hFc₂.1
        haveI hFc₂_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) p c₂) := hFc₂.2.1
        haveI hFc₂_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p c₂) :=
          hFc₂.2.2.1
        haveI hFc₂_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) p c₂) ≃ₐ[↥K]
          ↥(NK.LocalAnabelian.kummerField (K' := Ω) p c₂)) := hFc₂.2.2.2.1
        have hFc₂_exp : ∀ σ : ↥(NK.LocalAnabelian.kummerField (K' := Ω) p c₂) ≃ₐ[↥K]
            ↥(NK.LocalAnabelian.kummerField (K' := Ω) p c₂), σ ^ p = 1 := hFc₂.2.2.2.2
        have hFbg := kummerField_data p K ζ hζ bg
        haveI hFbg_fd : FiniteDimensional ↥K
            (NK.LocalAnabelian.kummerField (K' := Ω) p bg) := hFbg.1
        haveI hFbg_gal : IsGalois ↥K (NK.LocalAnabelian.kummerField (K' := Ω) p bg) := hFbg.2.1
        haveI hFbg_nf : NumberField ↥(NK.LocalAnabelian.kummerField (K' := Ω) p bg) :=
          hFbg.2.2.1
        haveI hFbg_cm : IsMulCommutative (↥(NK.LocalAnabelian.kummerField (K' := Ω) p bg) ≃ₐ[↥K]
          ↥(NK.LocalAnabelian.kummerField (K' := Ω) p bg)) := hFbg.2.2.2.1
        have hFbg_exp : ∀ σ : ↥(NK.LocalAnabelian.kummerField (K' := Ω) p bg) ≃ₐ[↥K]
            ↥(NK.LocalAnabelian.kummerField (K' := Ω) p bg), σ ^ p = 1 := hFbg.2.2.2.2
        -- ### the big level `E = F ⊔ ↥K⟮a^{1/p}⟯ ⊔ ↥K⟮c₁^{1/p}⟯ ⊔ ↥K⟮c₂^{1/p}⟯ ⊔ ↥K⟮bg^{1/p}⟯`
        obtain ⟨E, hEfd, hEgal, hEcomm, hEnf, hFE, hFaE, hc₁E, hc₂E, hbgE, hexpE⟩ :=
          Work.SSGRoute.N2v2.sup5_abelian_expP (k := k) (Ω := Ω) p K F
            (NK.LocalAnabelian.kummerField (K' := Ω) p a)
            (NK.LocalAnabelian.kummerField (K' := Ω) p c₁)
            (NK.LocalAnabelian.kummerField (K' := Ω) p c₂)
            (NK.LocalAnabelian.kummerField (K' := Ω) p bg)
            hexpF hFa_exp hFc₁_exp hFc₂_exp hFbg_exp
        haveI hEfdI : FiniteDimensional ↥K E := hEfd
        haveI hEgalI : IsGalois ↥K E := hEgal
        haveI hEcommI : IsMulCommutative (↥E ≃ₐ[↥K] ↥E) := hEcomm
        haveI hEnfI : NumberField ↥E := hEnf
        haveI hEft : Fintype (↥E ≃ₐ[↥K] ↥E) := AlgEquiv.fintype ↥K ↥E
        -- ### the Artin map of `E` and its local factors
        obtain ⟨Φ_E, hΦkerE, hΦlocE, hΦfrobE, hΦprodE, hΦdecompE, hΦinertiaE⟩ :=
          Work.SSGRoute.N2v2.exists_artinMap_fullClauses (K := K) E
        let θ : (v : NK.GlobalCFT.Place ↥K) →
            (NK.GlobalCFT.Place.localField ↥K v)ˣ →* (↥E ≃ₐ[↥K] ↥E) :=
          fun v => Φ_E.comp (NK.CFTLib.IdeleHasse.onePlaceHom (K := ↥K) v)
        have hθker : ∀ v : NK.GlobalCFT.Place ↥K,
            (θ v).ker = NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥E) v := by
          intro v
          ext u
          rw [MonoidHom.mem_ker]
          exact hΦlocE v u
        have hθprod : ∀ (x : (↥K)ˣ) (s : Finset (NK.GlobalCFT.Place ↥K)),
            (∀ v, v ∉ s → θ v (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v x) = 1) →
            NK.CFTLib.IdeleHasse.cprod (fun a b => mul_comm' a b) s
              (fun v => θ v (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) v x)) = 1 :=
          fun x s hs => hΦprodE x s (fun v hv => hs v hv)
        have harch : ∀ v : NK.GlobalCFT.Place ↥K,
            (∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, v ≠ NK.GlobalCFT.Place.ofFinite 𝔮) →
            ∀ u : (NK.GlobalCFT.Place.localField ↥K v)ˣ, θ v u = 1 := by
          intro v hv u
          have hv' : ¬ v.IsFinite := by
            rw [NK.GlobalCFT.Place.isFinite_iff]
            rintro ⟨𝔮, h𝔮⟩
            exact hv 𝔮 h𝔮
          exact Work.SSGRoute.N2v2.arch_localFactor_eq_one_aux p K ζ hζ hKimag Φ_E v hv' u
        have hlift : ∀ (A : ValuationSubring Ω) (_hA : _root_.SSGRoute.IsFinPlace k A)
            (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
            A.comap (algebraMap ↥K Ω) =
              IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
            ∀ x : (↥K)ˣ, ∃ σ : Ω ≃ₐ[↥K] Ω, σ ∈ _root_.SSGRoute.decomp (k := ↥K) A ∧
              AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
                θ (NK.GlobalCFT.Place.ofFinite 𝔭)
                  (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                    (NK.GlobalCFT.Place.ofFinite 𝔭) x) :=
          fun A hA 𝔭 h𝔭 x => hΦdecompE A hA 𝔭 h𝔭 x
        have hunith : ∀ (A : ValuationSubring Ω) (_hA : _root_.SSGRoute.IsFinPlace k A)
            (𝔭 : NK.Chebotarev.PrimeIdeal ↥K),
            A.comap (algebraMap ↥K Ω) =
              IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 →
            ∀ u : (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite 𝔭))ˣ,
              u ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔭) →
              ∃ σ : Ω ≃ₐ[↥K] Ω, _root_.SSGRoute.IsInertia k A (σ.restrictScalars k) ∧
                AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ =
                  θ (NK.GlobalCFT.Place.ofFinite 𝔭) u :=
          fun A hA 𝔭 h𝔭 u hu => hΦinertiaE A hA 𝔭 h𝔭 u hu
        -- ### the twisted diagonal (the `p = 2` correction included)
        have hdiagLift : ∀ 𝔭 ∈ T', ∃ σ₀ : Ω ≃ₐ[↥K] Ω,
            ∀ (y : (↥K)ˣ), NK.LocalAnabelian.kummerField (K' := Ω) p y ≤ E →
            ∀ τ : Ω ≃ₐ[↥K] Ω,
              AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E τ =
                θ (NK.GlobalCFT.Place.ofFinite 𝔭)
                  (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                    (NK.GlobalCFT.Place.ofFinite 𝔭) y) →
              Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ y τ =
                Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ y σ₀ :=
          fun 𝔭 _h𝔭 => Work.SSGRoute.N2v2.hdiag_E p K ζ hζ E Φ_E 𝔭
            (fun c hcE => Work.SSGRoute.N2v2.hdata_of_kummerField_le p K ζ hζ E Φ_E
              hΦkerE hΦfrobE 𝔭 c hcE)
        -- ### `g` vanishes on the fixing subgroup of `E`
        have hgE : ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ E.fixingSubgroup → g (σ.restrictScalars k) = 0 := by
          intro σ hσE
          have hσK : σ.restrictScalars k ∈ K.fixingSubgroup := by
            rw [IntermediateField.mem_fixingSubgroup_iff]
            intro x hx
            exact σ.commutes ⟨x, hx⟩
          rw [hbg (σ.restrictScalars k) hσK,
            Work.SSGRoute.N2v2.fixingSubgroupEquiv_restrictScalars K σ]
          exact Work.SSGRoute.N2v2.kummerCharZMod_eq_zero_of_kummerField_le p k Ω K ζ hζ bg E
            hbgE σ hσE
        -- ### the character at level `E` and the level-`F` character of `c`
        have hcE : NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ E := hcF.trans hFE
        obtain ⟨χE, hχE⟩ :=
          Work.SSGRoute.N2v2.exists_kummerChar_level p k Ω K ζ hζ E c hcE
        -- ### the heart
        have hsum := Work.SSGRoute.N2v2.heart_localSum_vanishes p k Ω K ζ hζ hKimag L₁ L₂
          hKL₁ hKL₂ T hTfin T' hTbelow hT'above
          (fun B hB h => hTcov B hB h) g hg hgc
          (fun B hB h1 h2 σ hσ hI => hgram B hB (fun A hA => by
            rintro ⟨τ, hτ, hτA⟩
            exact h1 A hA τ hτ hτA) h2 σ hσ hI)
          h hh horth₁ horth₂ a ha E hexpE θ hθker hθprod harch hlift hunith
          hdiagLift hgE hFaE c hcE c₁ c₂ hc₁E hc₂E hc₁L hc₂L hsplitc χE hχE
        -- ### reading the heart back at the level `F`
        have hsumF : ∑ 𝔭 ∈ T',
            (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite 𝔭) a)))).toAdd = 0 := by
          rw [← hsum]
          refine Finset.sum_congr rfl (fun 𝔭 h𝔭 => ?_)
          obtain ⟨A, hAT, hAcomap⟩ := hT'above 𝔭 h𝔭
          obtain ⟨σ, _hσdec, hσeq⟩ := hΦdecompE A (hTfin A hAT) 𝔭 hAcomap a
          have h1 : (χE (θ (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite 𝔭) a))).toAdd =
              Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ := by
            have hθeq : θ (NK.GlobalCFT.Place.ofFinite 𝔭)
                (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                  (NK.GlobalCFT.Place.ofFinite 𝔭) a) =
                Φ_E (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
                  (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                    (NK.GlobalCFT.Place.ofFinite 𝔭) a)) := rfl
            rw [hθeq, ← hσeq, hχE σ]
            rfl
          have h2 : (χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
              (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite 𝔭) a)))).toAdd =
              Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ := by
            have htrans := Work.SSGRoute.N2v2.restrictNormalHom_artinMap_eq_of_le p K F E hFE
              Φ hΦker hΦfrob Φ_E hΦkerE hΦfrobE σ
              (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
                (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
                  (NK.GlobalCFT.Place.ofFinite 𝔭) a)) hσeq
            rw [← htrans, hχ σ]
            rfl
          rw [h1, h2]
        have hinj : Function.Injective
            (Multiplicative.toAdd : Multiplicative (ZMod p) → ZMod p) := fun _ _ h => h
        refine hinj ?_
        rw [Work.SSGRoute.GrunwaldEscapeCore.toAdd_prod_eq_sum p T', hsumF]
        rfl
    simpa using h1
  -- ## the Artin symbol of `𝔡` is a norm idèle class
  have hmem : NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a)
      ∈ Φ.ker := MonoidHom.mem_ker.mpr hPhi
  rw [hΦker] at hmem
  have hmap : (Idele.normImage ↥K ↥F ⊔ Idele.principalSubgroup ↥K).map
        (IdeleClassGroup.mk ↥K) = Idele.normClassSubgroup ↥K ↥F := by
    rw [Subgroup.map_sup]
    have h1 : (Idele.principalSubgroup ↥K).map (IdeleClassGroup.mk ↥K) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, Work.SSGRoute.ker_mk_eq_principal]
    rw [h1, sup_bot_eq]
    rfl
  have hmk : IdeleClassGroup.mk ↥K
      (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
      ∈ Idele.normClassSubgroup ↥K ↥F := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [← hFnorm]
  exact hmk

end Work.SSGRoute.N2v2
